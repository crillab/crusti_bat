use anyhow::{Context, Result};
use crusti_app_helper::{debug, info, App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_bat::{
    AggregatorEncoding, CNFDimacsWriter, CNFFormula, DiscrepancyEncoding, DistanceEncoding,
    DrasticDistanceEncoding, ExternalMaxSatSolver, HammingDistanceEncoding, LexiAggregatorEncoding,
    MergingDimacsReader, RevisionDimacsReader, SumAggregatorEncoding, VarWeights, Weighted,
};
use std::{
    fmt::Display,
    fs::{self, File},
    io::{self, BufReader, BufWriter, Write},
    path::PathBuf,
};

const CMD_NAME_MERGING: &str = "belief-merging";
const CMD_NAME_REVISION: &str = "belief-revision";

const ARG_INPUT: &str = "ARG_INPUT";
const ARG_OUTPUT: &str = "ARG_OUTPUT";
const ARG_DISTANCE: &str = "ARG_DISTANCE";
const ARG_AGGREGATOR: &str = "ARG_AGGREGATOR";
const ARG_SOLVER: &str = "ARG_SOLVER";

#[derive(Default)]
pub(crate) struct BeliefMergingCommand;

impl<'a> Command<'a> for BeliefMergingCommand {
    fn name(&self) -> &str {
        CMD_NAME_MERGING
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        clap_subcommand_for(
            CMD_NAME_MERGING,
            "Merge belief bases",
            "the input file that contains the merging problem",
        )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let file_reader = create_input_file_reader(arg_matches)?;
        let input_data = MergingDimacsReader.read(file_reader)?;
        let (belief_bases, belief_bases_weights): (Vec<_>, Vec<_>) = input_data
            .belief_bases()
            .iter()
            .map(|w| (w.thing(), w.weight()))
            .unzip();
        let discrepancy_encoding =
            create_discrepancy_encoding(input_data.integrity_constraint(), &belief_bases);
        let var_weights_vec = std::iter::repeat(input_data.var_weights())
            .take(discrepancy_encoding.discrepancy_var_ranges().count())
            .collect::<Vec<_>>();
        let distance_encoding =
            create_distance_encoding(arg_matches, &discrepancy_encoding, var_weights_vec);
        let enforced_cnf = enforce_cnf(
            arg_matches,
            distance_encoding.as_ref(),
            &belief_bases_weights,
        )?;
        write_enforced_cnf(arg_matches, &enforced_cnf)
    }
}

#[derive(Default)]
pub(crate) struct BeliefRevisionCommand;

impl<'a> Command<'a> for BeliefRevisionCommand {
    fn name(&self) -> &str {
        CMD_NAME_REVISION
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        clap_subcommand_for(
            CMD_NAME_REVISION,
            "Revise a formula with another",
            "the input file that contains the revision problem",
        )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let file_reader = create_input_file_reader(arg_matches)?;
        let input_data = RevisionDimacsReader.read(file_reader)?;
        let discrepancy_encoding = create_discrepancy_encoding_repeated(
            input_data.revision_formula(),
            input_data.initial_base(),
            input_data.topics().len(),
        );
        let (topics_var_weights_vec, topics_weights): (Vec<_>, Vec<_>) = input_data
            .topics()
            .iter()
            .map(|t| {
                let mut var_weights = VarWeights::new(input_data.n_vars());
                t.thing()
                    .iter()
                    .for_each(|v| var_weights.add(Weighted::new(*v, 1)));
                (var_weights, t.weight())
            })
            .unzip();
        let distance_encoding = create_distance_encoding(
            arg_matches,
            &discrepancy_encoding,
            topics_var_weights_vec.iter().collect(),
        );
        let enforced_cnf = enforce_cnf(arg_matches, distance_encoding.as_ref(), &topics_weights)?;
        write_enforced_cnf(arg_matches, &enforced_cnf)
    }
}

fn create_input_file_reader(arg_matches: &ArgMatches<'_>) -> Result<BufReader<File>> {
    let input_file_canonicalized = realpath_from_arg(arg_matches, ARG_INPUT)?;
    info!("reading input file {:?}", input_file_canonicalized);
    Ok(BufReader::new(File::open(input_file_canonicalized)?))
}

fn create_discrepancy_encoding<'a>(
    prevalent: &'a CNFFormula,
    dominated: &'a [&CNFFormula],
) -> DiscrepancyEncoding<'a> {
    let discrepancy_encoding = DiscrepancyEncoding::new(prevalent, dominated);
    debug!(
        "discrepancy encoding with vars {}",
        format_var_ranges(
            discrepancy_encoding
                .discrepancy_var_ranges()
                .map(|r| (r.start, r.end - 1))
        )
    );
    discrepancy_encoding
}

fn create_discrepancy_encoding_repeated<'a>(
    prevalent: &'a CNFFormula,
    dominated: &'a CNFFormula,
    n: usize,
) -> DiscrepancyEncoding<'a> {
    let discrepancy_encoding = DiscrepancyEncoding::new_repeated(prevalent, dominated, n);
    debug!(
        "discrepancy encoding with vars {}",
        format_var_ranges(
            discrepancy_encoding
                .discrepancy_var_ranges()
                .map(|r| (r.start, r.end - 1))
        )
    );
    discrepancy_encoding
}

fn clap_subcommand_for<'a>(
    subcommand_name: &'static str,
    about: &'static str,
    arg_input_help: &'static str,
) -> App<'a, 'a> {
    SubCommand::with_name(subcommand_name)
        .about(about)
        .setting(AppSettings::DisableVersion)
        .arg(
            Arg::with_name(ARG_INPUT)
                .short("i")
                .long("input")
                .empty_values(false)
                .multiple(false)
                .help(arg_input_help)
                .required(true),
        )
        .arg(
            Arg::with_name(ARG_OUTPUT)
                .short("o")
                .long("output")
                .empty_values(false)
                .multiple(false)
                .help("outputs to a file instead of standard output"),
        )
        .arg(
            Arg::with_name(ARG_DISTANCE)
                .short("d")
                .long("distance")
                .empty_values(false)
                .multiple(false)
                .possible_values(&["drastic", "hamming"])
                .help("the metrics used for distances")
                .required(true),
        )
        .arg(
            Arg::with_name(ARG_AGGREGATOR)
                .short("a")
                .long("aggregator")
                .empty_values(false)
                .multiple(false)
                .possible_values(&["sum", "gmin", "gmax"])
                .help("the aggregator used for the distances")
                .required(true),
        )
        .arg(
            Arg::with_name(ARG_SOLVER)
                .short("s")
                .long("solver")
                .empty_values(false)
                .multiple(false)
                .help("the path to the MaxSAT solver")
                .required(true),
        )
        .arg(crusti_app_helper::logging_level_cli_arg())
}

fn enforce_cnf(
    arg_matches: &ArgMatches<'_>,
    distance_encoding: &dyn DistanceEncoding,
    distance_weights: &[usize],
) -> Result<CNFFormula> {
    let maxsat_solver = Box::new(ExternalMaxSatSolver::from(realpath_from_arg(
        arg_matches,
        ARG_SOLVER,
    )?));
    Ok(match arg_matches.value_of(ARG_AGGREGATOR).unwrap() {
        "sum" => enforce_cnf_with_aggregator(SumAggregatorEncoding::new(
            distance_encoding,
            distance_weights,
            maxsat_solver,
        ))?,
        "gmin" => enforce_cnf_with_aggregator(LexiAggregatorEncoding::new_for_leximin(
            distance_encoding,
            distance_weights,
            maxsat_solver,
        ))?,
        "gmax" => enforce_cnf_with_aggregator(LexiAggregatorEncoding::new_for_leximax(
            distance_encoding,
            distance_weights,
            maxsat_solver,
        ))?,
        _ => unreachable!(),
    })
}

fn enforce_cnf_with_aggregator<T, U>(mut aggregator_encoding: T) -> Result<CNFFormula>
where
    T: AggregatorEncoding<U>,
    U: Display,
{
    let optimum = aggregator_encoding
        .compute_optimum()
        .context("while computing the optimal value for the aggregation")?;
    info!("optimum is {}", optimum);
    Ok(aggregator_encoding.enforce_value(optimum))
}

fn write_enforced_cnf(arg_matches: &ArgMatches<'_>, enforced_cnf: &CNFFormula) -> Result<()> {
    let cnf_writer = CNFDimacsWriter;
    let (str_out, unbuffered_out): (String, Box<dyn Write>) = match arg_matches.value_of(ARG_OUTPUT)
    {
        None => ("standard output".to_string(), Box::new(io::stdout())),
        Some(path) => {
            let file = File::create(path).context("while creating the output file")?;
            let str_path = fs::canonicalize(PathBuf::from(path))
                .with_context(|| format!(r#"while opening file "{}""#, path))?;
            (format!("{:?}", str_path), Box::new(file))
        }
    };
    info!("writing enforced CNF to {}", str_out);
    cnf_writer.write(&mut BufWriter::new(unbuffered_out), enforced_cnf)
}

fn format_var_ranges(it: impl Iterator<Item = (usize, usize)>) -> String {
    it.fold(String::new(), |mut acc, x| {
        if !acc.is_empty() {
            acc.push_str(", ")
        }
        acc.push_str(&format!("[{}..={}]", x.0, x.1));
        acc
    })
}

fn realpath_from_arg(arg_matches: &ArgMatches<'_>, arg: &str) -> Result<PathBuf> {
    let file_path = arg_matches.value_of(arg).unwrap();
    fs::canonicalize(PathBuf::from(file_path))
        .with_context(|| format!(r#"while opening file "{}""#, file_path))
}

fn create_distance_encoding<'a>(
    arg_matches: &ArgMatches<'_>,
    discrepancy_encoding: &'a DiscrepancyEncoding,
    var_weights_vec: Vec<&'a VarWeights>,
) -> Box<dyn DistanceEncoding + 'a> {
    assert_eq!(
        discrepancy_encoding.discrepancy_var_ranges().count(),
        var_weights_vec.len()
    );
    let encoding: Box<dyn DistanceEncoding + 'a> = match arg_matches.value_of(ARG_DISTANCE).unwrap()
    {
        "drastic" => Box::new(DrasticDistanceEncoding::new(
            discrepancy_encoding,
            var_weights_vec,
        )),
        "hamming" => Box::new(HammingDistanceEncoding::new(
            discrepancy_encoding,
            var_weights_vec,
        )),
        _ => unreachable!(),
    };
    debug!(
        "distance encoding with vars {}",
        format_var_ranges(
            encoding
                .distance_vars()
                .iter()
                .map(|r| (r.start, r.end - 1))
        )
    );
    encoding
}
