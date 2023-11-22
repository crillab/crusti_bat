use anyhow::{Context, Result};
use crusti_app_helper::{debug, info, App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_bat::{
    AggregatorEncoding, CNFDimacsWriter, DiscrepancyEncoding, DistanceEncoding,
    DrasticDistanceEncoding, ExternalMaxSatSolver, HammingDistanceEncoding, LexiAggregatorEncoding,
    MergingDimacsReader, SumAggregatorEncoding, VarWeights,
};
use std::{
    fs::{self, File},
    io::{self, BufReader, BufWriter, Write},
    path::PathBuf,
};

const CMD_NAME: &str = "belief-merging";

const ARG_INPUT: &str = "ARG_INPUT";
const ARG_OUTPUT: &str = "ARG_OUTPUT";
const ARG_DISTANCE: &str = "ARG_DISTANCE";
const ARG_AGGREGATOR: &str = "ARG_AGGREGATOR";
const ARG_SOLVER: &str = "ARG_SOLVER";

#[derive(Default)]
pub(crate) struct BeliefMergingCommand;

impl<'a> Command<'a> for BeliefMergingCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Merge belief bases")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name(ARG_INPUT)
                    .short("i")
                    .long("input")
                    .empty_values(false)
                    .multiple(false)
                    .help("the input file that contains the formulas to merge")
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

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let reader = MergingDimacsReader;
        let input_file_canonicalized = realpath_from_arg(arg_matches, ARG_INPUT)?;
        info!("reading input file {:?}", input_file_canonicalized);
        let file_reader = BufReader::new(File::open(input_file_canonicalized)?);
        let input_data = reader.read(file_reader)?;
        let (belief_bases, belief_bases_weights): (Vec<_>, Vec<_>) = input_data
            .belief_bases()
            .iter()
            .map(|w| (w.thing(), w.weight()))
            .unzip();
        let discrepancy_encoding =
            DiscrepancyEncoding::new(input_data.integrity_constraint(), &belief_bases);
        debug!(
            "discrepancy encoding with vars {}",
            format_var_ranges(
                discrepancy_encoding
                    .discrepancy_var_ranges()
                    .map(|r| (r.start, r.end - 1))
            )
        );
        let distance_encoding =
            create_distance_encoding(arg_matches, &discrepancy_encoding, input_data.var_weights());
        debug!(
            "distance encoding with vars {}",
            format_var_ranges(
                distance_encoding
                    .distance_vars()
                    .iter()
                    .map(|r| (r.start, r.end - 1))
            )
        );
        let maxsat_solver = Box::new(ExternalMaxSatSolver::from(realpath_from_arg(
            arg_matches,
            ARG_SOLVER,
        )?));
        let enforced_cnf = match arg_matches.value_of(ARG_AGGREGATOR).unwrap() {
            "sum" => {
                let mut sum_aggregator_encoding = SumAggregatorEncoding::new(
                    distance_encoding.as_ref(),
                    &belief_bases_weights,
                    maxsat_solver,
                );
                let optimum = sum_aggregator_encoding
                    .compute_optimum()
                    .context("while computing the optimal value for the aggregation")?;
                info!("optimum is {}", optimum);
                sum_aggregator_encoding.enforce_value(optimum)
            }
            "gmin" => {
                let mut gmax_aggregator = LexiAggregatorEncoding::new_for_leximin(
                    distance_encoding.as_ref(),
                    &belief_bases_weights,
                    maxsat_solver,
                );
                let optimum = gmax_aggregator
                    .compute_optimum()
                    .context("while computing the optimal value for the aggregation")?;
                info!("optimum is {}", optimum);
                gmax_aggregator.enforce_value(optimum)
            }
            "gmax" => {
                let mut gmax_aggregator = LexiAggregatorEncoding::new_for_leximax(
                    distance_encoding.as_ref(),
                    &belief_bases_weights,
                    maxsat_solver,
                );
                let optimum = gmax_aggregator
                    .compute_optimum()
                    .context("while computing the optimal value for the aggregation")?;
                info!("optimum is {}", optimum);
                gmax_aggregator.enforce_value(optimum)
            }
            _ => unreachable!(),
        };
        let cnf_writer = CNFDimacsWriter;
        let (str_out, unbuffered_out): (String, Box<dyn Write>) =
            match arg_matches.value_of(ARG_OUTPUT) {
                None => ("standard output".to_string(), Box::new(io::stdout())),
                Some(path) => {
                    let file = File::create(path).context("while creating the output file")?;
                    let str_path = fs::canonicalize(PathBuf::from(path))
                        .with_context(|| format!(r#"while opening file "{}""#, path))?;
                    (format!("{:?}", str_path), Box::new(file))
                }
            };
        info!("writing enforced CNF to {}", str_out);
        cnf_writer.write(&mut BufWriter::new(unbuffered_out), &enforced_cnf)
    }
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
    var_weights: &'a VarWeights,
) -> Box<dyn DistanceEncoding + 'a> {
    match arg_matches.value_of(ARG_DISTANCE).unwrap() {
        "drastic" => Box::new(DrasticDistanceEncoding::new(
            discrepancy_encoding,
            var_weights,
        )),
        "hamming" => Box::new(HammingDistanceEncoding::new(
            discrepancy_encoding,
            var_weights,
        )),
        _ => unreachable!(),
    }
}
