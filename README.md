# crusti_bat

A Belief Aggregation Tool.

This project is a new implementation of two existing tools dedicated to belief bases, one dedicated to belief merging ([bm2cnf](http://www.cril.univ-artois.fr/kc/bm2cnf.html)) and one to belief revision ([br2cnf](http://www.cril.univ-artois.fr/kc/br2cnf.html)).

## Compiling/installing crusti_bat

Crusti_bat requires a recent version of the Rust toolchain (>= 1.66.1).
See [rust-lang.org](https://www.rust-lang.org/tools/install) for more information on how to install Rust.

You can install the latest release from `crates.io` with `cargo install crusti_bat` (or update it with `cargo install crusti_bat --force`).
To build from source, run `cargo build --release` to compile the binary. It will be set in the `target/release` directory.

## How to use

The crusti_bat tool expects a subcommand.
To get the list, just invoke the command with the help flag.

```
crusti_bat -h
```

In the same way, you can obtain the list of expected and optional arguments by adding the help flag after the subcommand.

```
crusti_bat belief-revision -h
```

The input formats for the `belief-merging` and the `belief-revision` commands follow the ones described on the webpages describing [bm2cnf](http://www.cril.univ-artois.fr/kc/bm2cnf.html) and [br2cnf](http://www.cril.univ-artois.fr/kc/br2cnf.html).
Both commands require a MaxSAT solver. At this time, none are provided with the library.
Some can be found for example [on the MaxSAT Evaluation website](https://maxsat-evaluations.github.io/2023/).
The external MaxSAT solvers must follow the requirements of the MaxSAT Evaluation 2023.

The `belief-merging` and the `belief-revision` commands share most of their options.
Here some some example of use.

Merge the belief bases described in `merging_instance.cnfs` using the hamming distance, the sum aggregator, the `cashwmaxsatcoreplus` MaxSAT solver, and write the result to `enforced.cnf`.

```
crusti_bat belief-merging -i merging_instance.cnfs -d hamming -a sum -s cashwmaxsatcoreplus -o enforced.cnf
```

Solve the revision problem described in `revision_instance.cnfs` using the drastic distance, the leximax aggregator, the `cashwmaxsatcoreplus` MaxSAT solver, and write the result to the standard output.
Log messages are deactivated.

```
crusti_bat belief-revision -i revision_instance.cnfs -d drastic -a gmax -s cashwmaxsatcoreplus --logging-level off
```

## License

crusti_bat is developed at CRIL (Univ. Artois & CNRS).
It is made available under the terms of the GNU GPLv3 license.