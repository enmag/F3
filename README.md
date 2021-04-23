# F3 (FindFairFunnel)
F3 searches for fair paths in transition systems.    
F3 is capable of searching for counterexamples to LTL specification.    
F3 can discard all paths in which the sum of the assignments to some symbol does not diverge to infinity. This can be used to remove all zeno-paths in timed systems.

Upon success F3 will write on stdout the sequence of abstract regions and transition of the funnel-loop in a human readable format. For every loop the associated ranking function is provided. 

## Install in Docker image
Using docker and the `Dockerfile` it is possible to create a docker image with F3 installed from your local copy of this repository.   
Please be aware that the installation process downloads the SMT-solvers `mathsat` and `z3` and accepts their respective licences on your behalf. Do not proceed if you do not accept them.

Depending on your system-setup you might need to run the following commands as `sudo`.

From the root directory of the project run (the directory containing the file `Dockerfile`)
```shell
docker build --tag f3 ./
```
This creates a new docker image with tag `f3` based on the Ubuntu:20.04 image.    
The following command lists the docker images on your system. There should be one named `f3`.
```shell
docker images
```

The docker image contains all the benchmarks of this repository.   
To run F3 on the software nontermination benchmark `NonTerminationSimple2_false-termination` execute:
```shell
docker run f3 /home/F3/benchmarks/benchmarks/software_nontermination/f3/C/Ultimate/NonTerminationSimple2_false-termination.py
```

To run F3 on some benchmark not included in this repository using the docker image, create a shared directory between the docker container and your host system and place the benchmark in this directory.
For example to share the `/tmp` directory and execute a benchmark `/tmp/bench.py` run:
```shell
docker run -v /tmp:/tmp f3 /tmp/bench.py
```

Command line options for F3 can be appended after the image tag.
For example to run F3 with verbosity 1 on some benchmark `BENCHMARK` add the option `-v 1` as follows:
```shell
docker run f3 -v 1 $BENCHMARK
```

In general to tun F3 with options OPTS on benchmark BENCH run:
```shell
docker run f3 $OPTS $BENCH
```
If $BENCH is a directory instead of a single file, F3 will visit recursively all the subdirectories and try to load and execute every *.py file it finds.


## Manual install on host system
`INSTALL` contains the required information to install F3 on your system.


## Benchmarks
The directory benchmarks contains a collection of software (non)termination and LTL model checking problems.    
More details on the benchmarks are provided in `benchmarks/README`.   
The benchmarks are organised in the following categories:
* LS : linear software programs (directory `software_nontermination`),
* NS : non-linear software programs (directory `nonlinear_software`),
* ITS : LTL model checking on infinite state transition systems (directory `ltl_infinite_state`),
* TA : LTL model checking on timed automata (directory `ltl_timed_automata`)
* TTS : LTL model checking on timed transition systems (directory `ltl_timed_transition_system`)
* HS : LTL model checking on hybrid systems (directory `ltl_hybrid_system`)

Each directory contains the benchmarks in the input language of a number of tools including F3.


## F3 input files
F3 loads a Python source files as input.    
Such file should declare either a function `transition_system` or a function `check_ltl`.    
The first method is used to provide a fair transition system for which we want to find a fair path, the second one is used to provide a transition system and a LTL specification for which we want to find a counterexample.
Inputs that declare the `check_ltl` function can optionally define another function called `diverging_symbs`. Such function can be used to tell F3 which symbols of the system must diverge to infinity in the counterexample: the sum of all their assignments diverges to infinity.


## F3 command line options
Every command line option supported by F3 comes with a default value, hence you can "just run it" without specifying anything special.
Here we briefly describe the main command line options supported by F3.
* `-h, --help`: writes on stdout the list of available options and a description for each of them.
* `-v, --verbose`: control the amount of messages that F3 writes on stdout.
* `-motzkin, --use-motzkin`: enable/disable the use of Motzkin's transposition theorem for funnel synthesis.
* `-motzkin-rf, --use-motzkin-rf`: enable/disable the use of Motzkin's transposition theorem for ranking function synthesis.
* `-rf-motzkin-t, --synth-rf-motzkin-timeout`: set the timeout of the SMT-queries used to solve the Motzkin transpose problem.
* `-ef, --use-ef`: use EF-solve procedure for funnel synthesis.
* `-ef-rf, --use-ef-rf`: use EF-solve procedure for ranking function synthesis.
* `-learn-ef, --motzkin-learn-ef`: enable/disable carrying of statements learned in EF-solve to the Motzkin transpose problem.
* `-ef-t, --efsolver-timeout`: set the timeout of the SMT-queries in the EF-solve procedure.
* `-ef-its, --efsolver-iterations`: set the maximum number of iterations of the EF-solve procedure.
* `-approx-prec, --approx-precision`: set precision to be used to simplify EF-solve models.
* `-approx-max-val, --approx-max-val`: EF-solve model simplification will try and keep the constants below the given value.
* `-bmc-t, --bmc-timeout`: set the BMC SMT-query timeout.
* `-bmc-k, --bmc-length`: set maximum path length to be considered in the BMC unrolling.
* `-max-extend, --loop_extension_bound`: discard all candiate loop that cannot be exetended by the given factor.
* `-bool-impl, --use-bool-impl`: enable/disable boolean implicant computation.
* `-unsat-cores, --use-unsat-cores`: enable/disable usage of unsat-cores for implicant computation.
* `-merge-ineqs, --merge-ineqs`: enable/disable merging of inequalities `a >= b & b <= a` into `a = b`.
* `-s, --solvers`: set sequence of SMT-solvers to be used.
* `-min-ineqs, --min-inequalities`: set minimum number of inequalities to be synthesised for each funnel.
* `-max-ineqs, --max-inequalities`: set minimum number of inequalities to be synthesised for each funnel.
* `-propagate, --constr-propagate`: set mode of propagation of state inequalities through transition equalities.
* `-generalised-lasso, --generalised-lasso`: enable/disable detection of generalised lassos.
* `-smv-out, --smv-out`: write SMV model representing the funnel-loop in the given directory.
