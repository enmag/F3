# F3 (FindFairFunnel)
F3 searches for fair paths in transition systems.
F3 is capable of searching for counterexamples to LTL specification.
F3 can discard all paths in which the sum of the assignments to some symbol does not diverge to infinity. This can be used to remove all zeno-paths in timed systems.

Upon success F3 will write on stdout the sequence of regions and transitions of the funnel-loop in a human readable format. For every loop the associated ranking function is provided.


## Install in Docker image
Using docker and the `Dockerfile` it is possible to create a docker image with F3 installed from your local copy of this repository.
The file `INSTALL_DOCKER` details the commands that can be used to build the Docker image and to execute it.


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
F3 loads a Python source file as input.
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
* `-min-core', --minimal-core`: requires enabled unsat-cores, enable/disable computation of minimal unsat core.
* `-merge-ineqs, --merge-ineqs`: enable/disable merging of inequalities `a >= b & b <= a` into `a = b`.
* `-s, --solvers`: set sequence of SMT-solvers to be used.
* `-min-ineqs, --min-inequalities`: set minimum number of inequalities to be synthesised for each funnel.
* `-max-ineqs, --max-inequalities`: set minimum number of inequalities to be synthesised for each funnel.
* `-propagate, --constr-propagate`: set mode of propagation of state inequalities through transition equalities.
* `-generalised-lasso, --generalised-lasso`: enable/disable detection of generalised lassos.
* `-det-div, --deterministic-diverging-monitor`: enable/disable deterministic reset of diverging symbol monitor.
* `-smv-out, --smv-out`: write SMV model representing the funnel-loop in the given directory.


## F3 output
On success F3 prints on stdout a description of the counterexample it found.
The counterexample is a sequence of states and transitions between them.
The following example describes a path that starts from a state in which pc = 0 and x = 0 in State 0.
Then it loops over the first two states while `x + 3/4 < 0` executing transitions 0 -- 1 and 1 -- 0.
Finally, it reaches the destination `State 1`, reported after the `End do-while`.
From such state it follows transition 1 -- 2, where with 2 means State 0 at the next iteration.
Hence, the path reaches State 0 again (possibly with a different assignment) and executes the same steps.
```
Do states 0..1 while ((ToReal(x) + 3/4) < 0.0)
State 0
	pc = 0
	((-1 * x) <= 0)
Trans 0 -- 1
	_x_x : x
State 1
	pc = 1
Trans 1 -- 0
	_x_x : (x + 1)
End do-while
State 1
	pc = 1
	(((-1.0 * ToReal(x)) + -3/4) <= 0.0)
	((-1 * x) <= 1)
Trans 1 -- 2
	_x_x = (x + 1)
starting from: {pc: 0, x: 0}
```
By default F3 does not print any information about the search and simply prints the end result when it finds one.
By increasing the verbosity (option `-v`) it is possible to obtain more information about the funnel-loop templates, the solver that are being used etc.


## Generating the plots
The directory `expeval_output` contains the outputs obtained by executing of F3 and other tools on the benchmarks contained in the `benchmarks` directory.
The `script` directory contains 2 python scripts that can be used to parse and plot such outputs.
Please, refer to the file `GENERATE_PLOTS` for a more detailed description of the commands that can be used to generate such plots.
