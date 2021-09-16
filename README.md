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
* `-h`, `--help`: print on stdout usage and command line options.
* `-approx-prec`, `--approx-precision`: set precision of approximation of rational values to simplify constants in models.
* `-approx-max-val`, `--approx-max-val`: try to keep constants below given number.
* `-bmc-t`, `--bmc-timeout`: set timeout for each BMC SMT query.
* `-bmc-k`, `--bmc-length`: set max BMC unrolling, 0 or negative for unbounded.
* `-h-mode`, `--hint-mode`: type of hint choice encoding; 0: may enable; 1: must enable at least 1; 2: must enable all.
* `-ef-t`, `--efsolver-timeout`: set timeout for each SMT query in EF-solver.
* `-ef-its`, `--efsolver-iterations`: set max number of iteration in EF-solver.
* `-ef-approx`, `--ef-approx-model`: enable/disable simplification of constants in EF-models.
* `-motzkin`, `--use-motzkin`: enable/disable motzkin transposition to solve EF quantified queries.
* `-motzkin-t`, `--motzkin-timeout`: set timeout for each Motzkin-generated SMT query.
* `-fun-learn-ef`, `--fun-learn-ef`: add constraints learned by EF-solver to motzkin SMT-query in Funnel synthesis.
* `-ef`, `--use-ef`: enable/disable EF-solver for EF quantified queries.
* `-min-ineqs`, `--min-inequalities`: set minimum number of inequalities in nontermination argument.
* `-max-ineqs`, `--max-inequalities`: set max number of inequalities in nontermination argument.
* `-propagate`, `--propagate-mode`: set predicate propagation mode inFunnels 0: no; 1: partial; 2: full.
* `-propagate-max-it`, `--propagate-max-iterations`: set max number of backward propagations.
* `-bool-impl`, `--use-bool-impl`: enable/disable model-based boolean implicant.
* `-unsat-cores`, `--use-unsat-cores`: enable/disable unsat-cores to compute implicant.
* `-min-core`, `--minimal-core`: shrink unsat-core to obtain a minimal one w.r.t inequalities.
* `-merge-ineqs`, `--merge-ineqs`: merge a <= b & b >= a into a = b in implicant computation.
* `-rf-motzkin-t`, `--synth-rf-motzkin-timeout`: set timeout for Motzkin SMT queries for RF synthesis.
* `-motzkin-rf`, `--use-motzkin-rf`: enable/disable motzkin transposition to solve EF quantified queries for ranking function.
* `-rank-approx`, `--rank-approx-model`: enable/disable parameter assignment simplification for ranking functions.
* `-rf-learn-ef`, `--rf-learn-ef`: enable/disable addition of constraints learned by EF-solver to motzkin SMT-query in Ranking Function synthesis.
* `-ef-rf`, `--use-ef-rf`: enable/disable EF-solver for EF quantified queries for Ranking Funciton.
* `-v`, `--verbose`: set verbosity level.
* `-s`, `--solvers`: set list of available solvers, see `pysmt-install --check`.
* `-generalised-lasso`, `--generalised-lasso`: enable/disable detection of generalised lasso using pattern described in Timed-nuXmv paper CAV 2019.
* `-det-div`, `--deterministic-diverging-monitor`: 1: use deterministic diverging monitor, 0: use nondeterministic reset for diverging monitor.
* `-smv-out`, `--smv-out`: write smv representation of nontermination argument in the given directory.
* `-check-h`, `--check-hints`: 1: check hints correctness, 0: assume hints are correct.


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
Please, refer to the file `GENERATE_PLOTS` for a more detailed description of the commands that can be used to generate such plots.
