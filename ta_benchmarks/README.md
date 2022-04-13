This directory contains a collection of Invariant, LTL and MTL model checking problems on Timed Automata.
The benchmarks are organised in the following categories:
* TINV: true invariant properties,
* FINV: false invariant properties,
* TLTL: true LTL properties,
* FLTL: false LTL properties,
* TMTL: true MTL properties,
* FMTL: false MTL properties.

Each benchmark is written in the input language of a number of different tools.

The benchmarks have been taken from [1], which provides a collection of timed automata from different sources, and from Uppaal website [2].
We considered the models for the following protocols:
* `critical-region` contains the protocol with the same name taken from [2].
* `csma-cd` contains models of the Carrier-sense multiple access with collision detection protocol [1].
* `fddi` contains models of the Token-Ring FDDI protocol [1].
* `fischer` contains models of the Fischer mutual exclusion protocol [1].
* `lynch` contains models of the Lynch mutual exclusion protocol [1].
* `train` contains models describing the interaction between trains and a gate [1].
For each of them we wrote a true and a false property for each of the 3 specification languages (invariant, LTL and MTL).
The script `generate_all.sh` calls a number of python script that generate the benchmarks for an increasing number of processes.


[1] https://github.com/farkasrebus/XtaBenchmarkSuite
[2] https://uppaal.org/benchmarks/