#! /usr/bin/env bash

swig -python -c++ -v -Isrc -features autodoc -o ltl_wrap.cxx ltl.i
g++ -g -c -fPIC -Wall -std=c++17 ltl_wrap.cxx ltl.cpp ts.cpp utils.cpp $(python3-config --cflags) -lpython3 -lmathsat -lgmp -lgmpxx
g++ -g -shared -fPIC -ldl -Wall -std=c++17 ltl_wrap.o ltl.o ts.o utils.o $(python3-config --ldflags) -o _ltl.so -lmathsat -lgmp -lgmpxx
