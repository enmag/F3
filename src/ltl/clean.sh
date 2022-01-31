#! /usr/bin/env bash

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
rm -rf $SCRIPT_DIR/__pycache__ $SCRIPT_DIR/*.o $SCRIPT_DIR/*.so $SCRIPT_DIR/*.pyc $SCRIPT_DIR/ltl.py $SCRIPT_DIR/*wrap.*
