#! /usr/bin/env bash

DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
NUM=$1

find $DIR -name "generate_*.py" -exec python3 -u -B {} $NUM \;
