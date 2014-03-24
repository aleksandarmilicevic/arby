#!/bin/bash

for N in 2 3 4; do
  for C in 2 1 0; do
    for F in no yes; do
      export N=$N C=$C F=$F && timeout 1000 ./run_tests.sh test/unit/arby/model/synth/array_search_test.rb -ntest_search
    done
  done
done


for F in no yes; do
  export N=5 C=2 F=$F && timeout 1000 ./run_tests.sh test/unit/arby/model/synth/array_search_test.rb -ntest_search
done
