#!/bin/bash

for N in 2 3 4 5 6 7; do
  for C in 2 1 0; do
    for F in no yes; do
      export N=$N C=$C F=$F && timeout 1000 ./run_tests.sh test/unit/arby/model/synth/max_test.rb -ntest_max
    done
  done
done

export N=8 C=2 F=no && timeout 1500 ./run_tests.sh test/unit/arby/model/synth/max_test.rb -ntest_max

export N=8 C=2 F=yes && timeout 1500 ./run_tests.sh test/unit/arby/model/synth/max_test.rb -ntest_max