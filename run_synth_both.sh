#!/bin/bash

./run_synth_max_bench.sh | tee synth_max_res.2.txt

./run_synth_array_search_bench.rb  | tee synth_arr_res.2.txt