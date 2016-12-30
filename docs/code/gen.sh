#!/bin/bash

f=$1

if [[ -z $f ]]; then
  f="sudoku-1"
fi

pygmentize -l ruby193 -f html -o $f.html $f; 
echo '<!DOCTYPE html><html><head><link rel="stylesheet" type="text/css" href="../css/github.css"/></head><body>' > tmp.html
cat $f.html >> tmp.html
echo "</body></html>" >> tmp.html