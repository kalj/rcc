#!/bin/bash

test_stages=$(echo k {1..8})


cd wacc
output=$(./test_compiler.sh ../build.sh $test_stages)

res=$?

echo "$output"  | fgrep -v '....OK'

if [ $res -ne 0 ] ; then
    echo "TEST FAILED"
    exit 1
else
    echo "TEST PASSED"
    exit 0
fi
