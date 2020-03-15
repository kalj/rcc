#!/bin/bash

test_stages=$(echo {1..10} extraops void )


cd wacc
./test_compiler.sh ../build.sh $test_stages

res=$?

if [ $res -ne 0 ] ; then
    echo "TEST FAILED"
    exit 1
else
    echo "TEST PASSED"
    exit 0
fi
