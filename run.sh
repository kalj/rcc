#!/bin/bash
#
# @(#)run.sh
# @author Karl Ljungkvist <k.ljungkvist@gmail.com>

prog=$1

$prog
echo "result: $?"
