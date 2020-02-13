#!/bin/bash
#
# @(#)build.sh
# @author Karl Ljungkvist <k.ljungkvist@gmail.com>

repo_root=$(dirname $0)

CC=${repo_root}/target/debug/rcc

source_file=$1
prog_name=${source_file%.c}
assembly_file=${prog_name}.s
object_file=${prog_name}.o

LINK_FLAGS="-dynamic-linker /lib64/ld-linux-x86-64.so.2 /usr/lib/x86_64-linux-gnu/Scrt1.o /usr/lib/x86_64-linux-gnu/crti.o  /usr/lib/x86_64-linux-gnu/crtn.o -lc"

#echo "Compiling ${source_file} -> ${assembly_file}"
${CC} -o $assembly_file $source_file

#echo "Assembling ${assembly_file} -> ${object_file}"
as -o $object_file $assembly_file

#echo "Linking ${object_file} -> ${prog_name}"
ld ${LINK_FLAGS} -o $prog_name $object_file
