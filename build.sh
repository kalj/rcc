#!/bin/bash
#
# @(#)build.sh
# @author Karl Ljungkvist <k.ljungkvist@gmail.com>

set -e

BITS=32

if [ $1 == -64 ] ; then
    BITS=64
    shift
elif [ $1 == -32 ] ; then
    BITS=32
    shift
fi

if [ $BITS == 32 ] ; then
    ARCH=i386
    DYNAMIC_LINKER="/lib/ld-linux.so.2"
elif [ $BITS == 64 ] ; then
    ARCH=x86_64
    DYNAMIC_LINKER="/lib64/ld-linux-x86-64.so.2"
fi


repo_root=$(dirname $0)

CC=${repo_root}/target/debug/rcc

source_file=$1
prog_name=${source_file%.c}
assembly_file=${prog_name}.s
object_file=${prog_name}.o

LIB_DIR="/usr/lib/${ARCH}-linux-gnu"
LINK_FLAGS="-m elf_${ARCH} -dynamic-linker ${DYNAMIC_LINKER} ${LIB_DIR}/Scrt1.o ${LIB_DIR}/crti.o ${LIB_DIR}/crtn.o -lc"

#echo "Compiling ${source_file} -> ${assembly_file}"
BITSFLAG=""
if [ $BITS == 32 ] ; then
    BITSFLAG="--32"
fi
${CC} ${BITSFLAG} -o $assembly_file $source_file

#echo "Assembling ${assembly_file} -> ${object_file}"
as --${BITS} -o $object_file $assembly_file

#echo "Linking ${object_file} -> ${prog_name}"
ld ${LINK_FLAGS} -o $prog_name $object_file
