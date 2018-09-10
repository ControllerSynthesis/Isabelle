#!/bin/bash

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    CYGWIN*)    machine=Cygwin;;
    MINGW*)     machine=MinGw;;
    *)          machine="UNKNOWN:${unameOut}"
esac
echo "config/config.sh: detected ${machine}"

if [ ${machine} = "Linux" ]
then
    ISABELLE_BINARY=~/Downloads/Isabelle2018/bin/isabelle
    LOGDIR=~/.isabelle/Isabelle2018/heaps/polyml-5.7.1_x86-linux/log
    ISABELLE_MEMORY=7000m
elif [ ${machine} = "Cygwin" ]
then
    ISABELLE_BINARY=~/Downloads/Isabelle2018/bin/isabelle
    LOGDIR=~/.isabelle/Isabelle2018/heaps/polyml-5.7.1_x86-windows/log
    ISABELLE_MEMORY=15000m
elif [ ${machine} = "Mac" ]
then
    ISABELLE_BINARY=/Applications/Isabelle2018.app/Isabelle/bin/isabelle
    LOGDIR=~/.isabelle/Isabelle2018/heaps/polyml-5.7.1_x86-mac/log
    ISABELLE_MEMORY=7000m
else
    echo "config/config.sh: unknown system"
    exit
fi

which pdflatex
if [ "$?" = "1" ]
then
    echo "config/config.sh: pdflatex not available?"
    exit
fi

if [ ! -f ${ISABELLE_BINARY} ]
then
    echo "config/config.sh: ISABELLE_BINARY=${ISABELLE_BINARY} is not set properly"
    exit
fi

echo "config/config.sh: using ISABELLE_BINARY=${ISABELLE_BINARY}"
echo "config/config.sh: using LOGDIR=${LOGDIR}"
echo "config/config.sh: using ISABELLE_MEMORY=${ISABELLE_MEMORY}"

