#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	creates formalization.tar.bz2 containing all current files

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="package"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

echo "[$SCRIPT_NAME] WARNING: also packaging temporary and configuration files"

cd ..
rm formalization.tar.bz2

base=$(basename $PWD)
cd ..
tar -cjvf formalization.tar.bz2 $base
mv formalization.tar.bz2 $base

