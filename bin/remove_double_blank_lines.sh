#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	removes double blank lines

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="remove_double_blank_lines"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

function test_file {
  echo -n "TESTING "
  basename $1
  cp $1 /tmp/INP
  cat -s /tmp/INP > $1
}

cd ..

find . | grep "thy$" | sort > /tmp/FILES

MAX=$(cat /tmp/FILES|wc -l)
CUR=0

while read file
do
  let CUR++;
  echo "$CUR/$MAX"
  test_file "$file"
done < /tmp/FILES

