#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	removes double spaces that are not leading white space

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="rremove_inner_double_space"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

function test_file {
  echo -n "TESTING "
  basename $1
  cp $1 /tmp/INP

  rm -rf /tmp/tmp_fileY
  while IFS='' read -r line
  do
#     echo "$line"
    echo "$line" | sed ':labelA;s/^\(.*[^ ] *\)[ \t][ \t]/\1 /g;t labelA' >> /tmp/tmp_fileY
  done </tmp/INP
  cp /tmp/tmp_fileY $1
}

# cp /tmp/test_inp.thy /tmp/test.thy
# test_file /tmp/test.thy
#
# exit

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

