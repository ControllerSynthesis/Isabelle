#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
#	OUT_FILE
# 	[desired_project_name]
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	creates a list of all projects the provided theory depends on
#	if desired_project_name is not provided the final image is used instead
#	stores the list of dependencies in OUT_FILE

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="create_dependency_list"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

PORJECTS=$(cat ${LIST_OF_PROJECTS} | grep -v "^#")
TARGET=$(echo $PORJECTS|sed 's/^.* \([^ ]*\)$/\1/g')
echo "[${SCRIPT_NAME}] final image = $TARGET"
if [ "$#" = "0" ]
then
  echo "[${SCRIPT_NAME}] no OUT_FILE provided"
  exit
fi
OUT_FILE=$1
echo "[${SCRIPT_NAME}] OUT_FILE = ${OUT_FILE}"

shift
if [ "$#" -gt "0" ]
then
  TARGET=$(echo $1|sed 's/\///g')
fi
echo "[${SCRIPT_NAME}] target = $TARGET"

function compatible {
  if [ "$1" = "$2" ]
  then
    echo 1
  else
    if [ $(echo $1 | sed -n '/'$2'/p'| wc -l) -gt 0 ]
    then
      echo 1
    else
      echo 0
    fi
  fi
}

DEP=""
for i in $PORJECTS
do
  if [ -z "$DEP" ]
  then
    DEP="$i"
  else
    DEP="$DEP $i"
  fi
  RES=$(compatible $i $TARGET)
  if [ "$RES" = "1" ]
  then
    echo "[${SCRIPT_NAME}] done"
    break
  fi
done

echo "[${SCRIPT_NAME}] writing file"
echo $DEP > $OUT_FILE
