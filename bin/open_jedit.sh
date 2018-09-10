#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	[desired_project_name]
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	option jedit to edit the project desired_project_name
#	if no desired_project_name has been provided the final project is used
#	if required the image of the previous project is created first

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="open_jedit"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

if [ "$1" = "continue" ]
then
    TARGET=$(ls $LOGDIR | sort | grep -v ".gz")
else
  if [ "$#" -gt "0" ]
  then
    TARGET=$(echo $1|sed 's/\///g')
  fi
fi
echo "[${SCRIPT_NAME}] target      = $TARGET"

echo "[${SCRIPT_NAME}] creating image if required"
bash create_image.sh $TARGET exclude
if [ "$?" -gt 0 ]
then
  echo "[${SCRIPT_NAME}] image creation failed"
  notify-send "[${SCRIPT_NAME}] done" -t 2000
  exit
fi
echo "[${SCRIPT_NAME}] image now exists"

touch ${TMP_DIR}/create_dependency_list
rm -f ${TMP_DIR}/create_dependency_list
bash create_dependency_list.sh ${TMP_DIR}/create_dependency_list ${TARGET}
if [ ! -f ${TMP_DIR}/create_dependency_list ]
then
  echo "[${SCRIPT_NAME}] dependency file not created"
  notify-send "[${SCRIPT_NAME}] done" -t 2000
  exit
fi
DEPENDENCIES=$(cat ${TMP_DIR}/create_dependency_list)
CMD_STRING=""
LAST_DEP="HOL"
BUTLAST_LAST_DEP="HOL"
BUTLAST_CMD_STRING=""
for i in $DEPENDENCIES
do
  BUTLAST_CMD_STRING=$CMD_STRING
#   echo "[${SCRIPT_NAME}] adding      = $i"
  if [ -z "$CMD_STRING" ]
  then
    CMD_STRING="-d ../$i"
  else
    CMD_STRING="$CMD_STRING -d ../$i"
  fi
  BUTLAST_LAST_DEP=$LAST_DEP
  LAST_DEP=$i
done

cd ../${TARGET}

CMD_STRING=$BUTLAST_CMD_STRING
LAST_DEP=$BUTLAST_LAST_DEP

echo "[${SCRIPT_NAME}] starting jedit :'( $(date)" 

${ISABELLE_BINARY} jedit -J -Xmx${ISABELLE_MEMORY} -d . -l $LAST_DEP $CMD_STRING *.thy
