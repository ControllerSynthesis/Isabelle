#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	[desired_project_name]
# 	[exclude]
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	creates (if possible) the image for project desired_project_name
#	if no desired_project_name has been provided the final image is used
# 	if exclude is provided, only the dependencies are created

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="create_image"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

if [ "$#" -gt "0" ]
then
  TARGET=$(echo $1|sed 's/\///g')
fi
shift
EXCLUDE=0
if [ "$#" -gt "0" ]
then
  EXCLUDE=1
fi

echo "[${SCRIPT_NAME}] target = $TARGET"

touch ${TMP_DIR}/create_dependency_list
rm -f ${TMP_DIR}/create_dependency_list
bash create_dependency_list.sh ${TMP_DIR}/create_dependency_list ${TARGET}
if [ ! -f ${TMP_DIR}/create_dependency_list ]
then
  echo "[${SCRIPT_NAME}] dependency file not created"
  exit
fi
DEPENDENCIES=$(cat ${TMP_DIR}/create_dependency_list)
CMD_STRING=""
BUTLAST_CMD_STRING=""
for i in $DEPENDENCIES
do
  BUTLAST_CMD_STRING=${CMD_STRING}
  if [ -z "$CMD_STRING" ]
  then
    CMD_STRING="-D $i"
  else
    CMD_STRING="$CMD_STRING -D $i"
  fi
done

if [ "$EXCLUDE" = "1" ]
then
  CMD_STRING="$BUTLAST_CMD_STRING"
fi
cd ..

# echo "[${SCRIPT_NAME}] executing isabelle ${CMD_STRING}
echo "[${SCRIPT_NAME}] isabelle begin time is $(date)"
${ISABELLE_BINARY} build -b $CMD_STRING
RESULT=$?
echo "[${SCRIPT_NAME}] isabelle done time is $(date)"
exit $RESULT
