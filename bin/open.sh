#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	desired_project: name or number of project to be opened
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	open jedit to edit the project desired_project
#	(if required, the image of the previous project is created first)

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="open"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

if [ "$#" = "0" ]
then
	nl -nrz -w2 -s: $LIST_OF_PROJECTS | grep -v "^#"
	
	echo "choose number or project name as argument"
	exit
fi

PRJ=$1
if [ $(echo $1 | sed -n '/^[0-9]*$/p'| wc -l) -gt "0" ]
then
    echo "[${SCRIPT_NAME}] converting from number to project"
    PRJ=$(cat $LIST_OF_PROJECTS | grep -v "^#" | nl -nrz -w2 -s: | grep "^$1" | cut -c 4-)
fi
if [ $(cat $LIST_OF_PROJECTS | grep -v "^#" | grep PRJ | sed -n '/^'$PRJ'$/p' | wc -l) -eq "0" ]
then
	echo "[${SCRIPT_NAME}] obtained project $PRJ from input $1 but this project does not exist"
	exit
fi

echo "[${SCRIPT_NAME}] opening project $PRJ"
echo "[${SCRIPT_NAME}] executing>> bash open_jedit.sh $PRJ"

bash open_jedit.sh $PRJ
