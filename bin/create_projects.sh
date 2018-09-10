#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	establishes the project hierarchy mentioned in LIST_OF_PROJECTS file
# 	- creates project directories
# 	- creates ROOT files
# 	- creates _ENTRY and _EXIT theory files
# 		- _EXIT theory file has /all/ theories as import

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="create_projects"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

echo "[$SCRIPT_NAME] WARNING: do you know what you are doing? Y/N"
read ANSWER
if [ ! "$ANSWER" = "Y" ]
then
    echo "[$SCRIPT_NAME] aborting."
    exit
fi

function my_generate {
  LAST_PROJECT="HOL"
  LAST_PROJECT_FILE="Main"

  echo "(1) removing old ENTRY"
  for i in `find .. | grep __ENTRY.thy$`
  do
     echo $i
    #svn rm --force $i
  done

  echo "(2) removing old EXIT"
  for i in `find .. | grep __EXIT.thy$`
  do
     echo $i
    #svn rm --force $i
  done
#   exit
  echo "(3) creating projects"
  for project in `cat ${LIST_OF_PROJECTS} | grep -v "^#"`
  do
    if [ -z ${project} ]
    then
      echo "empty"
      exit
    fi
    echo ${project}
    mkdir ../${project}
    mkdir ../${project}/document
    cat ../config/root.tex | sed 's:\\title{Test}:\\title{'"$(echo ${project} | sed 's/__/ /g' | sed 's/_/-/g')"'}:g' > ../${project}/document/root.tex
    FILE="../${project}/ROOT"
    rm -rf ${FILE}
    touch ${FILE}
    echo "session \"${project}\" = \"${LAST_PROJECT}\" +" >> ${FILE}
    echo "  options [document = pdf, document_output = \"output\", document_variants=\"document:outline=/proof,/ML\"]" >> ${FILE}      
    #echo "  options [document = false]" >> ${FILE}
    echo "  theories" >> ${FILE}
    echo "    ${project}__EXIT" >> ${FILE}
    echo "  document_files \"root.tex\"" >> ${FILE}

    stat ${FILE}

    FILE="../${project}/${project}__ENTRY.thy"
    rm -rf ${FILE}
    touch ${FILE}
    echo "theory  ${project}__ENTRY" >> ${FILE}
    echo "imports" >> ${FILE}
    if [ "${LAST_PROJECT}" = "HOL" ]
    then
        echo "  ${LAST_PROJECT_FILE}" >> ${FILE}
    else
        echo "  ${LAST_PROJECT}.${LAST_PROJECT_FILE}" >> ${FILE}
    fi    
    echo "begin" >> ${FILE}
    echo "(*automatically created; do not modify*)" >> ${FILE}
    echo "end" >> ${FILE}

    FILE="../${project}/${project}__EXIT.thy"
    rm -rf ${FILE}
    touch ${FILE}
    echo "theory  ${project}__EXIT" >> ${FILE}
    echo "imports" >> ${FILE}
    for theory_file in `ls ../${project}/*.thy | sort -u | sed 's/\.thy$//g'`
    do
      theory_file=$(basename $theory_file)
#       if [ "$theory_file" = "${project}__ENTRY" ]
#       then
# 	continue;
#       fi
      if [ "$theory_file" = "${project}__EXIT" ]
      then
	continue;
      fi
      if [ "$theory_file" = "test" ]
      then
	continue;
      fi
      if [ "$theory_file" = "unused" ]
      then
	continue;
      fi
      echo "  ${theory_file}" >> ${FILE}
    done

    for theory_file in `ls ../${project}/*.thy | sort -u | sed 's/\.thy$//g'`
    do
      sed -i.bak -e's/^  .*__ENTRY/'"  ${project}__ENTRY"'/g' ${theory_file}.thy
#       exit
    done

    echo "begin" >> ${FILE}
    echo "(*automatically created; do not modify*)" >> ${FILE}
    echo "end" >> ${FILE}

    LAST_PROJECT=${project}
    LAST_PROJECT_FILE=${project}__EXIT
  done
}

my_generate
