#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	computes main document.pdf
#	computes main outline.pdf

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="full_document_outline"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

function my_generate_MAIN_SESSION(){
  rm ../output/document/session.tex
  rm ../output/outline/session.tex
  for project in `cat ${LIST_OF_PROJECTS} | grep -v "^#"`
  do
    if [ -z ${project} ]
    then
      echo "empty"
      exit
    fi
    mkdir -p ../output/document
    mkdir -p ../output/outline
    echo ${project}
    echo "\chapter{$(echo ${project} | sed 's/_/\\_/g')}" >> ../output/document/session.tex
    echo "\chapter{$(echo ${project} | sed 's/_/\\_/g')}" >> ../output/outline/session.tex
    cat ../${project}/output/document/session.tex | sed 's/{/\{..\/..\/'${project}'\/output\/document\//g' >> ../output/document/session.tex
    cat ../${project}/output/outline/session.tex | sed 's/{/\{..\/..\/'${project}'\/output\/outline\//g' >> ../output/outline/session.tex
    
  done
    
}

echo "[${SCRIPT_NAME}] BEGIN: generating the two session files by collecting the tex files from the projects"
my_generate_MAIN_SESSION
echo "[${SCRIPT_NAME}] END: generating the two session files by collecting the tex files from the projects"



cd ../output

echo "[${SCRIPT_NAME}] BEGIN: building document"
cd document
pdflatex root.tex
pdflatex root.tex
cp root.pdf ../document.pdf
cd ..
echo "[${SCRIPT_NAME}] END: building document"

echo "[${SCRIPT_NAME}] BEGIN: building outline"
cd outline
pdflatex root.tex
pdflatex root.tex
cp root.pdf ../outline.pdf
cd ..
echo "[${SCRIPT_NAME}] END: building outline"
