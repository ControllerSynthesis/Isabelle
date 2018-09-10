#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	determines lemmas, theorems, corollaries with identical name 
#   (rename these to prevent undesired hiding and confusion)

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="find_duplicate_names"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"


function find_duplicates {
    LAST=""
    cnt=0
    for str in `cat /tmp/names2.txt`
    do
        if [ "$str" = "$LAST" ]
        then
            let cnt++;
            echo "ALERT <$cnt> <$str>"
            grep -n "lemma $str:" -r --include=\*.thy --exclude=test*.thy . \
                | grep ":lemma" | sed 's/:/ : /g'
            grep -n "corollary $str:" -r --include=\*.thy --exclude=test*.thy . \
                | grep ":corollary" | sed 's/:/ : /g'
            grep -n "theorem $str:" -r --include=\*.thy --exclude=test*.thy . \
                | grep ":theorem" | sed 's/:/ : /g'
            fgrep "$str" **/*.thy

            echo
        fi
        LAST=$str
    done
}

cd ..

grep -n lemma -r --include=\*.thy --exclude=test*.thy --exclude=unused.thy . \
  | grep ":lemma" \
  | sed -n '/lemma [0-9A-Za-z_'"'"']*: "$/p' \
  | sed 's/^.*:lemma \(.*\): "$/\1/g' \
  | sort > /tmp/names.txt

grep -n theorem -r --include=\*.thy --exclude=test*.thy  --exclude=unused.thy . \
  | grep ":theorem" \
  | sed -n '/theorem [0-9A-Za-z_'"'"']*: "$/p' \
  | sed 's/^.*:theorem \(.*\): "$/\1/g' \
  | sort >> /tmp/names.txt

grep -n corollary -r --include=\*.thy --exclude=test*.thy  --exclude=unused.thy . \
  | grep ":corollary" \
  | sed -n '/corollary [0-9A-Za-z_'"'"']*: "$/p' \
  | sed 's/^.*:corollary \(.*\): "$/\1/g' \
  | sort >> /tmp/names.txt

cat /tmp/names.txt | sort > /tmp/names2.txt
cat /tmp/names.txt | awk '{ print length, $0 }' | sort -n -s | cut -d" " -f2-  > /tmp/names3.txt

find_duplicates
