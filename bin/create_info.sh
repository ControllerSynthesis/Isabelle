#!/bin/bash
# 2018, Sven Schneider
#
# INPUT
# 	<none>
# OUTPUT
# 	<none>
# SIDE EFFECTS
#	creates tex/pdf file with info about the usage of keywords in the projects

cd $(cd -P -- "$(dirname -- "$0")" && pwd -P) # change to directory of script
source ../config/config.sh
SCRIPT_NAME="create_info"
CONFIG_DIR="../config"
LIST_OF_PROJECTS="${CONFIG_DIR}/LIST_OF_PROJECTS"
TMP_DIR="/tmp"

# Function round(precision, number)
function round() {
    n=$(printf "%.${1}g" "$2")
    if [ "$n" != "${n#*e}" ]
    then
        f="${n##*e-}"
        test "$n" = "$f" && f= || f=$[ $f+$1-1 ]
        printf "%0.${f}f" "$n"
    else
        printf "%s" "$n"
    fi
}

function calc {
  my_var=$(echo "scale=1; 100*$1/$2" | bc | sed 's/^0$/.0/g' | sed 's/^\./  0./g' | sed 's/^\([0-9]\)\./  \1./g' | sed 's/^\([0-9][0-9]\)\./ \1./g'|sed 's/ *//g')
  echo "$my_var"
}

cd ..
CNT_OOPS=$(cat **/*.thy | sed -n '/^ *oops/p' | wc -l)
CNT_LEMMA=$(cat **/*.thy | sed -n '/^lemma /p' | wc -l)
CNT_COROLLARY=$(cat **/*.thy | sed -n '/^corollary /p' | wc -l)
CNT_THEOREM=$(cat **/*.thy | sed -n '/^theorem /p' | wc -l)
PROOFS=0
let PROOFS+=$CNT_LEMMA
let PROOFS+=$CNT_THEOREM
let PROOFS+=$CNT_COROLLARY
let PROOFS-=$CNT_OOPS

TOTAL_LOC=$(cat **/*.thy | wc -l)

#===========================================
function get_size {
    wc -l PRJ_$1*/*.thy | grep total | sed 's/ *//g;s/total//g'
}

function get_proofs {
    >&2 echo "function get_proofs $*"
    CNT_LOCAL_OOPS=$(cat PRJ_$1*/*.thy | sed -n '/^ *oops/p' | wc -l)
    CNT_LOCAL_LEMMA=$(cat PRJ_$1**/*.thy | sed -n '/^lemma /p' | wc -l)
    CNT_LOCAL_COROLLARY=$(cat PRJ_$1*/*.thy | sed -n '/^corollary /p' | wc -l)
    CNT_LOCAL_THEOREM=$(cat PRJ_$1*/*.thy | sed -n '/^theorem /p' | wc -l)
    CNT_LOCAL_PROOFS=0
    let CNT_LOCAL_PROOFS+=$CNT_LOCAL_LEMMA
    let CNT_LOCAL_PROOFS+=$CNT_LOCAL_THEOREM
    let CNT_LOCAL_PROOFS+=$CNT_LOCAL_COROLLARY
    let CNT_LOCAL_PROOFS-=$CNT_LOCAL_OOPS
    echo $CNT_LOCAL_PROOFS
}

function check_size {
    >&2 echo "function check_size $*"
    num=$(printf "%02d" $1)
    loc=$(get_size $num)
    percent_LOC=$(calc $loc $TOTAL_LOC)
    proofs=$(get_proofs $num)
    percent_PROOFS=$(calc $proofs $PROOFS)    
    #proofs=$(round 2 $proofs)
    #loc=$(round 2 $loc)
    echo "    &\\num{$proofs}"
    echo "    &\\num{$percent_PROOFS}"
    echo "    &\\num{$loc}"
    echo "    &\\num{$percent_LOC}\\\\"
}

# function 
# percent=$(expr $(expr 10000 \* $loc) / $TOTAL_LOC)

# pSUM=0
# for i in `seq 1 14`
# do
#     num=$(printf "%02d" $i)
#     loc=$(get_size $num)
#     percent=$(expr $(expr 10000 \* $loc) / $TOTAL_LOC)
#     #let pSUM+=$loc
#     #rotation=$(expr $(expr 3600 \* $pSUM) / $TOTAL_LOC)
#     #echo $num $loc $percent $rotation    
# done

function update_rotation_proof_number {
    let INDEX++
    num=$(printf "%02d" $INDEX)
    proofs=$(get_proofs $num)
    let pSUM+=$proofs
    rotation=$(scale=1; echo "360 * $pSUM/$PROOFS" | bc)
    >&2 echo $rotation
}

function export_for_proof_number_figure {
    
    INDEX=0
    pSUM=0
    rotation=0
    
    update_rotation_proof_number
    echo "\\PRINTX{1}{$rotation}{black!33}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{2}{$rotation}{black!66}{6mm}{-2}"
    
    update_rotation_proof_number
    echo "\\PRINTX{3}{$rotation}{green!0}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{4}{$rotation}{green!33}{6mm}{2}"    
    update_rotation_proof_number
    echo "\\PRINTX{5}{$rotation}{green!99}{6mm}{0}"
    
    update_rotation_proof_number
    echo "\\PRINTX{6}{$rotation}{blue!25}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{7}{$rotation}{blue!50}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{8}{$rotation}{blue!75}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{9}{$rotation}{blue!100}{6mm}{0}"
    
    update_rotation_proof_number
    echo "\\PRINTX{10}{$rotation}{red!25}{6mm}{-5}"
    update_rotation_proof_number
    echo "\\PRINTX{11}{$rotation}{red!25}{6mm}{5}"
    update_rotation_proof_number
    echo "\\PRINTX{12}{$rotation}{red!50}{6mm}{0}"
    update_rotation_proof_number
    echo "\\PRINTX{13}{$rotation}{red!75}{6mm}{-5}"
    update_rotation_proof_number
    echo "\\PRINTX{14}{$rotation}{red!100}{6mm}{5}"
}
echo "############ export_for_proof_number_figure"
export_for_proof_number_figure > ../thesis/additional_files/proof_distribution_figure.tex

function update_rotation {
    let INDEX++
    num=$(printf "%02d" $INDEX)
    loc=$(get_size $num)
    let pSUM+=$loc
    rotation=$(scale=1; echo "360 * $pSUM/$TOTAL_LOC" | bc)
}

function export_for_size_loc_figure {
    
    INDEX=0
    pSUM=0
    rotation=0    
    
    update_rotation
    echo "\\PRINTX{1}{$rotation}{black!33}{6mm}{-3}"
    update_rotation
    echo "\\PRINTX{2}{$rotation}{black!66}{6mm}{0}"
    
    update_rotation
    echo "\\PRINTX{3}{$rotation}{green!0}{6mm}{6}"
    update_rotation
    echo "\\PRINTX{4}{$rotation}{green!33}{6mm}{11}"    
    update_rotation
    echo "\\PRINTX{5}{$rotation}{green!99}{6mm}{13}"
    
    update_rotation
    echo "\\PRINTX{6}{$rotation}{blue!25}{6mm}{3}"
    update_rotation
    echo "\\PRINTX{7}{$rotation}{blue!50}{6mm}{0}"
    update_rotation
    echo "\\PRINTX{8}{$rotation}{blue!75}{6mm}{0}"
    update_rotation
    echo "\\PRINTX{9}{$rotation}{blue!100}{6mm}{0}"
    
    update_rotation
    echo "\\PRINTX{10}{$rotation}{red!25}{6mm}{-5}"
    update_rotation
    echo "\\PRINTX{11}{$rotation}{red!25}{6mm}{5}"
    update_rotation
    echo "\\PRINTX{12}{$rotation}{red!50}{6mm}{0}"
    update_rotation
    echo "\\PRINTX{13}{$rotation}{red!75}{6mm}{-15}"
    update_rotation
    echo "\\PRINTX{14}{$rotation}{red!100}{6mm}{-10}"
}
echo "############ export_for_size_loc_figure"
export_for_size_loc_figure > ../thesis/additional_files/size_distribution_figure.tex

function export_for_size_table {
    echo "    \\strut    "
    echo "    &\\emph{foundations}"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut\\\\"
    echo "\\num{1}"
    echo "    &foundational and built-in operations"
    echo "    &\\strut"
    check_size 1
    echo "\\num{2}"
    echo "    &words and languages"
    echo "    &\\strut"
    check_size 2
    echo "\\midrule"
    echo "\\strut"
    echo "    &\\emph{abstract controller synthesis}"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut\\\\"
    echo "\\num{3}"
    echo "    &discrete event systems"
    echo "    &\\PAGELAB{section:discrete_event_systems}"
    check_size 3
    echo "\\num{4}"
    echo "    &abstract supervisory control problem"
    echo "    &\\PAGELAB{section:abstract_supervisory_control_problem_for_discrete_event_systems}"
    check_size 4
    echo "\\num{5}"
    echo "    &abstract controller synthesis algorithm"
    echo "    &\\PAGELAB{chapter:abstract_synthesis_algorithm_for_discrete_event_systems}"
    check_size 5
    echo "\\midrule"
    echo "\\strut    "
    echo "    &\\emph{concrete formalisms}"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut    "
    echo "    &\\strut"
    echo "    &\\strut\\\\"
    echo "\\num{6}"
    echo "    &locales for transition systems"
    echo "    &\\strut"
    check_size 6
    echo "\\num{7}"
    echo "    &interpretation of locales for \\EPDA"
    echo "    &\\PAGELAB{section:finite_state_automata_and_pushdown_automata}"
    check_size 7
    echo "\\num{8}"
    echo "    &interpretation of locales for \\Parsers"
    echo "    &\\PAGELAB{section:parser}"
    check_size 8
    echo "\\num{9}"
    echo "    &interpretation of locales for \\CFGs"
    echo "    &\\PAGELAB{section:context_free_grammars}"
    check_size 9
    echo "\\midrule"
    echo "\\strut"
    echo "    &\\emph{concrete controller synthesis}"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\strut    "
    echo "    &\\strut"
    echo "    &\\strut\\\\"
    echo "\\num{10}"
    echo "    &construction of closed loop"
    echo "    &\\PAGELAB{section:concrete_building_block_for_the_synchronous_composition_of_deterministic_pushdown_automata_with_deterministic_finite_automata}"
    check_size 10
    echo "\\num{11}"
    echo "    &concrete supervisory control problem"
    echo "    &\\PAGELAB{section:concrete_supervisory_control_problem_for_deterministic_pushdown_automata}"
    check_size 11
    echo "\\num{12}"
    echo "    &enforcing nonblockingness"
    echo "    &\\PAGELAB{section:building_block_for_enforcing_nonblockingness_for_deterministic_pushdown_automata}"
    check_size 12
    echo "\\num{13}"
    echo "    &removing noncontrollability"
    echo "    &\\PAGELAB{section:building_block_for_enforcing_controllability_for_deterministic_pushdown_automata}"
    check_size 13
    echo "\\num{14}"
    echo "    &concrete controller synthesis algorithm"
    echo "    &\\PAGELAB{section:concrete_synthesis_algorithm_as_an_instantiation_of_the_abstract_synthesis_algorithm}"
    check_size 14
    echo "\\midrule"
    echo "\\strut"
    echo "    &\\strut"
    echo "    &\\strut"
    echo "    &\\llap{$\\Sigma~$}\\num{$PROOFS}"
    echo "    &\\strut    "
    echo "    &\\llap{$\\Sigma~$}\\num{$TOTAL_LOC}"
    echo "    &\\strut\\\\"
}

echo "############ export_for_size_table"
export_for_size_table > ../thesis/additional_files/size_distribution.tex
#===========================================



CNT_LINES=$(cat **/*.thy | wc -l)
CNT_NONEMPTY=$(cat **/*.thy | egrep -v "^$" | wc -l)
# echo "nonempty lines= $CNT_NONEMPTY"
# echo "lines= $CNT_LINES"

CNT_APPLY=$(cat **/*.thy | sed -n '/^ *apply *(/p' | wc -l)

function cntAPPLY {
  CNT=$(cat **/*.thy | sed -n '/^ *apply *( *'$1'\( \|)\|+\|,\|$\)/p' | wc -l)
#   if [ $(cat **/*.thy | grep apply | grep $1 | sed 's/^ *apply *( *'$1'\( \|)\|+\|,\)//g' | grep $1 | sort -u | wc -l) -gt "0" ]
#   then
#     
#     cat **/*.thy | grep apply | grep $1 | sed 's/^ *apply *( *'$1'\( \|)\|+\|,\)//g' | grep $1 | sort -u
#     echo $1
#     exit
#   fi
  PERCENT=$(calc ${CNT} $CNT_APPLY)
  #CNT=$(round 2 $CNT)
  echo "$(echo $1 | sed 's/_/\\_/g')&\num{$CNT}&\num{$PERCENT}\\\\"
  #calc ${CNT} $CNT_APPLY
}

# cntAPPLY auto
# exit

function printLine {
    PERCENT=$(calc ${2} $CNT_APPLY)
    echo "$1&\num{$2}&\num{$PERCENT}\\\\"
}

function cntRULE {
  CNT=$(cat **/*.thy | sed -n '/ '$1' *)/p' | wc -l)
  PERCENT=$(calc ${CNT} $CNT_APPLY)
  echo "$(echo $1 | sed 's/_/\\_/g')&\num{$CNT}&\num{$PERCENT}\\\\"
}

function cntRULES {
  CNT=0
  LABEL=$1
  shift
  for i in $*
  do
    let CNT+=$(cat **/*.thy | sed -n '/ '$i' *)/p' | wc -l)
  done
  PERCENT=$(calc ${CNT} $CNT_APPLY)
  echo "$LABEL&\num{$CNT}&\num{$PERCENT}\\\\"
}




function export_for_table {
    echo "total lines&\num{$CNT_LINES}&\\\\"
    echo "nonempty lines&\num{$CNT_NONEMPTY}&\\\\"
#     echo "\midrule"
#     echo "\multicolumn{3}{l}{\emph{proofs and properties}}\\\\"
    echo "proofs&\num{$PROOFS}&\\\\"
#     echo "lemma&\num{$CNT_LEMMA}&\\\\"
#     echo "corollary&\num{$CNT_COROLLARY}&\\\\"
#     echo "theorem&\num{$CNT_THEOREM}&\\\\"
    echo "apply&\num{$CNT_APPLY}&\num{100}\\\\"
    echo "\midrule"
    echo "\multicolumn{3}{l}{\emph{commands for solving goals}}\\\\"
    cntAPPLY "auto"
    cntAPPLY "force"
    cntAPPLY "blast"
    cntAPPLY "simp"
    cntAPPLY "arith"
    cntAPPLY "metis"
    cntAPPLY "clarify"
    cntAPPLY "clarsimp"

    echo "\midrule"
    echo "\multicolumn{3}{l}{\emph{commands for modifying goals}}\\\\"
    cntAPPLY "subgoal_tac"
    cntAPPLY "rename_tac"
    cntAPPLY "thin_tac"
    cntAPPLY "case_tac"
    cntAPPLY "fold"
    cntAPPLY "unfold"
# TODO: prefer
# TODO: defer
   
    echo "\midrule"
    echo "\multicolumn{3}{l}{\emph{commands for applying established properties}}\\\\"
    cntAPPLY "rule"
    cntAPPLY "erule"
#     cntAPPLY "drule"
#     cntAPPLY "frule"
    cntAPPLY "rule_tac"
    cntAPPLY "erule_tac"
#     cntAPPLY "drule_tac"
#     cntAPPLY "frule_tac"

    echo "\midrule"
    echo "\multicolumn{3}{l}{\emph{special properties}}\\\\"
    cntAPPLY "induct"
    cntAPPLY "induct_tac"
    cntRULE "rev_induct"
    cntRULES "other induction rules" "pinduct" "nat_less_induct" "length_induct" "List.length_induct" "list.induct" "nat.induct" "nat_induct" "Finite_Set.finite.induct"
    
    echo "\midrule"
    echo "\multicolumn{3}{l}{\emph{commands for locales and type classes}}\\\\"
    cntLOCALE=$(cat **/*.thy | sed -n '/^locale .*=/p' | wc -l)
    cntINTERPRETATION=$(cat **/*.thy | sed -n '/^interpretation "/p' | wc -l)
    cntINSTANTIATION=$(cat **/*.thy | sed -n '/^instantiation "/p' | wc -l)
    printLine "locale" $cntLOCALE    
    printLine "interpretation" $cntINTERPRETATION    
    printLine "instantiation" $cntINSTANTIATION    

}


# exit

echo "############ export_for_table"
export_for_table > ../thesis/additional_files/command_distribution.tex


# # # # # # # #

# echo $CNT_LEMMA
# exit

function find_proof_lengths {
    >&2 echo "================== find_proof_lengths $1 $2"
    TARGETDIR=/tmp/$1
    mkdir $TARGETDIR
    
    TOTAL_SUM=0
    CNT_OOPS=0
    
    
    for file in $(find $2 -name "*.thy" | sort)
    do
        >&2 echo find_proof_lengths $1 $file
        touch $TARGETDIR.txt
        rm -rf $TARGETDIR.txt
        touch $TARGETDIR.txt
        CHECKSUM=$(echo $file | md5sum | cut -c -32)
        if [ -f "$TARGETDIR/$CHECKSUM" ]
        then
            continue
        fi
        LOCAL_LEMMA=$(cat $file | sed -n '/^lemma /p' | wc -l)
        LOCAL_COROLLARY=$(cat $file | sed -n '/^corollary /p' | wc -l)
        LOCAL_THEOREM=$(cat $file | sed -n '/^theorem /p' | wc -l)
        SUM=0
        let SUM+=$LOCAL_LEMMA
        let SUM+=$LOCAL_COROLLARY
        let SUM+=$LOCAL_THEOREM
        let TOTAL_SUM+=$SUM
        
        echo $SUM
        CNT_THIS=0
        
        echo $file        
        NUM=0
        MODE=0
        while IFS='' read -r line
        do
            if [ $(echo $line| sed -n '/^ *apply/p' | wc -l) -gt "0" ] && [ $(echo $line| sed -n '/rename_tac/p' | wc -l) -eq "0" ]
            then
                let NUM++
                continue
            fi
            if [ $(echo $line| sed -n '/^ *done/p' | wc -l) -gt "0" ]
            then
                if [ "$MODE" -eq "1" ]
                then
                  echo $NUM >> $TARGETDIR.txt
                  let CNT_THIS++
                  MODE=0
                fi
                continue
            fi
            if [ $(echo $line| sed -n '/^ *oops/p' | wc -l) -gt "0" ]
            then
                if [ "$MODE" -eq "1" ]
                then
                  #let CNT_THIS++
                  MODE=0
                fi
                let CNT_OOPS++
                let SUM--
                continue
            fi            
            if [ $(echo $line| sed -n '/^lemma /p' | wc -l) -gt "0" ]
            then
#                 echo start
                NUM=0
                if [ "$MODE" -eq "1" ]
                then
                    echo $file
                    echo $line
                    exit
                fi                
                MODE=1
                continue
            fi
            if [ $(echo $line| sed -n '/^corollary /p' | wc -l) -gt "0" ]
            then
#                 echo start
                NUM=0
                if [ "$MODE" -eq "1" ]
                then
                    echo $file
                    echo $line
                    exit
                fi                
                MODE=1
                continue
            fi
            if [ $(echo $line| sed -n '/^theorem /p' | wc -l) -gt "0" ]
            then
#                 echo start
                NUM=0
                if [ "$MODE" -eq "1" ]
                then
                    echo PROBLEM
                    echo FILE $file
                    echo LINE $line
                    CNT_THIS=-1
                    break
                fi
                MODE=1
                continue
            fi
       
        done < $file
        CNT_EXPORTED=$(cat $TARGETDIR.txt | wc -l)
        echo END TOTAL_SUM=$TOTAL_SUM
        echo END file=$file
        echo END mod=$MODE
        echo END sum=$SUM
        echo END CNT_THIS=$CNT_THIS
        echo END CNT_EXPORTED=$CNT_EXPORTED
        if [ "$MODE" -eq "1" ]
        then
            echo mode failure
            exit
        fi
        if [ ! "$SUM" -eq "$CNT_THIS" ]
        then
            echo sum/cnt_this failure
            exit
        fi
        #let CNT_EXPORTED+=$CNT_OOPS
        if [ ! "$CNT_EXPORTED" -eq "$CNT_THIS" ]
        then
            echo cnt_exported/cnt_this failure
            exit
        fi
        mv $TARGETDIR.txt $TARGETDIR/$CHECKSUM
    done
    #echo TOTAL_SUM=$TOTAL_SUM
    #echo CNT_OOPS=$CNT_OOPS
}

function export_find_proof_lengths {
    TARGETDIR=/tmp/$1
    FIBA=0
    FIBB=1

    total_val=0
    index=0
    while [ 1 ]
    do    
        let index++
        >&2 echo $index $FIBA $FIBB $total_val $PROOFS
        FIBx=$(expr $FIBA + $FIBB)
        FIBA=$FIBB
        FIBB=$FIBx
        
        let lower=$FIBA
        let lower++
        if [ $lower -gt $FIBx ]
        then
            let lower--
        fi
        upper=$FIBx
        
        cnt=0
        for val in $(cat $TARGETDIR/*)
        do
            if [ "$val" -ge "$lower" ] && [ "$val" -le "$upper" ]
            then
                let cnt++
            fi
        done
        let total_val+=$cnt
        percent_proofs=$(calc $cnt $PROOFS)
        #cnt=$(round 2 $cnt)
        percentile=$(calc $total_val $PROOFS)
        echo "\\num{$index}&\\num{$lower}&\\num{$upper}&\\num{$cnt}&\\num{$percent_proofs}&\\num{$percentile}\\\\"
        if [ $total_val -eq "$PROOFS" ]
        then
            break
        fi
    done
}

function export_find_proof_lengths_median_average {   
    TARGETDIR=/tmp/$1
    total_val=0
    cnt=0
    for val in $(cat $TARGETDIR/*)
    do
        let cnt++
        let total_val+=$val
    done
    average=$(echo "scale=1; $total_val/$cnt" | bc)
    echo "\\newcommand{\ProofLengthAverage}{$average}%"

    cat $TARGETDIR/* | sort -n > /tmp/tmpXX.txt
    MID=$(expr $cnt / 2)
    >&2 echo $1 $MID $total_var $cnt
    mean=$(sed $MID'q;d' < /tmp/tmpXX.txt)
    echo "\\newcommand{\ProofLengthMean}{$mean}%"
    >&2 echo $1 $mean $average

}


function export_find_proof_lengths_percentile {
    TARGETDIR=/tmp/$1
    echo "\\newcommand{\HISTOGRAMheight}[1]{%"
    FIBA=0
    FIBB=1

    total_val=0
    index=0
    while [ 1 ]
    do    
        let index++
        FIBx=$(expr $FIBA + $FIBB)
        FIBA=$FIBB
        FIBB=$FIBx
        
        let lower=$FIBA
        let lower++
        if [ $lower -gt $FIBx ]
        then
            let lower--
        fi
        upper=$FIBx
        
        cnt=0
        for val in $(cat $TARGETDIR/*)
        do
            if [ "$val" -ge "$lower" ] && [ "$val" -le "$upper" ]
            then
                let cnt++
            fi
        done
        let total_val+=$cnt
        percent_proofs=$(calc $cnt $PROOFS)
        #cnt=$(round 2 $cnt)
        percentile=$(calc $total_val $PROOFS)
        #total_valDIV=$(echo "scale=3; $total_val/100" | bc)
        echo "\\ifthenelse{\\equal{#1}{$index}}{\\drawBAR{#1}{$percentile}}{}%"
        if [ $total_val -eq "$PROOFS" ]
        then
            break
        fi
    done
    echo "}"
}

function export_find_proof_lengths_histogram {
    TARGETDIR=/tmp/$1
    echo "\\newcommand{\HISTOGRAMheight}[1]{%"
    FIBA=0
    FIBB=1

    total_val=0
    index=0
    while [ 1 ]
    do    
        let index++
        FIBx=$(expr $FIBA + $FIBB)
        FIBA=$FIBB
        FIBB=$FIBx
        
        let lower=$FIBA
        let lower++
        if [ $lower -gt $FIBx ]
        then
            let lower--
        fi
        upper=$FIBx
        
        cnt=0
        for val in $(cat $TARGETDIR/*)
        do
            if [ "$val" -ge "$lower" ] && [ "$val" -le "$upper" ]
            then
                let cnt++
            fi
        done
        let total_val+=$cnt
        percent_proofs=$(calc $cnt $PROOFS)
        #cnt=$(round 2 $cnt)
        percentile=$(calc $total_val $PROOFS)
        cntDIV=$(echo "scale=3; $cnt/100" | bc)
        echo "\\ifthenelse{\\equal{#1}{$index}}{\\drawBAR{#1}{$cntDIV}}{}%"
        if [ $total_val -eq "$PROOFS" ]
        then
            break
        fi
    done
    echo "}"
}

function export_find_proof_lengths_rotation_update_rotation {
    let INDEX++    
    proofs=$1
    let pSUM+=$proofs
    rotation=$(scale=1; echo "360 * $pSUM/$PROOFS" | bc)
    >&2 echo $rotation
}

SEPERATION=(FOO 20 0 0 0 0 0 0 0 0 -10 -10 -15 -15 -10 0 10 20 30)
function export_find_proof_lengths_rotation {
    TARGETDIR=/tmp/$1
    FIBA=0
    FIBB=1
    
    INDEX=0
    pSUM=0
    rotation=0
    
    total_val=0
    while [ 1 ]
    do    
        FIBx=$(expr $FIBA + $FIBB)
        FIBA=$FIBB
        FIBB=$FIBx
        
        let lower=$FIBA
        let lower++
        if [ $lower -gt $FIBx ]
        then
            let lower--
        fi
        upper=$FIBx
        
        cnt=0
        for val in $(cat $TARGETDIR/*)
        do
            if [ "$val" -ge "$lower" ] && [ "$val" -le "$upper" ]
            then
                let cnt++
            fi
        done
        let total_val+=$cnt
        percent_proofs=$(calc $cnt $PROOFS)
        export_find_proof_lengths_rotation_update_rotation $cnt
        color=$(expr $INDEX \* 5)
        echo "\\PRINTX{$INDEX}{$rotation}{red!$color}{6mm}{${SEPERATION[$INDEX]}}"
        if [ $total_val -eq "$PROOFS" ]
        then
            break
        fi
    done
}
find_proof_lengths proof_length_distribution_PART_1 "PRJ_01* PRJ_02*"
find_proof_lengths proof_length_distribution_PART_2 "PRJ_03* PRJ_04* PRJ_05*"
find_proof_lengths proof_length_distribution_PART_3 "PRJ_06* PRJ_07* PRJ_08* PRJ_09*"
find_proof_lengths proof_length_distribution_PART_4 "PRJ_10* PRJ_11* PRJ_12* PRJ_13* PRJ_14*"
mkdir /tmp/proof_length_distribution
cp /tmp/proof_length_distribution_PART_1/* /tmp/proof_length_distribution/
cp /tmp/proof_length_distribution_PART_2/* /tmp/proof_length_distribution/
cp /tmp/proof_length_distribution_PART_3/* /tmp/proof_length_distribution/
cp /tmp/proof_length_distribution_PART_4/* /tmp/proof_length_distribution/


echo "############ export_find_proof_lengths"
export_find_proof_lengths proof_length_distribution > ../thesis/additional_files/proof_length_distribution.tex
echo "############ export_find_proof_lengths_percentile"
export_find_proof_lengths_percentile proof_length_distribution > ../thesis/additional_files/proof_length_distribution_percentile.tex
echo "############ export_find_proof_lengths_histogram"
export_find_proof_lengths_histogram proof_length_distribution > ../thesis/additional_files/proof_length_distribution_histogram.tex
# 
echo "############ export_find_proof_lengths_rotation"
export_find_proof_lengths_rotation proof_length_distribution > ../thesis/additional_files/proof_length_distribution_figure.tex

export_find_proof_lengths_median_average proof_length_distribution > ../thesis/additional_files/proof_length_distribution_median_average.tex

export_find_proof_lengths_median_average proof_length_distribution_PART_1 > ../thesis/additional_files/proof_length_distribution_median_average_PART_1.tex
export_find_proof_lengths_median_average proof_length_distribution_PART_2 > ../thesis/additional_files/proof_length_distribution_median_average_PART_2.tex
export_find_proof_lengths_median_average proof_length_distribution_PART_3 > ../thesis/additional_files/proof_length_distribution_median_average_PART_3.tex
export_find_proof_lengths_median_average proof_length_distribution_PART_4 > ../thesis/additional_files/proof_length_distribution_median_average_PART_4.tex


