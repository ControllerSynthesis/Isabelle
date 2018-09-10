#!/bin/bash

PRJ=$1
if [ -z "$PRJ" ] 
then
    echo no args
    exit
fi

found=0
for project in $(cat config/LIST_OF_PROJECTS | sed -n '/^PRJ/p')
do
    if [ "$project" = "$PRJ" ] 
    then
        echo found
        found=1
        break
    fi
done

if [ $found -eq "0" ]
then
    echo not found
    exit
fi

found=0
rm /tmp/found_facts.txt
rm /tmp/later_found_facts.txt
for project in $(cat config/LIST_OF_PROJECTS | sed -n '/^PRJ/p')
do
    if [ $found -eq "0" ]
    then
        echo not found yet
        if [ "$project" = "$PRJ" ] 
        then
            echo found now
            found=1
            cat $project/*.thy | sed -n '/^lemma /p' | sed 's/^lemma \(.*\):.*$/\1/g' >> /tmp/found_facts.txt
            cat $project/*.thy | sed -n '/^theorem /p' | sed 's/^theorem \(.*\):.*$/\1/g' >> /tmp/found_facts.txt
            cat $project/*.thy | sed -n '/^corollary /p' | sed 's/^corollary \(.*\):.*$/\1/g' >> /tmp/found_facts.txt            
        fi
    else
        echo found
        for rule in $(cat /tmp/found_facts.txt)
        do
            if [ $(cat $project/*.thy | sed -n '/'$rule'$/p' | wc -l) -gt 0 ]
            then
                echo $rule >> /tmp/later_found_facts.txt
                continue
            fi
            if [ $(cat $project/*.thy | sed -n '/'$rule'[^a-zA-Z0-9_'"'"']/p' | wc -l) -gt 0 ]
            then
                echo $rule >> /tmp/later_found_facts.txt
                continue                
            fi
        done
    fi
done

# cat /tmp/found_facts.txt
# cat /tmp/later_found_facts.txt

set_union () {
   sort $1 $2 | uniq
}

set_difference () {
   sort $1 $2 $2 | uniq -u
}

set_symmetric_difference() {
   sort $1 $2 | uniq -u
}

for rule in $(set_difference /tmp/found_facts.txt /tmp/later_found_facts.txt)
do
    echo "hide_fact $rule"
done


for rule in $(cat /tmp/later_found_facts.txt | sort -u)
do
    echo "(* important $rule *)"
done



# fgrep lemma *.thy | sed 's/^[^:]*:lemma //g;s/: "//g;s/\(.*\)/hide_fact \1/g;'
# fgrep theorem *.thy | sed 's/^[^:]*:theorem //g;s/: "//g;s/\(.*\)/hide_fact \1/g;'


