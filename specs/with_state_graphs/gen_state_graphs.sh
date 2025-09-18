#!/bin/sh
#
# Re-generate DOT/JSON state graphs for specs that are used for "conformance tests" i.e.
# testing equivalence between the Javascript interpreter and TLC. We treat TLC as our 
# test oracle.
#

set -e

# Check for specific spec argument.
if [ -z "$1" ] 
then
    specarg="*"
else
    specarg=$1
fi

tlc="java -cp tla2tools.jar tlc2.TLC"
for spec in `ls $specarg.tla`; do
    # $tlc -deadlock -fp 10 -seed 10 -metadir "states/$spec" -dump jsonitf $spec.json -noGenerateSpecTE $spec
    
    # Generate DOT state graph and then convert it to JSON.
    $tlc -fp 10 -seed 10 -deadlock -noGenerateSpecTE -dump dot $spec.dot $spec
    dot -Txdot_json -o $spec.dot.json $spec.dot
done
