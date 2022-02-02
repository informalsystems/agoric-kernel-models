#!/bin/bash

# Check that each invariant is violated

declare -a array=(
"PseudoLiveness0" 
"PseudoLiveness1" 
"PseudoLiveness2" 
"PseudoLiveness3" 
"PseudoLiveness4" 
"PseudoLiveness5" 
"PseudoLiveness6" 
"PseudoLiveness7" 
"PseudoLiveness8" 
"PseudoLiveness9" 
"PseudoLiveness10" 
"PseudoLiveness11" 
"PseudoLiveness12" 
"PseudoLiveness13" 
)

# get length of an array
arraylength=${#array[@]}

# use for loop to read all values and indexes
for (( i=0; i<${arraylength}; i++ ));
do
  printf "INIT Init\nNEXT Next\nINVARIANT ${array[$i]}" > kernel_enhanced.cfg;
  java -XX:+UseParallelGC -Xmx12g -cp ~/Documents/model-checkers/tla2tools.jar tlc2.TLC -workers auto kernel_enhanced.tla > "${array[$i]}".txt
done

printf "INIT Init\nNEXT Next\nINVARIANT Inv" > kernel_enhanced.cfg;
