#!/bin/bash
echo "hello"

# no_lemma_files=(
# 	"list_append_ass.smt2"
# 	"list_append_len.smt2"
# 	"list_len_butlast.smt2"
# 	"list_append_nil.smt2"
# 	"tree_insert_size.smt2"
# 	)

#	"heap_insert.smt2"

lemma_synth_files=(
	"list_rev.smt2" 
	"list_rev_append.smt2"
	"list_rev2_append.smt2"
	"list_rev2.smt2" # 2 minutes without --try-assoc
	"list_rev_len.smt2"
	"list_rev2_len.smt2"
	"queue_push.smt2"
	"queue_len.smt2"
	)

lemma_synth_cfg=(
	"--try-assoc"
	"--try-assoc"
	"--try-assoc"
	""
	"--gen-fapp"
	""
	"--gen-fapp" # default is 15
	"--gen-fapp"
	)
files_path="bench_adt/"
solver_bin="build/tools/adt/ind"

red=`tput setaf 1`
green=`tput setaf 2`
blue=`tput setaf 4`
bold=`tput bold`
reset=`tput sgr0`

# idx=0
# for f in "${no_lemma_files[@]}"
# do
# 	echo "${blue}>>> Solving ${bold}${f}${reset}"
# 	echo "=== ${solver_bin} ${f}"
# 	${solver_bin} "${files_path}${f}"
# 	if [ $? -eq 0 ]; then
# 		echo "${green}${bold}=== Proved${reset}"
# 	else
# 		echo "${red}${bold}=== FAILED${reset}"
# 	fi
# 	(( idx++ ))
# done


idx=0
for f in "${lemma_synth_files[@]}"
do
	echo "${blue}>>> Solving ${bold}${f}${reset}"
	cfg=${lemma_synth_cfg[$idx]}
	echo "=== ${solver_bin} ${cfg} ${f}"
	${solver_bin} ${cfg} "${files_path}${f}"
	if [ $? -eq 0 ]; then
		echo "${green}${bold}=== Proved${reset}"
	else
		echo "${red}${bold}=== FAILED${reset}"
	fi
	echo
	(( idx++ ))
done

