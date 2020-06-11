#!/bin/bash

set -euo pipefail

# This script removes the pluscal translation from a tla file on the standard input.

IN_TRANSLATION_BLOCK=0

while IFS='$\n' read -r line; do
	if [ "$line" == "\\* BEGIN TRANSLATION" ]; then
		IN_TRANSLATION_BLOCK=1
	elif [ "$line" == "\\* END TRANSLATION" ]; then
		IN_TRANSLATION_BLOCK=0
	elif [[ $IN_TRANSLATION_BLOCK == 0 ]]; then
		echo "$line"
	fi
done
