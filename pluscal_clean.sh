#!/bin/bash

set -euo pipefail

# This script removes the pluscal translation from a tla file on the standard input.

IN_TRANSLATION_BLOCK=0
begin="\\* BEGIN TRANSLATION"
end="\\* END TRANSLATION"

while IFS='$\n' read -r line; do
	if [[ "$line" =~ $begin ]]; then
		IN_TRANSLATION_BLOCK=1
    echo "\\* BEGIN TRANSLATION"
    echo ""
	elif [[ "$line" =~ $end ]]; then
		IN_TRANSLATION_BLOCK=0
    echo "\\* END TRANSLATION"
	elif [[ $IN_TRANSLATION_BLOCK == 0 ]]; then
		echo "$line"
	fi
done
