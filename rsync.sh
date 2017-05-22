#!/bin/sh
BUILD="_build/${1}/"
DONE=$(rsync -iud --delete --ignore-missing-args --include '*.ml' --exclude='*' ${1}/ ${BUILD})
if [ $? -eq 0 ]; then
    if [ -n "${DONE}" ]; then
        DEL=$(echo ${DONE} | sed -rn 's/\*deleting\s(\w+)\.ml([^\*]+)?/\1\.*,/gp' | sed -re 's/,$//')
        if [ -n "${DEL}" ]; then
            eval rm -- "${BUILD}{${DEL}}"
        fi
        echo 1 >_build/.mkdepends
	else
		if [ ! -f _build/.mkdepends ]; then
			echo 1 >_build/.mkdepends
		fi
    fi
else
    exit 1
fi
