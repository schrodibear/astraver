#!/bin/sh

# why_proofmgr.sh "option_pour_why" "option_pour_why-dp" nom_du_fichier
#
#


why $1 $3 -output - | why-dp -timeout 0 -simple $2
