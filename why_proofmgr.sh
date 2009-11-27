#!/bin/sh

# why_proofmgr.sh "option_pour_why" "option_pour_why-dp" nom_du_fichier
#
#


TEMPFILEWHY=$(tempfile -s .why)||exit
TEMPFILE=${TEMPFILEWHY%.why}
trap "rm -f -- '$TEMPFILEWHY'" EXIT

cp $3 $TEMPFILEWHY
why $1 $TEMPFILEWHY || why --no-pervasives $1 $TEMPFILEWHY || exit 1
why-dp $2 ${TEMPFILE}_why*

rm -f -- "$TEMPFILEWHY" ${TEMPFILE}_why*

trap - EXIT
exit
