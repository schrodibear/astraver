#! /bin/sh

if test "$FRAMAC_OPT" = ""; then FRAMAC_OPT=frama-c; fi
if test "$FRAMAC_BYTE" = ""; then FRAMAC_BYTE=frama-c.byte; fi

if (ocamlopt -shared -o test_dynlink.cmxs check_opt.ml) 2> /dev/null; then
  echo $FRAMAC_OPT
else
  echo $FRAMAC_BYTE
fi
