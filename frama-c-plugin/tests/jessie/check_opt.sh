#! /bin/sh

if (ocamlopt -shared -o test_dynlink.cmxs check_opt.ml) 2> /dev/null; then
  echo frama-c
else
  echo frama-c.byte
fi

