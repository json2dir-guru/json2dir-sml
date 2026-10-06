# json2dir-sml

json2dir in Standard ML: creates the directory tree a JSON document describes, using only the SML Basis Library (Posix structures included), built with MLton.

    mlton -output out/json2dir json2dir.sml && out/json2dir < tree.json
