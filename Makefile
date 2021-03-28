
all:
	dune test
	OCAMLRUNPARAM=b dune exec ./app/protocol.exe

debug:
	 menhir --dump --explain lib/parser.mly

end-debug:
	 rm lib/parser.{ml,mli,automaton,conflicts}