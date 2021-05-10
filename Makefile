
all:
	dune test
	OCAMLRUNPARAM=b dune exec ./app/protocol.exe

dev:
	OCAMLRUNPARAM=b dune test -w

parser:
	menhir --list-errors lib/parser.mly > lib/parser.messages

debug:
	 menhir --dump --explain lib/parser.mly

end-debug:
	 rm lib/parser.{ml,mli,automaton,conflicts}