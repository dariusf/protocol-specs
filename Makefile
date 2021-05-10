
all:
	dune test
	OCAMLRUNPARAM=b dune exec ./app/protocol.exe

2pc:
	dune build @install
	OCAMLRUNPARAM=b protocol print test/2pc.t/2pc.spec --types

dev:
	OCAMLRUNPARAM=b dune test -w

messages:
	menhir --list-errors lib/parser.mly > lib/parser.messages

debug-parser:
	 menhir --dump --explain lib/parser.mly

end-debug-parser:
	 rm lib/parser.{ml,mli,automaton,conflicts}
