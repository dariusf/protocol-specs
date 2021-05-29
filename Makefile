
export OCAMLRUNPARAM=b

all:
	dune test
	dune exec ./app/protocol.exe

2pc:
	dune build @install
	protocol print test/2pc.t/2pc.spec --parties C,P --project P --actions | dot -Tpng -o p.png
	protocol print test/2pc.t/2pc.spec --parties C,P --project C --actions | dot -Tpng -o c.png
	protocol tla test/2pc.t/2pc.spec --parties C,P --project C > 2pc.tla

clean:
	rm -rf *.png *.tla

dev:
	dune test -w

messages:
	menhir --list-errors lib/parser.mly > lib/parser.messages

debug-parser:
	 menhir --dump --explain lib/parser.mly

end-debug-parser:
	 rm lib/parser.{ml,mli,automaton,conflicts}
