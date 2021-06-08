
export OCAMLRUNPARAM=b

.PHONY: monitor

all:
	dune test
	dune exec ./app/protocol.exe

2pc:
	dune build @install
	protocol print test/2pc.t/2pc.spec --parties C,P --project P --actions | dot -Tpng -o p.png
	protocol print test/2pc.t/2pc.spec --parties C,P --project C --actions | dot -Tpng -o c.png
	protocol tla test/2pc.t/2pc.spec --parties C,P --project C
	open p.png c.png

monitor-2pc:
	dune test
	protocol monitor --parties C,P --project C test/2pc.t/2pc.spec

deps:
	git ls | depgraph | sd '\{' '{rankdir=BT;' | dot -Tpng > modules.png
	dune-deps | tred | dot -Tpng > deps.png
	open modules.png deps.png

ltl:
	ltl2mon "a U b" | dot -Tpng > ltl.png
	open ltl.png

monitor:
	protocol monitor --parties C,P --project C <<< 'forall c in C c.a = 1 ltl ([] (a > 0))'

clean:
	rm -rf *.png *.tla

dev:
	# dune test -w
	git ls | grep ml$ | entr -c -r dune test

messages:
	menhir --list-errors lib/parser.mly > lib/parser.messages

debug-parser:
	 menhir --dump --explain lib/parser.mly

end-debug-parser:
	 rm lib/parser.{ml,mli,automaton,conflicts}
