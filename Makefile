
export OCAMLRUNPARAM=b

.PHONY: all
all:
	dune test --display=short
	dune build @install

.PHONY: w
w:
	dune test --display=short --watch --terminal-persistence=clear-on-rebuild
	dune build @install

.PHONY: test-go
test-go:
	@for test in $(shell find test/go -d -depth 1); do \
		cd $$test && make; \
	done

deps:
	git ls | depgraph | sd '\{' '{rankdir=BT;' | dot -Tpng > modules.png
	dune-deps | tred | dot -Tpng > deps.png
	open modules.png deps.png

ltl:
	ltl2mon "a U b" | dot -Tpng > ltl.png
	open ltl.png

clean:
	rm -rf *.png *.tla *.cfg *.dot *.log *.go

dev:
	# dune test -w
	git ls | grep ml$ | entr -c -r dune test

messages:
	menhir --list-errors lib/parser.mly > lib/parser.messages

debug-parser:
	menhir --dump --explain --interpret --interpret-show-cst --trace lib/parser.mly

debug-parser-end:
	 rm lib/parser.{automaton,conflicts}

image:
	docker build -t dariusf/protocol-specs .
