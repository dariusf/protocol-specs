
.PHONY: all
all:
	protocol monitor preamble.spec
	protocol monitor join.spec
	protocol monitor disj.spec

	mkdir -p rvp
	mkdir -p rvq
	mkdir -p rvr
	mv monitorP.go rvp
	mv monitorQ.go rvq
	mv monitorR.go rvr
	rm monitorS.go

	go run main.go