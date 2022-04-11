
.PHONY: all
all:
	protocol monitor preamble.spec
	protocol monitor join.spec
	protocol monitor disj.spec
	protocol monitor selfsend.spec

	mkdir -p rvp
	mkdir -p rvq
	mkdir -p rvr
	mkdir -p rvt
	mv monitorP.go rvp
	mv monitorQ.go rvq
	mv monitorR.go rvr
	rm monitorS.go
	mv monitorT.go rvt

	go run main.go