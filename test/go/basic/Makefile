
.PHONY: all
all:
	protocol monitor disj.spec
	mkdir -p rvp
	mv monitorP.go rvp
	mkdir -p rvq

	protocol monitor preamble.spec
	mv monitorQ.go rvq
	mkdir -p rvr

	protocol monitor join.spec
	mv monitorR.go rvr
	rm monitorS.go

	protocol monitor selfsend.spec
	mkdir -p rvt
	mv monitorT.go rvt

	protocol monitor selfsend1.spec
	mkdir -p rvu
	mv monitorU.go rvu

	go run main.go