
.PHONY: all
all:
	protocol monitor ../../../test/functions.t/fns.spec
	mkdir -p rvc
	mkdir -p rvp
	mv monitorC.go rvc
	mv monitorP.go rvp
	go run main.go