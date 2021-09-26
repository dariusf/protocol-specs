#!/usr/bin/env bash

set -x

sudo apt update
sudo apt install opam golang -y
opam init -y
opam switch create 4.12.0
eval $(opam env)
echo "eval \$(opam en)" >> ~/.bashrc

git clone https://github.com/dariusf/protocol-specs.git
cd protocol-specs

sudo ltl3tools/install.sh
sudo chmod -R 775 /ltl2ba-1.3

# check that ltl3tools was installed correctly
ltl2mon '[] a'

opam install . --deps-only --with-test --locked -y

# all tests should pass here
make

export PATH="$(pwd)/_build/install/default/bin:$PATH"
echo "export PATH=\"$(pwd)/_build/install/default/bin:\$PATH\"" >> ~/.bashrc

# check that the executable is built and available on the $PATH
protocol

export GOPATH=$HOME/go
echo "export GOPATH=\$HOME/go" >> ~/.bashrc

mkdir -p $GOPATH/src

# we can't `go get` any of the repos...

# ... because import paths don't have github.com in them
git clone https://github.com/dariusf/distributed-transactions.git $GOPATH/src/distributed-transactions

# ... because forks don't work
git clone https://github.com/dariusf/committer.git $GOPATH/src/github.com/vadiminshakov/committer
git clone https://github.com/dariusf/gotwopc.git $GOPATH/src/github.com/ianobermiller/gotwopc

cd $GOPATH/src/distributed-transactions
./bench.py

cd $GOPATH/src/github.com/vadiminshakov/committer
./bench.py

cd $GOPATH/src/github.com/ianobermiller/gotwopc
./bench.py
