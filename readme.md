
# Artifact Evaluation

The VM we provide contains the source code of our tool and that of the projects we evaluated it on. The tool itself has been compiled and is available on the `$PATH`, along with all dependencies needed to compile and run it.

Downstream tools not required for the evaluation, such as Graphviz and TLA+, are not installed.

## Running the tool

`~/protocol-specs` contains the source code of our tool. Typing `make` in here will compile it and run tests. The shell commands executed should appear, and there should be nothing else printed if everything was successful.

```sh
dune test
dune build @install
```

The (working) name of the executable is `protocol`.

The `test` directory contains many examples of using the tool. Of note are the three directories `2pc.t`, `paxos.t`, and `nbac.t`, which contain the protocols we specify in Tab. 1 in the paper. The inputs _and_ outputs of each command are given in the `run.t` file, which uses the cram test format.

To summarize the tool's functionality, it has three subcommands, all of which take protocol specifications as input (files):

1. `print` renders a protocol (or a projection of it) either as an AST, in pretty-printed form with or without inferred types, or as a graph (as shown in Fig. 4 of the paper).
2. `tla` generates a TLA+ model and configuration from the protocol
3. `monitor` generates a monitor for each role as Go source files

Other details, such as the concrete flags to use, may be obtained by passing `--help` to `protocol` or any subcommand. 

## Replicating the evaluation results

All of the claims in the paper can be replicated.

### Expressiveness

The DistAlgo and TLA+ specifications mentioned in Tab. 1 may be found in `~/protocol-specs/case-studies`. There is also a script `count.sh` in that directory which counts lines as we did, minus comments.

```sh
cd case-studies
./count.sh
```

There was a minor revision to our version of Paxos which isn't reflected in the paper, so its line count is 30 instead of 31.

### Runtime verification

`~/go` contains all the projects in Tab. 2 which we instrumented and evaluated the tool on.

The git history of each project shows the changes needed to instrument each project. Monitors were generated from `~/protocol-specs/test/2pc.t/2pc.spec` and are already in each project in the `rvc` and `rvp` directories.

A script `bench.py` is provided in each project for cleaning, compiling, and running it with the numbers of replicas and requests from the paper and measuring monitor overhead. Results are printed to stdout. The results we included in the paper are captured in `results.txt` in each project directory.

We ran our experiments on a 2020 2.3 GHz Quad-Core MacBook Pro with 16GB RAM. Each project should take no more than a few minutes to run.

Finally, the bug we found in `prevosis/distributed-transactions` may be reproduced by running its script with any argument, e.g. `./bench.py 1`. After running it, the violation is printed in `out/master.log`.

## Building the VM from scratch

To create this VM, starting from vmcai-ae22.ova, we used [this](install.sh) script. If anything goes wrong or is unclear, this might help with troubleshooting.
