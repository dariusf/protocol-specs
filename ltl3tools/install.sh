#!/usr/bin/env bash

# Installs everything in /, then places an executable in /usr/bin

set -ex

apt-get update && apt-get install curl make build-essential -y

pushd .
cd /

# AT&T's fsmlibrary
curl https://www3.cs.stonybrook.edu/~algorith/implement/fsm/distrib/fsm-4_0.linux.x86_64.tar.gz | tar xzv

# ltl3tools
curl -L https://github.com/nondeterministic/ltl3tools/releases/download/0.0.8/ltl3tools-0.0.8.tar.gz | tar xzv

# ltl2ba
curl http://www.lsv.fr/~gastin/ltl2ba/ltl2ba-1.3.tar.gz | tar xzv
(cd ltl2ba-1.3 && make)

# ltl3tools
cd ltl3tools-0.0.8
ls /fsm-4.0/bin | xargs -L1 -I'{}' ln -snf "/fsm-4.0/bin/{}" $(pwd)/'third-party/{}' && \
  ln -snf /ltl2ba-1.3/ltl2ba $(pwd)/third-party/ltl2ba

popd

printf '#!/bin/bash\n/ltl3tools-0.0.8/ltl2mon "$1" --prefix /ltl3tools-0.0.8' > /usr/bin/ltl2mon
chmod +x /usr/bin/ltl2mon