#!/usr/bin/env bash

empty_lines() {
  sed '/^[[:space:]]*$/d'
}

distalgo() {
  sd '#.*' '' | sd '\n\n+' '\n' | wc -l
}

tla() {
  sd '\(\*.*\*\)' '' | empty_lines | sd '\\\*.*' '' | sd '\n\n+' '\n' | wc -l
}

ours() {
  sd '//.*' '' | empty_lines | sd '\n\n+' '\n' | wc -l
}

echo '--- 2pc async'
echo 'TLA+'
tla < 2pc/TwoPhase.tla
echo 'ours'
ours < ../test/2pc.t/2pc-wait.spec

echo '--- 2pc sync'
echo DistAlgo
distalgo < 2pc/2pc.da
echo 'ours'
ours < ../test/2pc.t/2pc.spec

echo '--- paxos'
echo DistAlgo
distalgo < paxos/paxos.da
echo 'TLA+'
tla < paxos/Paxos.tla
echo 'ours'
ours < ../test/paxos.t/paxos.spec

echo '--- nbac'
# echo DistAlgo
# distalgo < paxos/paxos.da
echo 'TLA+'
tla < nbac/nbacc_ray97.tla
echo 'ours'
ours < ../test/nbac.t/nbac.spec

