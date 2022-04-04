Raft

$ protocol print raft.spec

$ protocol print raft.spec --parties P,A,L --project P

$ protocol print raft.spec --parties P,A,L --project A

$ protocol print raft.spec --parties P,A,L --project L

$ protocol print raft.spec > paxos1.spec && protocol print paxos1.spec | protocol print > paxos2.spec && diff -uw paxos1.spec paxos2.spec
