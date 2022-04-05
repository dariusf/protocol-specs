Raft

  $ protocol print raft.spec
  (forall s in S
     s.role = 'follower';
     s.current_term = 1;
     s.voted_for = none;
     s.votes_responded = {};
     s.votes_granted = {};
     s.voter_log = {};
     s['log'] = [];
     s.next_index = ${{k: 1 for k, _ in S}};
     s.match_index = ${{k: 0 for k, _ in S}});
  $timeout()
  ||
  $restart()
  ||
  $start_election()
  ||
  $client_requests()
  ||
  $replicate()

  $ protocol monitor raft.spec

$ protocol print raft.spec --project P

$ protocol print raft.spec --project A

$ protocol print raft.spec --project L

$ protocol print raft.spec > paxos1.spec && protocol print paxos1.spec | protocol print > paxos2.spec && diff -uw paxos1.spec paxos2.spec
