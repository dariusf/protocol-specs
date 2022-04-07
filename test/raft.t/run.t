Raft

  $ protocol print raft.spec
  (forall s in S
     s.role = 'follower';
     s.current_term = 1;
     s.voted_for = [ ];
     s.votes_responded = {};
     s.votes_granted = {};
     s.log = [ ];
     s.commit_index = 0;
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

Types

  $ protocol print --types raft.spec
  protocol client_requests() (
    (forall c in C
       (forall s in S
          c->s : req(v=c.value);
          (s.role == 'leader' =>*
             s.log = append(s.log, [<<term: s.current_term, value: s.v>>])));
       c.value = c.value + 1);
    $client_requests()
  )
  protocol replicate() (
    (forall s in S
       s.role == 'leader' =>*
         (forall t in (S \ {s})
            s._prev_log_index = s.next_index[t] - 1;
            s._prev_log_term = (s._prev_log_index > 0) ? (s.log[s._prev_log_index]['term']) : (0);
            s._last_entry = min({length(s.log), s.next_index[t]});
            s._entries = slice(s.log, s.next_index[t], s._last_entry);
            s->t : append_entries(term=s.term, prev_log_index=s._prev_log_index, prev_log_term=s._prev_log_term, entries=s._entries, commit_index=min({s.commit_index, s._last_entry}))));
    $replicate()
  )
  protocol restart() (
    (forall s in S
       s.role = 'follower';
       s.votes_responded = {};
       s.votes_granted = {};
       s.next_index = ${{s.k: 1 for k, v in S}};
       s.match_index = ${{s.k: 0 for k, v in S}});
    $restart()
  )
  protocol start_election() (
    forall s in S
      s.role = s.role;
      (s.role == 'candidate' =>*
         s.current_term = s.current_term + 1;
         s.voted_for = [ ];
         s.votes_responded = {};
         s.votes_granted = {};
         (forall t in (S \ {s})
            s->t : request_vote(term=s.current_term, last_log_term=(length(s.log) == 0) ? (0) : (last(s.log)['term']), last_log_index=length(s.log));
            t._log_ok = t.last_log_term > (length(t.log) == 0) ? (0) : (last(t.log)['term']) | t.last_log_term == (length(t.log) == 0) ? (0) : (last(t.log)['term']) & t.last_log_index >= length(t.log);
            t._grant = t.term == t.current_term & t._log_ok & (t.voted_for == [t] | t.voted_for == [ ]);
            (t.term <= t.current_term =>
               t._grant =>
                 t.voted_for = [t];
                 t->s : request_vote_resp(term=t.current_term, vote_granted=t._grant);
                 (s.term == s.current_term =>
                    s.votes_responded = union(s.votes_responded, {t});
                    (s.vote_granted =>
                       s.votes_granted = union(s.votes_granted, {t});
                       (card(s.votes_granted) > size(S) / 2 + 1 =>
                          s.role = 'leader';
                          s.next_index = ${{s.k: length(s.log) for k, _ in S}};
                          s.match_index = ${{s.k: 0 for k, _ in S}});
                       $start_election())))))
  )
  protocol timeout() (
    (forall s in S
       member(s.role, {'follower', 'candidate'}) =>*
         s.role = 'candidate');
    $timeout()
  )
  (forall (s : party S;global) in (S : map(party S, bool);global)
     (s.role : string;S) = 'follower';
     (s.current_term : int;S) = 1;
     (s.voted_for : map(int, party S);S) = [ ];
     (s.votes_responded : map(party S, bool);S) = {};
     (s.votes_granted : map(party S, bool);S) = {};
     (s.log : map(int, record(term:int, value:int));S) = [ ];
     (s.commit_index : int;S) = 0;
     (s.next_index : map(party S, int);S) = ${{(s.k : party S;S): 1 for k, _ in (S : map(party S, bool);global)}};
     (s.match_index : map(party S, int);S) = ${{(s.k : party S;S): 0 for k, _ in (S : map(party S, bool);global)}});
  $timeout()
  ||
  $restart()
  ||
  $start_election()
  ||
  $client_requests()
  ||
  $replicate()

Server projection

  $ protocol print --project S raft.spec
  protocol client_requests() (
    (forall c in C
       c-> : req(v);
       (role == 'leader' =>*
          log = append(log, [<<term: current_term, value: v>>])));
    $client_requests()
  )
  protocol replicate() (
    (role == 'leader' =>*
       (forall t in (S \ {self})
          _prev_log_index = next_index[t] - 1;
          _prev_log_term = (_prev_log_index > 0) ? (log[_prev_log_index]['term']) : (0);
          _last_entry = min({length(log), next_index[t]});
          _entries = slice(log, next_index[t], _last_entry);
          ->t : append_entries(term=term, prev_log_index=_prev_log_index, prev_log_term=_prev_log_term, entries=_entries, commit_index=min({commit_index, _last_entry})))
     ||
     forall s in (S \ {self})
       role == 'leader' =>*
         s-> : append_entries(term, prev_log_index, prev_log_term, entries, commit_index));
    $replicate()
  )
  protocol restart() (
    role = 'follower';
    votes_responded = {};
    votes_granted = {};
    next_index = ${{k: 1 for k, v in S}};
    match_index = ${{k: 0 for k, v in S}};
    $restart()
  )
  protocol start_election() (
    role = role;
    (role == 'candidate' =>*
       current_term = current_term + 1;
       voted_for = [ ];
       votes_responded = {};
       votes_granted = {};
       (forall t in (S \ {self})
          ->t : request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log));
          (term <= current_term =>
             _grant =>
               t-> : request_vote_resp(term, vote_granted);
               (term == current_term =>
                  votes_responded = union(votes_responded, {t});
                  (vote_granted =>
                     votes_granted = union(votes_granted, {t});
                     (card(votes_granted) > size(S) / 2 + 1 =>
                        role = 'leader';
                        next_index = ${{k: length(log) for k, _ in S}};
                        match_index = ${{k: 0 for k, _ in S}});
                     $start_election())))))
    ||
    forall s in (S \ {self})
      role == 'candidate' =>*
        (s-> : request_vote(term, last_log_term, last_log_index);
         _log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);
         _grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);
         (term <= current_term =>
            _grant =>
              voted_for = [self];
              ->s : request_vote_resp(term=current_term, vote_granted=_grant);
              (term == current_term =>
                 vote_granted =>
                   $start_election()))
         ||
         forall t in (S \ {self, s})
           term <= current_term =>
             _grant =>
               term == current_term =>
                 vote_granted =>
                   $start_election())
  )
  protocol timeout() (
    (member(role, {'follower', 'candidate'}) =>*
       role = 'candidate');
    $timeout()
  )
  role = 'follower';
  current_term = 1;
  voted_for = [ ];
  votes_responded = {};
  votes_granted = {};
  log = [ ];
  commit_index = 0;
  next_index = ${{k: 1 for k, _ in S}};
  match_index = ${{k: 0 for k, _ in S}};
  $timeout()
  ||
  $restart()
  ||
  $start_election()
  ||
  $client_requests()
  ||
  $replicate()

Client projection

  $ protocol print --project C raft.spec
  protocol client_requests() (
    (forall s in S
       ->s : req(v=value));
    value = value + 1;
    $client_requests()
  )
  protocol replicate() (
    $replicate()
  )
  protocol restart() (
    $restart()
  )
  protocol start_election() (
    forall s in S
      forall t in (S \ {s})
        $start_election()
  )
  protocol timeout() (
    $timeout()
  )
  $timeout()
  ||
  $restart()
  ||
  $start_election()
  ||
  $client_requests()
  ||
  $replicate()

Server actions

  $ protocol print --actions --project S raft.spec
  digraph G {
    1 [label="SChangeRole1\n{Smain = 1}\nrole = 'candidate'\n{Smain = 1}\n"];
    2 [label="SDummy2\n{Smain = 2}\nskip\n{Smain = 2}\n"];
    3 [label="SChangeRole3\n{Smain = 3}\nrole = 'follower';\nvotes_responded = {};\nvotes_granted = {};\nnext_index = ${{k: 1 for k, v in S}};\nmatch_index = ${{k: 0 for k, v in S}}\n{Smain = 3}\n"];
    4 [label="SDummy4\n{Smain = 4}\nskip\n{Smain = 4}\n"];
    5 [label="SReceiveReq5\n{Smain = 5}\nc→ : req(v)\n{St5(c:C) = 6}\n"];
    7 [label="SChangeLog7\n{St5(c:C) = 6}\nlog = append(log, [<<term: current_term, value: v>>])\n{Smain = 5}\n"];
    9 [label="SChangePrevLogIndex9\n{Smain = 4}\n_prev_log_index = next_index[t] - 1;\n_prev_log_term = (_prev_log_index > 0) ? (log[_prev_log_index]['term']) : (0);\n_last_entry = min({length(log), next_index[t]});\n_entries = slice(log, next_index[t], _last_entry)\n{St8(t:S) = 12}\n"];
    13 [label="SSendAppendEntries13\n{St8(t:S) = 12}\n→t : append_entries(term=term, prev_log_index=_prev_log_index, prev_log_term=_prev_log_term, entries=_entries, commit_index=min({commit_index, _last_entry}))\n{St8(t:S) = 13}\n"];
    14 [label="SReceiveAppendEntries14\n{Smain = 4}\ns→ : append_entries(term, prev_log_index, prev_log_term, entries, commit_index)\n{St9(s:S) = 14}\n"];
    15 [label="SCall15\n{All(∀ t:S{self}. St8(t:S) = 13, All(∀ s:S{self}. St9(s:S) = 14, All()))}\n$replicate()\n{Smain = 4}\n"];
    22 [label="SChangeRole22\n{Smain = 2}\nrole = role;\ncurrent_term = current_term + 1;\nvoted_for = [ ];\nvotes_responded = {};\nvotes_granted = {}\n{St10 = 26}\n"];
    27 [label="SSendRequestVote27\n{St10 = 26}\n→t : request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log))\n{St12(t:S) = 27}\n"];
    28 [label="SReceiveRequestVoteResp28\n{St12(t:S) = 27}\nt→ : request_vote_resp(term, vote_granted)\n{St12(t:S) = 28}\n"];
    29 [label="SChangeVotesResponded29\n{St12(t:S) = 28}\nvotes_responded = union(votes_responded, {t});\nvotes_granted = union(votes_granted, {t});\nrole = 'leader';\nnext_index = ${{k: length(log) for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{St12(t:S) = 2}\n"];
    35 [label="SReceiveRequestVote35\n{Smain = 2}\ns→ : request_vote(term, last_log_term, last_log_index)\n{St14(s:S) = 35}\n"];
    36 [label="SChangeLogOk36\n{St14(s:S) = 35}\n_log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);\n_grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);\nvoted_for = [self]\n{St14(s:S) = 38}\n"];
    39 [label="SSendRequestVoteResp39\n{St14(s:S) = 38}\n→s : request_vote_resp(term=current_term, vote_granted=_grant)\n{St14(s:S) = 2}\n"];
    41 [label="SCall41\n{Smain = 2}\n$start_election()\n{St16(t:S, s:S) = 2}\n"];
    44 [label="SChangeRole44\n{start}\nrole = 'follower';\ncurrent_term = 1;\nvoted_for = [ ];\nvotes_responded = {};\nvotes_granted = {};\nlog = [ ];\ncommit_index = 0;\nnext_index = ${{k: 1 for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{St0 = 1}\n"];
    54 [label="SCall54\n{start}\n$restart()\n{St1 = 3}\n"];
    55 [label="SCall55\n{start}\n$start_election()\n{St2 = 2}\n"];
    56 [label="SCall56\n{start}\n$client_requests()\n{St3 = 5}\n"];
    57 [label="SCall57\n{start}\n$replicate()\n{St4 = 4}\n"];
    57 -> 4;
    56 -> 5;
    55 -> 2;
    54 -> 3;
    44 -> 1;
    41 -> 2;
    39 -> 2;
    36 -> 39;
    35 -> 36;
    29 -> 2;
    28 -> 29;
    27 -> 28;
    22 -> 27;
    15 -> 4;
    14 -> 15;
    13 -> 15;
    9 -> 13;
    7 -> 5;
    5 -> 7;
    4 -> 14;
    4 -> 9;
    3 -> 3;
    2 -> 41;
    2 -> 35;
    2 -> 22;
    1 -> 1;
  }

Client actions

  $ protocol print --actions --project C raft.spec
  digraph G {
    1 [label="CDummy1\n{Cmain = 1}\nskip\n{Cmain = 1}\n"];
    2 [label="CDummy2\n{Cmain = 2}\nskip\n{Ct7(t:S, s:S) = 2}\n"];
    3 [label="CDummy3\n{Cmain = 3}\nskip\n{Cmain = 3}\n"];
    4 [label="CDummy4\n{Cmain = 4}\nskip\n{Cmain = 4}\n"];
    5 [label="CSendReq5\n{Cmain = 5}\n→s : req(v=value)\n{Ct5(s:S) = 6}\n"];
    7 [label="CChangeValue7\n{∀ s:S. Ct5(s:S) = 6}\nvalue = value + 1\n{Cmain = 5}\n"];
    13 [label="CCall13\n{start}\n$timeout()\n{Ct0 = 1}\n"];
    14 [label="CCall14\n{start}\n$restart()\n{Ct1 = 3}\n"];
    15 [label="CCall15\n{start}\n$start_election()\n{Ct2 = 2}\n"];
    16 [label="CCall16\n{start}\n$client_requests()\n{Ct3 = 5}\n"];
    17 [label="CCall17\n{start}\n$replicate()\n{Ct4 = 4}\n"];
    17 -> 4;
    16 -> 5;
    15 -> 2;
    14 -> 3;
    13 -> 1;
    7 -> 5;
    5 -> 7;
    4 -> 4;
    3 -> 3;
    2 -> 2;
    1 -> 1;
  }

Parsing and printing. Note that this doesn't test functions (yet).

  $ protocol print raft.spec > raft1.spec && protocol print raft1.spec | protocol print > raft2.spec && diff -uw raft1.spec raft2.spec

Monitor

  $ protocol monitor raft.spec
  monitorS.go
  monitorC.go