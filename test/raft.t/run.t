Raft

  $ protocol print raft.spec
  (forall s in S
     s.current_term = 1;
     s.role = 'follower';
     s.voted_for = [ ];
     s.log = [ ];
     s.commit_index = 0;
     s.votes_responded = {};
     s.votes_granted = {};
     s.next_index = ${{k: 1 for k, _ in S}};
     s.match_index = ${{k: 0 for k, _ in S}});
  (forall c in C
     c.value = 0);
  ($restart()
   ||
   $timeout()
   ||
   $start_election()
   ||
   $client_requests()
   ||
   $replicate())

Types

  $ protocol print --types raft.spec
  protocol client_requests() (
    (forall c in C
       (forall s in S
          c->s : req(v=c.value);
          (s.role == 'leader' =>
             s.log = append(s.log, [<<term: s.current_term, value: s.v>>])));
       c.value = c.value + 1);
    $client_requests()
  )
  protocol replicate() (
    (forall s in S
       forall t in (S \ {s})
         s.role == 'leader' =>*
           s._prev_log_index = s.next_index[t] - 1;
           s._prev_log_term = (s._prev_log_index > 0) ? (s.log[s._prev_log_index]['term']) : (0);
           s._last_entry = min({length(s.log), s.next_index[t]});
           s._entries = slice(s.log, s.next_index[t] - 1, s._last_entry - 1);
           s->t : append_entries(term=s.current_term, prev_log_index=s._prev_log_index, prev_log_term=s._prev_log_term, entries=s._entries, mcommit_index=min({s.commit_index, s._last_entry}));
           t._log_ok = t.prev_log_index == 0 | t.prev_log_index > 0 & t._prev_log_index <= length(t.log) & t.prev_log_term == t.log[t.prev_log_index]['term'];
           (t.term <= t.current_term =>
              (t.term < t.current_term | t.term == t.current_term & t.role == 'follower' & !(t._log_ok) =>*
                 s->t : append_entries_resp(term=s.current_term, success=false, mmatch_index=0)
               \/
               t.term == t.current_term & t.role == 'candidate' =>*
                 t.role = 'follower'
               \/
               t._index = t.prev_log_index + 1;
               (t.term == t.current_term & t.role == 'follower' & t._log_ok =>*
                  t.entries == [ ] | t.entries != [ ] & length(t.log) >= t._index & t.log[t._index]['term'] == t.entries[0]['term'] =>*
                    t.commit_index = t.mcommit_index;
                    t->s : append_entries_resp(term=t.current_term, success=true, mmatch_index=t.prev_log_index + length(t.entries)))
               \/
               t.entries != [ ] & length(t.log) >= t._index & t.log[t._index]['term'] != t.entries[0]['term'] =>*
                 t.log = slice(t.log, 0, length(t.log) - 1)
               \/
               t.entries != [ ] & length(t.log) == t._index =>*
                 t.log = append(t.log, [t.entries[0]]))));
    $replicate()
  )
  protocol restart() (
    (forall s in S
       s.role = 'follower';
       s.votes_responded = {};
       s.votes_granted = {};
       s.next_index = ${{s.k: 1 for k, _ in S}};
       s.match_index = ${{s.k: 0 for k, _ in S}};
       s.commit_index = 0);
    $restart()
  )
  protocol start_election() (
    (forall s in S
       s.role == 'candidate' =>*
         s.current_term = s.current_term + 1;
         s.voted_for = [ ];
         s.votes_responded = {};
         s.votes_granted = {};
         (forall t in S
            s->t : request_vote(term=s.current_term, last_log_term=(length(s.log) == 0) ? (0) : (last(s.log)['term']), last_log_index=length(s.log));
            t._log_ok = t.last_log_term > (length(t.log) == 0) ? (0) : (last(t.log)['term']) | t.last_log_term == (length(t.log) == 0) ? (0) : (last(t.log)['term']) & t.last_log_index >= length(t.log);
            t._grant = t.term == t.current_term & t._log_ok & (t.voted_for == [t] | t.voted_for == [ ]);
            (t.term <= t.current_term =>
               t._grant =>
                 t.voted_for = [t];
                 t->s : request_vote_resp(term=t.current_term, granted=t._grant);
                 (s.term == s.current_term =>
                    s.votes_responded = union(s.votes_responded, {t});
                    (s.granted =>
                       s.votes_granted = union(s.votes_granted, {t})))));
         (card(s.votes_granted) > size(S) / 2 + 1 =>*
            s.role = 'leader';
            s.next_index = ${{s.k: length(s.log) for k, _ in S}};
            s.match_index = ${{s.k: 0 for k, _ in S}})
     \/
     skip);
    $start_election()
  )
  protocol timeout() (
    (forall s in S
       member(s.role, {'follower'}) =>*
         s.role = 'candidate');
    $timeout()
  )
  (forall (s : party S;global) in (S : map(party S, bool);global)
     (s.current_term : int;S) = 1;
     (s.role : string;S) = 'follower';
     (s.voted_for : map(int, party S);S) = [ ];
     (s.log : map(int, record(term:int, value:int));S) = [ ];
     (s.commit_index : int;S) = 0;
     (s.votes_responded : map(party S, bool);S) = {};
     (s.votes_granted : map(party S, bool);S) = {};
     (s.next_index : map(party S, int);S) = ${{(s.k : party S;S): 1 for k, _ in (S : map(party S, bool);global)}};
     (s.match_index : map(party S, int);S) = ${{(s.k : party S;S): 0 for k, _ in (S : map(party S, bool);global)}});
  (forall (c : party C;global) in (C : map(party C, bool);global)
     (c.value : int;C) = 0);
  ($restart()
   ||
   $timeout()
   ||
   $start_election()
   ||
   $client_requests()
   ||
   $replicate())

Client projection

  $ protocol print --project C raft.spec
  protocol client_requests() (
    (forall s in S
       s! req(v=value));
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
    $start_election()
  )
  protocol timeout() (
    $timeout()
  )
  value = 0;
  ($restart()
   ||
   $timeout()
   ||
   $start_election()
   ||
   $client_requests()
   ||
   $replicate())

Client actions

  $ protocol print --actions --project C raft.spec
  digraph G {
    5 [label="CSendReq5\n{Cmain = 5}\ns! req(v=value)\n{Ct5(s:S) = 6}\n"];
    7 [label="CChangeValue7\n{∀ s:S. Ct5(s:S) = 6}\nvalue = value + 1\n{Cmain = 5}\n"];
    13 [label="CChangeValue13\n{Cmain = start}\nvalue = 0\n{Cmain = 13}\n"];
    17 [label="CCall17\n{Cmain = 13}\n$client_requests()\n{Ct3 = 5}\n"];
    17 -> 5;
    13 -> 17;
    7 -> 5;
    5 -> 7;
  }

Server projection

  $ protocol print --project S raft.spec
  protocol client_requests() (
    (forall c in C
       c? req(v);
       (role == 'leader' =>
          log = append(log, [<<term: current_term, value: v>>])));
    $client_requests()
  )
  protocol replicate() (
    (forall t in (S \ {self})
       role == 'leader' =>*
         _prev_log_index = next_index[t] - 1;
         _prev_log_term = (_prev_log_index > 0) ? (log[_prev_log_index]['term']) : (0);
         _last_entry = min({length(log), next_index[t]});
         _entries = slice(log, next_index[t] - 1, _last_entry - 1);
         t! append_entries(term=current_term, prev_log_index=_prev_log_index, prev_log_term=_prev_log_term, entries=_entries, mcommit_index=min({commit_index, _last_entry}));
         (t! append_entries_resp(term=current_term, success=false, mmatch_index=0)
          \/
          t? append_entries_resp(term, success, mmatch_index))
     ||
     forall s in (S \ {self})
       s? append_entries(term, prev_log_index, prev_log_term, entries, mcommit_index);
       _log_ok = prev_log_index == 0 | prev_log_index > 0 & _prev_log_index <= length(log) & prev_log_term == log[prev_log_index]['term'];
       (term <= current_term =>
          (term < current_term | term == current_term & role == 'follower' & !(_log_ok) =>*
             s? append_entries_resp(term, success, mmatch_index)
           \/
           term == current_term & role == 'candidate' =>*
             role = 'follower'
           \/
           _index = prev_log_index + 1;
           (term == current_term & role == 'follower' & _log_ok =>*
              entries == [ ] | entries != [ ] & length(log) >= _index & log[_index]['term'] == entries[0]['term'] =>*
                commit_index = mcommit_index;
                s! append_entries_resp(term=current_term, success=true, mmatch_index=prev_log_index + length(entries)))
           \/
           entries != [ ] & length(log) >= _index & log[_index]['term'] != entries[0]['term'] =>*
             log = slice(log, 0, length(log) - 1)
           \/
           entries != [ ] & length(log) == _index =>*
             log = append(log, [entries[0]]))));
    $replicate()
  )
  protocol restart() (
    role = 'follower';
    votes_responded = {};
    votes_granted = {};
    next_index = ${{k: 1 for k, _ in S}};
    match_index = ${{k: 0 for k, _ in S}};
    commit_index = 0;
    $restart()
  )
  protocol start_election() (
    (role == 'candidate' =>*
       current_term = current_term + 1;
       voted_for = [ ];
       votes_responded = {};
       votes_granted = {};
       (self! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log));
        self? request_vote(term, last_log_term, last_log_index);
        _log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);
        _grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);
        (term <= current_term =>
           _grant =>
             voted_for = [self];
             self! request_vote_resp(term=current_term, granted=_grant);
             self? request_vote_resp(term, granted);
             (term == current_term =>
                votes_responded = union(votes_responded, {self});
                (granted =>
                   votes_granted = union(votes_granted, {self}))))
        ||
        forall t in (S \ {self})
          t! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log));
          t? request_vote_resp(term, granted);
          (term == current_term =>
             votes_responded = union(votes_responded, {t});
             (granted =>
                votes_granted = union(votes_granted, {t}))));
       (card(votes_granted) > size(S) / 2 + 1 =>*
          role = 'leader';
          next_index = ${{k: length(log) for k, _ in S}};
          match_index = ${{k: 0 for k, _ in S}})
     ||
     forall s in (S \ {self})
       s? request_vote(term, last_log_term, last_log_index);
       _log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);
       _grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);
       (term <= current_term =>
          _grant =>
            voted_for = [self];
            s! request_vote_resp(term=current_term, granted=_grant)));
    $start_election()
  )
  protocol timeout() (
    (member(role, {'follower'}) =>*
       role = 'candidate');
    $timeout()
  )
  current_term = 1;
  role = 'follower';
  voted_for = [ ];
  log = [ ];
  commit_index = 0;
  votes_responded = {};
  votes_granted = {};
  next_index = ${{k: 1 for k, _ in S}};
  match_index = ${{k: 0 for k, _ in S}};
  ($restart()
   ||
   $timeout()
   ||
   $start_election()
   ||
   $client_requests()
   ||
   $replicate())

Server actions

  $ protocol print --actions --project S raft.spec
  digraph G {
    1 [label="SChangeRole1\n{Smain = 1}\nrole = 'candidate'\n{Smain = 1}\n"];
    2 [label="SDummy2\n{Smain = 2}\nskip\n{Smain = 2}\n"];
    3 [label="SChangeRole3\n{Smain = 3}\nrole = 'follower';\nvotes_responded = {};\nvotes_granted = {};\nnext_index = ${{k: 1 for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}};\ncommit_index = 0\n{Smain = 3}\n"];
    4 [label="SDummy4\n{Smain = 4}\nskip\n{Smain = 4}\n"];
    5 [label="SReceiveReq5\n{Smain = 5}\nc? req(v)\n{St5(c:C) = 6}\n"];
    7 [label="SChangeLog7\n{St5(c:C) = 6}\nlog = append(log, [<<term: current_term, value: v>>])\n{All([St5(c:C) = 7, Smain = 5])}\n"];
    9 [label="SChange_PrevLogIndex9\n{Smain = 4}\n_prev_log_index = next_index[t] - 1;\n_prev_log_term = (_prev_log_index > 0) ? (log[_prev_log_index]['term']) : (0);\n_last_entry = min({length(log), next_index[t]});\n_entries = slice(log, next_index[t] - 1, _last_entry - 1)\n{St8(t:S) = 12}\n"];
    13 [label="SSendAppendEntries13\n{St8(t:S) = 12}\nt! append_entries(term=current_term, prev_log_index=_prev_log_index, prev_log_term=_prev_log_term, entries=_entries, mcommit_index=min({commit_index, _last_entry}))\n{St8(t:S) = 13}\n"];
    14 [label="SSendAppendEntriesResp14\n{St8(t:S) = 13}\nt! append_entries_resp(term=current_term, success=false, mmatch_index=0)\n{St8(t:S) = 14}\n"];
    15 [label="SReceiveAppendEntriesResp15\n{St8(t:S) = 13}\nt? append_entries_resp(term, success, mmatch_index)\n{St8(t:S) = 15}\n"];
    16 [label="SReceiveAppendEntries16\n{Smain = 4}\ns? append_entries(term, prev_log_index, prev_log_term, entries, mcommit_index)\n{St9(s:S) = 16}\n"];
    17 [label="SChange_LogOk17\n{St9(s:S) = 16}\n_log_ok = prev_log_index == 0 | prev_log_index > 0 & _prev_log_index <= length(log) & prev_log_term == log[prev_log_index]['term']\n{St9(s:S) = 17}\n"];
    18 [label="SReceiveAppendEntriesResp18\n{St9(s:S) = 17}\ns? append_entries_resp(term, success, mmatch_index)\n{St9(s:S) = 18}\n"];
    19 [label="SChangeRole19\n{St9(s:S) = 17}\nrole = 'follower'\n{St9(s:S) = 19}\n"];
    20 [label="SChange_Index20\n{St9(s:S) = 17}\n_index = prev_log_index + 1;\ncommit_index = mcommit_index\n{St9(s:S) = 21}\n"];
    22 [label="SSendAppendEntriesResp22\n{St9(s:S) = 21}\ns! append_entries_resp(term=current_term, success=true, mmatch_index=prev_log_index + length(entries))\n{St9(s:S) = 22}\n"];
    23 [label="SChangeLog23\n{St9(s:S) = 17}\nlog = slice(log, 0, length(log) - 1)\n{St9(s:S) = 23}\n"];
    24 [label="SChangeLog24\n{St9(s:S) = 17}\nlog = append(log, [entries[0]])\n{St9(s:S) = 24}\n"];
    25 [label="SCall25\n{All([∀ t:S{self}. Any([St8(t:S) = 14, St8(t:S) = 15]), ∀ s:S{self}. Any([Any([St9(s:S) = 18, St9(s:S) = 19]), Any([Any([St9(s:S) = 22, St9(s:S) = 23]), St9(s:S) = 24])])])}\n$replicate()\n{Smain = 4}\n"];
    33 [label="SChangeCurrentTerm33\n{Smain = 2}\ncurrent_term = current_term + 1;\nvoted_for = [ ];\nvotes_responded = {};\nvotes_granted = {}\n{St10 = 36}\n"];
    37 [label="SSendRequestVote37\n{St10 = 36}\nself! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log))\n{St12 = 37}\n"];
    38 [label="SReceiveRequestVote38\n{St12 = 37}\nself? request_vote(term, last_log_term, last_log_index)\n{St12 = 38}\n"];
    39 [label="SChange_LogOk39\n{St12 = 38}\n_log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);\n_grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);\nvoted_for = [self]\n{St12 = 41}\n"];
    42 [label="SSendRequestVoteResp42\n{St12 = 41}\nself! request_vote_resp(term=current_term, granted=_grant)\n{St12 = 42}\n"];
    43 [label="SReceiveRequestVoteResp43\n{St12 = 42}\nself? request_vote_resp(term, granted)\n{St12 = 43}\n"];
    44 [label="SChangeVotesResponded44\n{St12 = 43}\nvotes_responded = union(votes_responded, {self});\nvotes_granted = union(votes_granted, {self})\n{St12 = 45}\n"];
    46 [label="SSendRequestVote46\n{St10 = 36}\nt! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log))\n{St14(t:S) = 46}\n"];
    47 [label="SReceiveRequestVoteResp47\n{St14(t:S) = 46}\nt? request_vote_resp(term, granted)\n{St14(t:S) = 47}\n"];
    48 [label="SChangeVotesResponded48\n{St14(t:S) = 47}\nvotes_responded = union(votes_responded, {t});\nvotes_granted = union(votes_granted, {t})\n{St14(t:S) = 49}\n"];
    50 [label="SChangeRole50\n{All([St12 = 45, ∀ t:S{self}. St14(t:S) = 49])}\nrole = 'leader';\nnext_index = ${{k: length(log) for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{St10 = 52}\n"];
    53 [label="SReceiveRequestVote53\n{Smain = 2}\ns? request_vote(term, last_log_term, last_log_index)\n{St15(s:S) = 53}\n"];
    54 [label="SChange_LogOk54\n{St15(s:S) = 53}\n_log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);\n_grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);\nvoted_for = [self]\n{St15(s:S) = 56}\n"];
    57 [label="SSendRequestVoteResp57\n{St15(s:S) = 56}\ns! request_vote_resp(term=current_term, granted=_grant)\n{St15(s:S) = 57}\n"];
    58 [label="SCall58\n{All([St10 = 52, ∀ s:S{self}. St15(s:S) = 57])}\n$start_election()\n{Smain = 2}\n"];
    61 [label="SChangeCurrentTerm61\n{Smain = start}\ncurrent_term = 1;\nrole = 'follower';\nvoted_for = [ ];\nlog = [ ];\ncommit_index = 0;\nvotes_responded = {};\nvotes_granted = {};\nnext_index = ${{k: 1 for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{Smain = 69}\n"];
    70 [label="SCall70\n{Smain = 69}\n$restart()\n{St0 = 3}\n"];
    71 [label="SCall71\n{Smain = 69}\n$timeout()\n{St1 = 1}\n"];
    72 [label="SCall72\n{Smain = 69}\n$start_election()\n{St2 = 2}\n"];
    73 [label="SCall73\n{Smain = 69}\n$client_requests()\n{St3 = 5}\n"];
    74 [label="SCall74\n{Smain = 69}\n$replicate()\n{St4 = 4}\n"];
    74 -> 4;
    73 -> 5;
    72 -> 2;
    71 -> 1;
    70 -> 3;
    61 -> 74;
    61 -> 73;
    61 -> 72;
    61 -> 71;
    61 -> 70;
    58 -> 2;
    57 -> 58;
    54 -> 57;
    53 -> 54;
    50 -> 58;
    48 -> 50;
    47 -> 48;
    46 -> 47;
    44 -> 50;
    43 -> 44;
    42 -> 43;
    39 -> 42;
    38 -> 39;
    37 -> 38;
    33 -> 46;
    33 -> 37;
    25 -> 4;
    24 -> 25;
    23 -> 25;
    22 -> 25;
    20 -> 22;
    19 -> 25;
    18 -> 25;
    17 -> 24;
    17 -> 23;
    17 -> 20;
    17 -> 19;
    17 -> 18;
    16 -> 17;
    15 -> 25;
    14 -> 25;
    13 -> 15;
    13 -> 14;
    9 -> 13;
    7 -> 5;
    5 -> 7;
    4 -> 16;
    4 -> 9;
    3 -> 3;
    2 -> 53;
    2 -> 33;
    1 -> 1;
  }

Parsing and printing. Note that this doesn't test functions (yet).

  $ protocol print raft.spec > raft1.spec && protocol print raft1.spec | protocol print > raft2.spec && diff -uw raft1.spec raft2.spec

Monitor

  $ protocol monitor raft.spec
  monitorS.go
  monitorC.go

  $ sed -n '/func.*precondition/,/^}/p' monitorC.go
  func (m *Monitor) precondition(g *Global, action Action, cparams map[string]string, lparams map[string]string) error {
  	switch action {
  	case CSendReq79:
  		// no logical preconditions
  
  		if !(m.PC["Cmain"] == 79) {
  			return fmt.Errorf("control precondition of CSendReq79 %v violated", cparams)
  		}
  		return nil
  	case CChangeValue81:
  		// no logical preconditions
  
  		if !(allSet(m.vars["S"].(map[string]bool), func(s string) bool { return m.PC["Ct21_"+(s)] == 80 })) {
  			return fmt.Errorf("control precondition of CChangeValue81 %v violated", cparams)
  		}
  		return nil
  	case CChangeValue87:
  		// no logical preconditions
  
  		if !(m.PC["Cmain"] == 0) {
  			return fmt.Errorf("control precondition of CChangeValue87 %v violated", cparams)
  		}
  		return nil
  	case CCall91:
  		// no logical preconditions
  
  		if !(m.PC["Cmain"] == 87) {
  			return fmt.Errorf("control precondition of CCall91 %v violated", cparams)
  		}
  		return nil
  	default:
  		panic("invalid action")
  	}
  }

  $ sed -n '/func.*precondition/,/^}/p' monitorS.go
  func (m *Monitor) precondition(g *Global, action Action, cparams map[string]string, lparams map[string]string) error {
  	switch action {
  	case SChangeRole1:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 1) {
  			return fmt.Errorf("control precondition of SChangeRole1 %v violated", cparams)
  		}
  		return nil
  	case SDummy2:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 2) {
  			return fmt.Errorf("control precondition of SDummy2 %v violated", cparams)
  		}
  		return nil
  	case SChangeRole3:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 3) {
  			return fmt.Errorf("control precondition of SChangeRole3 %v violated", cparams)
  		}
  		return nil
  	case SDummy4:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 4) {
  			return fmt.Errorf("control precondition of SDummy4 %v violated", cparams)
  		}
  		return nil
  	case SReceiveReq5:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 5) {
  			return fmt.Errorf("control precondition of SReceiveReq5 %v violated", cparams)
  		}
  		return nil
  	case SChangeLog7:
  		// no logical preconditions
  		if _, ok := cparams["c"]; !ok {
  			return fmt.Errorf("expected c to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St5_"+(cparams["c"] /* : C */)] == 6) {
  			return fmt.Errorf("control precondition of SChangeLog7 %v violated", cparams)
  		}
  		return nil
  	case SChange_PrevLogIndex9:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 4) {
  			return fmt.Errorf("control precondition of SChange_PrevLogIndex9 %v violated", cparams)
  		}
  		return nil
  	case SSendAppendEntries13:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St8_"+(cparams["t"] /* : S */)] == 12) {
  			return fmt.Errorf("control precondition of SSendAppendEntries13 %v violated", cparams)
  		}
  		return nil
  	case SSendAppendEntriesResp14:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St8_"+(cparams["t"] /* : S */)] == 13) {
  			return fmt.Errorf("control precondition of SSendAppendEntriesResp14 %v violated", cparams)
  		}
  		return nil
  	case SReceiveAppendEntriesResp15:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St8_"+(cparams["t"] /* : S */)] == 13) {
  			return fmt.Errorf("control precondition of SReceiveAppendEntriesResp15 %v violated", cparams)
  		}
  		return nil
  	case SReceiveAppendEntries16:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 4) {
  			return fmt.Errorf("control precondition of SReceiveAppendEntries16 %v violated", cparams)
  		}
  		return nil
  	case SChange_LogOk17:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 16) {
  			return fmt.Errorf("control precondition of SChange_LogOk17 %v violated", cparams)
  		}
  		return nil
  	case SReceiveAppendEntriesResp18:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 17) {
  			return fmt.Errorf("control precondition of SReceiveAppendEntriesResp18 %v violated", cparams)
  		}
  		return nil
  	case SChangeRole19:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 17) {
  			return fmt.Errorf("control precondition of SChangeRole19 %v violated", cparams)
  		}
  		return nil
  	case SChange_Index20:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 17) {
  			return fmt.Errorf("control precondition of SChange_Index20 %v violated", cparams)
  		}
  		return nil
  	case SSendAppendEntriesResp22:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 21) {
  			return fmt.Errorf("control precondition of SSendAppendEntriesResp22 %v violated", cparams)
  		}
  		return nil
  	case SChangeLog23:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 17) {
  			return fmt.Errorf("control precondition of SChangeLog23 %v violated", cparams)
  		}
  		return nil
  	case SChangeLog24:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St9_"+(cparams["s"] /* : S */)] == 17) {
  			return fmt.Errorf("control precondition of SChangeLog24 %v violated", cparams)
  		}
  		return nil
  	case SCall25:
  		// no logical preconditions
  
  		if !(allSet(m.vars["S  {self}"].(map[string]bool), func(t string) bool { return m.PC["St8_"+(t)] == 14 || m.PC["St8_"+(t)] == 15 }) && allSet(m.vars["S  {self}"].(map[string]bool), func(s string) bool {
  			return m.PC["St9_"+(s)] == 18 || m.PC["St9_"+(s)] == 19 || m.PC["St9_"+(s)] == 22 || m.PC["St9_"+(s)] == 23 || m.PC["St9_"+(s)] == 24
  		})) {
  			return fmt.Errorf("control precondition of SCall25 %v violated", cparams)
  		}
  		return nil
  	case SChangeCurrentTerm33:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 2) {
  			return fmt.Errorf("control precondition of SChangeCurrentTerm33 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVote37:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 36) {
  			return fmt.Errorf("control precondition of SSendRequestVote37 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVote38:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 37) {
  			return fmt.Errorf("control precondition of SReceiveRequestVote38 %v violated", cparams)
  		}
  		return nil
  	case SChange_LogOk39:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 38) {
  			return fmt.Errorf("control precondition of SChange_LogOk39 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVoteResp42:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 41) {
  			return fmt.Errorf("control precondition of SSendRequestVoteResp42 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVoteResp43:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 42) {
  			return fmt.Errorf("control precondition of SReceiveRequestVoteResp43 %v violated", cparams)
  		}
  		return nil
  	case SChangeVotesResponded44:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 43) {
  			return fmt.Errorf("control precondition of SChangeVotesResponded44 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVote46:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 36) {
  			return fmt.Errorf("control precondition of SSendRequestVote46 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVoteResp47:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St14_"+(cparams["t"] /* : S */)] == 46) {
  			return fmt.Errorf("control precondition of SReceiveRequestVoteResp47 %v violated", cparams)
  		}
  		return nil
  	case SChangeVotesResponded48:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St14_"+(cparams["t"] /* : S */)] == 47) {
  			return fmt.Errorf("control precondition of SChangeVotesResponded48 %v violated", cparams)
  		}
  		return nil
  	case SChangeRole50:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 45 && allSet(m.vars["S  {self}"].(map[string]bool), func(t string) bool { return m.PC["St14_"+(t)] == 49 })) {
  			return fmt.Errorf("control precondition of SChangeRole50 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVote53:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 2) {
  			return fmt.Errorf("control precondition of SReceiveRequestVote53 %v violated", cparams)
  		}
  		return nil
  	case SChange_LogOk54:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St15_"+(cparams["s"] /* : S */)] == 53) {
  			return fmt.Errorf("control precondition of SChange_LogOk54 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVoteResp57:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St15_"+(cparams["s"] /* : S */)] == 56) {
  			return fmt.Errorf("control precondition of SSendRequestVoteResp57 %v violated", cparams)
  		}
  		return nil
  	case SCall58:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 52 && allSet(m.vars["S  {self}"].(map[string]bool), func(s string) bool { return m.PC["St15_"+(s)] == 57 })) {
  			return fmt.Errorf("control precondition of SCall58 %v violated", cparams)
  		}
  		return nil
  	case SChangeCurrentTerm61:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 0) {
  			return fmt.Errorf("control precondition of SChangeCurrentTerm61 %v violated", cparams)
  		}
  		return nil
  	case SCall70:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 69) {
  			return fmt.Errorf("control precondition of SCall70 %v violated", cparams)
  		}
  		return nil
  	case SCall71:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 69) {
  			return fmt.Errorf("control precondition of SCall71 %v violated", cparams)
  		}
  		return nil
  	case SCall72:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 69) {
  			return fmt.Errorf("control precondition of SCall72 %v violated", cparams)
  		}
  		return nil
  	case SCall73:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 69) {
  			return fmt.Errorf("control precondition of SCall73 %v violated", cparams)
  		}
  		return nil
  	case SCall74:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 69) {
  			return fmt.Errorf("control precondition of SCall74 %v violated", cparams)
  		}
  		return nil
  	default:
  		panic("invalid action")
  	}
  }
