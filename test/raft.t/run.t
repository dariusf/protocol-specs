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
       s.current_term = s.current_term + 1;
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
    5 [label="CSendReq5\n{Ct3 = 5}\ns! req(v=value)\n{Ct5(s:S) = 6}\n"];
    7 [label="CChangeValue7\n{∀ s:S. Ct5(s:S) = 6}\nvalue = value + 1\n{Ct3 = 5}\n"];
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
    current_term = current_term + 1;
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
    1 [label="SChangeRole1\n{St1 = 1}\nrole = 'candidate'\n{St1 = 1}\n"];
    2 [label="SDummy2\n{St2 = 2}\nskip\n{St2 = 2}\n"];
    3 [label="SChangeRole3\n{St0 = 3}\nrole = 'follower';\ncurrent_term = current_term + 1;\nvotes_responded = {};\nvotes_granted = {};\nnext_index = ${{k: 1 for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}};\ncommit_index = 0\n{St0 = 3}\n"];
    4 [label="SDummy4\n{St4 = 4}\nskip\n{St4 = 4}\n"];
    5 [label="SReceiveReq5\n{St3 = 5}\nc? req(v)\n{St5(c:C) = 6}\n"];
    7 [label="SChangeLog7\n{St5(c:C) = 6}\nlog = append(log, [<<term: current_term, value: v>>])\n{All([St5(c:C) = 7, St3 = 5])}\n"];
    9 [label="SChange_PrevLogIndex9\n{St4 = 4}\n_prev_log_index = next_index[t] - 1;\n_prev_log_term = (_prev_log_index > 0) ? (log[_prev_log_index]['term']) : (0);\n_last_entry = min({length(log), next_index[t]});\n_entries = slice(log, next_index[t] - 1, _last_entry - 1)\n{St8(t:S) = 12}\n"];
    13 [label="SSendAppendEntries13\n{St8(t:S) = 12}\nt! append_entries(term=current_term, prev_log_index=_prev_log_index, prev_log_term=_prev_log_term, entries=_entries, mcommit_index=min({commit_index, _last_entry}))\n{St8(t:S) = 13}\n"];
    14 [label="SSendAppendEntriesResp14\n{St8(t:S) = 13}\nt! append_entries_resp(term=current_term, success=false, mmatch_index=0)\n{St8(t:S) = 14}\n"];
    15 [label="SReceiveAppendEntriesResp15\n{St8(t:S) = 13}\nt? append_entries_resp(term, success, mmatch_index)\n{St8(t:S) = 15}\n"];
    16 [label="SReceiveAppendEntries16\n{St4 = 4}\ns? append_entries(term, prev_log_index, prev_log_term, entries, mcommit_index)\n{St9(s:S) = 16}\n"];
    17 [label="SChange_LogOk17\n{St9(s:S) = 16}\n_log_ok = prev_log_index == 0 | prev_log_index > 0 & _prev_log_index <= length(log) & prev_log_term == log[prev_log_index]['term']\n{St9(s:S) = 17}\n"];
    18 [label="SReceiveAppendEntriesResp18\n{St9(s:S) = 17}\ns? append_entries_resp(term, success, mmatch_index)\n{St9(s:S) = 18}\n"];
    19 [label="SChangeRole19\n{St9(s:S) = 17}\nrole = 'follower'\n{St9(s:S) = 19}\n"];
    20 [label="SChange_Index20\n{St9(s:S) = 17}\n_index = prev_log_index + 1;\ncommit_index = mcommit_index\n{St9(s:S) = 21}\n"];
    22 [label="SSendAppendEntriesResp22\n{St9(s:S) = 21}\ns! append_entries_resp(term=current_term, success=true, mmatch_index=prev_log_index + length(entries))\n{St9(s:S) = 22}\n"];
    23 [label="SChangeLog23\n{St9(s:S) = 17}\nlog = slice(log, 0, length(log) - 1)\n{St9(s:S) = 23}\n"];
    24 [label="SChangeLog24\n{St9(s:S) = 17}\nlog = append(log, [entries[0]])\n{St9(s:S) = 24}\n"];
    25 [label="SCall25\n{All([∀ t:S{self}. Any([St8(t:S) = 14, St8(t:S) = 15]), ∀ s:S{self}. Any([Any([St9(s:S) = 18, St9(s:S) = 19]), Any([Any([St9(s:S) = 22, St9(s:S) = 23]), St9(s:S) = 24])])])}\n$replicate()\n{St4 = 4}\n"];
    34 [label="SChangeCurrentTerm34\n{St2 = 2}\ncurrent_term = current_term + 1;\nvoted_for = [ ];\nvotes_responded = {};\nvotes_granted = {}\n{St10 = 37}\n"];
    38 [label="SSendRequestVote38\n{St10 = 37}\nself! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log))\n{St12 = 38}\n"];
    39 [label="SReceiveRequestVote39\n{St12 = 38}\nself? request_vote(term, last_log_term, last_log_index)\n{St12 = 39}\n"];
    40 [label="SChange_LogOk40\n{St12 = 39}\n_log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);\n_grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);\nvoted_for = [self]\n{St12 = 42}\n"];
    43 [label="SSendRequestVoteResp43\n{St12 = 42}\nself! request_vote_resp(term=current_term, granted=_grant)\n{St12 = 43}\n"];
    44 [label="SReceiveRequestVoteResp44\n{St12 = 43}\nself? request_vote_resp(term, granted)\n{St12 = 44}\n"];
    45 [label="SChangeVotesResponded45\n{St12 = 44}\nvotes_responded = union(votes_responded, {self});\nvotes_granted = union(votes_granted, {self})\n{St12 = 46}\n"];
    47 [label="SSendRequestVote47\n{St10 = 37}\nt! request_vote(term=current_term, last_log_term=(length(log) == 0) ? (0) : (last(log)['term']), last_log_index=length(log))\n{St14(t:S) = 47}\n"];
    48 [label="SReceiveRequestVoteResp48\n{St14(t:S) = 47}\nt? request_vote_resp(term, granted)\n{St14(t:S) = 48}\n"];
    49 [label="SChangeVotesResponded49\n{St14(t:S) = 48}\nvotes_responded = union(votes_responded, {t});\nvotes_granted = union(votes_granted, {t})\n{St14(t:S) = 50}\n"];
    51 [label="SChangeRole51\n{All([St12 = 46, ∀ t:S{self}. St14(t:S) = 50])}\nrole = 'leader';\nnext_index = ${{k: length(log) for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{St10 = 53}\n"];
    54 [label="SReceiveRequestVote54\n{St2 = 2}\ns? request_vote(term, last_log_term, last_log_index)\n{St15(s:S) = 54}\n"];
    55 [label="SChange_LogOk55\n{St15(s:S) = 54}\n_log_ok = last_log_term > (length(log) == 0) ? (0) : (last(log)['term']) | last_log_term == (length(log) == 0) ? (0) : (last(log)['term']) & last_log_index >= length(log);\n_grant = term == current_term & _log_ok & (voted_for == [self] | voted_for == [ ]);\nvoted_for = [self]\n{St15(s:S) = 57}\n"];
    58 [label="SSendRequestVoteResp58\n{St15(s:S) = 57}\ns! request_vote_resp(term=current_term, granted=_grant)\n{St15(s:S) = 58}\n"];
    59 [label="SCall59\n{All([St10 = 53, ∀ s:S{self}. St15(s:S) = 58])}\n$start_election()\n{St2 = 2}\n"];
    62 [label="SChangeCurrentTerm62\n{Smain = start}\ncurrent_term = 1;\nrole = 'follower';\nvoted_for = [ ];\nlog = [ ];\ncommit_index = 0;\nvotes_responded = {};\nvotes_granted = {};\nnext_index = ${{k: 1 for k, _ in S}};\nmatch_index = ${{k: 0 for k, _ in S}}\n{Smain = 70}\n"];
    71 [label="SCall71\n{Smain = 70}\n$restart()\n{St0 = 3}\n"];
    72 [label="SCall72\n{Smain = 70}\n$timeout()\n{St1 = 1}\n"];
    73 [label="SCall73\n{Smain = 70}\n$start_election()\n{St2 = 2}\n"];
    74 [label="SCall74\n{Smain = 70}\n$client_requests()\n{St3 = 5}\n"];
    75 [label="SCall75\n{Smain = 70}\n$replicate()\n{St4 = 4}\n"];
    75 -> 4;
    74 -> 5;
    73 -> 2;
    72 -> 1;
    71 -> 3;
    62 -> 75;
    62 -> 74;
    62 -> 73;
    62 -> 72;
    62 -> 71;
    59 -> 2;
    58 -> 59;
    55 -> 58;
    54 -> 55;
    51 -> 59;
    49 -> 51;
    48 -> 49;
    47 -> 48;
    45 -> 51;
    44 -> 45;
    43 -> 44;
    40 -> 43;
    39 -> 40;
    38 -> 39;
    34 -> 47;
    34 -> 38;
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
    2 -> 54;
    2 -> 34;
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
  	case CSendReq80:
  		// no logical preconditions
  
  		if !(m.PC["Ct19"] == 80) {
  			return fmt.Errorf("control precondition of CSendReq80 %v violated", cparams)
  		}
  		return nil
  	case CChangeValue82:
  		// no logical preconditions
  
  		if !(allSet(m.vars["S"].(map[string]bool), func(s string) bool { return m.PC["Ct21_"+(s)] == 81 })) {
  			return fmt.Errorf("control precondition of CChangeValue82 %v violated", cparams)
  		}
  		return nil
  	case CChangeValue88:
  		// no logical preconditions
  
  		if !(m.PC["Cmain"] == 0) {
  			return fmt.Errorf("control precondition of CChangeValue88 %v violated", cparams)
  		}
  		return nil
  	case CCall92:
  		// no logical preconditions
  
  		if !(m.PC["Cmain"] == 88) {
  			return fmt.Errorf("control precondition of CCall92 %v violated", cparams)
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
  
  		if !(m.PC["St1"] == 1) {
  			return fmt.Errorf("control precondition of SChangeRole1 %v violated", cparams)
  		}
  		return nil
  	case SDummy2:
  		// no logical preconditions
  
  		if !(m.PC["St2"] == 2) {
  			return fmt.Errorf("control precondition of SDummy2 %v violated", cparams)
  		}
  		return nil
  	case SChangeRole3:
  		// no logical preconditions
  
  		if !(m.PC["St0"] == 3) {
  			return fmt.Errorf("control precondition of SChangeRole3 %v violated", cparams)
  		}
  		return nil
  	case SDummy4:
  		// no logical preconditions
  
  		if !(m.PC["St4"] == 4) {
  			return fmt.Errorf("control precondition of SDummy4 %v violated", cparams)
  		}
  		return nil
  	case SReceiveReq5:
  		// no logical preconditions
  
  		if !(m.PC["St3"] == 5) {
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
  
  		if !(m.PC["St4"] == 4) {
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
  
  		if !(m.PC["St4"] == 4) {
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
  	case SChangeCurrentTerm34:
  		// no logical preconditions
  
  		if !(m.PC["St2"] == 2) {
  			return fmt.Errorf("control precondition of SChangeCurrentTerm34 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVote38:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 37) {
  			return fmt.Errorf("control precondition of SSendRequestVote38 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVote39:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 38) {
  			return fmt.Errorf("control precondition of SReceiveRequestVote39 %v violated", cparams)
  		}
  		return nil
  	case SChange_LogOk40:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 39) {
  			return fmt.Errorf("control precondition of SChange_LogOk40 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVoteResp43:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 42) {
  			return fmt.Errorf("control precondition of SSendRequestVoteResp43 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVoteResp44:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 43) {
  			return fmt.Errorf("control precondition of SReceiveRequestVoteResp44 %v violated", cparams)
  		}
  		return nil
  	case SChangeVotesResponded45:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 44) {
  			return fmt.Errorf("control precondition of SChangeVotesResponded45 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVote47:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 37) {
  			return fmt.Errorf("control precondition of SSendRequestVote47 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVoteResp48:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St14_"+(cparams["t"] /* : S */)] == 47) {
  			return fmt.Errorf("control precondition of SReceiveRequestVoteResp48 %v violated", cparams)
  		}
  		return nil
  	case SChangeVotesResponded49:
  		// no logical preconditions
  		if _, ok := cparams["t"]; !ok {
  			return fmt.Errorf("expected t to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St14_"+(cparams["t"] /* : S */)] == 48) {
  			return fmt.Errorf("control precondition of SChangeVotesResponded49 %v violated", cparams)
  		}
  		return nil
  	case SChangeRole51:
  		// no logical preconditions
  
  		if !(m.PC["St12"] == 46 && allSet(m.vars["S  {self}"].(map[string]bool), func(t string) bool { return m.PC["St14_"+(t)] == 50 })) {
  			return fmt.Errorf("control precondition of SChangeRole51 %v violated", cparams)
  		}
  		return nil
  	case SReceiveRequestVote54:
  		// no logical preconditions
  
  		if !(m.PC["St2"] == 2) {
  			return fmt.Errorf("control precondition of SReceiveRequestVote54 %v violated", cparams)
  		}
  		return nil
  	case SChange_LogOk55:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St15_"+(cparams["s"] /* : S */)] == 54) {
  			return fmt.Errorf("control precondition of SChange_LogOk55 %v violated", cparams)
  		}
  		return nil
  	case SSendRequestVoteResp58:
  		// no logical preconditions
  		if _, ok := cparams["s"]; !ok {
  			return fmt.Errorf("expected s to be in cparams: %v", cparams)
  		}
  		if !(m.PC["St15_"+(cparams["s"] /* : S */)] == 57) {
  			return fmt.Errorf("control precondition of SSendRequestVoteResp58 %v violated", cparams)
  		}
  		return nil
  	case SCall59:
  		// no logical preconditions
  
  		if !(m.PC["St10"] == 53 && allSet(m.vars["S  {self}"].(map[string]bool), func(s string) bool { return m.PC["St15_"+(s)] == 58 })) {
  			return fmt.Errorf("control precondition of SCall59 %v violated", cparams)
  		}
  		return nil
  	case SChangeCurrentTerm62:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 0) {
  			return fmt.Errorf("control precondition of SChangeCurrentTerm62 %v violated", cparams)
  		}
  		return nil
  	case SCall71:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 70) {
  			return fmt.Errorf("control precondition of SCall71 %v violated", cparams)
  		}
  		return nil
  	case SCall72:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 70) {
  			return fmt.Errorf("control precondition of SCall72 %v violated", cparams)
  		}
  		return nil
  	case SCall73:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 70) {
  			return fmt.Errorf("control precondition of SCall73 %v violated", cparams)
  		}
  		return nil
  	case SCall74:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 70) {
  			return fmt.Errorf("control precondition of SCall74 %v violated", cparams)
  		}
  		return nil
  	case SCall75:
  		// no logical preconditions
  
  		if !(m.PC["Smain"] == 70) {
  			return fmt.Errorf("control precondition of SCall75 %v violated", cparams)
  		}
  		return nil
  	default:
  		panic("invalid action")
  	}
  }
