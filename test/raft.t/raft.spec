
// In Search of an Understandable Consensus Algorithm (2014)

party s in S (
  // Global
  // messages, elections, allLogs

  // Servers
  s.current_term = 1;
  s.role = 'follower';
  s.voted_for = [ ]; // optional

  // Log
  s.log = [ ];
  s.commit_index = 0;
  
  // Candidates
  s.votes_responded = {};
  s.votes_granted = {};
  // s.voter_log

  // Leaders
  s.next_index = ${{ k:1 for k, _ in S }};
  s.match_index = ${{ k:0 for k, _ in S }}
)

party c in C (
  c.value = 0
)

//fn last_term(log) (
//  length(log) == 0 ? 0 : last(log).term
//)

//fn quorum(S) (
//  |S|/2+1
//)

// has to be first or instantiated collection problem
protocol client_requests() (
  (forall c in C
    (forall s in S
      c->s: req(v=c.value);
      // TODO forward the request instead of dropping it
      s.role == 'leader' =>
        s.log = append(s.log, [<< term: s.current_term, value: v >>])
    );
    c.value = c.value + 1
  );
  $client_requests()
)

protocol start_election() (
  (forall s in S
    s.role == 'candidate' =>*
      s.current_term = s.current_term + 1;
      s.voted_for = [ ]; // none
      s.votes_responded = {};
      s.votes_granted = {};

      //(forall t in (S \ {s}) // vote
      (forall t in S // vote for ourselves
        s->t: request_vote(
          term = s.current_term,
          //last_log_term = last_term(s.log),
          last_log_term = (length(s.log) == 0 ? 0 : last(s.log)['term']),
          last_log_index = length(s.log));

        t._log_ok =
          //last_log_term > last_term(t.log) |
            //(last_log_term == last_term(t.log) && last_log_index >= length(t.log))
          t.last_log_term > (length(t.log) == 0 ? 0 : last(t.log)['term'])
            or (t.last_log_term == (length(t.log) == 0 ? 0 : last(t.log)['term'])
              and t.last_log_index >= length(t.log));
        t._grant =
          t.term == t.current_term and t._log_ok and
            (t.voted_for == [t] or t.voted_for == [ ]); // some, none
        t.term <= t.current_term => // drop stale message
          t._grant =>
            t.voted_for = [t]; // some
          t->s: request_vote_resp(
            term = t.current_term,
            granted = t._grant);

        s.term == s.current_term => // drop stale message
          s.votes_responded = union(s.votes_responded, {t});
          s.granted =>
            s.votes_granted = union(s.votes_granted, {t}));

  // become leader
  // length(s.votes_granted) > quorum(S) =>
  (card(s.votes_granted) > size(S)/2+1 =>*
    s.role = 'leader';
    s.next_index = ${{ s.k:length(s.log) for k, _ in S }};
    s.match_index = ${{ s.k:0 for k, _ in S }})
  \/
  // we can always time out while waiting for a quorum (but not before trying to send a message to everyone)
  skip);

  // can repeatedly start elections if we time out
  $start_election()
)

protocol timeout() (
  (forall s in S
    member(s.role, {'follower'}) =>*
      s.role = 'candidate');
  $timeout()
)

protocol restart() (
  // everything but current term, voted for, and log is lost
  (forall s in S
    s.role = 'follower';
    // forces this subprotocol to be here or this type can't be inferred
    // TODO defer checking instantiatedness until after all subprotocols are checked, so ordering doesn't matter
    s.votes_responded = {};
    s.votes_granted = {};
    s.next_index = ${{ k:1 for k, _ in S }};
    s.match_index = ${{ k:0 for k, _ in S }};
    s.commit_index = 0);
  $restart()
)

protocol replicate() (
  (forall s in S
    forall t in (S \ {s})
      s.role == 'leader' =>*
        // TODO should a send take a message value?
        //let prev_log_index = s.next_index[t] - 1 in
        //let prev_log_term = prev_log_index > 0 and s.log[prev_log_index]['term'] or 0 in
        //let last_entry = min({length(s.log), s.next_index[t]}) in
        //let entries = slice(s.log, s.next_index[t], last_entry) in
        s._prev_log_index = s.next_index[t] - 1;
        s._prev_log_term = s._prev_log_index > 0 ? s.log[s._prev_log_index]['term'] : 0;
        s._last_entry = min({length(s.log), s.next_index[t]});
        // subseq goes from 1 to n, slice goes from 0 to (n-1)
        s._entries = slice(s.log, s.next_index[t]-1, s._last_entry-1);
        s->t: append_entries(
          term = s.current_term,
          prev_log_index = s._prev_log_index,
          prev_log_term = s._prev_log_term,
          entries = s._entries,
          mcommit_index = min({s.commit_index, s._last_entry})
        );
        // TODO HandleAppendEntriesRequest
        t._log_ok = t.prev_log_index == 0
          or (t.prev_log_index > 0
            and t._prev_log_index <= length(t.log)
            and t.prev_log_term == t.log[t.prev_log_index]['term']);
        t.term <= t.current_term => ( // otherwise drop msg
          // reject msg
          (t.term < t.current_term or (t.term == t.current_term and t.role == 'follower' and !t._log_ok) =>*
            s->t: append_entries_resp(
              term = s.current_term,
              success = false,
              mmatch_index = 0)
              // ; TODO?
          ) \/ (
            // return to follower state
            t.term == t.current_term and t.role == 'candidate' =>*
              t.role = 'follower'
          ) \/ (
            t._index = t.prev_log_index + 1;
            // accept msg
            t.term == t.current_term and t.role == 'follower' and t._log_ok =>*
              (
                // already done with request
                t.entries == [ ] or
                  (t.entries != [ ] and length(t.log) >= t._index
                    and t.log[t._index]['term'] == t.entries[0]['term']) =>*
                  t.commit_index = t.mcommit_index;
                  t->s: append_entries_resp(
                    term = t.current_term,
                    success = true,
                    mmatch_index = t.prev_log_index + length(t.entries)
                  )
                  // ; TODO
              ) \/ (
                // conflict: remove an entry
                t.entries != [ ]
                  and length(t.log) >= t._index
                  and t.log[t._index]['term'] != t.entries[0]['term'] =>*
                    t.log = slice(t.log, 0, length(t.log)-1)
              ) \/ (
                // no conflict: append
                t.entries != [ ]
                  and length(t.log) == t._index =>*
                    t.log = append(t.log, [t.entries[0]])
              )
          ))

        // TODO HandleAppendEntriesResponse
  );
  $replicate()
)
// TODO UpdateTerm
// TODO DropStaleResponse

// "threads" can cooperate via shared memory, or directly via sequencing
$restart || $timeout || $start_election || $client_requests || $replicate
