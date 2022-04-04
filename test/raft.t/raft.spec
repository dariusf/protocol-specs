
//party c in C (
//  c.role = 'follower';
//  c.current_term = 1;
//  c.voted_for = none;
//  c.votes_responded = {};
//  c.votes_granted = {};
//  c.voter_log = {}; // TODO ghost
//  c['log'] = [ ];
//  c.next_index = ${{ k:1 for k, _ in S }};
//  c.match_index = ${{ k:0 for k, _ in S }}
//)

//fn last_term(log) (
//  length(log) == 0 ? 0 : last(log).term
//)

//fn quorum(S) (
//  |S|/2+1
//)

protocol start_election() (
  (forall s in S
    s.role == 'candidate' =>*
      s.current_term = s.current_term + 1;
      // some
      s.voted_for[i] = [0];
      s.votes_responded[i] = {};
      s.votes_granted[i] = {};
      s.voter_log = ${{k: [ ] for k, _ in S}}; // TODO

      forall t in (S \ {self})
        s->t: request_vote(
          term = s.current_term,
          //last_log_term = last_term(s['log']),
          //last_log_term = (length(log) == 0 ? 0 : last(log)['term']),
          last_log_term = (length(log) == 0 and 0 or last(log)['term']),
          last_log_index = length(s['log']));

        let log_ok =
          //last_log_term > last_term(t['log']) ||
            //(last_log_term == last_term(t['log']) && last_log_index >= length(t['log']))
          //last_log_term > (length(t['log']) == 0 ? 0 : last(t['log'])['term']) ||
          last_log_term > (length(t['log']) == 0 and 0 or last(t['log'])['term']) or
            //(last_log_term == (length(t['log']) == 0 ? 0 : last(t['log'])['term']) && last_log_index >= length(t['log']))
            (last_log_term == (length(t['log']) == 0 and 0 or last(t['log'])['term']) and last_log_index >= length(t['log']))
        in
        let grant =
          term == t.current_term and
            log_ok and
            // some
            (t.voted_for == [t] or t.voted_for == [ ])
        in
        term <= t.current_term =>
          grant =>
            // some
            t.voted_for = [t];
          t->s: request_vote_resp(
            term = t.current_term,
            vote_granted = grant);

          term == s.current_term =>
            s.votes_responded = union(s.votes_responded, {t});
            vote_granted =>
              s.votes_granted = union(s.votes_granted, {t});

          // become leader
          // (length(s.votes_granted) > quorum(S) =>

          (length(s.votes_granted) > size(S)/2+1 =>
            s.role = 'leader';
            s.next_index = ${{ k:length(s['log']) for k, _ in S }}; // TODO extra var
            s.match_index = ${{ k:0 for k, _ in S }});
            // TODO elections ghost variable

          // can repeatedly start elections if we time out
          // TODO should this be outside?
          $start_election()
    )//;
  )


protocol timeout() (
  (forall s in S
    member(s.role, {'follower', 'candidate'}) =>*
      s.role = 'candidate');
  $timeout()
)

protocol restart() (
  // everything but current term, voted for, and log is lost
  (forall s in S
    s.role = 'follower';
    s.votes_responded = {};
    s.votes_granted = {};
    s.voter_log = {};
    s.next_index = ${{ k:1 for k, v in S }};
    s.match_index = ${{ k:0 for k, v in S }});
  $restart()
)

protocol client_requests() (
  (forall c in C
    (forall s in C
      // TODO can this condition be implemented? the initiator doesn't have this state
      s.role == 'leader' =>*
        c->s: req(v=c.value);
        s['log'] = append(s['log'], [{{ term: s['term'], value: v }}]));
    c.value = c.value + 1
  );
  $client_requests()
)

protocol replicate() (
  (forall s in S
    s.role == 'leader' =>*
      forall t in (S \ {self})
        // TODO should a send take a message value?
        //let prev_log_index = s.next_index[t] - 1 in
        //let prev_log_term = prev_log_index > 0 and s['log'][prev_log_index]['term'] or 0 in
        //let last_entry = min({length(s['log']), s.next_index[t]}) in
        //let entries = slice(s['log'], s.next_index[t], last_entry) in
        s._prev_log_index = s.next_index[t] - 1;
        s._prev_log_term = prev_log_index > 0 and s['log'][prev_log_index]['term'] or 0;
        s._last_entry = min({length(s['log']), s.next_index[t]});
        s._entries = slice(s['log'], s.next_index[t], last_entry);
        s->t: append_entries(
          term = s.term,
          prev_log_index = s._prev_log_index,
          prev_log_term = s._prev_log_term,
          entries = s._entries,
          commit_index = min({s.commit_index, s._last_entry})
        )
  );
  $replicate()
)

(forall s in S
  s.role = 'follower';
  s.current_term = 1;
  s.voted_for = none;
  s.votes_responded = {};
  s.votes_granted = {};
  s.voter_log = {}; // TODO ghost
  s['log'] = [ ];
  s.next_index = ${{ k:1 for k, _ in S }};
  s.match_index = ${{ k:0 for k, _ in S }}
);

// "threads" can cooperate via shared memory, or directly via sequencing
$timeout() || $restart || $start_election || $client_requests() || $replicate()
