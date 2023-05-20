theory DDES
  imports Main BeispielTac
begin

section\<open>Deterministic Discrete Event Simulator\<close>

type_synonym time = nat (*months.
Because months seem to be the only time units which allow to consistently split a year
into something more fine-grained without having to worry about leap yeas.*)

text\<open>Raw events will be of type \<^typ>\<open>'event\<close>.\<close>

text\<open>We may want to know what happened in the past.\<close>
type_synonym 'event past_events = \<open>(time \<times> 'event) list\<close>

text\<open>We events as datatype (instead of a function) to reason about them.
An executor must describe how an event is actually executed,
by describing how it modifies the world.\<close>
type_synonym ('world, 'event) executor = \<open>'world \<Rightarrow> 'event past_events \<Rightarrow> 'event \<Rightarrow> 'world\<close>


text\<open>Events for the Simulator.\<close>
datatype 'event timed_event =
  SingletonEvent
    (at: time) \<comment>\<open>at: time when this event occurs\<close>
    (event: \<open>'event\<close>) \<comment>\<open>event: what actually happens\<close>
  |
  RepeatingEvent
    (at: time) \<comment>\<open>at: time when this event occurs\<close>
    time \<comment>\<open>every: once the event completed, when this event is to be scheduled again.\<close>
    (event: \<open>'event\<close>) \<comment>\<open>event: what actually happens\<close>

fun next_events :: \<open>'world timed_event \<Rightarrow> 'world timed_event list\<close> where
  "next_events (SingletonEvent _ _) = []"
| "next_events (RepeatingEvent at_time every ev) = [RepeatingEvent (at_time + every) every ev]"


(*sort may not be stable. There is a stable_sort_key*)
beispiel
  \<open>sort_key at
    [(RepeatingEvent 8 0 ''nothing''), RepeatingEvent 4 0 ''nothing'',
     SingletonEvent 1 ''nothing'', RepeatingEvent 42 0 ''nothing'', RepeatingEvent 2 0 ''nothing'']
  = [SingletonEvent 1 ''nothing'', RepeatingEvent 2 0 ''nothing'',
     RepeatingEvent 4 0 ''nothing'', RepeatingEvent 8 0 ''nothing'', RepeatingEvent 42 0 ''nothing'']\<close>
  by simp

type_synonym 'event future_events = \<open>'event timed_event list\<close>

datatype ('world, 'event) discrete_event_simulator =
  DiscreteEventSimulator
    \<open>time\<close>    \<comment>\<open>now\<close>
    \<open>'event past_events\<close> \<comment>\<open>history. reverse chronological order\<close>
    \<open>'world\<close>  \<comment>\<open>current state\<close>
    \<open>'event future_events\<close> \<comment>\<open>pending events\<close>


(*we assume processing an event takes 0 time.*)
definition duration :: "'event timed_event \<Rightarrow> time" where
  "duration _ \<equiv> 0"

fun process_one ::
  "('world, 'event) executor \<Rightarrow>
   ('world, 'event) discrete_event_simulator \<Rightarrow> ('world, 'event) discrete_event_simulator"
where
  "process_one f (DiscreteEventSimulator now hist current fel) = 
    (case sort_key at fel
     of [] \<Rightarrow> DiscreteEventSimulator now hist current []
      | e#events \<Rightarrow>
         DiscreteEventSimulator
            ((max now (at e)) + (duration e))
            ((max now (at e), event e)#hist)
            (f current hist (event e))
            (events @ next_events e)
      )"
(*TODO: max now (at e) wants an abbreviation*)

beispiel \<open>process_one (\<lambda>w hist e. if e = ''add42'' then w+42 else w)
  (DiscreteEventSimulator 0 [] (0::int)
    [RepeatingEvent 8 0 ''nothing'',
     RepeatingEvent 4 0 ''nothing'',
     SingletonEvent 2 ''add42'',
     RepeatingEvent 42 0 ''nothing'',
     RepeatingEvent 3 0 ''nothing'']) =
  (DiscreteEventSimulator 2 [(2, ''add42'')] 42
     [RepeatingEvent 3 0 ''nothing'',
      RepeatingEvent 4 0 ''nothing'',
      RepeatingEvent 8 0 ''nothing'',
      RepeatingEvent 42 0 ''nothing''])\<close>
  by(simp add: duration_def)

text\<open>Execute 5 events:
time 0
time 0
time 3
time 6
time 8\<close>
beispiel \<open>((process_one (\<lambda>w _ _. w+1))^^5)
  (DiscreteEventSimulator 0 [] (0::int)
    [RepeatingEvent 0 3 ''X'', RepeatingEvent 0 8 ''X''])
=
DiscreteEventSimulator 8
  (rev [(0, ''X''), (0, ''X''), (3, ''X''), (6, ''X''), (8, ''X'')])
  5
  [RepeatingEvent 9 3 ''X'', RepeatingEvent 16 8 ''X'']\<close> by eval

(*what if we still have backlog, i.e. past events.
Does `max now (at e)` do the right thing, i.e. process past events but do not progress or set back time?*)
lemma time_only_moves_forward:
  "process_one f (DiscreteEventSimulator now hist current fel) =
    DiscreteEventSimulator now' hist' current' fel' \<Longrightarrow>
  now \<le> now'"
  apply(simp)
  apply(cases "sort_key at fel")
   apply(simp; fail)
  apply(simp add: duration_def)
  apply(rename_tac e, case_tac e)
  apply(simp)
  apply fastforce
  by force

hide_const at

end