theory DDES
  imports Main BeispielTac
begin

section\<open>Deterministic Discrete Event Simulator\<close>

type_synonym time = nat (*months.
Because months seem to be the only time units which allow to consistently split a year
into something more fine-grained without having to worry about leap yeas.*)

datatype 'world event =
  SingletonEvent
    (at: time) \<comment>\<open>time when this event occurs\<close>
    (event: \<open>'world \<Rightarrow> 'world\<close>) \<comment>\<open>event: what actually happens\<close>
  |
  RepeatingEvent
    (at: time) \<comment>\<open>time when this event occurs\<close>
    time \<comment>\<open>once the event completed, when this event is to be scheduled again.\<close>
    (event: \<open>'world \<Rightarrow> 'world\<close>) \<comment>\<open>event: what actually happens\<close>

fun next_events :: \<open>'world event \<Rightarrow> 'world event list\<close> where
  "next_events (SingletonEvent _ _) = []"
| "next_events (RepeatingEvent at_time every ev) = [RepeatingEvent (at_time + every) every ev]"

type_synonym 'world future_event_list = \<open>'world event list\<close>

datatype 'world discrete_event_simulator =
  DiscreteEventSimulator
    time    \<comment>\<open>now\<close>
    'world  \<comment>\<open>current state\<close>
    \<open>'world future_event_list\<close> \<comment>\<open>pending events\<close>

(*sort may not be stable. There is a stable_sort_key*)
beispiel
  \<open>sort_key at
    [(RepeatingEvent 8 0 (id::unit\<Rightarrow>unit)), RepeatingEvent 4 0 id,
     SingletonEvent 1 id, RepeatingEvent 42 0 id, RepeatingEvent 2 0 id]
  = [SingletonEvent 1 id, RepeatingEvent 2 0 id,
     RepeatingEvent 4 0 id, RepeatingEvent 8 0 id, RepeatingEvent 42 0 id]\<close>
  by simp

(*we assume processing an event takes 0 time.*)
definition duration :: "'world event \<Rightarrow> time" where
  "duration _ \<equiv> 0"

fun process_one :: "'world discrete_event_simulator \<Rightarrow> 'world discrete_event_simulator" where
  "process_one (DiscreteEventSimulator now current fel) = 
    (case sort_key at fel
     of [] \<Rightarrow> DiscreteEventSimulator now current []
      | e#events \<Rightarrow>
         DiscreteEventSimulator
            ((max now (at e)) + (duration e))
            ((event e) current)
            (events @ next_events e)
      )"

beispiel \<open>process_one
  (DiscreteEventSimulator 0 (0::int)
    [RepeatingEvent 8 0 id, RepeatingEvent 4 0 id, SingletonEvent 2 (\<lambda>i. i+42),
     RepeatingEvent 42 0 id, RepeatingEvent 3 0 id]) =
  (DiscreteEventSimulator 2 42
     [RepeatingEvent 3 0 id, RepeatingEvent 4 0 id, RepeatingEvent 8 0 id, RepeatingEvent 42 0 id])\<close>
  by(simp add: duration_def)

value \<open>(process_one^^5)
  (DiscreteEventSimulator 0 (0::int)
    [RepeatingEvent 0 3 (\<lambda>i. i+1), RepeatingEvent 0 8 (\<lambda>i. i+1)])\<close>

(*what if we still have backlog, i.e. past events.
Does `max now (at e)` do the right thing, i.e. process past events but do not progress or set back time?*)
lemma "process_one (DiscreteEventSimulator now current fel) = DiscreteEventSimulator now' current' fel' \<Longrightarrow>
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