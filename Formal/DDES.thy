theory DDES
  imports Main BeispielTac
begin

section\<open>Deterministic Discrete Event Simulator\<close>

type_synonym time = nat (*months.
Because months seem to be the only time units which allow to consistently split a year
into something more fine-grained without having to worry about leap yeas.*)

datatype 'world event =
  RepeatingEvent
    (at: time) \<comment>\<open>time when this event occurs\<close>
    time \<comment>\<open>once the event completed, when this event is to be scheduled again.\<close>
      (*TODO: make an `every` function*)
    (event: \<open>'world \<Rightarrow> 'world\<close>) \<comment>\<open>event: what actually happens\<close>
  |
  SingletonEvent
    (at: time) \<comment>\<open>time when this event occurs\<close>
    (event: \<open>'world \<Rightarrow> 'world\<close>) \<comment>\<open>event: what actually happens\<close>

value \<open>SingletonEvent 0 (id::unit\<Rightarrow>unit)\<close>

type_synonym 'world future_event_list = \<open>'world event list\<close>

datatype 'world discrete_event_simulator =
  DiscreteEventSimulator
    'world  \<comment>\<open>current state\<close>
    time    \<comment>\<open>now\<close>
    \<open>'world future_event_list\<close> \<comment>\<open>pending events\<close>

(*TODO: do we need stable_sort_key?*)
value
  \<open>sort_key at
    [(RepeatingEvent 8 0 (id::unit\<Rightarrow>unit)), RepeatingEvent 4 0 id,
     SingletonEvent 0 id, RepeatingEvent 42 0 id, RepeatingEvent 2 0 id]\<close>

(*we assume processing an event takes 0 time.*)
fun process_one :: "'world discrete_event_simulator \<Rightarrow> 'world discrete_event_simulator" where
  "process_one (DiscreteEventSimulator current now fel) = 
    (case sort_key at fel
     of [] \<Rightarrow> DiscreteEventSimulator current now []
      | next_event#events \<Rightarrow>
         DiscreteEventSimulator
            ((event next_event) current)
            (now+0)
            events
      )"


beispiel \<open>process_one
  (DiscreteEventSimulator (0::int) 0
    [RepeatingEvent 8 0 id, RepeatingEvent 4 0 id, SingletonEvent 2 (\<lambda>i. i+42),
     RepeatingEvent 42 0 id, RepeatingEvent 3 0 id]) =
  (DiscreteEventSimulator 42 0
     [RepeatingEvent 3 0 id, RepeatingEvent 4 0 id, RepeatingEvent 8 0 id, RepeatingEvent 42 0 id])\<close>
  by(simp)


hide_const at

end