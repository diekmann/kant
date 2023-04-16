theory DDES
  imports Main
begin

section\<open>Deterministic Discrete Event Simulator\<close>

type_synonym time = nat (*months.
Because months seem to be the only time units which allow to consistently split a year
into something more fine-grained without having to worry about leap yeas.*)

datatype 'world event =
  (*Repeating event*)
  Event
    time \<comment>\<open>time when this event occurs\<close>
    time \<comment>\<open>once the event completed, when this event is to be scheduled again.\<close>
      (*TODO: make an `every` function*)
    \<open>'world \<Rightarrow> 'world\<close> \<comment>\<open>event: what actually happens\<close>

type_synonym 'world future_event_list = \<open>'world event list\<close>

datatype 'world discrete_event_simulator =
  DiscreteEventSimulator
    'world  \<comment>\<open>current state\<close>
    time    \<comment>\<open>now\<close>
    \<open>'world future_event_list\<close> \<comment>\<open>pending events\<close>

(*TODO: do we need stable_sort_key?*)
term sort
value
  \<open>sort_key (\<lambda>e. case e of Event t _ _ \<Rightarrow> t)
    [(Event 8 0 (id::unit\<Rightarrow>unit)), Event 4 0 id, Event 0 0 id, Event 42 0 id, Event 2 0 id]\<close>


end