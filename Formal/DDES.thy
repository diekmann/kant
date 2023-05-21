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
type_synonym ('world, 'event) executor = \<open>time \<Rightarrow> 'world \<Rightarrow> 'event past_events \<Rightarrow> 'event \<Rightarrow> 'world\<close>
                                        (* now \<Rightarrow> world  \<Rightarrow>  history           \<Rightarrow> event  \<Rightarrow> world *)


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

text\<open>The next time step. Usually, this is \<^term>\<open>at e\<close>.
But time moves forward monotonically, so if \<^term>\<open>now::time\<close> is already after \<^term>\<open>at e\<close>,
we stay at \<^term>\<open>now::time\<close> (instead of moving back in time).\<close>
definition next_time :: "time \<Rightarrow> 'event timed_event \<Rightarrow> time" where
  "next_time now e \<equiv> max now (at e)"

fun process_one ::
  "('world, 'event) executor \<Rightarrow>
   ('world, 'event) discrete_event_simulator \<Rightarrow> ('world, 'event) discrete_event_simulator"
where
  "process_one f (DiscreteEventSimulator now hist world fel) = 
    (case sort_key at fel
     of [] \<Rightarrow> DiscreteEventSimulator now hist world []
      | e#events \<Rightarrow>
         DiscreteEventSimulator
            ((next_time now e) + (duration e))
            ((next_time now e, event e)#hist)
            (f now world hist (event e))
            (events @ next_events e)
      )"

beispiel \<open>process_one (\<lambda>now w hist e. if e = ''add42'' then w+42 else w)
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
  by(simp add: duration_def next_time_def)

text\<open>Execute 5 events:
time 0
time 0
time 3
time 6
time 8\<close>
beispiel \<open>((process_one (\<lambda>_ w _ _. w+1))^^5)
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
  apply(simp add: duration_def next_time_def)
  apply(rename_tac e, case_tac e)
  apply(simp)
  apply fastforce
  by force

hide_const at

(*TODO: assumes time is sorted*)
fun events_since :: "time \<Rightarrow> 'event past_events \<Rightarrow> 'event past_events" where
  "events_since since [] = []"
| "events_since since ((t, ev)#hist) =
      (if t \<ge> since then (t,ev)#events_since since hist else events_since since hist)"

beispiel \<open>events_since 4 [(11, ''X''), (5, ''X''), (4, ''X''), (3, ''Y''), (2, ''Y''), (4, ''X'')] =
  [(11, ''X''), (5, ''X''), (4, ''X''), (4, ''X'')]\<close> by eval

subsection\<open>Steuerbeispiel\<close>

datatype event = Lohn int | (*Kapitalertraege int |*) Einkommenssteuer

fun sum_einkommen :: "event past_events \<Rightarrow> int" where
  "sum_einkommen evs = fold (\<lambda>ev acc. acc + (case ev of (_, Lohn n) \<Rightarrow> n | _ \<Rightarrow> 0)) evs 0"

(*Assumes 50% tax*)
fun exec :: "(int, event) executor" where
  "exec _   world hist (Lohn n) = world + n"
| "exec now world hist (Einkommenssteuer) = world - ((sum_einkommen (events_since (now - 12) hist)) div 2)"


beispiel \<open>((process_one exec)^^13)
  (DiscreteEventSimulator 0 [] (0::int)
    [RepeatingEvent 0 1 (Lohn 100), RepeatingEvent 12 12 Einkommenssteuer])
= DiscreteEventSimulator 12
  [(12, Einkommenssteuer), (11, Lohn 100), (10, Lohn 100), (9, Lohn 100), (8, Lohn 100), (7, Lohn 100),
   (6, Lohn 100), (5, Lohn 100), (4, Lohn 100), (3, Lohn 100), (2, Lohn 100), (1, Lohn 100), (0, Lohn 100)]
  600 [RepeatingEvent 12 1 (Lohn 100), RepeatingEvent 24 12 Einkommenssteuer]\<close> by eval


value \<open>((process_one exec)^^26)
  (DiscreteEventSimulator 0 [] (0::int)
    [RepeatingEvent 0 1 (Lohn 100), RepeatingEvent 12 12 Einkommenssteuer])\<close>

(*BUG: welt ist 1150, sollte 1200 sein. Off by one.*)

(*Weil lohn und einkommenssteuer gleichzeitig passieren brauche ich vmtl sort_stable*)

end