----------------------------- MODULE Scheduler -----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Workers

VARIABLES have_work_global, \* job count in global queue
          runners, searchers,  \* runners and searchers counters
          ctx, \* state of worker w
          idle_set \* idle list         

Vars == <<have_work_global, runners, searchers, ctx, idle_set>>
States == {"local", "execute", "submit", "try_wakeup", "wakeup", "register_idle", "check_global_q",
     "check_local_qs", "check_have_searchers", "self_wakeup", "wait", "global_search", "stealing", "commit_private_work", "search_done"}

WorkersCnt == Cardinality(Workers)

\****************************************************
\* Type invariants

TypeOk == 
    /\ have_work_global \in BOOLEAN
    /\ runners \in Int /\ runners >= 0
    /\ searchers \in Int /\ searchers >= 0
    /\ ctx \in [Workers -> [state: States, traverse_idx: SUBSET Workers, have_private_work: BOOLEAN, have_local_work: BOOLEAN, is_parked: BOOLEAN, is_searcher: BOOLEAN]]


\****************************************************
\* Utilities

ActiveQueues == {w \in Workers: ctx[w].have_local_work \/ ctx[w].have_private_work} \cup {x \in {"nil"}: have_work_global}
HaveWork == ActiveQueues # {} \*have_work_global \/ (\E w \in Workers: ctx[w].have_local_work \/ ctx[w].have_private_work)


Remove(s) == 
    LET x == CHOOSE x \in s: TRUE IN <<x, s \ {x}>>

\****************************************************
\* State machine invariants

TraverseIdxOk ==
    /\ \A w \in Workers: ctx[w].traverse_idx # {} => ctx[w].state \in {"stealing", "check_local_qs"}
    
PrivateWorkOk ==
    /\ \A w \in Workers: ctx[w].have_private_work => ctx[w].state = "commit_private_work"

LocalWorkOk ==
    /\ \A w \in Workers: ctx[w].have_local_work => ctx[w].state \in {"local", "execute", "submit", "try_wakeup", "wakeup", "search_done"}

SearchersOk == 
    /\ searchers = Cardinality({w \in Workers: ctx[w].is_searcher})
    /\ searchers =< runners

RunnersOk == runners =< WorkersCnt

SearcherStatesInv ==
    \A w \in Workers: ctx[w].state \in {"global_search", "stealing", "commit_private_work", "search_done"} => ctx[w].is_searcher

\****************************************************
\* Next-step relations

Local(w) == ctx[w].state = "local" /\
    /\ UNCHANGED <<runners, have_work_global, idle_set>>
    /\ CASE ctx[w].have_local_work ->
                /\ UNCHANGED searchers
                /\ LET NonDet(a) == ctx' = [ctx EXCEPT ![w].state = "execute", \* make local queue non-deterministically empty
                                                       ![w].have_local_work = a] 
                   IN NonDet(TRUE) \/ NonDet(FALSE)
         [] ~ctx[w].have_local_work /\ searchers = 0 -> 
                /\ searchers' = searchers + 1
                /\ ctx' = [ctx EXCEPT ![w].state = "global_search",
                                      ![w].is_searcher = TRUE] 
         [] ~ctx[w].have_local_work /\ searchers # 0 -> 
                /\ UNCHANGED searchers 
                /\ ctx' = [ctx EXCEPT ![w].state = "register_idle"]

GlobalSearch(w) == ctx[w].state = "global_search" /\
    /\ UNCHANGED <<runners, searchers, idle_set>>
    /\ CASE have_work_global -> /\ \/ have_work_global' = TRUE \* make global queue non-deterministically empty
                                   \/ have_work_global' = FALSE
                                /\ LET NonDet(a) == ctx' = [ctx EXCEPT ![w].state = "commit_private_work",
                                                                       ![w].have_private_work = a] \* non-deterministically take a batch of work
                                   IN NonDet(TRUE) \/ NonDet(FALSE)
         [] ~have_work_global -> /\ ctx' = [ctx EXCEPT ![w].state = "stealing",
                                                       ![w].traverse_idx = Workers]
                                 /\ UNCHANGED have_work_global                                       

Stealing(w) == ctx[w].state = "stealing" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ CASE ctx[w].traverse_idx = {} -> ctx' = [ctx EXCEPT ![w].state = "register_idle"]
         [] OTHER -> LET e == Remove(ctx[w].traverse_idx)
                         victim == e[1]
                         rest == e[2]
                     IN IF ctx[victim].have_local_work
                        THEN LET NonDetCtx(a, b) == ctx' = [ctx EXCEPT ![w].state = "commit_private_work",
                                                                       ![w].have_private_work = a,
                                                                       ![w].traverse_idx = {},
                                                                       ![victim].have_local_work = b]
                             IN NonDetCtx(TRUE, TRUE) \/ NonDetCtx(TRUE, FALSE) \/ NonDetCtx(FALSE, TRUE) \/ NonDetCtx(FALSE, FALSE)
                        ELSE ctx' = [ctx EXCEPT ![w].traverse_idx = rest]  


CommitPrivateWork(w) == ctx[w].state = "commit_private_work" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ ctx' = [ctx EXCEPT ![w].state = "search_done",
                          ![w].have_private_work = FALSE,
                          ![w].have_local_work = ctx[w].have_local_work \/ ctx[w].have_private_work]

SearchDone(w) == ctx[w].state = "search_done" /\
    /\ UNCHANGED <<runners, have_work_global, idle_set>>
    /\ LET new_searchers == searchers - 1
           next_state == CASE new_searchers = 0 -> "wakeup"
                           [] OTHER -> "execute" 
       IN /\ searchers' = new_searchers
          /\ ctx' = [ctx EXCEPT ![w].state = next_state,
                                ![w].is_searcher = FALSE]
                                
RegisterIdle(w) == ctx[w].state = "register_idle" /\
    /\ UNCHANGED <<have_work_global>>
    /\ LET searchers_delta == IF ctx[w].is_searcher THEN 1 ELSE 0
           new_searchers == searchers - searchers_delta
           next_state == IF new_searchers = 0 THEN "check_global_q" ELSE "wait"
       IN /\ idle_set' = idle_set \cup {w}
          /\ runners' = runners - 1
          /\ searchers' = new_searchers
          /\ ctx' = [ctx EXCEPT ![w].state = next_state,
                                ![w].is_parked = TRUE,
                                ![w].is_searcher = FALSE]

CheckGlobalQueue(w) == ctx[w].state = "check_global_q" /\    
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ CASE have_work_global ->
                ctx' = [ctx EXCEPT ![w].state = "check_have_searchers"]
         [] OTHER ->
                ctx' = [ctx EXCEPT ![w].state = "check_local_qs",
                                   ![w].traverse_idx = Workers]

CheckLocalQueues(w) == ctx[w].state = "check_local_qs" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ CASE ctx[w].traverse_idx = {} -> ctx' = [ctx EXCEPT ![w].state = "wait"]
         [] OTHER -> LET e == Remove(ctx[w].traverse_idx)
                         victim == e[1]
                         rest == e[2]
                     IN IF ctx[victim].have_local_work
                        THEN ctx' = [ctx EXCEPT ![w].state = "check_have_searchers",
                                                ![w].traverse_idx = {}]
                        ELSE ctx' = [ctx EXCEPT ![w].traverse_idx = rest]  
    
CheckHaveSearchers(w) == ctx[w].state = "check_have_searchers" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ CASE searchers # 0 -> ctx' = [ctx EXCEPT ![w].state = "wait"]
         [] OTHER -> ctx' = [ctx EXCEPT ![w].state = "self_wakeup"]

SelfWakeup(w) == ctx[w].state = "self_wakeup" /\
    /\ UNCHANGED have_work_global
    /\ CASE w \in idle_set ->
                /\ idle_set' = idle_set \ {w}
                /\ searchers' = searchers + 1
                /\ runners' = runners + 1
                /\ ctx' = [ctx EXCEPT ![w].state = "global_search",
                                      ![w].is_parked = FALSE,
                                      ![w].is_searcher = TRUE]
         [] OTHER -> 
                /\ UNCHANGED <<runners, searchers, idle_set>>
                /\ ctx' = [ctx EXCEPT ![w].state = "global_search", \* is_parked should be reseted by notifier
                                      ![w].is_searcher = TRUE]

Wait(w) == ctx[w].state = "wait" /\ ~ctx[w].is_parked /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ ctx' = [ctx EXCEPT ![w].state = "global_search"]

Execute(w) == ctx[w].state = "execute" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ \/ ctx' = [ctx EXCEPT ![w].state = "submit"] \* non-deterministically end job or submit new one
       \/ ctx' = [ctx EXCEPT ![w].state = "local"] 

Submit(w) == ctx[w].state = "submit" /\
    /\ UNCHANGED <<runners, searchers, idle_set>>
    /\ ctx' = [ctx EXCEPT ![w].state = "try_wakeup",
                          ![w].have_local_work = TRUE]
    /\ \/ have_work_global' = (have_work_global \/ ctx[w].have_local_work) \* simulation of `add to global if local queue is full`
       \/ UNCHANGED have_work_global

TryWakeup(w) == ctx[w].state = "try_wakeup" /\
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set>>
    /\ CASE searchers = 0 /\ runners < WorkersCnt ->
                ctx' = [ctx EXCEPT ![w].state = "wakeup"]
         [] OTHER ->
                ctx' = [ctx EXCEPT ![w].state = "execute"]

Wakeup(w) == ctx[w].state = "wakeup" /\
    /\ UNCHANGED have_work_global
    /\ CASE idle_set = {} -> 
                /\ UNCHANGED <<runners, searchers, idle_set>>
                /\ ctx' = [ctx EXCEPT ![w].state = "execute"]
         [] OTHER -> LET v == CHOOSE x \in idle_set: TRUE
                     IN /\ idle_set' = idle_set \ {v}
                        /\ searchers' = searchers + 1
                        /\ runners' = runners + 1
                        /\ ctx' = [ctx EXCEPT ![w].state = "execute",
                                              ![v].is_parked = FALSE,
                                              ![v].is_searcher = TRUE]

Termination == 
    /\ ctx = [w \in Workers |-> [
            state |-> "wait",
            traverse_idx |-> {},
            have_private_work |-> FALSE,
            have_local_work |-> FALSE,
            is_parked |-> TRUE,
            is_searcher |-> FALSE]]
    /\ UNCHANGED <<runners, searchers, have_work_global, idle_set, ctx>>

Next(w) ==
    \/ Local(w)
    \/ GlobalSearch(w)
    \/ Stealing(w)
    \/ CommitPrivateWork(w)
    \/ SearchDone(w)
    \/ RegisterIdle(w)
    \/ CheckGlobalQueue(w)
    \/ CheckLocalQueues(w)
    \/ CheckHaveSearchers(w)
    \/ SelfWakeup(w)
    \/ Wait(w)
    \/ Execute(w)
    \/ Submit(w)
    \/ TryWakeup(w)
    \/ Wakeup(w)
    \/ Termination

\****************************************************
\* Spec

Tick == \E w \in Workers: Next(w)

Init == 
    /\ have_work_global = TRUE
    /\ searchers = 0
    /\ runners = WorkersCnt
    /\ idle_set = {}
    /\ ctx = [w \in Workers |-> [
            state |-> "local",
            traverse_idx |-> {},
            have_private_work |-> FALSE,
            have_local_work |-> FALSE,
            is_parked |-> FALSE,
            is_searcher |-> FALSE]]


TriesAddSearcher(w) == 
    ctx[w].state \in {"wakeup", "try_wakeup", "self_wakeup", "check_global_q", "check_local_qs", "check_have_searchers"}

Spec == Init /\ [][Tick]_Vars /\ WF_Vars(Tick)

\* Needed for NoUnderSubscriptionProperty
NoUnderSubscriptionFairness == SF_Vars(\E w \in Workers: (ctx[w].is_searcher \/ TriesAddSearcher(w)) /\ Next(w))

\* Needed for NoOverSubscriptionProperty
NoOverSubscriptionFairness == SF_Vars(\E w \in Workers: (ctx[w].is_searcher) /\ Next(w))

\****************************************************
\* Temporal properties

UnderSubscriptionProblem == 
    HaveWork /\ runners < WorkersCnt /\ searchers = 0 

NoUnderSubscriptionProperty ==
    [] (UnderSubscriptionProblem => <> (~UnderSubscriptionProblem))
    
OverSubscriptionProblemRelaxed ==
    searchers > Cardinality(ActiveQueues)
    
NoOverSubscriptionProperty ==
    [] (OverSubscriptionProblemRelaxed => <> (searchers = 0)) 
  
=============================================================================