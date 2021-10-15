------------------------------------ MODULE MC_userspace -----------------------------
(*
  The model of the userspace VAT interactions via Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see userspace.tla.
  This file defines constants and Apalache trace views.

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
    - Daniel Tisdall <daniel@informal.systems>
    - Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  15.10.2021
*)

EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC, typedefs

VATS == {"vt0", "vt1", "vt2"}
\* VATS == {"vt0", "vt1"}
NUM_SLITS == 5

VARIABLES 
    \* @type: Int;
    step_cnt,
    \* @type: Str;
    step,
    \* @type: Int;
    resolve_target,
    \* @type: VAT;
    curr,
    \* @type: BANK;
    bank,
    \* @type: Int;
    cnt_promise

INSTANCE userspace

\* @type: Seq(STATE) => Bool;
TraceASeesBAndNotBSeesA(hist) == \* TRUE
    LET
        Behavior ==
        \E a, b \in VATS:
        /\   \E i \in DOMAIN hist : ASeesB(hist[i].bank, a, b)
        /\ ~(\E i \in DOMAIN hist : ASeesB(hist[i].bank, b, a))
    IN
    ~Behavior

\* @type: Seq(STATE) => Bool;
TraceResolvesPromiseSeenByOther(hist) == 
    LET 
        \* @type: (BANK, Int) => Set(VAT);
        WatchersForPromiseId(bank_, promiseId) == bank_[PromiseIxOrNeg1(bank_, promiseId)].watchers
    IN
    LET
        Behavior ==
        /\ \E i, j \in DOMAIN hist:
           /\ (i + 1) \in DOMAIN hist
           /\ i < j
           /\ \E k \in DOMAIN hist[i].bank:
              /\ hist[i].bank[k].type = "resolver"
              /\ hist[i+1].bank[k].type = "blank"
              \* Ensure that another vat has a turn after the resolving vat
              /\ hist[i+1].curr # hist[j].curr
              /\ hist[j].step # "transferControl"
              \* Find a case where a vat resolves a promise for which it is not the only watcher
              /\ {hist[i].curr} # WatchersForPromiseId(hist[i].bank, hist[i].bank[k].promiseId)
    IN
    ~Behavior

\* @type: Seq(STATE) => Bool;
ExploratoryTrace(hist) ==
    LET Currs ==
        {hist[i].curr : i \in { j \in DOMAIN hist : hist[j].step # "transferControl"}}
    IN
    LET
        Behavior ==
        /\ 5 < Len(hist)
        /\ Currs = {"vt0", "vt1", "vt2"}
    IN
    ~Behavior

ExploreView == IF step_cnt < 3 THEN "_" ELSE step

(*
JVM_ARGS="-Xmx12G" apalache-mc check --length=10 --view=ExploreView --max-error=1297\
 --inv=TraceResolvesPromiseSeenByOther MC_userspace.tla
*)

===============================================================================
