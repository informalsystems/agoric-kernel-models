------------------------------ MODULE typedefs --------------------------------
(*
  The model of the userspace VAT interactions via Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see userspace.tla.
  This file defines types and auxiliary operators.

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
    - Daniel Tisdall <daniel@informal.systems>
    - Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  15.10.2021
*)

EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC

(* Swingset Userspace Typedefs
   ========================

    @typeAlias: VAT = Str;

    NOTE: promiseId is only relevant for "promise" and "resolver" types.
    @typeAlias: SLIT = [ type: Str, promiseId: Int, watchers: Set(VAT), creator: VAT ];

    @typeAlias: BANK = Int -> SLIT;

    @typeAlias: STATE = [ bank: BANK, curr: VAT, cnt_promise: Int, step: Str, resolve_target: Int, step_cnt: Int ];

*)
typedefs_aliases == FALSE

(*
Pure function operators
*)

\* @type: () => SLIT;
BlankSlit == [type |-> "blank", promiseId |-> 0, watchers |-> {}, creator |-> "None"]

\* @type: (SLIT, VAT) => SLIT;
SlitPlusWatcher(slit, v) == [slit EXCEPT !.watchers = @ \cup {v}] 

\* @type: (SLIT, VAT) => SLIT;
SlitLessWatcher(slit, v) == IF slit.watchers = {v} 
                            THEN BlankSlit
                            ELSE [slit EXCEPT !.watchers = @ \ {v}] 

\* @type: (VAT) => SLIT;
SlitWithVatRef(v) == [type |-> "vat", promiseId |-> 0, watchers |-> {v}, creator |-> v] 

\* @type: (VAT, Int) => SLIT;
SlitWithPromise(v, promiseId) == [type |-> "promise", promiseId |-> promiseId, watchers |-> {v}, creator |-> v] 

\* @type: (VAT, Int) => SLIT;
SlitWithResolver(v, promiseId) == [type |-> "resolver", promiseId |-> promiseId, watchers |-> {v}, creator |-> v] 

\* @type: (BANK, VAT, VAT) => Bool;
ASeesB(bank_, a, b) == 
    \E i \in DOMAIN bank_:
    /\ bank_[i].type = "vat"
    /\ bank_[i].creator = b
    /\ a \in bank_[i].watchers

\* @type: (BANK, Int) => Int;
PromiseIxOrNeg1(bank_, promiseId) ==
    LET
        \* @type: (Int, Int) => Int; 
        Combine(i, j) == 
            IF /\ bank_[j].type = "promise"
               /\ bank_[j].promiseId = promiseId
            THEN j
            ELSE i
    IN FoldSet(Combine, (0-1), DOMAIN bank_)


===============================================================================
