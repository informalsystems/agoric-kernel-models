------------------------------------ MODULE userspace -----------------------------
(*
  The model of the userspace VAT interactions via Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  This is the main model file, which is complemented by:
    - typedefs.tla (defines types and auxiliary operators)
    - MC_userspace.tla (defines constants and Apalache trace views)

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

CONSTANTS
    \* @type: Set(VAT);
    VATS,
    \* @type: Int;
    NUM_SLITS

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

\* @type: (VAT) => Set(Int);
SlitsWatchedBy(v) == {i \in DOMAIN bank : v \in bank[i].watchers}

\* @type: () => Set(Int);
BlankSlits == {i \in DOMAIN bank : bank[i].type = "blank"}

\* Useful for debugging
BlankBank == [i \in (0..(NUM_SLITS-1)) |-> BlankSlit]

ConnectedVatBanks == 
    LET 
        PossibleSlits == {BlankSlit} \cup 
        [
        type : {"vat"},
        promiseId : {0},
        watchers : {{"vt0", "vt1", "vt2"}, {"vt0", "vt1"}, {"vt0", "vt2"}, {"vt0"}, {"vt2", "vt1"}, {"vt1"}, {"vt2"}},
        creator : VATS
        ]
    IN [(0..(NUM_SLITS-1)) -> PossibleSlits]

Init ==
    /\ step_cnt = 0
    /\ step = "init"
    \* /\ bank = BlankBank
    /\ bank \in ConnectedVatBanks
    /\ curr \in VATS
    /\ cnt_promise = 0
    /\ resolve_target = 0

TransferControlStep == 
    /\ UNCHANGED <<bank, cnt_promise, resolve_target>>
    /\ step' = "transferControl"
    /\ curr' \in VATS \ {curr}

SendItemStep ==
    LET
        SendItemAction(i, otherVat) ==
            /\ UNCHANGED <<curr, cnt_promise, resolve_target>>
            /\ step' = "sendItem"
            /\ bank' = [bank EXCEPT ![i] = SlitPlusWatcher(@, otherVat)]
    IN
    \E i \in SlitsWatchedBy(curr):
    \E otherVat \in VATS \ bank[i].watchers:
    /\ ASeesB(bank, curr, otherVat)
    /\ SendItemAction(i, otherVat)

DropItemStep == 
    \E i \in SlitsWatchedBy(curr):
    /\ UNCHANGED <<curr, cnt_promise, resolve_target>>
    /\ step' = "dropItem"
    /\ bank' = [bank EXCEPT ![i] = SlitLessWatcher(@, curr)]

StoreSelfRefStep ==
    \E i \in BlankSlits :
    /\ UNCHANGED <<curr, cnt_promise, resolve_target>>
    /\ step' = "storeSelfRef"
    /\ bank' = [bank EXCEPT ![i] = SlitWithVatRef(curr)]

StorePromiseStep == 
    LET
        StorePromiseAction(i, j, promiseId) ==
        LET 
            Mapped(k) ==
            CASE k = i -> SlitWithPromise(curr, promiseId)
            []   k = j -> SlitWithResolver(curr, promiseId)
            []   OTHER -> bank[k]
        IN 
        /\ UNCHANGED <<curr,resolve_target>>
        /\ step' = "storePromise"
        /\ cnt_promise' = cnt_promise + 1
        /\ bank' = [k \in DOMAIN bank |-> Mapped(k)]
    IN
    \E i, j \in BlankSlits :
    /\ i # j 
    /\ StorePromiseAction(i, j, cnt_promise')

ResolveStep == 
    LET
        \* @type: (Int, Int, Int) => Bool;
        ResolvePromisePre(resolverIx, promiseIx, resolveItemIx) ==
            /\ bank[resolverIx].type = "resolver"
            /\ promiseIx # -1
            \* Don't resolve promise itself (banned by JS)
            /\ resolveItemIx # promiseIx
            \* Cannot resolve a promise to another promise object (banned by JS)
            /\ bank[resolveItemIx].type # "promise"
    IN
    LET 
        ResolvePromiseAction(resolverIx, promiseIx, resolveItemIx) == 
        LET
            Mapped(k) ==
            CASE k = promiseIx        -> BlankSlit
            []   k = resolverIx       -> BlankSlit
            []   k = resolveItemIx -> [
                                        bank[resolveItemIx]
                                        EXCEPT
                                        !.watchers = @ \cup bank[promiseIx].watchers
                                    ]
            []   OTHER                -> bank[k]
        IN
        /\ UNCHANGED <<curr, cnt_promise>>
        /\ bank' = [k \in DOMAIN bank |-> Mapped(k)]
        /\ resolve_target' = resolveItemIx
        /\ step' = "resolve"
    IN
    LET
        ResolvePromiseInner(resolverIx, resolveItemIx) ==
            LET 
                \* @type: () => Int;
                PromiseIx == PromiseIxOrNeg1(bank, bank[resolverIx].promiseId)
            IN
            /\ ResolvePromisePre(resolverIx, PromiseIx, resolveItemIx)
            /\ ResolvePromiseAction(resolverIx, PromiseIx, resolveItemIx)
    IN
    \E resolverIx, resolveItemIx \in SlitsWatchedBy(curr) :
    ResolvePromiseInner(resolverIx, resolveItemIx)
    
Next == 
    \* Util purposes only
    /\ step_cnt' = step_cnt + 1
    /\
        \/ SendItemStep
        \* \/ DropItemStep 
        \/ StoreSelfRefStep 
        \/ StorePromiseStep
        \/ ResolveStep
        \/ TransferControlStep

===============================================================================
