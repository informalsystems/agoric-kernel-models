---- MODULE kernel_enhanced ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache, typedefs
EXTENDS  Integers, FiniteSets, Sequences, TLC, tlcFolds

(*
  A high fidelity model of garbage collection interactions in the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  This is the main model file, which is complemented by:
    - typedefs.tla (defines types and auxiliary operators)

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
    - Daniel Tisdall <daniel@informal.systems>
    - Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  22.12.2021
*)


(*

Notes:

1)
This model does not model data slots in messages. This is because it is hard to
understand processMaybeFree (https://github.com/Agoric/agoric-sdk/issues/4175), and it
drastically increases the complexity of the model. Ommiting data slots does have implications
in several places, most notably promises do not resolve to anything and promise notify DFS
is not required.

2)
Syscalls are 'single shot': only one thing is referenced in GC syscalls and subscribe. send and notify
syscalls only reference one thing (as opposed to the code where an array of things can be referenced).

*)

VARIABLES
    (*
    ~~~~~~~~~~~~~~~
    'parameterization' variables below
    *)

    (*
        Pipelining enabled for vat? 
    @type: VAT_ID -> Bool; *)
    pipeliningEnabled,

    (*
    ~~~~~~~~~~~~~~~
    'meta' variables below
    *)

    (*
    @type: Str; *)
    actionTaken,

    (*
    @type: VAT_ID -> Int; *)
    lifetimeSyscalls,

    (*
        The current executor in the program call stack. It
        can be either the kernel or a vat.
    @type: Str; *)
    executor,

    (*
        The allowed behavior of the current executor.
        if kernel:
            processGcAction
            runLoopBody
            processMaybeFree
        if vat:
            gcSyscall
            anySyscall
    @type: Str; *)
    executorPermittedOperations,

    (*
        A valid gc action which should be run by the kernel.
        The variable can be the zeroGC_ACTION if there is nothing to run.
    @type: GC_ACTION; *)
    validGcAction,
            
    (*
    ~~~~~~~~~~~~~~~
    'model' variables below
    *) 

    (*
        The set of GC actions
    @type: Set(GC_ACTION); *)
    gcActions,

    (*
        The true reachable/recognizable/unknown state of the thing
        from the perspective of the vat. 
    @type: <<THING_ID, VAT_ID>> -> Str; *)
    vatThingTrueState,

    (*
        All the kernel things.
    @type: THING_ID -> THING; *)
    things,

    (*
        Does the CLIST exist? 
        The CLIST contains mappings
            (vatId, vSlot) to kSlot
            (vatId, kSlot) to vSlot
            (vatId, kSlot) to isReachableFlag
        but we do not model these explicitly.
    @type: <<THING_ID, VAT_ID>> -> Bool; *)
    clistExists,

    (*
        For exporters: true iff a dispatch DropExport has not been sent.
        For importers: true iff vat can reach the object.
    @type: <<THING_ID, VAT_ID>> -> Bool; *)
    isReachable,

    (*
        The kernel run queue. 
    @type: Seq(Q_ENTRY); *)
    runQ,

    (*
        The set of kSlots that should maybe be freed
    @type: Set(THING_ID); *)
    maybeFree

\* @type: Str => Bool;
RecordAction(a) == actionTaken' = a

action_processGcActions == "processGcActions"
action_executeGcAction == "executeGcAction"
action_processMaybeFree == "processMaybeFree"
action_executeRunQueueEntry == "executeRunQueueEntry"
action_dropImportsSyscall == "dropImportsSyscall"
action_retireImportsSyscall == "retireImportsSyscall"
action_retireExportsSyscall == "retireExportsSyscall"
action_sendSyscall == "sendSyscall"
action_subscribeSyscall == "subscribeSyscall"
action_resolveSyscall == "resolveSyscall"
action_tryRunLoopBodyButNothingToDo == "tryRunLoopBodyButNothingToDo"
action_nothing == "nothing"
action_skipSyscall == "skipSyscall"

NullStr == "NullStr"
NullInt == 42

PROMISE_IDS == {"p0", "p1", "p2"}
OBJECT_IDS == {"o0", "o1", "o2"} 
THING_IDS == PROMISE_IDS \cup OBJECT_IDS
VAT_IDS == {"v0", "v1", "v2"}
SYSCALL_LIMIT == 3

KEYS == THING_IDS \X VAT_IDS

PriorityOfVat(v) == 
    CASE v = "v0" -> 1
    []   v = "v1" -> 2
    []   v = "v2" -> 3

TRULY_REACHABLE == "truly_reachable"
TRULY_RECOGNIZABLE == "truly_recognizable"
TRULY_UNKNOWN == "truly_unknown"
KERNEL == "kernel"

(* Natures *)
_retireExports == "retireExports"
_retireImports == "retireImports"
_dropExports == "dropExports"
_unresolved == "unresolved"
_fulfilled == "fulfilled"
_rejected == "rejected"
_promise == "promise"
_object == "object"
_notify == "notify"
_send == "send"

(* Meta natures *)
_processGcActions == "processGcActions"
_runLoopBody == "runLoopBody"
_processMaybeFree == "processMaybeFree"
_gcSyscall == "gcSyscall"
_anySyscall == "anySyscall"
_nothing == "nothing"

\* @type: (THING_ID, VAT_ID) => <<THING_ID, VAT_ID>>;
Key(thingId, vatId) == <<thingId, vatId>>

\* @type: (THING_ID, VAT_ID) => Bool;
IsTrulyReachableByVat(thingId, vatId) == vatThingTrueState[thingId, vatId] = TRULY_REACHABLE

\* @type: Int => Int;
NonNegative(z) == IF 0 < z THEN z ELSE 0

\* @type: THING_ID => NATURE;
nature(id) == things[id].nature

\* @type: THING_ID => Bool;
IsObject(id) == nature(id) = _object

\* @type: THING_ID => Bool;
IsPromise(id) == nature(id )= _promise

\* @type: THING_ID => VAT_ID;
owner(id) == things[id].owner          

\* @type: THING_ID => Seq(MESSAGE);
q(id) == things[id].q

\* @type: THING_ID => NATURE;
status(id) == things[id].status

\* @type: THING_ID => VAT_ID;
decider(id) == things[id].decider

\* @type: THING_ID => Set(VAT_ID);
subscribers(id) == things[id].subscribers

\* @type: THING_ID => Int;
refCnt(id) == things[id].refCnt

\* @type: THING_ID => Int;
reachableCnt(id) == things[id].reachableCnt

\* @type: THING_ID => Int;
recognizableCnt(id) == things[id].recognizableCnt

(*
    The true allocator for a thing is the exporting vat.
    This is known to the kernel via the vatKeeper but is separate
    from the .owner field.

@type: THING_ID => VAT_ID; *)
trueAllocator(id) == things[id].trueAllocator

\* @type: (THING_ID, VAT_ID) => Bool;
IsImportForVat(thingId, vatId) ==
    /\ isReachable[thingId, vatId]
    /\ trueAllocator(thingId) # vatId

\* @type: THING_ID => Set(VAT_ID);
ImportersOfThing(thingId) == { vatId \in VAT_IDS: IsImportForVat(thingId, vatId) }

\* @type: () => Bool;
AddToMaybeFree == maybeFree' = maybeFree \cup {
    id \in THING_IDS :
        \/ /\ things[id].reachableCnt     # 0
           /\ things[id].reachableCnt'    = 0
        \/ /\ things[id].recognizableCnt  # 0
           /\ things[id].recognizableCnt' = 0
        \/ /\ things[id].refCnt           # 0
           /\ things[id].refCnt'          = 0
}

\* @type: (THING_ID) => THING; 
ThingWithDecrementedCounters(id) == [
    things[id] EXCEPT 
    !.refCnt = IF IsPromise(id) THEN NonNegative(@-1) ELSE @,
    !.recognizableCnt = IF IsObject(id) THEN NonNegative(@-1) ELSE @,
    !.reachableCnt = IF IsObject(id) THEN NonNegative(@-1) ELSE @
]

\* @type: (THING_ID) => THING; 
zero_THING(id) == [
        nature          |-> IF id \in PROMISE_IDS THEN _promise ELSE _object,
        owner           |-> NullStr,
        q               |-> <<>>,
        status          |-> NullStr,
        decider         |-> NullStr,
        subscribers     |-> {},
        refCnt          |-> 0,
        reachableCnt    |-> 0,
        recognizableCnt |-> 0,
        trueAllocator   |-> NullStr
    ]

IsZeroThing(id) == things[id] = zero_THING(id)

\* @type: () => GC_ACTION; 
zero_GC_ACTION == [
        nature      |-> NullStr,
        objId     |-> NullStr,
        targetVatId |-> NullStr, \* Used when adding to gcActions
        groupedObjIds |-> {} \* Used for agglomoration when dispatching
    ]

\* @type: (THING_ID, VAT_ID) => Q_ENTRY;
new_notify_Q_ENTRY(promiseId, targetVatId) == [ 
        nature                   |-> _notify,
        msgForSend               |-> [argId |-> NullStr, resultId |-> NullStr], 
        targetIdForSend          |-> NullStr,
        targetVatIdForNotify     |-> targetVatId,
        promIdForNotify       |-> promiseId
    ]

\* @type: (THING_ID, THING_ID, THING_ID) => Q_ENTRY;
new_send_Q_ENTRY(messageArgId, messageResultId, targetThingId) == [ 
        nature                   |-> _send,
        msgForSend               |-> [argId |-> messageArgId, resultId |-> messageResultId], 
        targetIdForSend          |-> targetThingId,
        targetVatIdForNotify     |-> NullStr,
        promIdForNotify       |-> NullStr
    ]

(*
~~~~~~~~~~~~~~~~~~~~~~~~~
Define helpers for creating an initial configuration:
v0 exports o0 to v1, v2
v0 exports p0 to v1, v2

*)

\* @type: () => <<THING_ID, VAT_ID>> -> Str;
InitVatThingTrueState == LET
    \* @type: () => <<THING_ID, VAT_ID>> -> Str;
    Special == 
            Key("o0", "v0") :> TRULY_REACHABLE @@
            Key("o0", "v1") :> TRULY_REACHABLE @@
            Key("o0", "v2") :> TRULY_REACHABLE @@
            Key("p0", "v0") :> TRULY_REACHABLE @@
            Key("p0", "v1") :> TRULY_REACHABLE @@
            Key("p0", "v2") :> TRULY_REACHABLE
    \* @type: () => <<THING_ID, VAT_ID>> -> Str;
    Remainder == [e \in KEYS |-> TRULY_UNKNOWN]
    IN Special @@ Remainder

\* @type: () => THING_ID -> THING;
InitThings == LET
    \* @type: () => THING_ID -> THING;
    Special == 
        "o0" :>  [
            nature          |-> _object,
            owner           |-> "v0",
            q               |-> <<>>,
            status          |-> NullStr,
            decider         |-> NullStr,
            subscribers     |-> {},
            refCnt          |-> 0,
            reachableCnt    |-> 2,
            recognizableCnt |-> 2,
            trueAllocator   |-> "v0" ] @@ 
        "p0" :> [
            nature          |-> _promise,
            owner           |-> NullStr,
            q               |-> <<>>,
            status          |-> _unresolved,
            decider         |-> "v0",
            subscribers     |-> {"v0", "v1", "v2"},
            refCnt          |-> 3,
            reachableCnt    |-> 0,
            recognizableCnt |-> 0,
            trueAllocator   |-> "v0" ]
    \* @type: () => THING_ID -> THING;
    Remainder == [e \in THING_IDS |-> zero_THING(e)]
    IN Special @@ Remainder

\* @type: () => <<THING_ID, VAT_ID>> -> Bool;
InitClistExists ==
    LET
    Special == 
            Key("o0", "v0") :> TRUE @@
            Key("o0", "v1") :> TRUE @@
            Key("o0", "v2") :> TRUE @@
            Key("p0", "v0") :> TRUE @@
            Key("p0", "v1") :> TRUE @@
            Key("p0", "v2") :> TRUE
    Remainder == [e \in KEYS |-> FALSE]
    IN Special @@ Remainder

\* @type: () => <<THING_ID, VAT_ID>> -> Bool;
InitIsReachable == LET
    Special == 
            Key("o0", "v0") :> TRUE @@ 
            Key("o0", "v1") :> TRUE @@ 
            Key("o0", "v2") :> TRUE @@ 
            Key("p0", "v0") :> TRUE @@ 
            Key("p0", "v1") :> TRUE @@ 
            Key("p0", "v2") :> TRUE 
    Remainder == [e \in KEYS |-> FALSE]
    IN Special @@ Remainder

\* @type: () => Bool;
Init ==
    /\ actionTaken = "init"
    /\ lifetimeSyscalls = [v \in VAT_IDS |-> 0]
    /\ pipeliningEnabled \in [VAT_IDS -> BOOLEAN]
    /\ executor \in VAT_IDS
    /\ executorPermittedOperations = _anySyscall
    /\ validGcAction = zero_GC_ACTION
    /\ gcActions = {}
    /\ vatThingTrueState = InitVatThingTrueState
    /\ things = InitThings
    /\ clistExists = InitClistExists
    /\ isReachable = InitIsReachable
    /\ runQ = <<>>
    /\ maybeFree = {}

(*
    Process gcActions, deleting invalid ones and collecting
    a set of valid ones into validGcAction (if possible).
@type: () => Bool; *)
ProcessGcActions == 
    LET
    \* @type: () => Set(GC_ACTION);
    ValidActions ==
        LET Valid(nat, objId, targetVatId) ==
            CASE nat = _dropExports -> 
                /\ ~IsZeroThing(objId)
                /\ 0 = reachableCnt(objId)
                /\ clistExists[objId, targetVatId]
                /\ isReachable[objId, targetVatId]
            [] nat = _retireExports -> 
                /\ ~IsZeroThing(objId)
                /\ 0 = reachableCnt(objId)
                /\ 0 = recognizableCnt(objId)
                /\ clistExists[objId, targetVatId]
            [] nat = _retireImports -> 
                clistExists[objId, targetVatId]
        IN
        {
            e \in gcActions : Valid(e.nature, e.objId, e.targetVatId)
        }
    IN
    LET
    \* @type: NATURE => Int;
    PriorityOfNature(n) ==
            CASE n = _retireImports -> 1 
            [] n =  _retireExports -> 2 
            [] n =  _dropExports -> 3 \* Greater number <=> higher priority
    \* @type: () => Set(GC_ACTION);
    InvalidActions == gcActions \ ValidActions
    IN
    LET
    \* @type: GC_ACTION => Bool;
    PrecedenceIsMaximal(candidate) == 
        \* Vat must be highest priority among those with valid actions
        /\ \A e \in ValidActions:
           PriorityOfVat(e.targetVatId) <= PriorityOfVat(candidate.targetVatId)
        \* Action must have highest priority among those for the vat
        /\ \A e \in ValidActions: 
           \/ candidate.targetVatId # e.targetVatId
           \/ PriorityOfNature(e.nature) <= PriorityOfNature(candidate.nature)
    (*
    Deleted actions are 
        invalid actions with not lower priority from the same vat
        all actions from a higher priority vat
    *)
    \* @type: GC_ACTION => Set(GC_ACTION);
    DeletedActions(chosenAction) == 
        {
            e \in InvalidActions : 
                \* Higher priority vats have only invalid actions and all are deleted
                \/ PriorityOfVat(chosenAction.targetVatId) < PriorityOfVat(e.targetVatId)
                \* Deleted actions from the same vat have not lower priority
                \/ /\ chosenAction.targetVatId = e.targetVatId
                   /\ PriorityOfNature(chosenAction.nature) <= PriorityOfNature(e.nature)
        }
    \* @type: GC_ACTION => Set(GC_ACTION);
    SimilarActions(chosenAction) == {
        e \in ValidActions :
            /\ e.targetVatId = chosenAction.targetVatId
            /\ e.nature = chosenAction.nature
    }
    IN
    /\ \/ \E e \in ValidActions :
          /\ PrecedenceIsMaximal(e)
          \* Group all same-priority, same-vat actions
          /\ validGcAction' = [
                nature          |-> e.nature,
                objId         |-> NullStr,
                groupedObjIds |-> { a.objId : a \in SimilarActions(e) },
                targetVatId     |-> e.targetVatId
            ]
          /\ gcActions' = gcActions \ DeletedActions(e)
       \/ /\ ValidActions = {}
          /\ validGcAction' = zero_GC_ACTION
          /\ gcActions' = {} \* If there was no valid action then all actions were deleted
    /\ UNCHANGED <<vatThingTrueState, things, clistExists, isReachable, runQ, maybeFree>>
    /\ RecordAction(action_processGcActions)

(*
    Execute a valid GC action. This includes all kernel side processing and dispatch.

@type: (NATURE, VAT_ID, Set(THING_ID)) => Bool; *)
ExecuteGcAction(nat, targetVatId, groupedObjIds) ==
    LET
        RelevantKeys == groupedObjIds \X {targetVatId}
    IN
    LET
    \* @type: () => Bool;
    DropExportsCase ==
        /\ vatThingTrueState' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN
                    \* If reachable send to recognizable
                    \* Otherwise it is already recognizable or unknown
                    IF vatThingTrueState[key] = TRULY_REACHABLE
                    THEN TRULY_RECOGNIZABLE
                    ELSE vatThingTrueState[key]
                ELSE vatThingTrueState[key]
            ]
        /\ UNCHANGED things
        /\ UNCHANGED clistExists
        /\ isReachable' = [
                key \in KEYS |->
                IF key \in RelevantKeys 
                THEN FALSE 
                ELSE isReachable[key]
            ]
    \* @type: () => Bool;
    RetireExportsCase ==
        /\ vatThingTrueState' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN TRULY_UNKNOWN
                ELSE vatThingTrueState[key]
            ]
        /\ things' = [
                id \in THING_IDS |->
                IF id \in groupedObjIds 
                THEN zero_THING(id)
                ELSE things[id]
            ]
        /\ clistExists' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN FALSE
                ELSE clistExists[key]
            ]
        /\ isReachable' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN FALSE
                ELSE isReachable[key]
            ]
    \* @type: () => Bool;
    RetireImportsCase ==
        LET
        (*
        @type: THING_ID => THING; *)
        UpdatedThing(id) == [things[id] EXCEPT 
            !.recognizableCnt = NonNegative(@-1),
            !.reachableCnt = IF isReachable[id, targetVatId] THEN NonNegative(@-1) ELSE @
        ]
        IN
        /\ vatThingTrueState' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN TRULY_UNKNOWN
                ELSE vatThingTrueState[key]
            ]
        /\ things' = [
                id \in THING_IDS |->
                IF id \in groupedObjIds 
                THEN UpdatedThing(id)
                ELSE things[id]
            ]
        /\ clistExists' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN FALSE
                ELSE clistExists[key]
            ]
        /\ isReachable' = [
                key \in KEYS |->
                IF key \in RelevantKeys
                THEN FALSE
                ELSE isReachable[key]
            ]
    IN
    /\ CASE nat = _dropExports   ->   DropExportsCase
         [] nat = _retireExports -> RetireExportsCase
         [] nat = _retireImports -> RetireImportsCase
    /\ AddToMaybeFree
    /\ UNCHANGED runQ
    /\ RecordAction(action_executeGcAction)
    
(*
    Garbage collect promises, and add actions to gcActions
    for objects.
    Essentially models kernelKeeper::processRefcounts

@type: () => Bool; *)
ProcessMaybeFree ==
    LET
    Objects == {id \in maybeFree : IsObject(id)}
    Promises == {id \in maybeFree : IsPromise(id)}
    IN
    /\ maybeFree' = {}
    /\ things' = [id \in THING_IDS |->
            IF /\ id \in Promises
               /\ refCnt(id) = 0
            THEN zero_THING(id)
            ELSE things[id]
        ]
    /\ LET  
        \* @type: () => Set(GC_ACTION);
        NewDropExports == 
            LET 
            \* @type: () => Set(THING_ID);
            ids == {
                id \in Objects:
                /\ reachableCnt(id) = 0
                (*
                This owner check seems unnecessary but it authentically
                mirrors the code.
                *)
                /\ owner(id) # NullStr
                /\ isReachable[id, owner(id)]
            } IN {
                [
                    nature |-> _dropExports,
                    objId |-> id,
                    targetVatId |-> owner(id),
                    groupedObjIds |-> {}
                ] : id \in ids
            }
        \* @type: () => Set(GC_ACTION);
        NewRetireExports == 
            LET
            \* @type: () => Set(THING_ID);
            ids == {
                id \in Objects:
                /\ reachableCnt(id) = 0
                /\ recognizableCnt(id) = 0
                (*
                This owner check seems unnecessary but it authentically
                mirrors the code.
                *)
                /\ owner(id) # NullStr
            } IN {
                [
                    nature |-> _retireExports,
                    objId |-> id,
                    targetVatId |-> owner(id),
                    groupedObjIds |-> {}
                ] : id \in ids
            }
        IN
        gcActions' = gcActions \cup NewDropExports \cup NewRetireExports
    /\ UNCHANGED <<vatThingTrueState, clistExists, isReachable, runQ >>
    /\ RecordAction(action_processMaybeFree)

(*

@type: Q_ENTRY => Bool; *)
ExecuteRunQueueEntry(e) ==
    LET
        \* @type: (THING_ID, THING_ID, THING_ID) => Bool;
        SendCase(targetThingId, argId, resultId) ==
        (*
        Pseudocode:
        decrement counts of the three things
        update maybeFree
        if target is promise and status is not _unresolved
            for all subscribers of resultId
                add new_notify(resultId, subscriber) to runQ
                resultId.refCnt++
            for all m in q(resultId)
                add new_send(m.argId, m.resultId, resultId) to runQ
            resultId.q = <<>>
            resultId.subscribers = {}
            resultId.decider = null
            resultId.status = rejected
        if target is promise and is _unresolved and (target.decider = null or pipelining disabled)
            target.refCnt++
            resultId.refCnt++
            incrementRefCounts(argId)
            add m = [ argId |-> argId, resultId |-> resultId] to q of target
        if target is object
            map target to vSlot (through target.owner)
            map argId to vSlot (through target.owner)
            map resultId to vSlot (through target.owner)
            resultId.decider = target.owner
        if target is promise and is _unresolved and target.decider != null and pipelining enabled
            map target to vSlot (through target.decider)
            map argId to vSlot (through target.decider)
            map resultId to vSlot (through target.decider)
            resultId.decider = target.decider
        *)
        LET
        (*
        This occurs when sending a message to a resolved promise.
        The result promise of this send is rejected and its message queue is
        moved back on to the runQ to be delivered later.
        @type: () => Bool; *)
        ResolvedPromiseCase ==
            LET
            \* @type: () => Seq(Q_ENTRY); 
            newNotifies ==
                LET 
                (*
                The result promise will now be rejected so notify its subscribers.
                @type: (Seq(Q_ENTRY), VAT_ID) => Seq(Q_ENTRY); *)
                Combine(acc, subscriber) == acc \o <<new_notify_Q_ENTRY(resultId, subscriber)>>
                IN FoldSet(Combine, <<>>, subscribers(resultId)) 
            \* @type: () => Seq(Q_ENTRY); 
            newSends ==
                LET 
                (*
                The result promise will now be rejected so requeue its queue
                back onto the send queue to be handled in future.
                @type: (Seq(Q_ENTRY), MESSAGE) => Seq(Q_ENTRY); *)
                Combine(acc, m) == acc \o <<new_send_Q_ENTRY(m.argId, m.resultId, resultId)>>
                IN FoldSeq(Combine, <<>>, q(resultId)) 
            IN
            /\ executor' = KERNEL
            /\ executorPermittedOperations' = _processMaybeFree
            /\ UNCHANGED vatThingTrueState
            /\ things' = [ id \in THING_IDS |->
                CASE  id = targetThingId -> ThingWithDecrementedCounters(id)
                  []  id = argId -> ThingWithDecrementedCounters(id)
                  []  id = resultId -> [
                        things[id] EXCEPT 
                        !.q = <<>>,
                        !.subscribers = {},
                        !.decider = NullStr,
                        !.status = _rejected,
                        !.refCnt = NonNegative(@ + Cardinality(subscribers(id)) - 1)
                    ]
                  [] OTHER -> things[id]
                ]
            /\ UNCHANGED clistExists
            /\ UNCHANGED isReachable
            /\ runQ' = Tail(runQ) \o newNotifies \o newSends

        (*
        The promise is not yet resolved so we add the message to its queue. 
        @type: () => Bool; *)
        PromiseQueueCase ==
            /\ executor' = KERNEL
            /\ executorPermittedOperations' = _processMaybeFree
            /\ UNCHANGED vatThingTrueState
            /\ things' = [ things EXCEPT
                    ![targetThingId] = [@ EXCEPT
                        !.q = @ \o <<[argId|->argId, resultId|->resultId]>>,
                        !.refCnt = NonNegative(@-1) \* One count is lost by popping the runQ
                        ]
                ]
            /\ UNCHANGED clistExists
            /\ UNCHANGED isReachable
            /\ runQ' = Tail(runQ)

        (*
        The target of the message is an object, or a promise with pipelining, so we
        divert the message to the owner/decider of the target thing.
        @type: (VAT_ID) => Bool; *)
        ObjectCaseAndPipelinedCase(targetVat) ==
               \* The target vat might be able to perform any syscall afterwards
            /\ \/ /\ executor' = targetVat
                  /\ executorPermittedOperations' = _anySyscall
                \* It may not...
                \/ /\ executor' = KERNEL
                   /\ executorPermittedOperations' = _processMaybeFree
            /\ vatThingTrueState' = [
                    key \in KEYS |-> 
                    IF key \in ({targetThingId, argId} \X {targetVat})
                    THEN TRULY_REACHABLE
                    ELSE vatThingTrueState[key]
                ]
            /\ things' = [ id \in THING_IDS |->
                    CASE id \in {targetThingId, argId} -> [things[id] EXCEPT
                            \* Target thing can be promise or object
                                !.refCnt = 
                                    IF ~IsPromise(id) THEN @ 
                                    ELSE 
                                    IF
                                    ~clistExists[id, targetVat]
                                    THEN @
                                    ELSE NonNegative(@-1),
                                !.recognizableCnt = 
                                    IF ~IsObject(id) THEN @
                                    ELSE
                                    IF
                                    /\ ~clistExists[id, targetVat]
                                    (*
                                    Note: I once did a detailed read of the code, and I found
                                    that there is a no check here, to check if the targetVat is
                                    the exporter or not. However, I have added a check here because
                                    1. It seems to make sense
                                    2. I might have made a mistake when I read the code
                                    *)
                                    /\ owner(id) # targetVat
                                    THEN @
                                    ELSE NonNegative(@-1),
                                !.reachableCnt = 
                                    IF ~IsObject(id) THEN @
                                    ELSE
                                    IF
                                    /\ ~isReachable[id, targetVat]
                                    /\ trueAllocator(id) # targetVat 
                                    THEN @
                                    ELSE NonNegative(@-1)
                            ]
                    []  id = resultId -> [
                            things[id] EXCEPT 
                            !.refCnt = IF ~clistExists[id, targetVat] 
                                       THEN @ 
                                       ELSE NonNegative(@-1),
                            !.decider = targetVat 
                        ]
                    [] OTHER -> things[id]
                ]
            /\ clistExists' = [
                    k \in KEYS |->
                    CASE k = Key(targetThingId, targetVat) -> TRUE
                      [] k = Key(argId, targetVat) -> TRUE
                      [] k = Key(resultId, targetVat) -> TRUE
                      [] OTHER -> clistExists[k]
                ]
            /\ isReachable' = [
                    k \in KEYS |->
                    \* If the allocator is not targetVat then we do set the isReachableFlag
                    CASE k = Key(targetThingId, targetVat) -> isReachable[k] \/ trueAllocator(targetThingId) # targetVat 
                      [] k = Key(argId, targetVat) -> isReachable[k] \/ trueAllocator(argId) # targetVat 
                      [] k = Key(resultId, targetVat) -> isReachable[k] \/ trueAllocator(resultId) # targetVat 
                      [] OTHER -> isReachable[k]
                ]
            /\ runQ' = Tail(runQ)
        IN
        CASE /\ IsPromise(targetThingId) 
             /\ status(targetThingId) # _unresolved   
          -> ResolvedPromiseCase
          [] /\ IsPromise(targetThingId)
             /\ status(targetThingId) = _unresolved
             /\ \/ decider(targetThingId) = NullStr
                \/ ~pipeliningEnabled[decider(targetThingId)]
          -> PromiseQueueCase
          [] \/ IsObject(targetThingId)                  
          -> ObjectCaseAndPipelinedCase(owner(targetThingId))
          [] /\ IsPromise(targetThingId)
             /\ status(targetThingId) = _unresolved   
             /\ decider(targetThingId) # NullStr
             /\ pipeliningEnabled[decider(targetThingId)]
          -> ObjectCaseAndPipelinedCase(decider(targetThingId))

        (*
        Note: does not model recursive promise notification (as we do not model data slot)
        @type: (VAT_ID, THING_ID) => Bool; *)
        NotifyCase(targetVatId, promId) == 
               \* The target vat might be able to perform any syscall afterwards
            /\ \/ /\ executor' = targetVatId
                  /\ executorPermittedOperations' = _anySyscall
                \* It may not...
                \/ /\ executor' = KERNEL
                   /\ executorPermittedOperations' = _processMaybeFree
            /\ vatThingTrueState' = [
                    vatThingTrueState EXCEPT ![promId, targetVatId] = TRULY_UNKNOWN
                ]
            /\ things' = [things EXCEPT 
                    (*
                    Decremented once or twice:
                    1. once for popping the runQ entry
                    2. once because the targetVat might destroy the promise
                    *)
                    ![promId] = [ @ EXCEPT !.refCnt = 
                                    IF clistExists[promId, targetVatId]
                                    THEN NonNegative(@ - 2)
                                    ELSE NonNegative(@ - 1)
                                ]
                ]
            /\ clistExists' = [
                    clistExists EXCEPT ![promId, targetVatId] = FALSE
                ]
            /\ isReachable' = [
                    isReachable EXCEPT ![promId, targetVatId] = FALSE
                ]
            /\ runQ' = Tail(runQ)
    IN
    /\ CASE e.nature = _send   -> SendCase(e.targetIdForSend, e.msgForSend.argId, e.msgForSend.resultId)
         [] e.nature = _notify -> NotifyCase(e.targetVatIdForNotify, e.promIdForNotify)
    /\ AddToMaybeFree
    /\ RecordAction(action_executeRunQueueEntry)

(*

@type: VAT_ID => Bool; *)
dropImportsSyscall(v) == 
    LET
    Preconditions(id) ==
        /\ vatThingTrueState[id, v] = TRULY_REACHABLE
        /\ trueAllocator(id) # v
    Action(id) == 
        /\ UNCHANGED gcActions
        /\ vatThingTrueState' = [vatThingTrueState EXCEPT ![id, v] = TRULY_RECOGNIZABLE]
        /\ things' = [ things EXCEPT ![id] = [ @ EXCEPT !.reachableCnt = NonNegative(@-1) ] ] 
        /\ isReachable' = [isReachable EXCEPT ![id, v] = FALSE]
        /\ AddToMaybeFree
        /\ UNCHANGED <<clistExists, runQ>>
    IN
    \E id \in OBJECT_IDS:
    /\ Preconditions(id)
    /\ Action(id)
    /\ RecordAction(action_dropImportsSyscall)
    
(*

@type: VAT_ID => Bool; *)
retireImportsSyscall(v) ==
    LET
    Preconditions(id) == 
        /\ vatThingTrueState[id, v] = TRULY_RECOGNIZABLE
        /\ trueAllocator(id) # v
    Action(id) == 
        /\ UNCHANGED gcActions
        /\ vatThingTrueState' = [vatThingTrueState EXCEPT ![id, v] = TRULY_UNKNOWN]
        /\ things' = [things EXCEPT 
                ![id] = [ @ EXCEPT 
                    \* Imports are always objects
                    !.reachableCnt = IF isReachable[id, v] THEN NonNegative(@-1) ELSE @,
                    !.recognizableCnt = NonNegative(@-1)
                ]
            ]
        /\ clistExists' = [clistExists EXCEPT ![id, v] = FALSE]
        /\ isReachable' = [isReachable EXCEPT ![id, v] = FALSE]
        /\ AddToMaybeFree
        /\ UNCHANGED runQ
    IN
    \E id \in OBJECT_IDS:
    /\ Preconditions(id)
    /\ Action(id)
    /\ RecordAction(action_retireImportsSyscall)

(*

@type: VAT_ID => Bool; *)
retireExportsSyscall(v) ==
    LET
    Preconditions(id) == 
        /\ vatThingTrueState[id, v] = TRULY_RECOGNIZABLE
        /\ trueAllocator(id) = v
    Action(id) == 
        LET
        \* @type: () => Set(GC_ACTION);
        NewRetireImports == {
                [
                    nature |-> _retireImports,
                    objId |-> id,
                    targetVatId |-> targetVatId,
                    groupedObjIds |-> {}
                ] : targetVatId \in ImportersOfThing(id)
            }
        IN
        /\ gcActions' = gcActions \cup NewRetireImports
        /\ vatThingTrueState' = [vatThingTrueState EXCEPT ![id, v] = TRULY_UNKNOWN]
        /\ things' = [things EXCEPT ![id] = zero_THING(id)]
        /\ clistExists' = [clistExists EXCEPT ![id, v] = FALSE]
        /\ isReachable' = [isReachable EXCEPT ![id, v] = FALSE]
        /\ AddToMaybeFree
        /\ UNCHANGED runQ
    IN
    \E id \in OBJECT_IDS:
    /\ Preconditions(id)
    /\ Action(id)
    /\ RecordAction(action_retireExportsSyscall)

(*

@type: (VAT_ID) => Bool; *)
sendSyscall(v) ==
    LET
    \* @type: (THING_ID, THING_ID, THING_ID) => Bool;
    Preconditions(targetThingId, messageArgId, messageResultId) ==
        \* The message result promise must be an unused slot
        /\ IsZeroThing(messageResultId)
        /\ \/ IsTrulyReachableByVat(targetThingId, v) 
           \/ IsZeroThing(targetThingId)
        /\ \/ IsTrulyReachableByVat(messageArgId, v) 
           \/ IsZeroThing(messageArgId)
        /\ targetThingId # messageArgId
        /\ targetThingId # messageResultId
        /\ messageArgId # messageResultId

    \* @type: (THING_ID, THING_ID, THING_ID) => Bool;
    Action(targetThingId, messageArgId, messageResultId) == 
        LET 
        \* @type: () => Set(THING_ID);
        Refs == {targetThingId, messageArgId, messageResultId}
        RelevantKeys == Refs \X {v}

        \* @type: () => THING;
        new_promise_THING == [
                nature          |-> _promise,
                owner           |-> NullStr,
                q               |-> <<>>,
                status          |-> _unresolved,
                decider         |-> v,
                subscribers     |-> {},
                (*
                When a new promise is created in syscallSend the refCnt is
                doubly incremented (because the vat will have a reference to it
                and the send queue message will have a reference to it).
                *)
                refCnt          |-> 2,
                reachableCnt    |-> 0,
                recognizableCnt |-> 0,
                trueAllocator   |-> v
            ]

        \* @type: () => THING;
        new_result_promise_THING == [
                nature          |-> _promise,
                owner           |-> NullStr,
                q               |-> <<>>,
                status          |-> _unresolved,
                (*
                The promise decider will be set when the message pointing at
                this promise is handled in the runQ.
                *)
                decider         |-> NullStr,
                subscribers     |-> {},
                (*
                When a new promise is created in syscallSend the refCnt is
                doubly incremented (because the vat will have a reference to it
                and the send queue message will have a reference to it).
                *)
                refCnt          |-> 2,
                reachableCnt    |-> 0,
                recognizableCnt |-> 0,
                trueAllocator   |-> v
            ]

        \* @type: () => THING;
        new_object_THING == [
                nature          |-> _object,
                owner           |-> v,
                q               |-> <<>>,
                status          |-> NullStr,
                decider         |-> NullStr,
                subscribers     |-> {},
                refCnt          |-> 0,
                (*
                When a new object is created in syscallSend there is a count
                because of the message in the queue.
                Exporters should not increase the reachableCnt.
                *)
                reachableCnt    |-> 1,
                recognizableCnt |-> 1,
                trueAllocator   |-> v
            ]

        (*
        @type: THING_ID => THING; *)
         Mapped(id) == 
            (* Create new instances *)
            CASE id = messageResultId                                             -> new_result_promise_THING
            []   id # messageResultId /\ IsZeroThing(id) /\ nature(id) = _object  -> new_object_THING
            []   id # messageResultId /\ IsZeroThing(id) /\ nature(id) = _promise -> new_promise_THING

            (* Instance exists already. Increase counts again 
                (because it will be pointed to from queue) *)
            [] OTHER                                      -> [
                things[id] EXCEPT
                !.refCnt = IF IsPromise(id) THEN @ + 1 ELSE @,
                !.reachableCnt = IF IsObject(id) THEN @ + 1 ELSE @,
                !.recognizableCnt = IF IsObject(id) THEN @ + 1 ELSE @
            ]
        IN
        /\ UNCHANGED gcActions
        /\ vatThingTrueState' = [k \in KEYS |->
                IF k \in RelevantKeys THEN TRULY_REACHABLE ELSE vatThingTrueState[k]
            ]
        /\ things' = [id \in THING_IDS |->
                IF id \in Refs THEN Mapped(id) ELSE things[id]
            ]
        \* ensure clist entries for the refs
        /\ clistExists' = [k \in KEYS |-> 
                clistExists[k] \/  k \in RelevantKeys
            ]
        \* ensure isReachable flag if allocated by the sending vat
        /\ isReachable' = [k \in KEYS |-> 
                isReachable[k] \/ (k \in RelevantKeys /\ trueAllocator(k[1]) = v)
            ]
        /\ runQ' = runQ \o <<new_send_Q_ENTRY(messageArgId, messageResultId, targetThingId)>>
        /\ AddToMaybeFree
    IN
    \E targetThingId \in THING_IDS, messageArgId \in THING_IDS, messageResultId \in PROMISE_IDS:
    /\ Preconditions(targetThingId, messageArgId, messageResultId)
    /\ Action(targetThingId, messageArgId, messageResultId)
    /\ RecordAction(action_sendSyscall)

(*

@type: (VAT_ID) => Bool; *)
subscribeSyscall(v) ==
    LET
    \* @type: (THING_ID) => Bool;
    Preconditions(promiseId) == IsTrulyReachableByVat(promiseId, v)
    \* @type: (THING_ID) => Bool;
    Action(promiseId) ==
        /\ UNCHANGED gcActions
        /\  \/ /\ status(promiseId) = _unresolved
               /\ things' = [
                   things EXCEPT ![promiseId] = [
                       @ EXCEPT !.subscribers = @ \cup {v}
                     ]
                    ]
               /\ UNCHANGED runQ
            \/ /\ status(promiseId) # _unresolved
               /\ things' = [
                   things EXCEPT ![promiseId] = [
                       @ EXCEPT !.refCnt = @ + 1
                     ]
                    ]
               /\ runQ' = runQ \o <<new_notify_Q_ENTRY(promiseId, v)>>
        \* ensure clist entries for the refs
        /\ clistExists' = [clistExists EXCEPT ![promiseId, v] = TRUE]
        \* ensure isReachable flag if allocated by the sending vat
        /\ isReachable' = [isReachable EXCEPT ![promiseId, v] = @ \/ trueAllocator(promiseId) = v]
        /\ AddToMaybeFree
        /\ UNCHANGED vatThingTrueState 
    IN
    \E promiseId \in PROMISE_IDS: 
    /\ Preconditions(promiseId)
    /\ Action(promiseId)
    /\ RecordAction(action_subscribeSyscall)

(*

@type: VAT_ID => Bool; *)
resolveSyscall(v) ==
    LET
    \* @type: (THING_ID, NATURE) => Bool;
    Preconditions(promiseId, newStatus) == 
        /\ IsTrulyReachableByVat(promiseId, v)
        /\ decider(promiseId) = v
    \* @type: (THING_ID, NATURE) => Bool;
    Action(promiseId, newStatus) ==
        LET 
        \* @type: () => Set(VAT_ID); 
        otherSubscribers == subscribers(promiseId)\{v}
        IN
        LET
        \* @type: () => Seq(Q_ENTRY); 
        newNotifies ==
            LET 
            \* @type: (Seq(Q_ENTRY), VAT_ID) => Seq(Q_ENTRY);
            Combine(acc, subscriber) == acc \o <<new_notify_Q_ENTRY(promiseId, subscriber)>>
            IN FoldSet(Combine, <<>>, otherSubscribers) 
        \* @type: () => Seq(Q_ENTRY); 
        newSends ==
            LET 
            (* 
            @type: (Seq(Q_ENTRY), MESSAGE) => Seq(Q_ENTRY); *)
            Combine(acc, m) == acc \o <<new_send_Q_ENTRY(m.argId, m.resultId, promiseId)>>
            IN FoldSeq(Combine, <<>>, q(promiseId)) 
        IN
        /\ UNCHANGED gcActions
        /\ vatThingTrueState' = [
                vatThingTrueState EXCEPT ![promiseId, v] = TRULY_UNKNOWN
            ]
        /\ things' = [
            things EXCEPT ![promiseId] = [
                @ EXCEPT
                !.q = <<>>,
                !.subscribers = {},
                !.decider = NullStr,
                !.status = newStatus,
                !.refCnt = NonNegative(@
                    + Len(newNotifies)
                    + Len(newSends)
                    - 1
                    )
                ]
            ]
        /\ clistExists' = [clistExists EXCEPT ![promiseId, v] = FALSE]
        /\ isReachable' = [isReachable EXCEPT ![promiseId, v] = FALSE]
        /\ runQ' = runQ \o newNotifies \o newSends
        /\ AddToMaybeFree
    IN
    \E promiseId \in PROMISE_IDS, newStatus \in {_fulfilled, _rejected}:
    /\ Preconditions(promiseId, newStatus)
    /\ Action(promiseId, newStatus)
    /\ RecordAction(action_resolveSyscall)

Next ==
    /\ UNCHANGED pipeliningEnabled
    /\  \/ /\ executor = KERNEL
           /\ UNCHANGED lifetimeSyscalls
              \* The kernel can run processGcActions()
           /\ \/ /\ executorPermittedOperations = _processGcActions
                 /\ executorPermittedOperations' = _runLoopBody
                 /\ UNCHANGED executor
                 /\ ProcessGcActions
              \* Or take a valid gcAction, process it and deliver it to a vat
              \/ /\ executorPermittedOperations = _runLoopBody
                 /\ validGcAction # zero_GC_ACTION
                    \* The vat might be able to make gc syscalls afterwards
                 /\ \/ /\ executor' = validGcAction.targetVatId
                       /\ executorPermittedOperations' = _gcSyscall
                    \* It may not...
                    \/ /\ UNCHANGED executor
                       /\ executorPermittedOperations' = _processMaybeFree
                 /\ validGcAction' = zero_GC_ACTION
                 /\ UNCHANGED gcActions
                 /\ ExecuteGcAction(validGcAction.nature, validGcAction.targetVatId, validGcAction.groupedObjIds)
              \* Or it should process an item on the run queue
              \/ /\ executorPermittedOperations = _runLoopBody
                 /\ validGcAction = zero_GC_ACTION
                 /\ 0 < Len(runQ) \* changes to runQ are captured in ExecuteRunQueueEntry
                    \* The vat might be able to make arbitrary syscalls afterwards
                 /\ UNCHANGED validGcAction
                 /\ UNCHANGED gcActions
                 /\ ExecuteRunQueueEntry(Head(runQ))
              \* Or there is no more work to do
              \/ /\ executorPermittedOperations = _runLoopBody
                 /\ validGcAction = zero_GC_ACTION
                 /\ Len(runQ) <= 0
                 /\ UNCHANGED <<
                    executor, 
                    validGcAction, 
                    gcActions, 
                    vatThingTrueState, 
                    things, 
                    clistExists, 
                    isReachable, 
                    runQ, 
                    maybeFree>>
                 /\ executorPermittedOperations' = _nothing \* Kernel is finished.
                 /\ RecordAction(action_tryRunLoopBodyButNothingToDo)
              \* Or it should process maybeFree
              \/ /\ executorPermittedOperations = _processMaybeFree
                 /\ executorPermittedOperations' = _processGcActions
                 /\ UNCHANGED executor
                 /\ UNCHANGED validGcAction
                 /\ ProcessMaybeFree
              \* Or the kernel is finished
              \/ /\ executorPermittedOperations = _nothing
                 /\ UNCHANGED <<
                    executor, 
                    executorPermittedOperations,
                    validGcAction, 
                    gcActions, 
                    vatThingTrueState, 
                    things, 
                    clistExists, 
                    isReachable, 
                    runQ, 
                    maybeFree>>
                 /\ RecordAction(action_nothing)
        \/ /\ executor \in VAT_IDS
              \* Either transfer control back to kernel afterwards
           /\ \/ /\ executor' = KERNEL
                 /\ executorPermittedOperations' = _processMaybeFree
              \* Or perform subsequent syscall
              \/ /\ UNCHANGED executor
                 /\ UNCHANGED executorPermittedOperations
           /\ UNCHANGED validGcAction
           /\ \/ /\ UNCHANGED << \* Maybe don't make a syscall
                    vatThingTrueState, 
                    things, 
                    clistExists, 
                    isReachable, 
                    runQ, 
                    maybeFree,
                    gcActions,
                    lifetimeSyscalls>>
                 /\ RecordAction(action_skipSyscall) 
              \/ /\ executorPermittedOperations = _gcSyscall
                 /\ lifetimeSyscalls[executor] < SYSCALL_LIMIT
                 /\ lifetimeSyscalls' = [lifetimeSyscalls EXCEPT ![executor] = @ + 1] 
                 /\ \/ dropImportsSyscall(executor)
                    \/ retireImportsSyscall(executor)
                    \/ retireExportsSyscall(executor)
              \/ /\ executorPermittedOperations = _anySyscall
                 /\ lifetimeSyscalls[executor] < SYSCALL_LIMIT
                 /\ lifetimeSyscalls' = [lifetimeSyscalls EXCEPT ![executor] = @ + 1] 
                 /\ \/ dropImportsSyscall(executor)
                    \/ retireImportsSyscall(executor)
                    \/ retireExportsSyscall(executor)
                    \/ sendSyscall(executor)
                    \/ subscribeSyscall(executor)
                    \/ resolveSyscall(executor)

\* @type: () => Bool;
SaneType == 
    LET
    \* @type: () => Bool;
    NonNegativeCounts ==
        \A id \in THING_IDS :
        /\ 0 <= refCnt(id)
        /\ 0 <= reachableCnt(id)
        /\ 0 <= recognizableCnt(id)
    \* @type: () => Bool;
    CorrectIdentifierTypes ==
        LET
        Executor == executor \in VAT_IDS \cup {KERNEL}
        
        ValidGcAction == 
           \/ validGcAction = zero_GC_ACTION
           \/ /\ validGcAction.nature \in {_dropExports, _retireExports, _retireImports}
              /\ \/ /\ validGcAction.objId \in THING_IDS
                    /\ validGcAction.groupedObjIds = {}
                 \/ /\ validGcAction.objId = NullStr
                    /\ \A id \in validGcAction.groupedObjIds: id \in THING_IDS
              /\ validGcAction.targetVatId \in VAT_IDS

        GcActions ==
           \A a \in gcActions:
           /\ a.nature \in {_dropExports, _retireExports, _retireImports}
           /\ a.objId \in OBJECT_IDS
           /\ \A id \in a.groupedObjIds: id \in OBJECT_IDS
           /\ a.targetVatId \in VAT_IDS

        VatThingTrueState ==
           /\ DOMAIN vatThingTrueState = KEYS
           /\ \A key \in KEYS:
              vatThingTrueState[key] \in {
                   TRULY_REACHABLE,
                   TRULY_RECOGNIZABLE,
                   TRULY_UNKNOWN
              }

        Things == 
           /\ DOMAIN things = THING_IDS
           /\ \A id \in THING_IDS:
              /\ \/ IsZeroThing(id)
                 \* Is a promise
                 \/ /\ nature(id) = _promise
                    /\ owner(id) = NullStr
                    /\ \A i \in DOMAIN q(id):
                       /\ q(id)[i].argId \in THING_IDS
                       /\ q(id)[i].resultId \in PROMISE_IDS
                    /\ status(id) \in {_unresolved, _fulfilled, _rejected}
                    /\ decider(id) \in VAT_IDS => status(id) = _unresolved
                    /\ \A v \in subscribers(id): v \in VAT_IDS
                    /\ trueAllocator(id) \in VAT_IDS
                 \* Is an object
                 \/ /\ nature(id) = _object
                    /\ owner(id) \in VAT_IDS
                    /\ q(id) = <<>>
                    /\ status(id) = NullStr
                    /\ decider(id) = NullStr
                    /\ subscribers(id) = {}
                    /\ trueAllocator(id) \in VAT_IDS

        ClistExists ==
           DOMAIN clistExists = KEYS

        IsReachable ==
           DOMAIN isReachable = KEYS

        RunQ ==
           /\ \A i \in DOMAIN runQ:
              \* Is a send
              \/ /\ runQ[i].nature = _send
                 /\ runQ[i].msgForSend.argId \in THING_IDS
                 /\ runQ[i].msgForSend.resultId \in PROMISE_IDS
                 /\ runQ[i].targetIdForSend \in THING_IDS
                 /\ runQ[i].targetVatIdForNotify = NullStr
                 /\ runQ[i].promIdForNotify = NullStr
              \* Is a notify
              \/ /\ runQ[i].nature = _notify
                 /\ runQ[i].msgForSend.argId = NullStr
                 /\ runQ[i].msgForSend.resultId = NullStr
                 /\ runQ[i].targetIdForSend = NullStr
                 /\ runQ[i].targetVatIdForNotify \in VAT_IDS
                 /\ runQ[i].promIdForNotify \in PROMISE_IDS
        MaybeFree ==
           \A id \in maybeFree: id \in THING_IDS
        
        IN
        /\ Executor
        /\ ValidGcAction 
        /\ GcActions
        /\ VatThingTrueState
        /\ Things 
        /\ ClistExists
        /\ IsReachable
        /\ RunQ
        /\ MaybeFree
        /\ TRUE
        /\ TRUE

    IN
    /\ NonNegativeCounts
    /\ CorrectIdentifierTypes

(*
    For importers, require that isReachableFlag is false only if the vat cannot truly
    reach the object.
*)
Sane0 == 
    \A v \in VAT_IDS, id \in OBJECT_IDS:
    v # owner(id) => (~isReachable[id, v] <=> vatThingTrueState[id, v] # TRULY_REACHABLE)

(*
    If a thing is zero (null), no vat can reach it.
*)
Sane1 ==
    \A id \in THING_IDS: IsZeroThing(id) => (
        \A v \in VAT_IDS: vatThingTrueState[id, v] # TRULY_REACHABLE
    )

(*
    reachableCnt <= recognizableCnt
*)
Sane2 ==
    \A id \in OBJECT_IDS: reachableCnt(id) <= recognizableCnt(id)

(*
    counts are not less than the number of references across all kernel
    data structures.
*)
Sane3 ==
    LET
    \* @type: (THING_ID, Seq(MESSAGE)) => Int;
    CountMatchingRefsInMessageSeq(id, seq) ==
        LET
        \* @type: (Int, MESSAGE) => Int;
        Combine(acc, m) == acc
                               + (IF m.argId = id THEN 1 ELSE 0)
                               + (IF m.resultId = id THEN 1 ELSE 0)
        IN FoldSeq(Combine, 0, seq)
    IN
    LET
    \* @type: THING_ID => Int;
    RunQRefs(id) == 
        LET
        \* This kills Apalache typechecking (need 'toSeq')
        Msgs ==  [i \in DOMAIN runQ |-> runQ[i].msgForSend] IN
        CountMatchingRefsInMessageSeq(id, Msgs)
        + Cardinality({i \in DOMAIN runQ : runQ[i].targetIdForSend = id})
        + Cardinality({i \in DOMAIN runQ : runQ[i].promIdForNotify = id})
    \* @type: THING_ID => Int;
    PromiseQRefs(id) ==
        LET
        \* @type: (Seq(MESSAGE), Seq(MESSAGE)) => Seq(MESSAGE);
        Combine(acc, pq) == acc \o pq IN LET
        Msgs == FoldSet(Combine, <<>>, {
            things[pid].q : pid \in PROMISE_IDS
        }) IN
        CountMatchingRefsInMessageSeq(id, Msgs) 
    \* @type: THING_ID => Int;
    ClistRefs(id) == Cardinality({k \in {id} \X VAT_IDS : clistExists[k]})
    \* @type: THING_ID => Int;
    ImporterClistRefs(id) == Cardinality({
            k \in {id} \X (VAT_IDS \ {owner(id)}) : clistExists[k]
        })
    IN
    /\ \A id \in PROMISE_IDS: RunQRefs(id) + PromiseQRefs(id) + ClistRefs(id) = refCnt(id)
    /\ \A id \in  OBJECT_IDS: reachableCnt(id) <= RunQRefs(id) + PromiseQRefs(id) + Cardinality(VAT_IDS)

(*
    From the docs
    '... a general invariant is that the exporting clist entry and
    the kernel object table entry are either both present or both missing'
*)
Sane4 == 
    \A id \in OBJECT_IDS: 
        \/ /\ ~IsZeroThing(id)
           /\ IF owner(id) \in VAT_IDS
              THEN clistExists[id, owner(id)]
              ELSE TRUE
        \/ IsZeroThing(id)
        
PseudoLiveness0  == actionTaken # action_processGcActions
PseudoLiveness1  == actionTaken # action_executeGcAction
PseudoLiveness2  == actionTaken # action_processMaybeFree
PseudoLiveness3  == actionTaken # action_executeRunQueueEntry
PseudoLiveness4  == actionTaken # action_tryRunLoopBodyButNothingToDo
PseudoLiveness5  == actionTaken # action_nothing 
PseudoLiveness6  == actionTaken # action_skipSyscall
PseudoLiveness7  == actionTaken # action_sendSyscall
PseudoLiveness8  == actionTaken # action_subscribeSyscall
PseudoLiveness9  == actionTaken # action_resolveSyscall
PseudoLiveness10 == actionTaken # action_dropImportsSyscall
PseudoLiveness11 == actionTaken # action_retireImportsSyscall
PseudoLiveness12 == actionTaken # action_retireExportsSyscall

(*
An object has something in its queue *)
PseudoLiveness13 ==
    ~(\E id \in PROMISE_IDS : q(id) # <<>>)

Inv == 
    /\ SaneType
    /\ Sane0
    /\ Sane1
    /\ Sane2
    /\ Sane3
    /\ Sane4

====