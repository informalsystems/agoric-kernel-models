------------------------------------ MODULE kernel -----------------------------
(*
  The model of the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  It represents the object and promise management in the kernel 
  as done via the Syscall interface between the kernel and vats.

  This is the main model file, which contains:
    - variables (representing the kernel state)
    - parameterized actions (which modify the state)
    - action preconditions (when are the action parameters considered valid)
    - variables that are changed / unchanged by each action

  This main model is complemented by:
    - kernel_typedef.tla (defines types and auxiliary typed constants)
    - kernel_exec.tla (state initialization, externally visible actions, and scheduling)
    - kernel_test.tla (unit tests for the model)
    
  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
  Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  07.07.2021
*)

EXTENDS Apalache, Integers, FiniteSets, Sequences, kernel_typedef, TLC

(**************************** Kernel variables *********************************
  These variables model how the kernel keeps track of objects and promises.
*******************************************************************************)
VARIABLES 
  (*********************************** Await *************************************
    Await holds the message scheduled for immediate delivery.
    In the code it is sometimes the case that a message from the run queue
    is being processed, then forwarded for an asynchronous execution,
    and then awaited for the asynchronous call to return.
    We model this flow with the help of the `await` variable.
  *******************************************************************************)
  \* @type: MESSAGE;
  await,
  (*************************** terminationTrigger ********************************
    terminationTrigger may hold a VAT_ID of a Vat to be terminated.
    terminationTrigger has a lower priority than await; 
    i.e. await is processed first if set, and then terminationTrigger.
  *******************************************************************************)
  \* @type: VAT_ID;
  terminationTrigger,
  (*********************************** Run Queue *********************************
    Run queue holds messages scheduled for a delivery in a FIFO order.
    It can hold messages of several types: CreateVat, Notify, Send.
    Run queue message processing is performed with the lowest priority,
    if neither await nor terminationTrigger is set.
  *******************************************************************************)
  \* @type: RUN_QUEUE;
  runQueue,
  \* Next identifier for a kernel object
  \* @type: Int;
  koNextId,
  \* Next identifier for a kernel promise
  \* @type: Int;
  kpNextId,
  \* A table holding kernel objects: KERNEL_SLOT -> OBJECT
  \* @type: OBJECT_TABLE;
  kernelObjects,
  \* A table holding kernel promises: KERNEL_SLOT -> PROMISE
  \* @type: PROMISE_TABLE;
  kernelPromises, 
  \* Known VATs: VAT_ID -> VAT
  \* @type: VAT_TABLE;
  vats, 
  \* A capability list from Vat slots to kernel slots: VAT_ID -> VAT_SLOT -> KERNEL_SLOT
  \* @type: VAT_TO_KERNEL;
  vatToKernel,
  \* A capability list from kernel slots to Vat slots: VAT_ID -> KERNEL_SLOT -> VAT_SLOT
  \* @type: KERNEL_TO_VAT;
  kernelToVat,
  \* Which kernel slots are reachable for a Vat 
  \* @type: VAT_ID -> Set(KERNEL_SLOT);
  vatReachSlots,
  \* Action taken by the model
  \* @type: ACTION;
  action,
  \* The error is set when some erroneous input comes to the kernel
  \* @type: Str;
  error

AllVars == << await, terminationTrigger, runQueue, koNextId, kpNextId, kernelObjects, kernelPromises, vats, vatToKernel, kernelToVat, vatReachSlots, action, error >>
\* Action scheduling
SchedulingVars == << await, terminationTrigger, runQueue >>
\* Kernel object management
KernelVars == << koNextId, kpNextId, kernelObjects, kernelPromises >>
\* Vat management, capability lists
VatVars == << vats, vatToKernel, kernelToVat, vatReachSlots >>
\* modeling utilities
ModelVars == << action, error >>

  
\* Scheduling of specific message types into `await` execution
  AwaitCreateVat(vatID, enablePipelining) ==
    await' = CreateVatMessage(vatID, enablePipelining)

  AwaitProcessNotify(vatID, kpid) ==
    await' = NotifyMessage(vatID, kpid)  

  AwaitDeliverToTarget(target, msg) == 
    await' = SendMessage(target, msg)

  AwaitDeliverToVat(vatID, target, vatMsg) == 
    await' = SendMessageToVat(vatID, target, vatMsg)

  AwaitNoMessage == 
    await' = NoMessage

\* Schedule the VAT with vatID for removal
SetTerminationTrigger(vatID, shouldReject, slots) ==
  \/ terminationTrigger /= NULL
  \/ terminationTrigger' = vatID
  \* TODO: not clear what happens when the message is sent to vatAdminWrapper: vatTerminated
  \* \/ terminationTrigger' = [ vatID |-> vatID, shouldReject |-> shouldReject, slots |-> slots ]


\* Add a message to the run queue
AddToRunQueue(message) ==
  runQueue' = Append(runQueue, message)

\* Add a sequence of messages to the run queue
ConcatToRunQueue(messages) ==
  runQueue' = runQueue \o messages

\* Checks whether a Vat is known to the kernel
\* type: (VAT_ID) => Bool
KnownVat(vatID) == 
  /\ vatID \in DOMAIN vats
  \* It should be the case that a vat is added in synchrony into vats, vatToKernel, kernelToVat, vatReachSlots
  \* /\ vatID \in DOMAIN vatToKernel
  \* /\ vatID \in DOMAIN kernelToVat
  \* /\ vatID \in DOMAIN vatReachSlots

\* Checks that a Vat is unknown to the kernel
\* type: (VAT_ID) => Bool
UnknownVat(vatID) == 
  /\ vatID \notin DOMAIN vats
  \* It should be the case that a vat is removed in synchrony from vats, vatToKernel, kernelToVat, vatReachSlots
  \* /\ vatID \notin DOMAIN vatToKernel
  \* /\ vatID \notin DOMAIN kernelToVat
  \* /\ vatID \notin DOMAIN vatReachSlots


(*********************************** Create Vat *******************************
  CreateVat is triggered when a "create-vat" run queue message is processed.
*******************************************************************************)

\* kernel.js processCreateVat(): https://git.io/JnvdR
\* type: (VAT_ID, Bool) => Bool
CreateVatPre(vatID, enablePipelining) == 
  UnknownVat(vatID)

CreateVatChanges == <<vats, vatToKernel, kernelToVat, vatReachSlots>>
CreateVatNotChanges == <<await, terminationTrigger, runQueue, koNextId, kpNextId, kernelObjects, kernelPromises>>

\* kernel.js processCreateVat(): https://git.io/JnvdR
\* @type: (VAT_ID, Bool) => Bool;
CreateVat(vatID, enablePipelining) == 
  /\ vats' = [k \in DOMAIN vats \union {vatID} |-> 
      IF k = vatID THEN NEW_VAT(enablePipelining) ELSE vats[k] ]
  /\ vatToKernel' = [k \in DOMAIN vatToKernel \union {vatID} |-> 
      IF k = vatID THEN EMPTY_VAT_TO_KERNEL_ENTRY ELSE vatToKernel[k] ]
  /\ kernelToVat' = [k \in DOMAIN kernelToVat \union {vatID} |-> 
      IF k = vatID THEN EMPTY_KERNEL_TO_VAT_ENTRY ELSE kernelToVat[k] ]
  /\ vatReachSlots' = [k \in DOMAIN vatReachSlots \union {vatID} |-> 
      IF k = vatID THEN {} ELSE vatReachSlots[k] ]


\* Extends the vat <-> kernel maps with the new mapping vatSlot <-> kernelSlot,
\* and sets that the kernelSlot is reachable from vatID
\* Auxiliary operator for Export and Import.
ExtendVatKernelMaps(vatID, vatSlot, kernelSlot) ==
  /\ vatToKernel' = [vatToKernel EXCEPT ![vatID] = 
        [k \in DOMAIN @ \union {vatSlot} |-> IF k = vatSlot THEN kernelSlot ELSE @[k]] ]
  /\ kernelToVat' = [kernelToVat EXCEPT ![vatID] = 
        [k \in DOMAIN @ \union {kernelSlot} |-> IF k = kernelSlot THEN vatSlot ELSE @[k]] ] 
  /\ vatReachSlots' = [vatReachSlots EXCEPT ![vatID] = @ \union {kernelSlot}]


(*********************************** Export ***********************************
  Export from Vat slots to kernel slots happens in the code 
  as an intermediate translation when a Vat message arrives into the kernel.
  As exporting modifies kernel tables, we model this as a separate model step.
*******************************************************************************)

\* vatKeeper.js MapVatSlotToKernelSlot(): https://git.io/JZaER
\* @type: (VAT_ID, VAT_SLOT) => Bool;
ExportPre(vatID, vatSlot) ==
  /\ KnownVat(vatID)
  \* if not exported by vat:
  \*  // the vat didn't allocate it, and the kernel didn't allocate it
  \*  // (else it would have been in the c-list), so it must be bogus
  /\ vatSlot.exported
  /\ vatSlot.type = VAT_OBJECT \/ vatSlot.type = VAT_PROMISE
  /\ vatSlot \notin DOMAIN vatToKernel[vatID]

ExportChanges == <<koNextId, kpNextId, vatToKernel, kernelToVat, vatReachSlots, kernelObjects, kernelPromises>>
ExportNotChanges == <<await, terminationTrigger, runQueue, vats>>

\* vatKeeper.js MapVatSlotToKernelSlot(): https://git.io/JZaER
\* Creates a kernel slot from a vat slot, assuming it doesn't exist yet
\* @type: (VAT_ID, VAT_SLOT) => Bool;
Export(vatID, vatSlot) ==
  CASE vatSlot.type = VAT_OBJECT ->
    LET kernelSlot == KO(koNextId) IN 
      /\ koNextId' = koNextId + 1
      \* /\ kernelObjects' = Extend(kernelObjects, kernelSlot, NEW_OBJECT(vatID) ])
      /\ ExtendVatKernelMaps(vatID, vatSlot, kernelSlot)
      /\ kernelObjects' = [k \in DOMAIN kernelObjects \union {kernelSlot} |-> IF k = kernelSlot THEN NEW_OBJECT(vatID) ELSE kernelObjects[k]]
      /\ UNCHANGED <<kpNextId, kernelPromises>>
  [] vatSlot.type = VAT_PROMISE  ->
    LET kernelSlot == KP(kpNextId) IN 
      /\ kpNextId' = kpNextId + 1
      /\ ExtendVatKernelMaps(vatID, vatSlot, kernelSlot)
      \* /\ kernelPromises' = Extend(kernelPromises, kernelSlot, NEW_PROMISE(vatID) ])
      /\ kernelPromises' = [k \in DOMAIN kernelPromises \union {kernelSlot} |-> IF k = kernelSlot THEN NEW_PROMISE(vatID) ELSE kernelPromises[k]]
      /\ UNCHANGED <<koNextId, kernelObjects>>


(*********************************** Import ***********************************
  Import from kernel slots ino Vat slots happens in the code 
  as an intermediate translation when a kernel message goes into a Vat.
  As importing modifies kernel tables, we model this as a separate model step.
*******************************************************************************)

\* vatKeeper.js mapKernelSlotToVatSlot(): https://git.io/Jnvcc
\* @type: (VAT_ID, KERNEL_SLOT) => Bool;
ImportPre(vatID, kernelSlot) ==
  /\ KnownVat(vatID)
  /\ kernelSlot.type = KERNEL_OBJECT \/ kernelSlot.type = KERNEL_PROMISE
  /\ kernelSlot \notin DOMAIN kernelToVat[vatID]

ImportChanges == <<vats, vatToKernel, kernelToVat, vatReachSlots>>
ImportNotChanges == <<await, terminationTrigger, runQueue, koNextId, kpNextId, kernelObjects, kernelPromises>>

\* vatKeeper.js mapKernelSlotToVatSlot(): https://git.io/Jnvcc
\* Creates a vat slot from a kernel slot, assuming it doesn't exist yet
\* @type: (VAT_ID, KERNEL_SLOT) => Bool;
Import(vatID, kernelSlot) ==
  CASE kernelSlot.type = KERNEL_OBJECT ->
    LET vatSlot == [ type |-> VAT_OBJECT, id |-> vats[vatID].oNextId, exported |-> FALSE ] IN 
      /\ vats' = [vats EXCEPT ![vatID] = [@ EXCEPT !.oNextId = @ + 1]]
      /\ ExtendVatKernelMaps(vatID, vatSlot, kernelSlot)
  [] kernelSlot.type = KERNEL_PROMISE  ->
    LET vatSlot == [ type |-> VAT_PROMISE, id |-> vats[vatID].pNextId, exported |-> FALSE ] IN 
      /\ vats' = [vats EXCEPT ![vatID] = [@ EXCEPT !.pNextId = @ + 1]]
      /\ ExtendVatKernelMaps(vatID, vatSlot, kernelSlot)


\* Deletes entries from vatToKernel and vatToKernel that correspond to vatID and kernelSlots.
\* Auxiliary operator for Resolve.
\* Changes: kernelToVat, vatToKernel.
\* vatKeeper.js deleteCListEntry(): https://git.io/JZ4EO
\* vatKeeper.js DeleteCListEntries(): https://git.io/JZ4gQ
\* @type: (VAT_ID, Set(KERNEL_SLOT)) => Bool;
DeleteCListEntries(vatID, kernelSlots) ==
  IF vatID \in (DOMAIN kernelToVat \intersect DOMAIN vatToKernel) THEN
    LET k2v == kernelToVat[vatID] IN
    LET v2k == vatToKernel[vatID] IN
    LET nextk2v == [ slot \in (DOMAIN k2v \ kernelSlots) |-> k2v[slot] ] IN
    LET vatSlots == { k2v[kpid] : kpid \in kernelSlots } IN
    LET nextv2k == [ slot \in (DOMAIN v2k \ vatSlots) |-> v2k[slot] ] IN 
      /\ kernelToVat' = [kernelToVat EXCEPT ![vatID] = nextk2v ]
      /\ vatToKernel' = [vatToKernel EXCEPT ![vatID] = nextv2k ]
  ELSE
    UNCHANGED <<kernelToVat, vatToKernel>>


\* @type: (PROMISE_TABLE, RESOLUTION) => PROMISE_TABLE;
AddPromiseEntry(table, resolution) ==
  LET ResSlotsToPromiseSlots(slots, slot) ==
        slots \union {slot} IN
  LET kpid == resolution.kpid IN
  LET promiseSlots == FoldSeq(ResSlotsToPromiseSlots, {}, resolution.slots) IN
  LET promise == IF resolution.rejected THEN [ state |-> REJECTED, slots |-> promiseSlots ]
      ELSE [ state |-> FULFILLED, slots |-> promiseSlots ]
  IN [k \in DOMAIN table \union {kpid} |-> IF k = kpid THEN promise ELSE table[k] ]

\* Compute a set of promises that gets resolved in the given resolutions.
\* Auxiliary operator for DoResolve.
\* kernelKeeper.js resolveKernelPromise(): https://git.io/JZLso
\* @type: (Seq(RESOLUTION)) => PROMISE_TABLE;
ResolvedKernelPromises(resolutions) ==
  FoldSeq(AddPromiseEntry, EMPTY_PROMISE_TABLE, resolutions)

\* Construct messages from the promise to the run queue when it gets resolved
\* @type: (VAT_ID, KERNEL_SLOT) => Seq(MESSAGE);
PromiseToQueueMessages(vatID, kpid) ==
  LET AppendNotify(seq, vat) == 
        IF vat /= vatID THEN Append(seq, NotifyMessage(vat, kpid)) 
        ELSE seq IN
  LET AppendSend(seq, msg) == 
        Append(seq, SendMessage(kpid, msg)) IN
  LET promise == kernelPromises[kpid] IN
  LET notifyMessages == FoldSet(AppendNotify, <<>>, promise.subscribers) IN
  LET sendMessages == FoldSeq(AppendSend, <<>>, promise.queue) IN
    notifyMessages \o sendMessages

\* kernelSyscall.js DoResolve(): https://git.io/JZmSJ
\* kernel.js doResolve(): https://git.io/JZmyS
\* Auxiliary operator for Resolve and ResolveToError.
\* Changes: kernelPromises, runQueue.
\* @type: (VAT_ID, Seq(RESOLUTION)) => Bool;
DoResolve(vatID, resolutions) ==
  LET \* @type: (Seq(MESSAGE), RESOLUTION) => Seq(MESSAGE);
      AddPromiseMessages(messages, resolution) ==
        messages \o PromiseToQueueMessages(vatID, resolution.kpid) IN
  LET resolved == ResolvedKernelPromises(resolutions) IN
  LET messages == FoldSeq(AddPromiseMessages, <<>>, resolutions) IN
    /\ kernelPromises' = [ kpid \in DOMAIN kernelPromises |-> 
        IF kpid \in DOMAIN resolved THEN resolved[kpid] 
        ELSE kernelPromises[kpid] ]
    /\ ConcatToRunQueue(messages)


(*********************************** Resolve **********************************
  Resolve happens when a "resolve" syscall arrives at the kernel. 
  Export should have happened as a precondition.
  Resolve happens both by _immediately_ resolving some promises in kernelPromises,
  and scheduling others for later resolution via runQueue.
*******************************************************************************)

\* vatTranslator.js translateResolve(): https://git.io/JZ48U
\* kernel.js doResolve(): https://git.io/JZmyS
\* @type: (VAT_ID, Seq(RESOLUTION)) => Bool;
ResolvePre(vatID, resolutions) ==
  LET resolved == ResolvedKernelPromises(resolutions) IN
  /\ DOMAIN resolved \subseteq DOMAIN kernelPromises
  /\ \A kpid \in DOMAIN resolved:
       /\ kernelPromises[kpid].state = UNRESOLVED
       /\ kernelPromises[kpid].decider = vatID

ResolveChanges == <<kernelPromises, runQueue, vatToKernel, kernelToVat>>
ResolveNotChanges == <<await, terminationTrigger, koNextId, kpNextId, kernelObjects, kernelPromises, vats, vatReachSlots>>

\* kernelSyscall.js DoResolve(): https://git.io/JZmSJ
\* kernel.js doResolve(): https://git.io/JZmyS
\* vatTranslator.js translateResolve(): https://git.io/JnUsU
\* @type: (VAT_ID, Seq(RESOLUTION)) => Bool;
Resolve(vatID, resolutions) ==
  /\ DeleteCListEntries(vatID, DOMAIN ResolvedKernelPromises(resolutions))
  /\ DoResolve(vatID, resolutions)


\* Auxiliary operator that resolves a set of promises as rejected.
\* Changes: kernelPromises, runQueue
\* kernel.js resolveToError(): https://git.io/JZV4R
\* @type: (VAT_ID, Set(KERNEL_SLOT)) => Bool;
ResolveToError(vatID, promises) == 
  LET 
    AddResolution(resolutions, kpid) ==
      Append(resolutions, [ kpid |-> kpid, rejected |-> TRUE, slots |-> <<>> ])
  IN DoResolve(vatID, FoldSet(AddResolution, <<>>, promises))


(******************************* TerminateVat *********************************
  TerminateVat happens when terminationTrigger is set; e.g. via "exit" syscall. 
  It removes all mentions of this vat from kernel tables,
  and resolves to error its promises.
*******************************************************************************)

\* kernel.js terminateVat(): https://git.io/JZa0S
TerminateVatPre(vatID) ==
  KnownVat(vatID)

TerminateVatChanges == <<runQueue, kernelObjects, kernelPromises, vats, vatToKernel, kernelToVat >>
TerminateVatNotChanges == <<await, terminationTrigger, koNextId, kpNextId, vatReachSlots>>

\* kernel.js terminateVat(): https://git.io/JZa0S
\* @type: (VAT_ID) => Bool;
TerminateVat(vatID) ==
  LET v2k == vatToKernel[vatID]
      vatObjects == { slot \in DOMAIN v2k : 
        slot.type = VAT_OBJECT /\ slot.exported /\ kernelObjects[v2k[slot]].owner = vatID }
      objects == { v2k[slot] : slot \in vatObjects }
      vatPromises == { slot \in DOMAIN v2k : LET p ==  kernelPromises[v2k[slot]] IN
        slot.type = VAT_PROMISE /\ p.state = UNRESOLVED /\ p.decider = vatID }
      promises == { v2k[slot] : slot \in vatPromises }
  IN
    /\ vats' = [ vat \in DOMAIN vats \ {vatID} |-> vats[vat] ]
    /\ vatToKernel' = [ vat \in DOMAIN vatToKernel \ {vatID} |-> vatToKernel[vat] ]
    /\ kernelToVat' = [ vat \in DOMAIN kernelToVat \ {vatID} |-> kernelToVat[vat] ]
    /\ kernelObjects' = [ object \in DOMAIN kernelObjects \ objects |-> kernelObjects[object] ]
    /\ ResolveToError(vatID, promises)


(***************************** DeliverToTarget ********************************
  DeliverToTarget processes "send" messages from the run queue.
*******************************************************************************)

\* @type: (KERNEL_SLOT, VAT_MESSAGE) => Bool;
DeliverToTargetPre(target, msg) ==
  \/ target.type = KERNEL_OBJECT
  \/ target.type = KERNEL_PROMISE /\ target \in DOMAIN kernelPromises
  
DeliverToTargetChanges == <<await, kernelPromises, runQueue>> 
DeliverToTargetNotChanges == <<terminationTrigger, koNextId, kpNextId, kernelObjects, vats, vatToKernel, kernelToVat, vatReachSlots>>

\* kernel.js deliverToTarget(): https://git.io/JZVGA
\* @type: (KERNEL_SLOT, VAT_MESSAGE) => Bool;
DeliverToTarget(target, msg) ==
  CASE target.type = KERNEL_OBJECT -> 
    IF target \in DOMAIN kernelObjects /\ kernelObjects[target].owner /= NULL THEN 
      LET vatID == kernelObjects[target].owner IN
      /\ AwaitDeliverToVat(vatID, target, msg)
      /\ UNCHANGED <<kernelPromises, runQueue>>
    ELSE
      /\ ResolveToError(NULL, {msg.result})
      /\ UNCHANGED await
  [] target.type = KERNEL_PROMISE ->
    LET promise == kernelPromises[target] IN 
    CASE promise.state = FULFILLED ->
      IF Cardinality(promise.slots) = 1 THEN 
        LET presence == CHOOSE slot \in promise.slots: TRUE IN 
          /\ AwaitDeliverToTarget(presence, msg)
          /\ UNCHANGED <<kernelPromises, runQueue>>
      ELSE 
        ResolveToError(NULL, {msg.result})
        /\ UNCHANGED await
    [] promise.state = REJECTED ->
      ResolveToError(NULL, {msg.result})
    [] promise.state = UNRESOLVED ->
      IF promise.decider = NULL THEN
        /\ kernelPromises' = [kernelPromises EXCEPT ![target].queue = Append(promise.queue, msg)]
        /\ UNCHANGED <<await, runQueue>>
      ELSE
        IF promise.decider \in DOMAIN vats THEN 
          IF vats[promise.decider].enablePipelining THEN 
            /\ AwaitDeliverToVat(promise.decider, target, msg)
            /\ UNCHANGED <<kernelPromises, runQueue>>
          ELSE 
            /\ kernelPromises' = [kernelPromises EXCEPT ![target].queue = Append(promise.queue, msg)]
            /\ UNCHANGED <<await, runQueue>>
        ELSE 
          /\ ResolveToError(NULL, {msg.result})
          /\ UNCHANGED await

RECURSIVE GetKpidsToRetire(_, _)
\* @type: (KERNEL_SLOT, Set(KERNEL_SLOT)) => Set(KERNEL_SLOT);
GetKpidsToRetire(kpid, slots) ==
    LET 
      toAdd == { slot \in slots : 
        /\ slot \in DOMAIN kernelPromises
        /\ kernelPromises[slot].state /= UNRESOLVED }
    IN 
      {kpid} \union UNION { GetKpidsToRetire(slot, kernelPromises[slot].slots) : slot \in toAdd }
UNROLL_TIMES_GetKpidsToRetire == 10
\* on the 11th time, return just {}
UNROLL_DEFAULT_GetKpidsToRetire == {}


(******************************* DeliverToVat *********************************
  DeliverToVat processes "send-vat" messages from the run queue.
*******************************************************************************)

\* @type: (VAT_ID, KERNEL_SLOT, VAT_MESSAGE) => Bool;
DeliverToVatPre(vatID, target, vatMsg) ==
  /\ KnownVat(vatID)
  /\ target \in DOMAIN kernelToVat[vatID]
  /\ \/ (target \in DOMAIN kernelObjects /\ kernelObjects[target].exported)
     \/ (target \in DOMAIN kernelPromises /\ kernelPromises[target].decider = vatID)
  /\ \/ vatMsg.result = NULL_KERNEL_SLOT
     \/ /\ vatMsg.result \in DOMAIN kernelPromises
        /\ kernelPromises[vatMsg.result].state = UNRESOLVED
        /\ kernelPromises[vatMsg.result].decider = NULL_VAT_ID
  /\ \A slot \in vatMsg.slots :
      /\ slot \in (DOMAIN kernelPromises \union DOMAIN kernelObjects)
      /\ slot \in DOMAIN kernelToVat[vatID]

DeliverToVatChanges == <<terminationTrigger, kernelPromises, runQueue>>
DeliverToVatNotChanges == <<await, koNextId, kpNextId, kernelObjects, vats, kernelToVat, vatToKernel, vatReachSlots>>

\* kernel.js deliverToVat(): https://git.io/JcX8e
\* kernel.js deliverAndLogToVat(): https://git.io/JcXlV
\* @type: (VAT_ID, KERNEL_SLOT, VAT_MESSAGE) => Bool;
DeliverToVat(vatID, target, vatMsg) ==
  \/ UnknownVat(vatID) /\ ResolveToError(vatID, {vatMsg.result})
  \/ KnownVat(vatID) /\ UNCHANGED <<kernelPromises, runQueue>> /\
     \* An error occurs in VAT
     \/ SetTerminationTrigger(vatID, TRUE, {}) 
     \* No error occurs in VAT
     \/ UNCHANGED terminationTrigger


(******************************* ProcessNotify ********************************
  ProcessNotify processes "notify" messages from the run queue.
*******************************************************************************)

\* kernel.js processNotify():https://git.io/JnJdd
\* @type: (VAT_ID, KERNEL_SLOT) => Bool;
ProcessNotifyPre(vatID, kpid) ==
  \/ UnknownVat(vatID)
  \/ /\ kpid \in DOMAIN kernelPromises
     /\ kernelPromises[kpid].state /= UNRESOLVED

ProcessNotifyChanges == <<await, kernelToVat, vatToKernel>>
ProcessNotifyNotChanges == <<terminationTrigger, runQueue, koNextId, kpNextId, kernelObjects, kernelPromises, vats, vatReachSlots>> 

\* kernel.js processNotify():https://git.io/JnJdd
\* @type: (VAT_ID, KERNEL_SLOT) => Bool;
ProcessNotify(vatID, kpid) ==
  IF  KnownVat(vatID) THEN 
    IF kpid \in DOMAIN kernelToVat[vatID] THEN
      LET targets == GetKpidsToRetire(kpid, kernelPromises[kpid].slots) IN 
        /\ DeleteCListEntries(vatID, targets)
        /\ AwaitDeliverToVat(vatID, kpid, [slots |-> targets])
    ELSE
      UNCHANGED ProcessNotifyChanges \* skipping notify of ${kpid} because it's already been done
  ELSE
    UNCHANGED ProcessNotifyChanges \* dropping notify of ${kpid} to ${vatID} because vat is dead


(**************************** ProcessQueueMessage *****************************
  ProcessQueueMessage picks up the next message from the run queue, 
  and schedules it via "await" for further processing.
*******************************************************************************)

ProcessQueueMessagePre ==
  runQueue /= <<>>

ProcessQueueMessageChanges == <<await, runQueue>>
ProcessQueueMessageNotChanges == <<terminationTrigger, koNextId, kpNextId, kernelObjects, kernelPromises, vats, kernelToVat, vatToKernel, vatReachSlots>>

ProcessQueueMessage ==
  /\ runQueue' = Tail(runQueue)
  /\ LET message == Head(runQueue) IN 
     CASE message.type = SEND -> 
       AwaitDeliverToTarget(message.target, message.msg)
     [] message.type = CREATE_VAT ->
       AwaitCreateVat(message.vatID, message.enablePipelining)
     [] message.type = NOTIFY ->
       AwaitProcessNotify(message.vatID, message.kpid)



(******************************** Subscribe ***********************************
  Subscribe is triggered via "subscribe" syscall.
  The subscribed promise should be first exported.
*******************************************************************************)

\* kernelSyscall.js subscribe(): https://git.io/JZlfm
SubscribePre(vatID, kpid) ==
  /\ KnownVat(vatID)
  /\ kpid \in DOMAIN kernelPromises

SubscribeChanges == <<kernelPromises, runQueue>>
SubscribeNotChanges == <<await, terminationTrigger, koNextId, kpNextId, kernelObjects, vats, kernelToVat, vatToKernel, vatReachSlots>>

Subscribe(vatID, kpid) ==
  IF kernelPromises[kpid].state = UNRESOLVED THEN 
      /\ kernelPromises' = [kernelPromises EXCEPT ![kpid].subscribers = (@ \union {vatID})]
      /\ UNCHANGED runQueue
  ELSE 
      /\ AddToRunQueue(NotifyMessage(vatID, kpid))
      /\ UNCHANGED kernelPromises


(********************************** Send **************************************
  Send is triggered via "send" syscall.
  The result and message slots should be first exported.
*******************************************************************************)


\* vatTranslator.js translateSend(): https://git.io/JZ8RN
\* In the real code the kernel slots are created on the fly by applying mapVatSlotToKernelSlot.
\* In the model we require this to be a separate Export action, 
\* and assume that the kernel slots are already created when Send is done.
\* @type: (VAT_ID, KERNEL_SLOT, VAT_MESSAGE) => Bool;
SendPre(vatID, target, msg) ==
  /\ KnownVat(vatID)
  /\ target \in (DOMAIN kernelPromises \union DOMAIN kernelObjects)
  /\ target \in DOMAIN kernelToVat[vatID]
  /\ \/ msg.result = NULL_KERNEL_SLOT
     \/ /\ msg.result \in DOMAIN kernelPromises
        /\ kernelPromises[msg.result].state = UNRESOLVED
        /\ kernelPromises[msg.result].decider = vatID
  /\ \A slot \in msg.slots :
      /\ slot \in (DOMAIN kernelPromises \union DOMAIN kernelObjects)
      /\ slot \in DOMAIN kernelToVat[vatID]

SendChanges == <<kernelPromises, runQueue>>
SendNotChanges == <<await, terminationTrigger, koNextId, kpNextId, kernelObjects, vats, kernelToVat, vatToKernel, vatReachSlots>>

\* kernelSyscall.js doSend(): https://git.io/JZllI
\* vatTranslator.js translateSend(): https://git.io/JZ8RN
\* @type: (VAT_ID, KERNEL_SLOT, VAT_MESSAGE) => Bool;
Send(vatID, target, msg) ==
  /\ \/ msg.result = NULL_KERNEL_SLOT /\ UNCHANGED kernelPromises
     \/ kernelPromises' = [kernelPromises EXCEPT ![msg.result].decider = NULL]
  /\ AddToRunQueue(SendMessage(target, msg))


(********************************** Exit *************************************
  Exit is triggered via "exit" syscall.
  The Vat is scheduled for termination via terminationTrigger.
*******************************************************************************)

\* vatTranslator.js translateExit(): https://git.io/JnJZw
ExitPre(vatID, isFailure, slots) ==
  \A slot \in slots : 
    \/ slot \in DOMAIN kernelObjects
    \/ slot \in DOMAIN kernelPromises

\* @type: () => Seq(VAT_ID);
ExitChanges == <<terminationTrigger>>
ExitNotChanges == <<await, runQueue, koNextId, kpNextId, kernelObjects, kernelPromises, vats, kernelToVat, vatToKernel, vatReachSlots>>

\* kernelSyscall.js exit(): https://git.io/JnJG7
Exit(vatID, isFailure, slots) ==
    SetTerminationTrigger(vatID, isFailure, slots)

===============================================================================
