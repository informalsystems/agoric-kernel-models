------------------------------------ MODULE kernel_exec -----------------------------
(*
  The model of the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see kernel.tla.
  This file defines execution semantics for the kernel:
    - constants (representing the model search space)
    - initialization of state variables and constants
    - externally observable actions
    - scheduling of actions 

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
  Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  07.07.2021
*)

EXTENDS kernel

(******************************* Constants ************************************
  Constants define the search space of the model.
  We advise to use Apalache's CInit mechanism to define constants symbolically.
*******************************************************************************)
CONSTANTS
  \* @type: Set(VAT_ID);
  VAT_IDS,
  \* @type: Set(VAT_SLOT);
  VAT_SLOTS,
  \* @type: Set(KERNEL_SLOT);
  KERNEL_SLOTS,
  \* @type: Set(VAT_MESSAGE);
  VAT_MESSAGES,
  \* @type: Set(RESOLUTION);
  RESOLUTIONS



\* @typeAlias: STATE = [
\*    await: MESSAGE, terminationTrigger: VAT_ID, runQueue: Seq(MESSAGE),
\*    koNextId: Int, kpNextId: Int, kernelObjects: OBJECT_TABLE, kernelPromises: PROMISE_TABLE,
\*    vats: VAT_TABLE, vatToKernel: VAT_TO_KERNEL, kernelToVat: KERNEL_TO_VAT, vatReachSlots: VAT_ID -> Set(KERNEL_SLOT),
\*    action: ACTION, error: Str
\* ];
\* 
\* Default constant initialization
CInit == 
  LET
    ids == 1..3
    vat_ids == { "a", "b", "c" }
    vat_slots == { [ type |-> type, id |-> id, exported |-> exported ] : 
        type \in { VAT_OBJECT, VAT_PROMISE, VAT_DEVICE },
        id \in ids,
        exported \in { TRUE, FALSE }
      }
    kernel_slots == { [ type |-> type, id |-> id ] : 
        type \in { KERNEL_OBJECT, KERNEL_PROMISE, KERNEL_DEVICE },
        id \in ids
      }
  IN
  /\ VAT_IDS = vat_ids
  /\ VAT_SLOTS = vat_slots
  /\ KERNEL_SLOTS = kernel_slots
  /\ VAT_MESSAGES = { [ result |-> result, slots |-> slots ] : 
        result \in kernel_slots,
        slots \in { {x} \union {x,y} : x \in kernel_slots, y \in kernel_slots }
      }
  /\ RESOLUTIONS = { [ kpid |-> kpid, rejected |-> rejected, slots |-> slots ] : 
        kpid \in kernel_slots,
        rejected \in { TRUE, FALSE },
        slots \in { <<x>> : x \in kernel_slots} \union { <<x,y>> : x \in kernel_slots, y \in kernel_slots }
      }
\* Initialize all variables with defaults, except for the ones provided explicitely.
\* NB: This slightly abuses the Apalache type system;
\*     It is known to work with the version 0.15.9,
\*     But will likely stop to work as soon as https://github.com/informalsystems/apalache/issues/874 is fixed.
\* @type: ([ vats: VAT_TABLE, await: MESSAGE, runQueue: Seq(MESSAGE), koNextId: Int, kpNextId: Int, 
\*   kernelToVat: KERNEL_TO_VAT, vatToKernel: VAT_TO_KERNEL,
\*   kernelObjects: OBJECT_TABLE, kernelPromises: PROMISE_TABLE]) => Bool;
InitDefaultsExcept(update) ==
  LET vars == update IN
  /\ await = IF "await" \in DOMAIN vars THEN vars.await ELSE NoMessage
  /\ terminationTrigger = IF "terminationTrigger" \in DOMAIN vars THEN vars.terminationTrigger ELSE NULL_VAT_ID
  /\ runQueue = IF "runQueue" \in DOMAIN vars THEN vars.runQueue ELSE <<>>
  /\ koNextId = IF "koNextId" \in DOMAIN vars THEN vars.koNextId ELSE 1
  /\ kpNextId = IF "kpNextId" \in DOMAIN vars THEN vars.kpNextId ELSE 1
  /\ kernelObjects = IF "kernelObjects" \in DOMAIN vars THEN vars.kernelObjects ELSE EMPTY_OBJECT_TABLE
  /\ kernelPromises = IF "kernelPromises" \in DOMAIN vars THEN vars.kernelPromises ELSE EMPTY_PROMISE_TABLE
  /\ vats = IF "vats" \in DOMAIN vars THEN vars.vats ELSE EMPTY_VAT_TABLE
  /\ kernelToVat = IF "kernelToVat" \in DOMAIN vars THEN vars.kernelToVat ELSE EMPTY_KERNEL_TO_VAT
  /\ vatToKernel = IF "vatToKernel" \in DOMAIN vars THEN vars.vatToKernel ELSE EMPTY_VAT_TO_KERNEL
  /\ vatReachSlots = IF "vatReachSlots" \in DOMAIN vars THEN vars.vatReachSlots ELSE EMPTY_VAT_REACH_SLOTS
  /\ error = IF "error" \in DOMAIN vars THEN vars.error ELSE NULL
  /\ action = IF "action" \in DOMAIN vars THEN vars.action ELSE NULL_ACTION


\* An initial kernel state with some default contents in tables
DefaultInit ==
  InitDefaultsExcept([
    koNextId |-> 3,
    kpNextId |-> 3,
    kernelObjects |-> KO(1) :> NEW_OBJECT("a") @@ KO(2) :> NEW_OBJECT("b"),
    kernelPromises |-> KP(1) :> NEW_PROMISE("a") @@ KP(2) :> NEW_PROMISE("b"),
    vats |-> "a" :> NEW_VAT(FALSE) @@ "b" :> NEW_VAT(FALSE),
    vatToKernel   |-> "a" :> (EVO(1) :> KO(1) @@ IVP(1) :> KP(2)) @@
                      "b" :> (EVO(1) :> KO(2) @@ IVP(1) :> KP(1)),
    kernelToVat   |-> "a" :> (KO(1) :> EVO(1) @@ KP(2) :> IVP(1)) @@
                      "b" :> (KO(2) :> EVO(1) @@ KP(1) :> IVP(1)),
    vatReachSlots |-> "a" :> { KO(1), KP(2)} @@  "b" :> { KO(2), KP(1)} 
  ])


(*************************** Actions & steps **********************************
  Actions define the steps that the system can take.
  Actions are defined based on the parameterized actions from kernel.tla:
    - Do not change unchanged variables
      (this allows to search over all possible inputs)
    - Save the action being executed in the "action" variable
    - If the action precondition is satisfied, perform an update
    - Otherwise do not perform an update, but set the "error" variable instead
  Steps differ from actions in that they quantify existentially
     on step parameters, using constants
*******************************************************************************)

CreateVatAction(vatID, enablePipelining) ==
  UNCHANGED CreateVatNotChanges /\
    action' = [ type |-> "CreateVat", vatID |-> vatID, enablePipelining |-> enablePipelining ] /\
    IF CreateVatPre(vatID, enablePipelining) THEN
       /\ CreateVat(vatID, enablePipelining)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED CreateVatChanges
       /\ error' = "CreateVat"

CreateVatStep == 
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E enablePipelining \in {TRUE, FALSE}:
    CreateVatAction(vatID, enablePipelining)

ExportAction(vatID, vatSlot) ==
  UNCHANGED ExportNotChanges /\
    action' = [ type |-> "Export", vatID |-> vatID, vatSlot |-> vatSlot ] /\
    IF ExportPre(vatID, vatSlot) THEN
       /\ Export(vatID, vatSlot)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ExportChanges
       /\ error' = "Export"

ExportStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E vatSlot \in VAT_SLOTS:
    ExportAction(vatID, vatSlot)

ImportAction(vatID, kernelSlot) ==
  UNCHANGED ImportNotChanges /\
    action' = [ type |-> "Import", vatID |-> vatID, kernelSlot |-> kernelSlot ] /\
    IF ImportPre(vatID, kernelSlot) THEN
       /\ Import(vatID, kernelSlot)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ImportChanges
       /\ error' = "Import"

ImportStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E kernelSlot \in KERNEL_SLOTS:
    ImportAction(vatID, kernelSlot)


SendAction(vatID, target, msg) ==
  UNCHANGED SendNotChanges /\
    action' = [ type |-> "Send", vatID |-> vatID, target |-> target, msg |-> msg ] /\
    IF SendPre(vatID, target, msg) THEN
       /\ Send(vatID, target, msg)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED SendChanges
       /\ error' = "Send"

SendStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E target \in KERNEL_SLOTS:
  \E msg \in VAT_MESSAGES:
    SendAction(vatID, target, msg)


\* @type: (VAT_ID, Seq(RESOLUTION)) => Bool;
ResolveAction(vatID, resolutions) ==
  UNCHANGED ResolveNotChanges /\
    action' = [ type |-> "Resolve", vatID |-> vatID, resolutions |-> resolutions ] /\
    IF ResolvePre(vatID, resolutions) THEN
       /\ Resolve(vatID, resolutions)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ResolveChanges
       /\ error' = "Resolve"

ResolveStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E resolution \in RESOLUTIONS:
    ResolveAction(vatID, <<resolution>>) \* we restrict to a single resolution for now

\* @type: (VAT_ID, KERNEL_SLOT) => Bool;
ProcessNotifyAction(vatID, kpid) ==
  UNCHANGED ProcessNotifyNotChanges /\
    action' = [ type |-> "ProcessNotify", vatID |-> vatID, kpid |-> kpid ] /\
    IF ProcessNotifyPre(vatID, kpid) THEN
       /\ ProcessNotify(vatID, kpid)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ProcessNotifyChanges
       /\ error' = "ProcessNotify"

ProcessNotifyStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E kpid \in KERNEL_SLOTS:
    ProcessNotifyAction(vatID, kpid)


DeliverToTargetAction(target, msg) ==
  UNCHANGED DeliverToTargetNotChanges /\
    action' = [ type |-> "DeliverToTarget", target |-> target, msg |-> msg ] /\
    IF DeliverToTargetPre(target, msg) THEN
       /\ DeliverToTarget(target, msg)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED DeliverToTargetChanges
       /\ error' = "DeliverToTarget"

DeliverToTargetStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E target \in KERNEL_SLOTS:
  \E msg \in VAT_MESSAGES:
    DeliverToTargetAction(target, msg)


DeliverToVatAction(vatID, target, vatMsg) ==
  UNCHANGED DeliverToVatNotChanges /\
    action' = [ type |-> "DeliverToVat", vatID |-> vatID, target |-> target, msg |-> vatMsg ] /\
    IF DeliverToVatPre(vatID, target, vatMsg) THEN
       /\ DeliverToVat(vatID, target, vatMsg)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED DeliverToVatChanges
       /\ error' = "DeliverToVat"

DeliverToVatStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E target \in KERNEL_SLOTS:
  \E vatMsg \in VAT_MESSAGES:
    DeliverToVatAction(vatID, target, vatMsg)


ExitAction(vatID, isFailure, slots) ==
  UNCHANGED ExitNotChanges /\
    action' = [ type |-> "Exit", vatID |-> vatID, isFailure |-> isFailure, slots |-> slots ] /\
    IF ExitPre(vatID, isFailure, slots) THEN
       /\ Exit(vatID, isFailure, slots)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ExitChanges
       /\ error' = "Exit"

ExitStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E isFailure \in {TRUE, FALSE}:
  \E slots \in { {slot} : slot \in KERNEL_SLOTS } \union {}:
    ExitAction(vatID, isFailure, slots)


SubscribeAction(vatID, kpid) ==
  UNCHANGED SubscribeNotChanges /\
    action' = [ type |-> "Subscribe", vatID |-> vatID, kpid |-> kpid ] /\
    IF SubscribePre(vatID, kpid) THEN
       /\ Subscribe(vatID, kpid)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED SubscribeChanges
       /\ error' = "Subscribe"

SubscribeStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
  \E kpid \in KERNEL_SLOTS:
    SubscribeAction(vatID, kpid)


ProcessQueueMessageAction ==
  UNCHANGED ProcessQueueMessageNotChanges /\
    action' = [ type |-> "ProcessQueueMessage" ] /\
    IF ProcessQueueMessagePre THEN
       /\ ProcessQueueMessage
       /\ error' = NULL
    ELSE
       /\ UNCHANGED ProcessQueueMessageChanges
       /\ error' = "ProcessQueueMessage"

ProcessQueueMessageStep ==
  ProcessQueueMessageAction

TerminateVatAction(vatID) ==
  UNCHANGED TerminateVatNotChanges /\
    action' = [ type |-> "TerminateVat", vatID |-> vatID ] /\
    IF TerminateVatPre(vatID) THEN
       /\ TerminateVat(vatID)
       /\ error' = NULL
    ELSE
       /\ UNCHANGED TerminateVatChanges
       /\ error' = "TerminateVat"

TerminateVatStep ==
  UNCHANGED <<await, terminationTrigger>> /\
  \E vatID \in VAT_IDS:
    TerminateVatAction(vatID)


AwaitStep ==
  /\ await /= NoMessage
  /\ await' = NoMessage
  /\ UNCHANGED terminationTrigger
  /\ CASE await.type = CREATE_VAT -> CreateVatAction(await.vatID, await.enablePipelining)
     []   await.type = NOTIFY -> ProcessNotifyAction(await.vatID, await.kpid)
     []   await.type = SEND -> DeliverToTargetAction(await.target, await.msg)
     []   await.type = SEND_VAT -> DeliverToVatAction(await.vatID, await.target, await.msg)

TerminationStep ==
  /\ terminationTrigger /= NULL_VAT_ID
  /\ terminationTrigger' = NULL_VAT_ID
  /\ UNCHANGED await
  /\ TerminateVatAction(terminationTrigger)


\* Kernel scheduling happens in the priority order:
\* - awaited step
\* - termination step
\* - any other step   
DefaultNext ==
  IF await /= NoMessage THEN
    AwaitStep
  ELSE IF terminationTrigger /= NULL_VAT_ID THEN 
    TerminationStep
  ELSE
    \/ ProcessQueueMessageStep
    \/ CreateVatStep
    \/ ExportStep
    \/ ImportStep
    \/ SendStep
    \/ SubscribeStep
    \/ ResolveStep
    \/ ExitStep

===============================================================================

