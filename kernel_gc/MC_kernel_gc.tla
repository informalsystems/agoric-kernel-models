------------------------------------ MODULE MC_kernel_gc -----------------------------
(*
  The model of garbage collection in the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see kernel_gc.tla.
  This file defines constants and invariants.

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
    - Daniel Tisdall <daniel@informal.systems>
    - Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  15.10.2021
*)

\* EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC, typedefs
EXTENDS Integers, FiniteSets, Sequences, TLC, typedefs

(*  For reference:
    * UNKNOWN: slotToVal[vref] is missing, vref not in deadSet
    * REACHABLE: slotToVal has live weakref, userspace can reach
    * UNREACHABLE: slotToVal has live weakref, userspace cannot reach
    * COLLECTED: slotToVal[vref] has dead weakref
    * FINALIZED: slotToVal[vref] is missing, vref is in deadSet
*)

(*
Kernel does not see these states
Known = REACHABLE or UNREACHABLE or COLLECTED
Unknown = it was COLLECTED and then FINALIZED at some points in time, but now it is UNKNOWN
*)
Known == "Known"
Unknown == "Unknown"

dispatchDropExport == "dispatchDropExport"
dispatchRetireExport == "dispatchRetireExport"
dispatchRetireImport == "dispatchRetireImport"
dispatchVenomousRetireImport == "dispatchVenomousRetireImport"

VARIABLES 
    \* @type: Str;
    mode,
    \* @type: STEP_NAME;
    step,

    (*Kernel*)
    
    \* @type: Set(ACTION);
    gc_actions,
    \* @type: Int;
    reachableCnt,
    \* @type: Int;
    recognizableCnt,
    \* @type: Bool;
    exporter_reachableFlag,
    \* @type: Bool;
    importer_reachableFlag,
    \* @type: Bool;
    venomous_reachableFlag,
    \* @type: Bool;
    exporter_clist,
    \* @type: Bool;
    importer_clist,
    \* @type: Bool;
    venomous_clist,
    \* @type: Bool;
    kernel_obj,
    \* @type: Bool;
    maybeFreeKRef,

    (*Vats*)

    \* @type: OBJECT_STATE;
    exporter_state,
    \* @type: OBJECT_STATE;
    importer_state,
    \* @type: Bool;
    exported_remotable


INSTANCE kernel_gc

ExporterUnknownOrNonRemotableImporterKnown ==
    /\ \/ exporter_state = Unknown
       \/ ~exported_remotable
    /\ importer_state = Known

KernelObjUnsafeFree ==
    /\ ~kernel_obj
    /\ \/ importer_state = Known
       \/ exporter_state = Known
       \/ 0 < reachableCnt


ClistUnsafeFree ==
    \/ /\ ~importer_clist
       /\ importer_state = Known
    \/ /\ ~exporter_clist
       /\ exporter_state = Known

\* (Just for checking model is written correctly)
GcActionsInsanity == \E x \in gc_actions : x \notin {
                                                dispatchDropExport,
                                                dispatchRetireImport,
                                                dispatchRetireExport,
                                                dispatchVenomousRetireImport
                                               }

(*
No failure should occur.
*)
MasterInv == 
    /\ ~ExporterUnknownOrNonRemotableImporterKnown
    /\ ~KernelObjUnsafeFree
    /\ ~ClistUnsafeFree
    /\ ~GcActionsInsanity
    /\ TRUE

(*
Some execution should free everything eventually.

Double negation allows finding such an execution via 'violating' the invariant.
*)
EventualDesiredOutcomeInv == 
    LET DesiredOutcome == 
        /\ importer_state = Unknown
        /\ exporter_state = Unknown
        /\ kernel_obj = FALSE
        /\ importer_clist = FALSE
        /\ exporter_clist = FALSE
        /\ venomous_clist = FALSE
    IN 
    ~DesiredOutcome

(*
JVM_ARGS="-Xmx12G" apalache-mc check --length=10 --max-error=1 --inv=EventualDesiredOutcomeInv MC_kernel_gc.tla
*)

===============================================================================
