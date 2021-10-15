------------------------------------ MODULE kernel_gc -----------------------------
(*
  The model of garbage collection in the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  This is the main model file, which is complemented by:
    - typedefs.tla (defines types and auxiliary operators)
    - MC_kernel_gc.tla (defines constants and Apalache trace views)

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
EXTENDS  Integers, FiniteSets, Sequences, TLC, typedefs

CONSTANTS
    \* @type: ACTION;
    dispatchDropExport,
    \* @type: ACTION;
    dispatchRetireImport,
    \* @type: ACTION;
    dispatchRetireExport,
    \* @type: ACTION;
    dispatchVenomousRetireImport,
    \* @type: OBJECT_STATE;
    Known,
    \* @type: OBJECT_STATE;
    Unknown

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


(*
For using tlc...
*)

RECURSIVE FoldSet(_,_,_)
FoldSet( Op(_,_), v, S ) == IF S = {}
                            THEN v
                            ELSE LET w == CHOOSE x \in S: TRUE
                                  IN LET T == S \ {w}
                                      IN FoldSet( Op, Op(v,w), T )
                                      

(*
Util
*)
ZeroMax(x) == IF x < 0 THEN 0 ELSE x

SemanticVars == <<
    gc_actions,
    reachableCnt,
    recognizableCnt,
    exporter_reachableFlag,
    importer_reachableFlag,
    venomous_reachableFlag,
    exporter_clist,
    importer_clist,
    venomous_clist,
    kernel_obj,
    maybeFreeKRef,
    exporter_state,
    importer_state,
    exported_remotable
    >>

Init ==
    \* Important for TLA model only
    /\ mode = "tryGcAction"
    /\ step = "init"

    \* Kernel implementation sees these
    /\ gc_actions = {}
    /\ reachableCnt = 2
    /\ recognizableCnt = 2
    /\ exporter_reachableFlag = TRUE
    /\ importer_reachableFlag = TRUE
    /\ venomous_reachableFlag = TRUE
    /\ exporter_clist = TRUE
    /\ importer_clist = TRUE
    /\ venomous_clist = TRUE
    /\ kernel_obj = TRUE
    /\ maybeFreeKRef = FALSE

    \* Relevant vats see these, kernel implementation does not
    /\ exporter_state = Known
    /\ importer_state = Known
    /\ exported_remotable = TRUE

dropExportIsValid ==
    /\ exporter_reachableFlag = TRUE
    /\ reachableCnt = 0
    /\ kernel_obj
    /\ exporter_clist

retireExportIsValid ==
    /\ reachableCnt = 0
    /\ recognizableCnt = 0
    /\ kernel_obj
    /\ exporter_clist

retireImportIsValid == 
       importer_clist
       
retireVenomousImportIsValid == 
       venomous_clist

ValidGcActions == 
    LET Filter(have, action) ==
        CASE action = dispatchDropExport -> 
            IF dropExportIsValid
             THEN have \cup {dispatchDropExport}
            ELSE have
        [] action = dispatchRetireExport -> 
            IF 
            \* DropExport has higher priority
            /\ ~((dispatchDropExport \in gc_actions) /\ dropExportIsValid)
            /\ retireExportIsValid
             THEN have \cup {dispatchRetireExport}
            ELSE have
        [] action = dispatchRetireImport -> 
            IF retireImportIsValid
             THEN have \cup {dispatchRetireImport}
            ELSE have
        [] action = dispatchVenomousRetireImport -> 
            IF retireVenomousImportIsValid
             THEN have \cup {dispatchVenomousRetireImport}
            ELSE have
    IN
    FoldSet(Filter, {}, gc_actions)

DeletedGcActions(unchosen_valid_actions) == 
    LET Filter(have, action) ==
        CASE action = dispatchDropExport -> have \cup {dispatchDropExport}
        [] action = dispatchRetireExport -> 
            \* Even if invalid it won't be deleted if dropExport was valid
            IF ~((dispatchDropExport \in gc_actions) /\ dropExportIsValid)
             THEN have \cup {dispatchRetireExport}
            ELSE have
        [] action = dispatchRetireImport -> have \cup {dispatchRetireImport}
        [] action = dispatchVenomousRetireImport -> have \cup {dispatchVenomousRetireImport}
    IN
    (*
    If an action wasn't nondeterministically chosen, but it was still valid
    then we must keep it in the set
    *)
    FoldSet(Filter, {}, gc_actions) \ unchosen_valid_actions

DispatchDropExport ==
    /\ step' = "dispatchDropExport"
    /\ UNCHANGED <<
        reachableCnt,
        recognizableCnt,
        importer_reachableFlag,
        exporter_clist,
        importer_clist,
        kernel_obj,
        maybeFreeKRef,
        exporter_state,
        importer_state,
        venomous_reachableFlag,
        venomous_clist
        >>
    /\ exporter_reachableFlag' = FALSE
    /\ exported_remotable' = FALSE

DispatchRetireExport ==
    /\ step' = "dispatchRetireExport"
    /\ UNCHANGED <<
        reachableCnt,
        recognizableCnt,
        importer_reachableFlag,
        importer_clist,
        maybeFreeKRef,
        importer_state,
        exported_remotable,
        venomous_reachableFlag,
        venomous_clist
        >>
    /\ exporter_reachableFlag' = FALSE
    /\ exporter_clist' = FALSE
    /\ exporter_state' = Unknown
    /\ kernel_obj' = FALSE

DispatchRetireImport ==
    /\ step' = "dispatchRetireImport"
    /\ UNCHANGED <<
        reachableCnt,
        exporter_reachableFlag,
        exporter_clist,
        kernel_obj,
        exporter_state,
        exported_remotable,
        venomous_clist,
        venomous_reachableFlag
        >>
    /\ importer_reachableFlag' = FALSE
    /\ importer_clist' = FALSE
    (*
    The vat source code does not currently actually react to a RetireImport
    dispatch in any way.
    *)
    /\ importer_state' = Unknown
    /\ kernel_obj' = FALSE
    /\ recognizableCnt' = ZeroMax(recognizableCnt - 1)
    /\ IF recognizableCnt' = 0 \/ reachableCnt = 0 THEN
        maybeFreeKRef' = TRUE
       ELSE UNCHANGED <<maybeFreeKRef>>

DispatchVenomousRetireImport ==
    /\ step' = "dispatchVenomousRetireImport"
    /\ UNCHANGED <<
        reachableCnt,
        exporter_reachableFlag,
        exporter_clist,
        kernel_obj,
        exporter_state,
        exported_remotable,
        importer_reachableFlag,
        importer_clist,
        importer_state
        >>
    /\ venomous_reachableFlag' = FALSE
    /\ venomous_clist' = FALSE
    /\ kernel_obj' = FALSE
    /\ recognizableCnt' = ZeroMax(recognizableCnt - 1)
    /\ IF recognizableCnt' = 0 \/ reachableCnt = 0 THEN
        maybeFreeKRef' = TRUE
       ELSE UNCHANGED <<maybeFreeKRef>>

TryGcAction == 
    \/ \E dispatch \in ValidGcActions:
        \* If there is a valid action, we must perform it.
        /\ gc_actions' = gc_actions \ DeletedGcActions(ValidGcActions \ {dispatch})
        /\ CASE dispatch = dispatchDropExport   -> DispatchDropExport
             [] dispatch = dispatchRetireExport -> DispatchRetireExport
             [] dispatch = dispatchRetireImport -> DispatchRetireImport
             [] dispatch = dispatchVenomousRetireImport -> DispatchVenomousRetireImport
    \/ /\ ValidGcActions = {}
       \* If there are no valid actions then we still erase invalid ones
       /\ step' = "noValidGcActions"
       /\ gc_actions' = gc_actions \ DeletedGcActions({})
       /\ UNCHANGED <<
           reachableCnt,
           recognizableCnt,
           exporter_reachableFlag,
           importer_reachableFlag,
           exporter_clist,
           importer_clist,
           kernel_obj,
           maybeFreeKRef,
           importer_state,
           exporter_state,
           exported_remotable,
           venomous_clist,
           venomous_reachableFlag
           >>

SyscallDropImport ==
    /\ step' = "syscallDropImport"
    /\ UNCHANGED <<
        gc_actions,
        exported_remotable,
        exporter_reachableFlag,
        venomous_reachableFlag,
        recognizableCnt,
        exporter_clist,
        importer_clist,
        venomous_clist,
        exporter_state,
        kernel_obj
        >>
    (*
    The importer state still to moves to Unknown because any object in
    the deadset will only be processed at most once. Moving to Unknown
    disables a subsequent RetireImport syscall, which would be invalid.
    *)
    /\ importer_state = Known
    /\ importer_state' = Unknown
    /\ importer_reachableFlag' = FALSE
    /\ IF importer_reachableFlag /\ kernel_obj THEN
        /\ reachableCnt' = ZeroMax(reachableCnt - 1)
        /\ IF reachableCnt' = 0 THEN
            maybeFreeKRef' = TRUE
           ELSE UNCHANGED maybeFreeKRef
       ELSE UNCHANGED  << reachableCnt, maybeFreeKRef>>

SyscallDropAndRetireImport ==
    /\ step' = "syscallDropAndRetireImport"
    /\ UNCHANGED <<
        gc_actions,
        exporter_reachableFlag,
        exporter_clist,
        kernel_obj,
        exporter_state,
        exported_remotable,
        venomous_reachableFlag,
        venomous_clist
        >>
    /\ importer_state = Known
    /\ importer_state' = Unknown
    /\ importer_reachableFlag' = FALSE
    /\ importer_clist' = FALSE
    /\ IF importer_reachableFlag /\ kernel_obj THEN
        reachableCnt' = ZeroMax(reachableCnt - 1)
       ELSE UNCHANGED reachableCnt
    /\ IF kernel_obj THEN
        /\ recognizableCnt' = ZeroMax(recognizableCnt - 1)
        /\ IF recognizableCnt' = 0 \/ reachableCnt = 0 THEN
            maybeFreeKRef' = TRUE
           ELSE UNCHANGED maybeFreeKRef
       ELSE UNCHANGED  << recognizableCnt, maybeFreeKRef>>

SyscallRetireExport ==
    /\ step' = "syscallRetireExport"
    /\ UNCHANGED <<
        reachableCnt,
        recognizableCnt,
        exporter_reachableFlag,
        importer_reachableFlag,
        venomous_reachableFlag,
        importer_clist,
        venomous_clist,
        maybeFreeKRef,
        importer_state,
        exported_remotable
        >>
    /\ ~exported_remotable
    /\ exporter_state = Known
    /\ exporter_state' = Unknown
    /\ gc_actions' = gc_actions \cup {
                                      dispatchRetireImport, 
                                      dispatchVenomousRetireImport
                                     }
    /\ kernel_obj' = FALSE
    /\ exporter_clist' = FALSE

SyscallVenomousDropImport ==
    /\ step' = "syscallVenomousDropImport"
    /\ UNCHANGED <<
        gc_actions,
        exporter_reachableFlag,
        exporter_clist,
        kernel_obj,
        exporter_state,
        exported_remotable,
        importer_reachableFlag,
        importer_clist,
        importer_state,
        venomous_clist,
        recognizableCnt
        >>
    /\ venomous_reachableFlag' = FALSE
    /\ IF venomous_reachableFlag /\ kernel_obj THEN
        /\ reachableCnt' = ZeroMax(reachableCnt - 1)
        /\ IF reachableCnt' = 0 THEN
            maybeFreeKRef' = TRUE
           ELSE UNCHANGED maybeFreeKRef
       ELSE UNCHANGED  << reachableCnt, maybeFreeKRef>>

SyscallVenomousRetireImport ==
    /\ step' = "syscallVenomousRetireImport"
    /\ UNCHANGED <<
        gc_actions,
        exporter_reachableFlag,
        exporter_clist,
        kernel_obj,
        exporter_state,
        exported_remotable,
        venomous_reachableFlag,
        importer_reachableFlag,
        importer_clist,
        importer_state,
        reachableCnt
        >>
    /\ venomous_clist' = FALSE
    (*This conditions is checked in the kernel source code*)
    /\ ~venomous_reachableFlag
    /\ IF kernel_obj THEN
        /\ recognizableCnt' = ZeroMax(recognizableCnt - 1)
        /\ IF recognizableCnt' = 0 \/ reachableCnt = 0 THEN
            maybeFreeKRef' = TRUE
           ELSE UNCHANGED maybeFreeKRef
       ELSE UNCHANGED  << recognizableCnt, maybeFreeKRef>>

Syscall ==
    \/ SyscallDropImport
    (*
    Correct liveSlots code will never Retire and not Drop first.
    *)
    \/ SyscallDropAndRetireImport
    \/ SyscallRetireExport
    (*
    Buggy liveSlots code will do whatever it wants (multiple times too)
    *)
    \/ SyscallVenomousDropImport
    \/ SyscallVenomousRetireImport

HandleKRef ==

    LET ToAdd ==
        CASE  exporter_reachableFlag /\  recognizableCnt = 0 -> {dispatchDropExport, dispatchRetireExport}
          []  exporter_reachableFlag /\ ~recognizableCnt = 0 -> {dispatchDropExport                      }
          [] ~exporter_reachableFlag /\  recognizableCnt = 0 -> {                    dispatchRetireExport}
          [] ~exporter_reachableFlag /\ ~recognizableCnt = 0 -> {                                        }
    IN

    /\ step' = "HandleKRef"
    /\ UNCHANGED <<
        reachableCnt,
        recognizableCnt,
        exporter_reachableFlag,
        importer_reachableFlag,
        venomous_reachableFlag,
        exporter_clist,
        importer_clist,
        venomous_clist,
        exporter_state,
        importer_state,
        exported_remotable,
        kernel_obj
        >>
    /\ maybeFreeKRef' = FALSE
    /\ \/ /\ ~(maybeFreeKRef /\ reachableCnt = 0)
          /\ UNCHANGED gc_actions
       \/ /\ maybeFreeKRef
          /\ reachableCnt = 0
          /\ maybeFreeKRef' = FALSE
          /\ gc_actions' = gc_actions \cup ToAdd

Next == 

    \/ /\ mode = "tryGcAction"
       /\ mode' = "trySyscall"
       /\ TryGcAction

    \/ /\ mode = "trySyscall"
       /\ mode' \in {"handleKRef", "trySyscall"}
       /\ \/ Syscall
          \/ /\ UNCHANGED SemanticVars
             /\ step' = "skipSyscall"

    \/ /\ mode = "handleKRef"
       /\ mode' = "tryGcAction"
       /\ HandleKRef

===============================================================================
