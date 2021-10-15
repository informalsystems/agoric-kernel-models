------------------------------ MODULE typedefs --------------------------------
(*
  The model of garbage collection in the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see kernel_gc.tla.
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

\* EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC
EXTENDS Integers, FiniteSets, Sequences, TLC

(* Swingset Kernel Garbage Collector Typedefs
   ========================

    @typeAlias: ACTION = Str;
    @typeAlias: OBJECT_STATE = Str;
    @typeAlias: STEP_NAME = Str;

*)

typedefs_aliases == FALSE



===============================================================================
