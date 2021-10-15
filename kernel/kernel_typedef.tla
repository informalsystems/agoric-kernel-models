------------------------------ MODULE kernel_typedef --------------------------------
(*
  The model of the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see kernel.tla.
  This file defines types and auxiliary typed constants.

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
  Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  07.07.2021
*)

(* Swingset Kernel Typedefs
   ========================
   Many types are defined just as aliases to strings;
   this will be improved when Apalache starts to support union types
   
    @typeAlias: VAT_ID = Str;
    @typeAlias: VAT_SLOT_T = Str;
    @typeAlias: VAT_SLOT = [ type: VAT_SLOT_T, id: Int, exported: Bool ];
    @typeAlias: VAT = [ oNextId: Int, pNextId: Int, enablePipelining: Bool ];
    
    @typeAlias: VAT_TABLE = VAT_ID -> VAT;

    @typeAlias: KERNEL_SLOT_T = Str;
    @typeAlias: KERNEL_SLOT = [ type: KERNEL_SLOT_T, id: Int ];

    @typeAlias: VAT_MESSAGE = [ result: KERNEL_SLOT, slots: Set(KERNEL_SLOT)];
    
    @typeAlias: MESSAGE_T = Str;
    @typeAlias: MESSAGE = [ type: MESSAGE_T, vatID: VAT_ID, enablePipelining: Bool, kpid: KERNEL_SLOT, target: KERNEL_SLOT, vatMsg: VAT_MESSAGE];

    @typeAlias: RESOLUTION = [ kpid: KERNEL_SLOT, rejected: Bool, slots: Seq(KERNEL_SLOT) ];

    @typeAlias: VAT_TO_KERNEL = VAT_ID -> VAT_SLOT -> KERNEL_SLOT;
    @typeAlias: KERNEL_TO_VAT = VAT_ID -> KERNEL_SLOT -> VAT_SLOT;

    @typeAlias: OBJECT = [ owner: VAT_ID ];

    @typeAlias: RUN_QUEUE = Seq(MESSAGE);

    @typeAlias: PROMISE_T = Str;
    @typeAlias: PROMISE = [state: PROMISE_T, decider: VAT_ID, subscribers: Set(VAT_ID), queue: RUN_QUEUE, slots: Set(KERNEL_SLOT)];
    \* Can be either [state == UNRESOLVED, decider: VAT_ID, subscribers: Set(VAT_ID), queue: RUN_QUEUE] 
    \* or [state == FULFILLED/REJECTED, slots: Set(KERNEL_SLOT)]

    @typeAlias: OBJECT_TABLE = KERNEL_SLOT -> OBJECT;
    @typeAlias: PROMISE_TABLE = KERNEL_SLOT -> PROMISE;

    An action taken by the model
    @typeAlias: ACTION = [ type: Str, vatID: VAT_ID, vatSlot: VAT_SLOT, kernelSlot: KERNEL_SLOT, kpid: KERNEL_SLOT, target: KERNEL_SLOT, 
                           msg: VAT_MESSAGE, isFailure: Bool, slots: Set(KERNEL_SLOT) ];

*)
NULL == "Null" \* An equivalent of Javascript null

NULL_ACTION == [ type |-> NULL ]


\* Vats
  NULL_VAT == [ oNextId |-> 50, pNextId |-> 60, enablePipelining |-> FALSE]
  NULL_VAT_ID == "null-vat-id"

\* Vat slots
  \* @type: () => VAT_SLOT_T;
  VAT_OBJECT == "vat-object"
  \* @type: () => VAT_SLOT_T;
  VAT_PROMISE == "vat-promise"
  \* @type: () => VAT_SLOT_T;
  VAT_DEVICE == "device" \* TODO ignoring for now

  \* @type: () => VAT_SLOT;
  NULL_VAT_SLOT == [ type |-> VAT_OBJECT, id |-> 0, exported |-> FALSE ]

  \* Exported Vat Object slot @type: (Int) => VAT_SLOT;
  EVO(id) == [ type |-> VAT_OBJECT, id |-> id, exported |-> TRUE ]
  \* Imported Vat Object slot @type: (Int) => VAT_SLOT;
  IVO(id) == [ type |-> VAT_OBJECT, id |-> id, exported |-> FALSE ]
  \* Exported Vat Promise slot @type: (Int) => VAT_SLOT;
  EVP(id) == [ type |-> VAT_PROMISE, id |-> id, exported |-> TRUE ]
  \* Imported Vat Promise slot @type: (Int) => VAT_SLOT;
  IVP(id) == [ type |-> VAT_PROMISE, id |-> id, exported |-> TRUE ]

\* Kernel slots
  \* @type: () => KERNEL_SLOT_T;
  KERNEL_OBJECT == "kernel-object"
  \* @type: () => KERNEL_SLOT_T;
  KERNEL_PROMISE == "kernel-promise"
  \* @type: () => KERNEL_SLOT_T;
  KERNEL_DEVICE == "kernel-device" \* TODO ignoring for now

  \* @type: () => KERNEL_SLOT;
  NULL_KERNEL_SLOT == [ type |-> KERNEL_OBJECT, id |-> 0 ]

  \* Kernel Object slot @type: (Int) => KERNEL_SLOT;
  KO(id) == [ type |-> KERNEL_OBJECT, id |-> id ]
  \* Kernel Promise slot @type: (Int) => KERNEL_SLOT;
  KP(id) == [ type |-> KERNEL_PROMISE, id |-> id ]

\* Kernel promises 
  \* @type: () => PROMISE_T;
  UNRESOLVED == "unresolved"
  \* @type: () => PROMISE_T;
  FULFILLED == "fulfilled"
  \* @type: () => PROMISE_T;
  REJECTED == "rejected"
  \* REDIRECTED == "redirected" \* not implemented in the code

  \* @type: () => PROMISE;
  NULL_PROMISE == [ state |-> REJECTED, slots |-> {} ]
  \* @type: (VAT_ID) => PROMISE;
  NEW_PROMISE(vatID) == [ state |-> UNRESOLVED, subscribers |-> {}, queue |-> <<>>, decider |-> vatID ]
  
  \* kernel.js processQueueMessage(): https://git.io/JGIh1
  PromiseState == { UNRESOLVED, FULFILLED, REJECTED  (*, RedirectedPromise *) }

\* Kernel objects
  \* @type: () => OBJECT;
  NULL_OBJECT == [ owner |-> NULL_VAT_ID ]
  \* @type: (VAT_ID) => OBJECT;
  NEW_OBJECT(vatID) == [ owner |-> vatID ]

\* Run queue messages 
\* (type MESSAGE)

  CREATE_VAT == "create-vat"
  NOTIFY == "notify"
  SEND == "send"
  \* Artificial message meaning that the message is absent
  NO_MESSAGE == "no-message"
  \* Artificial message to deliver to a specific VAT
  SEND_VAT == "send-vat"

  \* kernel.js start(): https://git.io/JGIx6
  \* @type: (VAT_ID, Bool) => MESSAGE;
  CreateVatMessage(vatID, enablePipelining) == [ type |-> CREATE_VAT, vatID |-> vatID, enablePipelining |-> enablePipelining ]

  \* kernelSyscall.js doSend(): https://git.io/JGLfH
  \* @type: (KERNEL_SLOT, VAT_MESSAGE) => MESSAGE;
  SendMessage(target, msg) == [ type |-> SEND, target |-> target, msg |-> msg ]
  
  \* kernel.js notify(): https://git.io/JGIAK
  \* @type: (VAT_ID, KERNEL_SLOT) => MESSAGE;
  NotifyMessage(vatID, kpid) == [ type |-> NOTIFY, vatID |-> vatID, kpid |-> kpid ]

  \* Artificial message to deliver to a specific VAT (needed in DeliverToTarget)
  \* @type: (VAT_ID, KERNEL_SLOT, VAT_MESSAGE) => MESSAGE;
  SendMessageToVat(vatID, target, msg) == [ type |-> SEND_VAT, vatID |-> vatID, target |-> target, msg |-> msg ]

  \* Artificial message meaning that the message is absent
  \* @type: () => MESSAGE;
  NoMessage == [ type |-> NO_MESSAGE ]


NEW_VAT(enablePipelining) == [ oNextId |-> 50, pNextId |-> 60, enablePipelining |-> enablePipelining]

\* @type: () => VAT_TABLE;
EMPTY_VAT_TABLE == [ vatID \in {} |-> NULL_VAT ]
\* @type: () => OBJECT_TABLE;
EMPTY_OBJECT_TABLE == [ slot \in {} |-> NULL_OBJECT ]
\* @type: () => PROMISE_TABLE;
EMPTY_PROMISE_TABLE == [ slot \in {} |-> NULL_PROMISE ]
\* @type: () => VAT_SLOT -> KERNEL_SLOT;
EMPTY_VAT_TO_KERNEL_ENTRY == [ slot \in {} |-> NULL_KERNEL_SLOT ]
\* @type: () => KERNEL_SLOT -> VAT_SLOT;
EMPTY_KERNEL_TO_VAT_ENTRY == [ slot \in {} |-> NULL_VAT_SLOT ]
\* @type: () => VAT_TO_KERNEL;
EMPTY_VAT_TO_KERNEL == [ id \in {} |-> EMPTY_VAT_TO_KERNEL_ENTRY ]
\* @type: () => KERNEL_TO_VAT;
EMPTY_KERNEL_TO_VAT == [ id \in {} |-> EMPTY_KERNEL_TO_VAT_ENTRY ]
\* @type: () => VAT_ID -> Set(KERNEL_SLOT);
EMPTY_VAT_REACH_SLOTS == [ id \in {} |-> {} ]


===============================================================================
