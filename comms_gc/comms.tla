---- MODULE comms ----

EXTENDS  Integers, FiniteSets, Sequences, TLC, tlcFolds
\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache, typedefs

VATS == {"v0", "v1", "v2", "v3"}

\* @type: () => Set(<<VAT, VAT>>);
VatPairs == VATS \X VATS
    
_kernel == "kernel"
_null == "null"

FIFO_LIMIT == 2
SEND_USE_LIMIT == 2

\* @type: () => TRUE_STATE;
TRULY_REACHABLE == "TRULY_REACHABLE"
\* @type: () => TRUE_STATE;
TRULY_RECOGNIZABLE == "TRULY_RECOGNIZABLE"
\* @type: () => TRUE_STATE;
TRULY_UNKNOWN == "TRULY_UNKNOWN"

\* @type: (VAT,VAT) => <<VAT,VAT>>;
Key(actor, remote) == <<actor, remote>>

\* @type: () => CMD;
_dropImport == "dropImport"
\* @type: () => CMD;
_dropExport == "dropExport"
\* @type: () => CMD;
_retireImport == "retireImport"
\* @type: () => CMD;
_retireExport == "retireExport"
\* @type: () => CMD;
_use == "use"

VARIABLES
    (*
    ~~~~~~~~~~~~~~
    System variables
    *)

    (*
       Maps VAT to VAT | _kernel | _null
       @type: VAT -> Str; *)
    owner,
    \* @type: <<VAT, VAT>> -> Bool;
    isReachable,
    \* @type: <<VAT, VAT>> -> Bool;
    clistExists,
    (*
       FIFO queue from [1] to [2]
       @type: <<VAT, VAT>> -> Seq(MESSAGE); *)
    fifo,
    \* @type: <<VAT, VAT>> -> Int;
    sentCnt,
    \* @type: <<VAT, VAT>> -> Int;
    receivedCnt,
    \* @type: <<VAT, VAT>> -> Int;
    lastUsage,

    (*
    ~~~~~~~~~~~~~~
    'modeling' variables
    *)

    \* @type: VAT -> TRUE_STATE;
    trueState,

    (*
       Hint which vat acted, and what they did (for trace inspection).
       @type: <<Str, Str>>; *)
    actionTakenHint,

    (*
       Limit the number of times an actor can use SendUse
       @type: VAT -> Int; *)
    sendUseCnt
    

(*
    The number of remotes with isReachable true, who are not the exporter (owner).
@type: VAT => Int; *)
reachableCnt(actor) ==
    LET Combine(acc, v) ==
        IF v # actor /\ v # owner[actor] /\ isReachable[actor, v] THEN acc + 1 ELSE acc
    IN FoldSet(Combine, 0, VATS)

(*
    The number of remotes with an existing clist, who are not the exporter (owner).
@type: VAT => Int; *)
recognizableCnt(actor) ==
    LET Combine(acc, v) ==
        IF v # actor /\ v # owner[actor] /\ clistExists[actor, v] THEN acc + 1 ELSE acc
    IN FoldSet(Combine, 0, VATS)

\* @type: () => Bool;
Init == 
    /\ trueState = "v0" :> TRULY_REACHABLE @@ [v \in VATS |-> TRULY_UNKNOWN]
    /\ owner = "v0" :> _kernel @@ [v \in VATS |-> _null]
    /\ isReachable = [p \in VatPairs |-> FALSE]
    /\ clistExists = [p \in VatPairs |-> FALSE]
    /\ fifo = [p \in VatPairs |-> <<>>]
    /\ sentCnt = [p \in VatPairs |-> 0]
    /\ receivedCnt = [p \in VatPairs |-> 0]
    /\ lastUsage = [p \in VatPairs |-> 0]
    /\ actionTakenHint = <<"_","_">>
    /\ sendUseCnt = [v \in VATS |-> 0]

(*
    Initialize with a state where "v0" has exported in a chain "v0" -> "v1" -> "v2" to "v2"
@type: () => Bool; *)
InitThreeVatsTrulyReachable == 
    /\ trueState = [v \in VATS |-> TRULY_REACHABLE]
    /\ owner = "v0" :> _kernel 
            @@ "v1" :> "v0" 
            @@ "v2" :> "v1" 
    /\ isReachable = 
           <<"v0", "v1">> :> TRUE
        @@ <<"v1", "v0">> :> TRUE
        @@ <<"v1", "v2">> :> TRUE
        @@ <<"v2", "v1">> :> TRUE
        @@ [p \in VatPairs |-> FALSE]
    /\ clistExists =
           <<"v0", "v1">> :> TRUE
        @@ <<"v1", "v0">> :> TRUE
        @@ <<"v1", "v2">> :> TRUE
        @@ <<"v2", "v1">> :> TRUE
        @@ [p \in VatPairs |-> FALSE]
    /\ fifo = [p \in VatPairs |-> <<>>]
    /\ sentCnt = [p \in VatPairs |-> 0]
    /\ receivedCnt = [p \in VatPairs |-> 0]
    /\ lastUsage = [p \in VatPairs |-> 0]
    /\ actionTakenHint = <<"_","_">>
    /\ sendUseCnt = [v \in VATS |-> 0]

(*
    Initialize with a state where "v0" has exported in a chain "v0" -> "v1" -> "v2" -> "v3" to "v3"
@type: () => Bool; *)
InitFourVatsTrulyReachable == 
    /\ trueState = [v \in VATS |-> TRULY_REACHABLE]
    /\ owner = "v0" :> _kernel 
            @@ "v1" :> "v0" 
            @@ "v2" :> "v1" 
            @@ "v3" :> "v2"
    /\ isReachable = 
           <<"v0", "v1">> :> TRUE
        @@ <<"v1", "v0">> :> TRUE
        @@ <<"v1", "v2">> :> TRUE
        @@ <<"v2", "v1">> :> TRUE
        @@ <<"v2", "v3">> :> TRUE
        @@ <<"v3", "v2">> :> TRUE
        @@ [p \in VatPairs |-> FALSE]
    /\ clistExists =
           <<"v0", "v1">> :> TRUE
        @@ <<"v1", "v0">> :> TRUE
        @@ <<"v1", "v2">> :> TRUE
        @@ <<"v2", "v1">> :> TRUE
        @@ <<"v2", "v3">> :> TRUE
        @@ <<"v3", "v2">> :> TRUE
        @@ [p \in VatPairs |-> FALSE]
    /\ fifo = [p \in VatPairs |-> <<>>]
    /\ sentCnt = [p \in VatPairs |-> 0]
    /\ receivedCnt = [p \in VatPairs |-> 0]
    /\ lastUsage = [p \in VatPairs |-> 0]
    /\ actionTakenHint = <<"_","_">>
    /\ sendUseCnt = [v \in VATS |-> 0]

(*
    When the object lifetime is finished, restart.
    This enables system cycling without infinitely increasing message counters.
@type: () => Bool; *)
Restart ==
    LET
    Precondition ==
        /\ fifo = [p \in VatPairs |-> <<>>]
        /\ trueState = [v \in VATS |-> TRULY_UNKNOWN]
        /\ isReachable = [p \in VatPairs |-> FALSE]
        /\ clistExists = [p \in VatPairs |-> FALSE]
    Action ==
        /\ trueState' = [v \in {"v0"} |-> TRULY_REACHABLE] @@ [v \in VATS |-> TRULY_UNKNOWN]
        /\ owner' = [v \in {"v0"} |-> _kernel] @@ [v \in VATS |-> _null]
        /\ isReachable' = [p \in VatPairs |-> FALSE]
        /\ clistExists' = [p \in VatPairs |-> FALSE]
        /\ fifo' = [p \in VatPairs |-> <<>>]
        /\ sentCnt' = [p \in VatPairs |-> 0]
        /\ receivedCnt' = [p \in VatPairs |-> 0]
        /\ lastUsage' = [p \in VatPairs |-> 0]
        /\ actionTakenHint' = <<"_","_">>
        /\ sendUseCnt' = [v \in VATS |-> 0]
    IN
    /\ Precondition
    /\ Action

(*
    Is a VAT in the completely blank state?
    Only allow introducing the object to a third party vat if the vat
    has not yet particapated in the system in any way.
@type: VAT => Bool; *)
IsBlank(v) ==
    \A z \in VATS:
        /\ trueState[v] = TRULY_UNKNOWN
        /\ owner[v] = _null
        /\ isReachable[z, v] = FALSE
        /\ isReachable[v, z] = FALSE
        /\ clistExists[z, v] = FALSE
        /\ clistExists[v, z] = FALSE
        /\ fifo[z, v] = <<>>
        /\ fifo[v, z] = <<>>
        /\ sentCnt[z, v] = 0
        /\ sentCnt[v, z] = 0
        /\ receivedCnt[z, v] = 0
        /\ receivedCnt[v, z] = 0
        /\ lastUsage[z, v] = 0
        /\ lastUsage[v, z] = 0

(*
@type: (VAT, VAT, Int) => Bool; *)
DeliverDropExport(actor, remote, ack) ==
    /\ UNCHANGED <<trueState, owner, clistExists>>
    /\ IF lastUsage[actor, remote] <= ack
       THEN isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
       ELSE UNCHANGED isReachable
    /\ actionTakenHint' = <<actor, "DeliverDropExport">>

(*
@type: (VAT, VAT, Int) => Bool; *)
DeliverRetireExport(actor, remote, ack) ==
    /\ UNCHANGED <<trueState, owner>>
    /\ IF lastUsage[actor, remote] <= ack
       THEN 
       /\ isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
       /\ clistExists' = [clistExists EXCEPT ![actor, remote] = FALSE]
       ELSE UNCHANGED <<isReachable, clistExists>>
    /\ actionTakenHint' = <<actor, "DeliverRetireExport">>

(*
@type: (VAT, VAT, Int) => Bool; *)
DeliverRetireImport(actor, remote, ack) ==
    /\ UNCHANGED <<trueState, owner>>
    /\ IF lastUsage[actor, remote] <= ack 
       THEN 
       /\ isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
       /\ clistExists' = [clistExists EXCEPT ![actor, remote] = FALSE]
       ELSE UNCHANGED <<isReachable, clistExists>>
    /\ actionTakenHint' = <<actor, "DeliverRetireImport">>

(*
@type: (VAT, VAT) => Bool; *)
DeliverUse(actor, remote) ==
    /\ trueState' = [trueState EXCEPT ![actor] = TRULY_REACHABLE]
    /\ owner' = [owner EXCEPT ![actor] = 
          IF owner[actor] = _null THEN remote ELSE @
        ]
    /\ isReachable' = [isReachable EXCEPT ![actor, remote] = TRUE]
    /\ clistExists' = [clistExists EXCEPT ![actor, remote] = TRUE]
    /\ actionTakenHint' = <<actor, "DeliverUse">>

(*
@type: (VAT, VAT, CMD) => Bool; *)
AddMessage(actor, remote, cmd) == 
    /\ fifo' = [fifo EXCEPT ![actor, remote] = @ \o <<[cmd |-> cmd, ack |-> receivedCnt[actor, remote]]>>]
    /\ sentCnt' = [sentCnt EXCEPT ![actor, remote] = @ + 1]

(*
@type: (VAT, VAT) => Bool; *)
SendDropExport(actor, remote) == 
    \* condition
    /\ remote = owner[actor]
    /\ reachableCnt(actor) = 0
    /\ isReachable[actor, remote]
    \* update
    /\ trueState[actor] # TRULY_REACHABLE
    /\ isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
    /\ UNCHANGED clistExists
    /\ UNCHANGED lastUsage
    /\ AddMessage(actor, remote, _dropExport)
    /\ actionTakenHint' = <<actor, "SendDropExport">>
    /\ UNCHANGED sendUseCnt

(*
@type: (VAT, VAT) => Bool; *)
SendRetireExport(actor, remote) == 
    \* condition
    /\ remote = owner[actor]
    /\ trueState[actor] = TRULY_UNKNOWN
    /\ clistExists[actor, remote]
    /\ reachableCnt(actor) = 0
    /\ recognizableCnt(actor) = 0
    \* update
    /\ isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
    /\ clistExists' = [clistExists EXCEPT ![actor, remote] = FALSE]
    /\ UNCHANGED lastUsage
    /\ AddMessage(actor, remote, _retireExport)
    /\ actionTakenHint' = <<actor, "SendRetireExport">>
    /\ UNCHANGED sendUseCnt

(*
@type: (VAT, VAT) => Bool; *)
SendRetireImport(actor, remote) ==
    \* condition
    /\ trueState[actor] # TRULY_REACHABLE
    /\ clistExists[actor, remote]
       (*
       retireImport is only enabled if the owner clist does not exist.
       This is because the actor should not tell downstream importers to
       drop their weak refs if it would be possible for the owner to
       reintroduce the item.

       If the owner is the kernel, then we go via a logical proxy to
       the true state of the actor. Since in this case the trueState is not
       TRULY_REACHABLE, we could not reintroduce the reference to downstream
       importers.
       *)
    /\ IF owner[actor] # _kernel THEN ~clistExists[actor, owner[actor]] ELSE TRUE
    /\ reachableCnt(actor) = 0
    \* update
    /\ isReachable' = [isReachable EXCEPT ![actor, remote] = FALSE]
    /\ clistExists' = [clistExists EXCEPT ![actor, remote] = FALSE]
    /\ UNCHANGED lastUsage
    /\ AddMessage(actor, remote, _retireImport)
    /\ actionTakenHint' = <<actor, "SendRetireImport">>
    /\ UNCHANGED sendUseCnt
    
(*
    Simulate usage of object in a regular message (non-gc message).
@type: (VAT, VAT) => Bool; *)
SendUse(actor, remote) ==
    \* condition
    /\ trueState[actor] = TRULY_REACHABLE
    /\ sendUseCnt[actor] < SEND_USE_LIMIT
    /\ \* use in message to importer/exporter
       \/ clistExists[actor, remote]
       \* use in message to other vat (actor becomes exporter)
       \/ IsBlank(remote)
    \* update
    /\ isReachable' = [isReachable EXCEPT ![actor, remote] = TRUE]
    /\ clistExists' = [clistExists EXCEPT ![actor, remote] = TRUE]
    /\ lastUsage' = [lastUsage EXCEPT ![actor, remote] = sentCnt[actor, remote] + 1]
    /\ AddMessage(actor, remote, _use)
    /\ actionTakenHint' = <<actor, "SendUse">>
    /\ sendUseCnt' = [sendUseCnt EXCEPT ![actor] = @ + 1]

(*
@type: VAT => Bool; *)
ReachableToRecognizable(actor) == 
    \* condition
    /\ trueState[actor] = TRULY_REACHABLE
    \* update
    /\ trueState' = [trueState EXCEPT ![actor] = TRULY_RECOGNIZABLE]
    /\ actionTakenHint' = <<actor, "spontaneouslyToRecognizable">>

(*
@type: VAT => Bool; *)
RecognizableToUnknown(actor) == 
    \* condition
    /\ trueState[actor] = TRULY_RECOGNIZABLE
       (*
       Cannot transition to unknown unless downstream are all unknowing.
       *)
    /\ recognizableCnt(actor) = 0
    \* update
    /\ trueState' = [trueState EXCEPT ![actor] = TRULY_UNKNOWN]
    /\ actionTakenHint' = <<actor, "spontaneouslyToUnknown">>

(*
@type: () => Bool; *)
Next ==
    \/ Restart
    \/ \E actor, remote \in VATS:
        /\ actor # remote
        /\ 0 < Len(fifo[remote, actor])
        /\ fifo' = [fifo EXCEPT ![remote, actor] = Tail(@)]
        /\ receivedCnt' = [receivedCnt EXCEPT ![actor, remote] = @ + 1]
        /\ LET m == Head(fifo[remote, actor]) IN
           CASE m.cmd = _dropExport -> DeliverDropExport(actor, remote, m.ack)
             [] m.cmd = _retireExport -> DeliverRetireExport(actor, remote, m.ack)
             [] m.cmd = _retireImport -> DeliverRetireImport(actor, remote, m.ack)
             [] m.cmd = _use -> DeliverUse(actor, remote)
        /\ UNCHANGED sentCnt
        /\ UNCHANGED lastUsage
        /\ UNCHANGED sendUseCnt
    \/ \E actor, remote \in VATS:
        /\ actor # remote
        /\ ~IsBlank(actor)
        /\ Len(fifo[actor, remote]) < FIFO_LIMIT
        /\ \/ SendDropExport(actor, remote)
           \/ SendRetireExport(actor, remote)
           \/ SendRetireImport(actor, remote)
           \/ SendUse(actor, remote)
        /\ UNCHANGED receivedCnt
        /\ UNCHANGED owner
        /\ UNCHANGED trueState
    \/ \E actor \in VATS:
       /\ \/ ReachableToRecognizable(actor)
          \/ RecognizableToUnknown(actor)
       /\ UNCHANGED
          <<owner,
            isReachable,
            clistExists,
            fifo,
            sentCnt,
            receivedCnt,
            lastUsage,
            sendUseCnt>>

Sanity == 
    /\ TRUE
    /\ \A p \in VatPairs: Len(fifo[p]) <= FIFO_LIMIT
    /\ \A p \in VatPairs: sentCnt[p] <= 10
    /\ \A p \in VatPairs: receivedCnt[p] <= 10

(*
    If some vat can reach the object then there should be some communication path
    for that vat to refer to the object in a message to the objects original owner (_kernel).
@type: () => Bool; *)
UsefulReferencePathExistsWhenItShould == 
    (*
    There is a path of clists leading back to the kernel?
    *)
    LET
    \* @type: (VAT) => Bool;
    ExistsPathThroughClistsToKernel(v) ==
        LET 
        (* 
        Compute transitive closure of the directed graph formed by edges.
        @type: Set(<<VAT,VAT>>) => Set(<<VAT,VAT>>); *)
        transitiveClosure(edges) ==
            IF edges = {} THEN {}
            ELSE LET
            RECURSIVE
            \* @type: (Set(<<VAT,VAT>>), Int) => Set(<<VAT,VAT>>);
            Combine(_, _)
            \* @type: (Set(<<VAT,VAT>>), Int) => Set(<<VAT,VAT>>);
            Combine(acc, k) == 
                IF k = 0
                THEN acc
                ELSE Combine(acc \cup { <<s[1],t[2]>> : s \in acc, t \in edges }, k - 1)
            IN Combine(edges, Cardinality(edges) - 1)
        IN
        \E edge \in transitiveClosure({p \in VatPairs : clistExists[p]}):
        /\ edge[1] = v
        /\ owner[edge[2]] = _kernel
        
    IN \A v \in VATS: trueState[v] = TRULY_REACHABLE => 
        \/ owner[v] = _kernel
        \/ ExistsPathThroughClistsToKernel(v)

Inv ==
    /\ Sanity
    /\ UsefulReferencePathExistsWhenItShould

(*
    Check that an execution exists where the object lifetime is successfully completed. *)
GarbageCollectionTrace ==
    LET Behavior == 
        /\ trueState = [v \in VATS |-> TRULY_UNKNOWN]
        /\ isReachable = [p \in VatPairs |-> FALSE]
        /\ clistExists = [p \in VatPairs |-> FALSE]
    IN ~Behavior

====