------------------------------ MODULE typedefs --------------------------------

\* EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC
EXTENDS Integers, FiniteSets, Sequences, TLC

(* 

   Swingset Kernel Garbage Collector (Enhanced) Typedefs
   ========================

    @typeAlias: ACTION_NAME = Str;

    @typeAlias: THING_ID = Str;
    @typeAlias: VAT_ID = Str;
    @typeAlias: NATURE = Str;

    @typeAlias: MESSAGE = [ 
        argId    : THING_ID, 
        resultId : THING_ID
    ];
    @typeAlias: Q_ENTRY = [ 
        nature                   : NATURE,
        msgForSend               : MESSAGE, 
        targetIdForSend          : THING_ID,
        targetVatIdForNotify     : VAT_ID,
        promIdForNotify       : THING_ID
    ];
    @typeAlias: THING = [
        nature          : NATURE,
        owner           : VAT_ID,
        q               : Seq(MESSAGE),
        status          : NATURE,
        decider         : VAT_ID,
        subscribers     : Set(VAT_ID),
        refCnt          : Int,
        reachableCnt    : Int,
        recognizableCnt : Int,
        trueAllocator   : VAT_ID
    ];
    @typeAlias: GC_ACTION = [
        nature : NATURE,
        objId : THING_ID,
        groupedObjIds : Set(THING_ID),
        targetVatId : VAT_ID
    ];

*)

sany_please_dont_forget_me == FALSE

===============================================================================
