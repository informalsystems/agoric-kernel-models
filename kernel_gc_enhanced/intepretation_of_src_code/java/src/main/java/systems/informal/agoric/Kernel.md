
mainLoop(){
    if there's a gc action
        for each kslot
            if retireExports
                for each kslot delete the owner and refCount, recognizableCnt, reachableCnt
                delete mapping and reachable
            if dropExports
                set isReachable false
            if retireImports
                if object
                    if reachable
                        reachableCnt--
                    recognizableCnt--
                    if reachableCnt 0 or recognizableCnt 0
                        add to kSlotsToMaybeFree
                if promise
                    refCount--
                    if refCount 0
                        add to kSlotsToMaybeFree
                delete mapping and reachable
        // do the actual vat delivery
        processKSlotsToMaybeFreeAndAddGcActionsToSet()
    else if item on runQueue
        if send
            decrement ref counts of target
            if there is a resultSlot
                decrement .refCount of resultSlot
                if refCount 0
                    add to kSlotsToMaybeFree
            decrement ref count of each slot in args
            deliverMsgToTarget(target, msg)
        if notify
            decrement refCount of target promise
            if refCount 0
                add to kSlotsToMaybeFree
            if target vatId has a mapping to the promise
                promises = 'retrieve a set of resolved promises by recursively looking
                            at the promises in the dataSlots of each seen resolved promise'
                for each promise found
                    get vSlot mapping
                    get vSlot mapping for all dataSlots
                    promise.refCount-- # Is this right? Why??
                    if refCount 0
                        add to kSlotsToMaybeFree
                    delete mapping and reachable
                // do the actual vat delivery
        processKSlotsToMaybeFreeAndAddGcActionsToSet()
    else: done
}

deliverMsgToTarget(targetKSlot, m){
    if target is object
        map to owner vSlot
        translate each arg slot to owner vSlot
        if there is a resultSlot
            map it to owner slot
            set decider of result slot to owner
        // do actual delivery
    if target is fulfilled preomise
        if the fulfilled promise has 1 data slot which is a fulfilled promise
            deliverMsgToTarget(kSlotOfThePromiseDataSlot0,m)
            return
        if resultKSlot
            queueNotifiesIntoRunQueue(resultKSlot, subscribers of reslutKSlot)
            requeuePromiseQueueIntoRunQueue(resultKSlot)
            resolveKPromise(resultKSlot, reject=true, dataslots=null)
    if target is rejected promise and there is a resultKSlot
        queueNotifiesIntoRunQueue(resultKSlot, subscribers of reslutKSlot)
        requeuePromiseQueueIntoRunQueue(resultKSlot)
        resolveKPromise(resultKSlot, reject=true, dataslots=null) 
    if target is unresolved promise
        if there's a decider and pipelining is enabled for it
            map targetKSlot to decider VSlot
            map each argSlot to decider VSlot
            if there is a result slot
                map it to decider VSlot
                set the decider of the result slot to the decider of the target promise
            // actual delivery to decider
        else
            targetPromise.refCount++
            if resultKSlot
                promise at resultKSlot.refCount++
            incrementRefCounts for each kSlotInArgs
            add message to targetPromise queue
}

processKSlotsToMaybeFreeAndAddGcActionsToSet(){
    for kslot in maybeFree
        if promise
            if refCount 0
                decrementRefCounts for all dataslots
                status = deleted
                q = empty
                subscribers = nulll
                dataslots= null
                decider = null
                refcount = null
        if object and reachableCnt 0 and owner is not null
            if isReachable for owner
                add dropExport action to gcActions with {
                    nature = dropExports
                    targetVatId = owner
                    kSlot = kSlot
                }
            if recongizableCnt 0
                add retireExport action to gcActions with {
                    nature = retireExports
                    targetVatId = owner
                    kSlot = kSlot
                }
    maybeFree = {}
}

sendSyscall(target, msg){
    m has args references
    m may have a result reference
    map the target, args and result references
    increase their refCount or reachableCnt, recognizableCnt
    queue a runQueue message aiming at the mapped target
}

subscribeSyscall(vpSlot){
    get the kpSlot mapping
    if unresolved
        add caller to subscribers
    if resolved
        increment refCount of targeted promise
        queue a notify for the calling vat, aiming at the promise
}

resolveSyscall(resolutions){
    for each resolution
        get the targeted kernel promise
        map the resolution dataSlots
        kernel promise refCount--
        if kernel promise refCount 0
            add to kSlotsToMaybeFree
        remove mappings and reachable for the kernel promise
        for each subscriber to the resolved promise (not including caller)
            queue a notify to the subscriber, for the promise
            increment refCount of promise
        for each message in the promise queue
            requeue it on the runQueue as a send targeted at the promise
        clear the q, the subscribers, decider of the promise
        mark as rejected/fullfilled
        for each reference in the resolved data, increment refCount or reachableCnt, recognizableCnt
}

dropImportsSyscall(vSlots){
    for each vSlot
        get kSlot via existing mapping
        if reachable
            set reachable false
            if object
                reachableCnt--
                if reachableCnt 0
                    add to kSlotsToMaybeFree
}

retireImportsSyscall(vSlots){
    for each vSlot
        get kSlot via existing mapping
        if promise
            refCount--
            if refCount 0
                add to kSlotsToMaybeFree
        if object
            if reachable
                reachableCnt--
            recognizableCnt--
            if reachableCnt 0 or recognizableCnt 0
                add to kSlotsToMaybeFree
            remove mappings and reachable
}

retireExportsSyscall(vSlots){
    for each vSlot
        get kSlot via existing mapping
        if promise
            refCount--
            if refCount 0
                add to kSlotsToMaybeFree
        remove mappings and reachable
        for each importer (mapping exist and not isAllocatedByVat)
            add a retireImports call targeting the importer, for the kSlot, to gcActions
        set owner to null
        delete refCount, reachableCnt, recognizableCnt
}

incrementRefCounts(kSlot){
    if promise
        refCount++
    if object
        reachableCnt++
        recognizableCnt++
}

decrementRefCounts(kSlot){
    if promise
        refCount--
        if refCount 0
            add kSlot to kSlotsToMaybeFree
    if object
        reachableCnt--
        recognizableCnt--
        if reachableCnt 0 or recognizableCnt 0
            add kSlot ot kSlotsToMaybeFree
}

mapVSlotToKSlot(vSlot){
    allocatedByVat is known
    type is known
    if mapping doesn't exist then it must be allocatedByVat
        create a new kSlot
        if object
            owner = vat
            reachableCnt, recognizableCnt = 0
        if promise
            refCount = 1
            subscribers = empty
            dataSlots = empty
            status =  unresolved
            decider = vat
        create slot mappings (map vslot to kslot and vice versa)
        set reachable false
    get kSlot
    if allocatedByVat
        set reachable true
    return kSlot
}

mapKSlotToVSlot(kSlot){
    if mapping doesn't exist
        if object
            recognizableCnt++
        if promise
            refCount++
        set not allocated by vat
        save the type
        create slot mappings
    get vSlot
    if not allocatedByVat and not reachable
        set reachable true
        if object
            reachableCnt++
    return vSlot
}