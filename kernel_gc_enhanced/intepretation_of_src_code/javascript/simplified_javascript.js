
mainloop(){
    while (true) {
        const gcMessage = processNextGCAction(kernelKeeper);
        if (gcMessage) {
            processQueueMessage(gcMessage)
        } else {
            if (kernelKeeper.isRunQueueEmpty()) {
                return
            }
            else processQueueMessage(kernelKeeper.getNextMsg());
        }
    }
}
processNextGCAction(kernelKeeper) {
    /*
    isValid(){
        if dropExport
            return (
                    kernelObj exists
                and reachableCnt positive
                and clist exist
                and isReachable true
            )
        if retireExport
            return (
                    kernelObj exists
                and reachableCnt positive or recognizableCnt positive
                and clist exist
            )
        if retireImport
            return clist exist
    }
    allActionSet = getGcActions()
    // group them by vat and action type
    deterministically, for each vat:
        // priorities are dropExport > retireExport > retireImport
        for each priority:
            get actions of type
            filter them according to isValid
            throw away invalid ones from allActionSet
            if there is a valid one
                deterministically pick one and return it
    */
}

processQueueMessage(message) {
    gcMessages = ['dropExports', 'retireExports', 'retireImports'];
    if (message.type === 'send') {
        decrementRefCountNoOpts(message.target)
        if (message.msg.result) {
            decrementRefCountNoOpts(message.msg.result)
        }
        for (argSlot of message.msg.args.slots) {
            decrementRefCountNoOpts(argSlot)
        }
        deliverToTarget(message.target, message.msg);
    } else if (message.type === 'notify') {
        decrementRefCountNoOpts(message.kpid)
        processNotify(message);
    } else if (gcMessages.includes(message.type)) {
        processGCMessage(message);
    }
    processRefcounts();
}

processGCMessage(message) {
    { type, vatID, krefs } = message;
    kd = ([type, krefs]);
    if (type === 'retireExports') {
        for (kref of krefs) {
            deleteKernelObjectOwnerAndRefCount(kref);
        }
    }
    vd = translateKernelDeliveryToVatDelivery(vatID, kd);
    await doActualVatDelivery(vatID, kd, vd);
}

deliverToTarget(target, msg) {
    { type } = readKernelSlot(target);
    if (type === 'object') {
        vatID = getOwnerVatOfKerObj(target);
        if (vatID) {
            await deliverToVat(vatID, target, msg);
        } else if (msg.result) {
            resolveToError(msg.result, VAT_TERMINATION_ERROR);
        }
    } else if (type === 'promise') {
        kp = readKerPromise(target);
        if (kp.state === 'fulfilled') {
            presence = extractPresenceIfPresent(kp.data);
            if (presence) {
                deliverToTarget(presence, msg);
            } else if (msg.result) {
                resolveToError(msg.result, "");
            }
        } else if (kp.state === 'rejected') {
            if (msg.result) {
                resolveToError(msg.result, kp.data);
            }
        } else if (kp.state === 'unresolved') {
            if (!kp.decider) {
                addMessageToPromiseQueue(target, msg);
            } else {
                deciderVat = kp.decider;
                if (deciderVat) {
                    if (deciderVat.enablePipelining) {
                        await deliverToVat(kp.decider, target, msg);
                    } else {
                        addMessageToPromiseQueue(target, msg);
                    }
                } else if (msg.result) {
                    resolveToError(msg.result, VAT_TERMINATION_ERROR);
                }
            }
        }
    }
}

deliverToVat(vatID, target, msg) {
    kd = (['message', target, msg]);
    vd = translateKernelDeliveryToVatDelivery(vatID, kd);
    doActualVatDelivery(vatID, kd, vd);
}

translateDropExportsDispatch(krefs) {
    vrefs = krefs.map(kref =>
        mapKernelSlotToVatSlotSetReachableFalseRequiredTrue(kref),
    );
    krefs.map(kref => clearReachableFlag(kref);
    vatDelivery = (['dropExports', vrefs]);
    return vatDelivery;
}
translateRetireExportsDispatch(krefs) {
    vrefs = [];
    for (kref of krefs) {
        vref = mapKernelSlotToVatSlotSetReachableFalseRequiredTrue(kref);
        deleteCListEntry(kref, vref);
        vrefs.push(vref);
    }
    vatDelivery = (['retireExports', vrefs]);
    return vatDelivery;
}
translateRetireImportsDispatch(krefs) {
    vrefs = [];
    for (kref of krefs) {
        vref = mapKernelSlotToVatSlotSetReachableFalseRequiredTrue(kref);
        deleteCListEntry(kref, vref);
        vrefs.push(vref);
    }
    vatDelivery = (['retireImports', vrefs]);
    return vatDelivery;
}
translateMessageDispatch(target, msg) {
    targetSlot = mapKernelSlotToVatSlotNoOpts(target);
    { type } = readVatSlot(targetSlot);
    if (type === 'promise') {
        p = readKerPromise(target);
    }
    inputSlots = msg.args.slots.map(slot => mapKernelSlotToVatSlotNoOpts(slot));
    let resultSlot = null;
    if (msg.result) {
        p = readKerPromise(msg.result);
        resultSlot = mapKernelSlotToVatSlotNoOpts(msg.result);
        setDecider(msg.result, vatID);
    }
    vatDelivery = (['message', targetSlot, {
        method: msg.method,
        args: { ...msg.args, slots: inputSlots },
        result: resultSlot,
    }]);
    return vatDelivery;
}
translateSubscribeSyscall(vpid) {
    kpid = mapVatSlotToKernelSlotNoOpts(vpid);
    ks = (['subscribe', vatID, kpid]);
    return ks;
}
translateResolveSyscall(vresolutions) {
    kresolutions = [];
    kpidsResolved = [];
    for (resolution of vresolutions) {
        [vpid, rejected, data] = resolution;
        kpid = mapVatSlotToKernelSlotNoOpts(vpid);
        kernelSlots = data.slots.map(slot => mapVatSlotToKernelSlotNoOpts(slot));
        kernelData = ({ ...data, slots: kernelSlots });
        kresolutions.push([kpid, rejected, kernelData]);
        kpidsResolved.push(kpid);
    }
    deleteCListEntriesForKernelSlots(kpidsResolved);
    return (['resolve', vatID, kresolutions]);
}
translateDropImportsSyscall(vrefs) {
    krefs = vrefs.map(vref => {
        // read vat slot using vref
        kref = mapVatSlotToKernelSlotRequiredTrueSetReachableFalse(vref);
        clearReachableFlag(kref);
        return kref;
    });
    return (['dropImports', krefs]);
}
translateRetireImportsSyscall(vrefs) {
    krefs = vrefs.map(vref => {
        // read vat slot using vref
        kref = mapVatSlotToKernelSlotRequiredTrueSetReachableFalse(vref);
        if (getReachableFlag(kref)) {
            throw Error(`syscall.retireImports but ${vref} is still reachable`);
        }
        deleteCListEntry(kref, vref);
        return kref;
    });
    return (['retireImports', krefs]);
}
translateRetireExportsSyscall(vrefs) {
    krefs = vrefs.map(vref => {
        // read vat slot using vref
        kref = mapVatSlotToKernelSlotRequiredTrueSetReachableFalse(vref);
        deleteCListEntry(kref, vref);
        return kref;
    });
    return (['retireExports', krefs]);
}
translateSendSyscall(targetSlot, msg) {
    { method, args, result: resultSlot } = msg;
    target = mapVatSlotToKernelSlotNoOpts(targetSlot);
    kernelSlots = args.slots.map(slot => mapVatSlotToKernelSlotNoOpts(slot));
    kernelArgs = ({ ...args, slots: kernelSlots });
    let result = null;
    if (resultSlot) {
        result = mapVatSlotToKernelSlotNoOpts(resultSlot);
        p = readKerPromise(result);
        clearDecider(result);
    }
    ks = (['send', target, {
        method,
        args: kernelArgs,
        result,
    }]);
    return ks;
}

doSendSyscall(kernelKeeper, target, msg) {
    readKernelSlot(target);
    m = ({ type: 'send', target, msg });
    incrementRefCountWithoutOptions(target);
    if (msg.result) {
        incrementRefCountWithoutOptions(msg.result);
    }
    for (argSlot of msg.args.slots) {
        incrementRefCountWithoutOptions(argSlot);
    }
    addToRunQueue(m);
}
doSubscribeSyscall(vatID, kpid) {
    p = readKerPromise(kpid);
    if (p.state === 'unresolved') {
        addSubscriberToPromise(kpid, vatID);
    } else {
        notify(vatID, kpid);
    }
}
doResolveSyscall(vatID, resolutions) {
    doResolve(vatID, resolutions);
}
doDropImportsSyscall(koids) {
}
doRetireImportsSyscall(koids) {
}
doRetireExportsSyscall(koids) {
    newActions = [];
    for (koid of koids) {
        importers = getImporters(koid);
        for (vatID of importers) {
            newActions.push(`${vatID} retireImport ${koid}`);
        }
        deleteKernelObjectOwnerAndRefCount(koid);
    }
    // add actions to gc actions
}

processRefcounts() {
    actions = getGCActions();
    for (kref of maybeFreeKrefs.values()) {
        { type } = readKernelSlot(kref);
        if (type === 'promise') {
            kpid = kref;
            kp = readKerPromise(kpid);
            if (kp.refCount === 0) {
                for (slot of kp.data.slots) {
                    decrementRefCountNoOpts(slot);
                }
                deleteKernelPromise(kpid);
            }
        }
        if (type === 'object') {
            { reachable, recognizable } = getReachCntRecCntForKerSlot(kref);
            if (reachable === 0) {
                ownerVatID = getOwnerVatOfKerObj(kref);
                if (ownerVatID) {
                    isReachable = getReachableFlag(kref);
                    if (isReachable) {
                        actions.add(`${ownerVatID} dropExport ${kref}`);
                    }
                    if (recognizable === 0) {
                        actions.add(`${ownerVatID} retireExport ${kref}`);
                    }
                }
            }
        }
    }
    setGCActions(actions);
    maybeFreeKrefs.clear();
}



processNotify(message) {
    { vatID, kpid } = message;
    p = readKerPromise(kpid);
    vatKeeper = provideVatKeeper(vatID);
    resolutions = [];
    if (!kvStoreHasClistEntryLikeVatIdCSlot(kpid)) {
        return
    }
    targets = getKpidsToRetire(kernelKeeper, kpid, p.data);
    if (targets.length === 0) {
        return
    }
    for (toResolve of targets) {
        p = readKerPromise(toResolve)
        vpid = mapKernelSlotToVatSlotNoOpts(toResolve)
        resolutions.push([vpid, p.state === 'rejected', {
            ...p.data,
            slots: p.data.slots.map(slot => mapKernelSlotToVatSlotNoOpts(slot))
        }])
    }
    // skip kd creation
    vd = (['notify', resolutions]);
    deleteCListEntriesForKernelSlots(targets);
    await doActualVatDelivery(vatID, vd);
}

notify(vatID, kpid) {
    m = ({ type: 'notify', vatID, kpid });
    incrementRefCountWithoutOptions(kpid);
    addToRunQueue(m);
}

doResolve(vatID, resolutions) {
    for (resolution of resolutions) {
        [kpid, rejected, data] = resolution;
        p = readKerPromise(kpid, vatID);
        { subscribers } = p;
        for (subscriber of subscribers) {
            if (subscriber !== vatID) {
                notify(subscriber, kpid);
            }
        }
        resolveKernelPromise(kpid, rejected, data);
    }
}
resolveKernelPromise(kernelSlot, rejected, capdata) {
    for (dataSlot of capdata.slots) {
        incrementRefCountWithoutOptions(dataSlot);
    }
    p = readKerPromise(kernelSlot);
    for (msg of p.queue) {
        entry = ({ type: 'send', target: kernelSlot, msg });
        runQueue.push(entry);
    }
    deleteKernelPromiseState(kernelSlot);
    if (rejected) {
        kvStore.set(`${kernelSlot}.state`, 'rejected');
    } else {
        kvStore.set(`${kernelSlot}.state`, 'fulfilled');
    }
    kvStore.set(`${kernelSlot}.data.body`, capdata.body);
    kvStore.set(`${kernelSlot}.data.slots`, capdata.slots.join(','));
}
resolveToError(kpid, errorData, expectedDecider) {
    doResolve(expectedDecider, [[kpid, true, errorData]]);
}

extractPresenceIfPresent(data) {
    { body } = data
    if (
        body &&
        typeof body === 'object' &&
        body['@qclass'] === 'slot' &&
        body.index === 0
    ) {
        if (data.slots.length === 1) {
            slot = data.slots[0];
            { type } = readKernelSlot(slot);
            if (type === 'object') {
                return slot;
            }
        }
    }
    return null;
}

deleteKernelObjectOwnerAndRefCount(koid) {
    kvStore.delete(`${koid}.owner`);
    kvStore.delete(`${koid}.refCount`);
}

getImporters(koid) {
    importers = [];
    doesImport(vatID) {
        return provideVatKeeper(vatID).importsKernelSlot(koid);
    }
    importers.push(...getDynamicVats().filter(doesImport));
    importers.push(
        ...getStaticVats()
            .map(nameAndVatID => nameAndVatID[1])
            .filter(doesImport),
    );
    importers.sort();
    return importers;
}

addToRunQueue(msg) {
    queue = JSON.parse(readFromKVStore('runQueue'));
    queue.push(msg);
    kvStore.set('runQueue', JSON.stringify(queue));
}

addKernelPromise(policy) {
    kpidNum = Nat(BigInt(readFromKVStore('kp.nextID')));
    kvStore.set('kp.nextID', `${kpidNum + 1n}`);
    kpid = makeKernelSlot('promise', kpidNum);
    kvStore.set(`${kpid}.state`, 'unresolved');
    kvStore.set(`${kpid}.subscribers`, '');
    kvStore.set(`${kpid}.queue.nextID`, `0`);
    kvStore.set(`${kpid}.refCount`, `0`);
    kvStore.set(`${kpid}.decider`, '');
    return kpid;
}
addKernelPromiseForVat(deciderVatID) {
    kpid = addKernelPromise();
    kvStore.set(`${kpid}.decider`, deciderVatID);
    return kpid;
}
hasKernelPromise(kernelSlot) {
    return kvStore.has(`${kernelSlot}.state`);
}
deleteKernelPromiseState(kpid) {
    kvStore.delete(`${kpid}.state`);
    kvStore.delete(`${kpid}.decider`);
    kvStore.delete(`${kpid}.subscribers`);
    kvStore.delete(`${kpid}.policy`);
    kvStore.deletePrefixedKeys(`${kpid}.queue.`);
    kvStore.delete(`${kpid}.queue.nextID`);
    kvStore.delete(`${kpid}.slot`);
    kvStore.delete(`${kpid}.data.body`);
    kvStore.delete(`${kpid}.data.slots`);
}
deleteKernelPromise(kpid) {
    deleteKernelPromiseState(kpid);
    kvStore.delete(`${kpid}.refCount`);
}
readKerPromise(kernelSlot) {
    p = { state: kvStore.get(`${kernelSlot}.state`) };
    switch (p.state) {
        case undefined:
        case 'unresolved':
            p.refCount = Number(kvStore.get(`${kernelSlot}.refCount`));
            p.decider = kvStore.get(`${kernelSlot}.decider`);
            if (p.decider === '') {
                p.decider = undefined;
            }
            p.policy = kvStore.get(`${kernelSlot}.policy`) || 'ignore';
            p.subscribers = commaSplit(kvStore.get(`${kernelSlot}.subscribers`));
            p.queue = Array.from(
                kvStore.getPrefixedValues(`${kernelSlot}.queue.`),
            ).map(s => JSON.parse(s));
            break;
        case 'rejected' or 'fulfilled':
            p.refCount = Number(kvStore.get(`${kernelSlot}.refCount`));
            p.data = {
                body: kvStore.get(`${kernelSlot}.data.body`),
                slots: commaSplit(kvStore.get(`${kernelSlot}.data.slots`)),
            };
            p.data.slots.map(readKernelSlot);
            break;
        default:
    }
    return (p);
}
setDecider(kpid, decider) {
    p = readKerPromise(kpid);
    kvStore.set(`${kpid}.decider`, decider);
}
clearDecider(kpid) {
    p = readKerPromise(kpid);
    kvStore.set(`${kpid}.decider`, '');
}
addSubscriberToPromise(kernelSlot, vatID) {
    p = readKerPromise(kernelSlot);
    s = new Set(p.subscribers);
    s.add(vatID);
    v = Array.from(s)
        .sort()
        .join(',');
    kvStore.set(`${kernelSlot}.subscribers`, v);
}

getKpidsToRetire(kernelKeeper, rootKPID, rootKernelData) {
    seen = new Set();
    scanKernelPromise(kpid, kernelData) {
        seen.add(kpid);
        if (kernelData) {
            for (slot of kernelData.slots) {
                { type } = readKernelSlot(slot);
                if (type === 'promise') {
                    if (!seen.has(slot)) {
                        kp = readKerPromise(slot);
                        { data, state } = kp;
                        if (state !== 'unresolved') {
                            if (data) {
                                scanKernelPromise(slot, data);
                            }
                        }
                    }
                }
            }
        }
    }
    scanKernelPromise(rootKPID, rootKernelData);
    return Array.from(seen);
}

addMessageToPromiseQueue(kernelSlot, msg) {
    incrementRefCountWithoutOptions(kernelSlot);
    if (msg.result) {
        incrementRefCountWithoutOptions(msg.result);
    }
    let idx = 0;
    for (kref of msg.args.slots) {
        incrementRefCountWithoutOptions(kref);
        idx += 1;
    }
    p = readKerPromise(kernelSlot);
    nkey = `${kernelSlot}.queue.nextID`;
    nextID = Nat(BigInt(kvStore.get(nkey)));
    kvStore.set(nkey, `${nextID + 1n}`);
    qid = `${kernelSlot}.queue.${nextID}`;
    kvStore.set(qid, JSON.stringify(msg));
}

incrementRefCountWithoutOptions(kernelSlot){
    { type } = readKernelSlot(kernelSlot);
    if (type === 'promise') {
        refCount = Nat(BigInt(kvStore.get(`${kernelSlot}.refCount`))) + 1n;
        kvStore.set(`${kernelSlot}.refCount`, `${refCount}`);
    }
    if (type === 'object') {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        reachable += 1;
        recognizable += 1;
        setObjectRefCount(kernelSlot, { reachable, recognizable });
    }
}
incrementRefCountExportTrueOnlyRecTrue(kernelSlot) {
    { type } = readKernelSlot(kernelSlot);
    if (type === 'promise') {
        refCount = Nat(BigInt(kvStore.get(`${kernelSlot}.refCount`))) + 1n;
        kvStore.set(`${kernelSlot}.refCount`, `${refCount}`);
    }
}
incrementRefCountExportFalseOnlyRecTrue(kernelSlot) {
    { type } = readKernelSlot(kernelSlot);
    if (type === 'promise') {
        refCount = Nat(BigInt(kvStore.get(`${kernelSlot}.refCount`))) + 1n;
        kvStore.set(`${kernelSlot}.refCount`, `${refCount}`);
    }
    if (type === 'object') {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        recognizable += 1;
        setObjectRefCount(kernelSlot, { reachable, recognizable });
    }
}
decrementRefCountNoOpts(kernelSlot) {
    { type } = readKernelSlot(kernelSlot);
    if (type === 'promise') {
        let refCount = Nat(BigInt(kvStore.get(`${kernelSlot}.refCount`)));
        refCount -= 1n;
        kvStore.set(`${kernelSlot}.refCount`, `${refCount}`);
        if (refCount === 0n) {
            maybeFreeKrefs.add(kernelSlot);
            return true;
        }
    }
    if (type === 'object' && refCountExistsForKerSlot(kernelSlot)) {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        reachable -= 1;
        recognizable -= 1;
        if (!reachable || !recognizable) {
            maybeFreeKrefs.add(kernelSlot);
        }
        setObjectRefCount(kernelSlot, { reachable, recognizable });
    }
    return false;
}
decrementRefCountWithOnlyRecTrue(kernelSlot, allocatedByVat) {
    { type } = readKernelSlot(kernelSlot);
    if (type === 'promise') {
        let refCount = Nat(BigInt(kvStore.get(`${kernelSlot}.refCount`)));
        refCount -= 1n;
        kvStore.set(`${kernelSlot}.refCount`, `${refCount}`);
        if (refCount === 0n) {
            maybeFreeKrefs.add(kernelSlot);
            return true;
        }
    }
    if (type === 'object' && !allocatedByVat && refCountExistsForKerSlot(kernelSlot)) {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        recognizable -= 1;
        if (!reachable || !recognizable) {
            maybeFreeKrefs.add(kernelSlot);
        }
        setObjectRefCount(kernelSlot, { reachable, recognizable });
    }
    return false;
}

deleteCListEntry(kernelSlot, vatSlot) {
    { allocatedByVat } = readVatSlot(vatSlot);
    kernelKey = `${vatID}.c.${kernelSlot}`;
    vatKey = `${vatID}.c.${vatSlot}`;
    clearReachableFlag(kernelSlot);
    decrementRefCountWithOnlyRecTrue(kernelSlot, allocatedByVat);
    kvStore.delete(kernelKey);
    kvStore.delete(vatKey);
}
deleteCListEntriesForKernelSlots(kernelSlots) {
    for (kernelSlot of kernelSlots) {
        vatSlot = mapKernelSlotToVatSlotNoOpts(kernelSlot);
        deleteCListEntry(kernelSlot, vatSlot);
    }
}

getReachableFlag(kernelSlot) {
    kernelKey = `${vatID}.c.${kernelSlot}`;
    data = kvStore.get(kernelKey);
    { isReachable } = getReachableVatSlot(..)
    return isReachable;
}
setReachableFlag(kernelSlot) {
    { type } = readKernelSlot(kernelSlot);
    kernelKey = `${vatID}.c.${kernelSlot}`;
    { isReachable, vatSlot } = getReachableVatSlot(..)
    { allocatedByVat } = readVatSlot(vatSlot);
    kvStore.set(kernelKey, setReachableAndVatSlot(true, vatSlot));
    if (!isReachable && type === 'object' && !allocatedByVat) {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        reachable += 1;
        setObjectRefCount(kernelSlot, { reachable, recognizable });
    }
}
clearReachableFlag(kernelSlot) {
    { type } = readKernelSlot(kernelSlot);
    kernelKey = `${vatID}.c.${kernelSlot}`;
    { isReachable, vatSlot } = getReachableVatSlot()
    { allocatedByVat } = readVatSlot(vatSlot);
    kvStore.set(kernelKey, setReachableAndVatSlot(false, vatSlot));
    if (
        isReachable &&
        type === 'object' &&
        !allocatedByVat &&
        refCountExistsForKerSlot(kernelSlot)
    ) {
        let { reachable, recognizable } = getReachCntRecCntForKerSlot(kernelSlot);
        reachable -= 1;
        setObjectRefCount(kernelSlot, { reachable, recognizable });
        if (reachable === 0) {
            addMaybeFreeKref(kernelSlot);
        }
    }
}

mapVatSlotToKernelSlotNoOpts(vatSlot) {
    { type, allocatedByVat } = readVatSlot(vatSlot);
    vatKey = `${vatID}.c.${vatSlot}`;
    if (!kvStore.has(vatKey)) {
        if (allocatedByVat) {
            let kernelSlot;
            if (type === 'object') {
                kernelSlot = createKernelObjectWithOwnerReachCntRecCnt(vatID);
            } else if (type === 'promise') {
                kernelSlot = addKernelPromiseForVat(vatID);
            }
            incrementRefCountExportTrueOnlyRecTrue(kernelSlot);
            kernelKey = `${vatID}.c.${kernelSlot}`;
            kvStore.set(kernelKey, setReachableAndVatSlot(false, vatSlot));
            kvStore.set(vatKey, kernelSlot);
        }
    }
    kernelSlot = readFromKVStore(vatKey);
    if (allocatedByVat) {
        setReachableFlag(kernelSlot);
    }
    return kernelSlot;
}
mapVatSlotToKernelSlotRequiredTrueSetReachableFalse(vatSlot) {
    { type, allocatedByVat } = readVatSlot(vatSlot);
    vatKey = `${vatID}.c.${vatSlot}`;
    // kvStore must have vatKey
    kernelSlot = readFromKVStore(vatKey);
    return kernelSlot;
}
mapKernelSlotToVatSlotNoOpts(kernelSlot) {
    kernelKey = `${vatID}.c.${kernelSlot}`;
    if (!kvStore.has(kernelKey)) {
        { type } = readKernelSlot(kernelSlot);
        incrementRefCountExportFalseOnlyRecTrue(kernelSlot);
        vatSlot = makeVatSlot(type, false, id);// write allocated = false, and type do memory
        vatKey = `${vatID}.c.${vatSlot}`;
        kvStore.set(vatKey, kernelSlot);
        kvStore.set(kernelKey, setReachableAndVatSlot(false, vatSlot));
    }
    { isReachable, vatSlot } = getReachableAndVatSlot(vatID, kernelSlot);
    { allocatedByVat } = readVatSlot(vatSlot);
    if (!allocatedByVat) {
        setReachableFlag(kernelSlot);
    }
    return vatSlot;
}

mapKernelSlotToVatSlotSetReachableFalseRequiredTrue(kernelSlot) {
    kernelKey = `${vatID}.c.${kernelSlot}`;
    // kvStore must have kerKey
    { isReachable, vatSlot } = getReachableAndVatSlot(vatID, kernelSlot);
    { allocatedByVat } = readVatSlot(vatSlot);
    return vatSlot;
}