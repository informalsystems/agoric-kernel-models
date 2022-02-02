package systems.informal.agoric;

import lombok.AllArgsConstructor;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

public class Kernel {
    enum Nature {
        retireExports,
        retireImports,
        dropExports,
        unresolved,
        fulfilled,
        rejected,
        DELETED,
        promise,
        object,
        notify,
        send,
    }

    class Msg {
        List<Integer> slotsInArgs;
        Integer resultPKSlot;
        Integer resultPVSlot;
    }

    class QEntry {
        Nature nature;
        Msg mForSend;
        Integer targetKSlotForSend;
        List<Integer> kSlotsForGc;
        Integer targetVatIdForGcOrNotify;
        Integer kSlotOfNotifyPromise;
    }

    // Can represent a resolution sent by vat (vresolution) or one from kernel perspective (kresolution)
    class VResolution {
        Integer vpSlot;
        boolean rejected;
        List<Integer> dataVSlots;
    }

    class KThing {
        List<Msg> q;
        Nature nature;
        Integer owner;
        Nature status;
        Integer decider;
        Integer refCount;
        Integer reachableCnt;
        Integer recognizableCnt;
        List<Integer> importers;
        List<Integer> dataSlots;
        List<Integer> subscribers;
    }

    class GcAction {
        Nature nature;
        Integer kSlot;
        Integer targetVatId;
    }

    Queue<QEntry> runQueue = new LinkedList();
    Map<Integer, KThing> kThings = new HashMap();
    Map<Integer, Boolean> pipeliningEnabledForVatWithId = new HashMap();
    Set<GcAction> gcActions = new HashSet<>();
    Set<Integer> kSlotsToMaybeFree = new HashSet<>();
    Integer nextKThingId = 0;
    Integer nextVSlotId = 0;

    @AllArgsConstructor
    class VatIdAndVSlot {
        Integer vatId;
        Integer vSlot;
    }

    @AllArgsConstructor
    class VatIdAndKSlot {
        Integer vatId;
        Integer kSlot;
    }

    Map<VatIdAndKSlot, Boolean> vatIdAndKSlotToIsReachable = new HashMap<>();
    Map<VatIdAndKSlot, Integer> vatIdAndKSlotToVSlot = new HashMap<>();
    Map<VatIdAndVSlot, Integer> vatIdAndVSlotToKSlot = new HashMap<>();
    Map<VatIdAndVSlot, Boolean> vatIdAndVSlotToAllocatedByVat = new HashMap<>();
    Map<VatIdAndVSlot, Nature> vatIdAndVSlotToType = new HashMap<>();


    void mainLoop() {
        while (true) {
            QEntry e = processNextGCAction();
            if (e != null) {
                for (Integer kSlot : e.kSlotsForGc) {
                    if (e.nature == Nature.dropExports) {
                        vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(e.targetVatIdForGcOrNotify, kSlot), false);
                    }
                    if (e.nature == Nature.retireExports) {
                        // TODO I'm not sure if here I should delete more things or just the relevant parts
                        KThing t = kThings.get(kSlot);
                        t.owner = null;
                        // delete semantic refCount
                        Integer vSlot = vatIdAndKSlotToVSlot.get(new VatIdAndKSlot(e.targetVatIdForGcOrNotify, kSlot));
                        physicallyRemoveMappingsAndReachable(e.targetVatIdForGcOrNotify, vSlot, kSlot);
                    }
                    if (e.nature == Nature.retireImports) {
                        KThing t = kThings.get(kSlot);
                        if (t.nature == Nature.object) {
                            if (vatIdAndKSlotToIsReachable.get(new VatIdAndKSlot(e.targetVatIdForGcOrNotify, kSlot))) {
                                t.reachableCnt -= 1;
                            }
                            t.recognizableCnt--;
                            if (t.reachableCnt == 0 || t.recognizableCnt == 0) {
                                kSlotsToMaybeFree.add(kSlot);
                            }
                        }
                        if (t.nature == Nature.promise) {
                            t.refCount--;
                            if (t.refCount == 0) {
                                kSlotsToMaybeFree.add(kSlot);
                            }
                        }
                        Integer vSlot = vatIdAndKSlotToVSlot.get(new VatIdAndKSlot(e.targetVatIdForGcOrNotify, kSlot));
                        physicallyRemoveMappingsAndReachable(e.targetVatIdForGcOrNotify, vSlot, kSlot);
                    }
                }
                // The actual delivery happens here but we don't model it
                processKSlotsToMaybeFreeAndAddGcActionsToSet();
            } else if (!runQueue.isEmpty()) {
                e = runQueue.poll();
                if (e.nature == Nature.send) {
                    decrementRefCounts(e.targetKSlotForSend);
                    if (e.mForSend.resultPKSlot != null) {
                        kThings.get(e.mForSend.resultPKSlot).refCount--;
                        if (kThings.get(e.mForSend.resultPKSlot).refCount == 0) {
                            kSlotsToMaybeFree.add(e.mForSend.resultPKSlot);
                        }
                    }
                    e.mForSend.slotsInArgs.forEach(it -> decrementRefCounts(it));
                    deliverMsgToTarget(e.targetKSlotForSend, e.mForSend);
                } else if (e.nature == Nature.notify) {
                    kThings.get(e.kSlotOfNotifyPromise).refCount--;
                    if (kThings.get(e.kSlotOfNotifyPromise).refCount == 0) {
                        kSlotsToMaybeFree.add(e.kSlotOfNotifyPromise);
                    }
                    List<Integer> promiseDataSlots = kThings.get(e.kSlotOfNotifyPromise).dataSlots;
                    if (vatIdAndKSlotToVSlot.containsKey(new VatIdAndKSlot(e.targetVatIdForGcOrNotify, e.kSlotOfNotifyPromise))) {
                        // This inlines translation
                        for (Integer kpSlot : collectResolvedPromisesRecursivelyViaDataReferences(e.kSlotOfNotifyPromise, promiseDataSlots)) {
                            Integer vSlot = mapKSlotToVSlot(e.targetVatIdForGcOrNotify, kpSlot);
                            for (Integer dataKSlot : kThings.get(kpSlot).dataSlots) {
                                mapKSlotToVSlot(e.targetVatIdForGcOrNotify, dataKSlot);
                            }
                            kThings.get(kpSlot).refCount--;
                            if (kThings.get(kpSlot).refCount == 0) {
                                kSlotsToMaybeFree.add(kpSlot);
                            }
                            physicallyRemoveMappingsAndReachable(e.targetVatIdForGcOrNotify, vSlot, kpSlot);
                        }
                        // delivery happens here but we don't model it
                    }
                }
                processKSlotsToMaybeFreeAndAddGcActionsToSet();
            } else {
                return;
            }
        }
    }

    QEntry processNextGCAction() {
        /* Logic for this is clear and doesn't need inlining right now*/
        return null;
    }

    void deliverMsgToTarget(int targetKSlot, Msg m) {
        KThing t = kThings.get(targetKSlot);
        if (t.nature == Nature.object) {
            // vatId must not be null (assume not crashed)
            // This inlines translation
            mapKSlotToVSlot(t.owner, targetKSlot);
            m.slotsInArgs.forEach(kSlot -> {
                mapKSlotToVSlot(t.owner, kSlot);
            });
            if (m.resultPKSlot != null) {
                mapKSlotToVSlot(t.owner, m.resultPKSlot);
                kThings.get(m.resultPKSlot).decider = t.owner;
            }
            // Actual delivery happens here but we don't model it
        }
        if (t.nature == Nature.promise && t.status == Nature.fulfilled) {
            // Check if resolved to a presence
            // I don't do the body checks here. is it still correct? (Probably not)
            if (t.dataSlots.size() == 1) {
                KThing thingInData = kThings.get(t.dataSlots.get(0));
                if (thingInData.nature == Nature.object) {
                    Integer kSlotOfPresence = t.dataSlots.get(0);
                    deliverMsgToTarget(kSlotOfPresence, m);
                    return;
                }
            }
            if (m.resultPKSlot != null) {
                queueNotifiesIntoRunQueue(m.resultPKSlot, kThings.get(m.resultPKSlot).subscribers);
                requeuePromiseQueueIntoRunQueue(m.resultPKSlot);
                resolveKPromise(m.resultPKSlot, true, null);
            }
        }
        if (t.nature == Nature.promise && t.status == Nature.rejected && m.resultPKSlot != null) {
            queueNotifiesIntoRunQueue(m.resultPKSlot, kThings.get(m.resultPKSlot).subscribers);
            requeuePromiseQueueIntoRunQueue(m.resultPKSlot);
            resolveKPromise(m.resultPKSlot, true, t.dataSlots);
        }
        if (t.nature == Nature.promise && t.status == Nature.unresolved) {
            if (t.decider != null && pipeliningEnabledForVatWithId.get(t.decider)) {
                // This inlines translation
                mapKSlotToVSlot(t.decider, targetKSlot);
                m.slotsInArgs.forEach(kSlot -> {
                    mapKSlotToVSlot(t.decider, kSlot);
                });
                if (m.resultPKSlot != null) {
                    mapKSlotToVSlot(t.decider, m.resultPKSlot);
                    kThings.get(m.resultPKSlot).decider = t.decider;
                }
                // Actual delivery happens here but we don't model it
            } else {
                t.refCount++;
                if (m.resultPKSlot != null) {
                    kThings.get(m.resultPKSlot).refCount++;
                }
                m.slotsInArgs.forEach(kSlotInArgs -> incrementRefCounts(kSlotInArgs));
                kThings.get(targetKSlot).q.add(m);
            }
        }
    }

    void translateAndExecuteSendSyscall(int callerVatId, int targetVSlot, Msg vMsg) {
        QEntry e = new QEntry();
        e.mForSend = new Msg();
        e.nature = Nature.send;
        e.targetKSlotForSend = mapVSlotToKSlot(callerVatId, targetVSlot);
        e.mForSend.resultPKSlot = null;
        vMsg.slotsInArgs.forEach(vSlotInArgs -> e.mForSend.slotsInArgs.add(mapVSlotToKSlot(callerVatId, vSlotInArgs)));
        if (vMsg.resultPVSlot != null) {
            e.mForSend.resultPKSlot = mapVSlotToKSlot(callerVatId, vMsg.resultPVSlot);
            kThings.get(e.mForSend.resultPKSlot).decider = null;
        }
        // TODO: in the code there is a weird passthrough of ...args which I haven't mimicked
        incrementRefCounts(e.targetKSlotForSend);
        if (e.mForSend.resultPKSlot != null) {
            kThings.get(e.mForSend.resultPKSlot).refCount++;
        }
        e.mForSend.slotsInArgs.forEach(kSlot -> incrementRefCounts(kSlot));
        runQueue.add(e);
    }

    void translateAndExecuteSubscribeSyscall(int callerVatId, int vpSlot) {
        Integer kpSlot = mapVSlotToKSlot(callerVatId, vpSlot);
        KThing p = kThings.get(kpSlot);
        if (p.status == Nature.unresolved) {
            kThings.get(kpSlot).subscribers.add(callerVatId);
        } else {
            QEntry e = new QEntry();
            e.nature = Nature.notify;
            e.kSlotOfNotifyPromise = kpSlot;
            e.targetVatIdForGcOrNotify = callerVatId;
            kThings.get(kpSlot).refCount++;
            runQueue.add(e);
        }
    }

    void translateAndExecuteResolveSyscall(int callerVatId, List<VResolution> vResolutions) {
        vResolutions.forEach(vres -> {
            Integer kpSlot = mapVSlotToKSlot(callerVatId, vres.vpSlot);
            List<Integer> kresDataKSlots = new ArrayList<>();
            vres.dataVSlots.forEach(vSlot -> kresDataKSlots.add(mapVSlotToKSlot(callerVatId, vSlot)));
            kThings.get(kpSlot).refCount--;
            if (kThings.get(kpSlot).refCount == 0) {
                kSlotsToMaybeFree.add(kpSlot);
            }
            physicallyRemoveMappingsAndReachable(callerVatId, vres.vpSlot, kpSlot);
            List<Integer> vatsToNotify = kThings.get(kpSlot)
                    .subscribers.stream()
                    .filter(s -> s != callerVatId)
                    .collect(Collectors.toList());
            queueNotifiesIntoRunQueue(kpSlot, vatsToNotify);
            requeuePromiseQueueIntoRunQueue(kpSlot);
            resolveKPromise(kpSlot, vres.rejected, kresDataKSlots);
        });

    }

    private void queueNotifiesIntoRunQueue(Integer kpSlot, List<Integer> vatsToNotify) {
        vatsToNotify.forEach(v -> {
            QEntry e = new QEntry();
            e.nature = Nature.notify;
            e.kSlotOfNotifyPromise = kpSlot;
            e.targetVatIdForGcOrNotify = v;
            kThings.get(kpSlot).refCount++;
            runQueue.add(e);
        });
    }

    void requeuePromiseQueueIntoRunQueue(Integer kpSlot) {
        KThing p = kThings.get(kpSlot);
        p.q.forEach(mInPromiseQueue -> {
            QEntry e = new QEntry();
            e.nature = Nature.send;
            e.targetKSlotForSend = kpSlot;
            e.mForSend = mInPromiseQueue;
            runQueue.add(e);
        });
    }

    void resolveKPromise(Integer kpSlot, boolean reject, List<Integer> dataSlots) {
        KThing p = kThings.get(kpSlot);
        p.q = new ArrayList<>();
        p.subscribers = null;
        p.decider = null;
        p.status = reject ? Nature.rejected : Nature.fulfilled;
        p.dataSlots = dataSlots;
        dataSlots.forEach(dataKSlot -> {
            incrementRefCounts(dataKSlot);
        });
    }

    void translateAndExecuteDropImportsSyscall(int callerVatId, List<Integer> vSlots) {
        vSlots.forEach(vSlot -> {
            int kSlot = vatIdAndVSlotToKSlot.get(new VatIdAndVSlot(callerVatId, vSlot));
            KThing t = kThings.get(kSlot);
            if (vatIdAndKSlotToIsReachable.get(new VatIdAndKSlot(callerVatId, kSlot))) {
                vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(callerVatId, kSlot), false);
                if (t.nature == Nature.object) {
                    t.reachableCnt -= 1;
                    if (t.reachableCnt == 0) {
                        kSlotsToMaybeFree.add(kSlot);
                    }
                }
            }
        });
    }

    void translateAndExecuteRetireImportsSyscall(int callerVatId, List<Integer> vSlots) {
        vSlots.forEach(vSlot -> {
            int kSlot = vatIdAndVSlotToKSlot.get(new VatIdAndVSlot(callerVatId, vSlot));
            // the code throws here if reachableFlag is set
            KThing t = kThings.get(kSlot);
            if (t.nature == Nature.promise) {
                t.refCount--;
                if (t.refCount == 0) {
                    kSlotsToMaybeFree.add(kSlot);
                }
            }
            if (t.nature == Nature.object) {
                if (vatIdAndKSlotToIsReachable.get(new VatIdAndKSlot(callerVatId, kSlot))) {
                    t.reachableCnt -= 1;
                }
                t.recognizableCnt--;
                if (t.reachableCnt == 0 || t.recognizableCnt == 0) {
                    kSlotsToMaybeFree.add(kSlot);
                }
            }
            physicallyRemoveMappingsAndReachable(callerVatId, vSlot, kSlot);
        });
    }

    void translateAndExecuteRetireExportsSyscall(int callerVatId, List<Integer> vSlots) {
        vSlots.forEach(vSlot -> {
            int kSlot = vatIdAndVSlotToKSlot.get(new VatIdAndVSlot(callerVatId, vSlot));
            KThing t = kThings.get(kSlot);
            if (t.nature == Nature.promise) {
                t.refCount--;
                if (t.refCount == 0) {
                    kSlotsToMaybeFree.add(kSlot);
                }
            }
            physicallyRemoveMappingsAndReachable(callerVatId, vSlot, kSlot);

            // Here I compressed the loop
            // In the code, the krefs are collected and then the below code is run in a separate loop
            // I don't think it makes a difference.

            kThings.get(kSlot).importers.forEach(vatId -> {
                GcAction a = new GcAction();
                a.kSlot = kSlot;
                a.nature = Nature.retireImports;
                a.targetVatId = vatId;
                gcActions.add(a);
            });

            // TODO I'm not sure if here I should delete the whole thing or just the relevant parts
            t.owner = null;
            // also delete refCount, reachableCnt, recognizableCnt
        });
    }

    void processKSlotsToMaybeFreeAndAddGcActionsToSet() {
        kSlotsToMaybeFree.forEach(kSlot -> {
            KThing t = kThings.get(kSlot);
            if (t.nature == Nature.promise) {
                if (t.refCount == 0) {
                    t.dataSlots.forEach(dataKSlot -> {
                        // "Note: the following decrement can result in an addition to the
                        // maybeFreeKrefs set, which we are in the midst of iterating.
                        // TC39 went to a lot of trouble to ensure that this is kosher."
                        decrementRefCounts(dataKSlot);
                    });
                    t.status = Nature.DELETED;
                    t.q = new ArrayList<>();
                    t.subscribers = null;
                    t.dataSlots = null;
                    t.decider = null;
                    t.refCount = null;
                }
            }
            if (t.nature == Nature.object && t.reachableCnt == 0 && t.owner != null) {
                if (vatIdAndKSlotToIsReachable.get(new VatIdAndKSlot(t.owner, kSlot))) {
                    GcAction a = new GcAction();
                    a.nature = Nature.dropExports;
                    a.targetVatId = t.owner;
                    a.kSlot = kSlot;
                    gcActions.add(a);
                }
                if (t.recognizableCnt == 0) {
                    GcAction a = new GcAction();
                    a.nature = Nature.retireExports;
                    a.targetVatId = t.owner;
                    a.kSlot = kSlot;
                    gcActions.add(a);
                }
            }
        });
        kSlotsToMaybeFree.clear();
    }

    static class Recursive<F> {
        F fun;
    }

    Set<Integer> collectResolvedPromisesRecursivelyViaDataReferences(int rootKPSlot, List<Integer> rootDataKSlots) {

        Recursive<BiConsumer<Integer, List<Integer>>> f =
                new Recursive<>();

        Set<Integer> seen = new HashSet<>();
        f.fun = (kpSlot, dataKSlots) -> {
            seen.add(kpSlot);
            if (dataKSlots != null) {
                dataKSlots.forEach(dataKSlot -> {
                    KThing t = kThings.get(dataKSlot);
                    if (t.nature == Nature.promise) {
                        if (!seen.contains(dataKSlot)) {
                            if (t.status != Nature.unresolved) {
                                f.fun.accept(dataKSlot, t.dataSlots);
                            }
                        }
                    }
                });
            }
        };

        f.fun.accept(rootKPSlot, rootDataKSlots);

        return seen;
    }

    void incrementRefCounts(int kSlot) {
        KThing t = kThings.get(kSlot);
        if (t.nature == Nature.promise) {
            t.refCount++;
        }
        if (t.nature == Nature.object) {
            t.reachableCnt++;
            t.recognizableCnt++;
        }
    }

    void decrementRefCounts(int kSlot) {
        KThing t = kThings.get(kSlot);
        if (t.nature == Nature.promise) {
            t.refCount--;
            if (t.refCount == 0) {
                kSlotsToMaybeFree.add(kSlot);
            }
        }
        if (t.nature == Nature.object) {
            t.reachableCnt--;
            t.recognizableCnt--;
            if (t.reachableCnt == 0 || t.recognizableCnt == 0) {
                kSlotsToMaybeFree.add(kSlot);
            }
        }
    }

    Integer mapVSlotToKSlot(int vatId, int vSlot) {
        if (!vatIdAndVSlotToKSlot.containsKey(new VatIdAndVSlot(vatId, vSlot))) {
            Integer kSlot = nextKThingId;
            nextKThingId++;
            KThing t = new KThing();
            if (vatIdAndVSlotToType.get(new VatIdAndVSlot(vatId, vSlot)) == Nature.object) {
                t.owner = vatId;
                t.reachableCnt = 0;
                t.recognizableCnt = 0;
            } else if (vatIdAndVSlotToType.get(new VatIdAndVSlot(vatId, vSlot)) == Nature.promise) {
                t.subscribers = new ArrayList<>();
                t.dataSlots = new ArrayList<>();
                t.refCount = 1;
                t.status = Nature.unresolved;
                t.decider = vatId;
            }
            kThings.put(kSlot, t);
            vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(vatId, kSlot), false);
            vatIdAndKSlotToVSlot.put(new VatIdAndKSlot(vatId, kSlot), vSlot);
            vatIdAndVSlotToKSlot.put(new VatIdAndVSlot(vatId, vSlot), kSlot);
        }
        Integer kSlot = vatIdAndVSlotToKSlot.get(new VatIdAndVSlot(vatId, vSlot));
        if (vatIdAndVSlotToAllocatedByVat.get(new VatIdAndVSlot(vatId, vSlot))) {
            vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(vatId, kSlot), true);
        }
        return kSlot;
    }

    Integer mapKSlotToVSlot(int vatId, int kSlot) {
        if (!vatIdAndKSlotToVSlot.containsKey(new VatIdAndKSlot(vatId, kSlot))) {
            KThing t = kThings.get(kSlot);
            Integer vSlot = nextVSlotId;
            nextVSlotId++;
            if (t.nature == Nature.object) {
                t.recognizableCnt++;
            }
            if (t.nature == Nature.promise) {
                t.refCount++;
            }
            vatIdAndVSlotToAllocatedByVat.put(new VatIdAndVSlot(vatId, vSlot), false);
            vatIdAndVSlotToType.put(new VatIdAndVSlot(vatId, vSlot), t.nature);
            vatIdAndVSlotToKSlot.put(new VatIdAndVSlot(vatId, vSlot), kSlot);
            vatIdAndKSlotToVSlot.put(new VatIdAndKSlot(vatId, kSlot), vSlot);
            vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(vatId, kSlot), false);
        }
        Integer vSlot = vatIdAndKSlotToVSlot.get(new VatIdAndKSlot(vatId, kSlot));
        if (!vatIdAndVSlotToAllocatedByVat.get(new VatIdAndVSlot(vatId, vSlot))) {
            if (!vatIdAndKSlotToIsReachable.get(new VatIdAndKSlot(vatId, kSlot))) {
                vatIdAndKSlotToIsReachable.put(new VatIdAndKSlot(vatId, kSlot), true);
                if (kThings.get(kSlot).nature == Nature.object) {
                    kThings.get(kSlot).reachableCnt += 1;
                }
            }
        }
        return vSlot;
    }

    void physicallyRemoveMappingsAndReachable(Integer vatId, Integer vSlot, Integer kSlot) {
        vatIdAndVSlotToKSlot.remove(new VatIdAndVSlot(vatId, vSlot));
        vatIdAndKSlotToVSlot.remove(new VatIdAndKSlot(vatId, kSlot));
        vatIdAndKSlotToIsReachable.remove(new VatIdAndKSlot(vatId, kSlot));
        //TODO: I'm pretty sure this is correct and that I should not remove 'type' or 'allocatedByVat' too
    }


}
