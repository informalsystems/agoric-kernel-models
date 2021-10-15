These notes show a representation of what is happening in the source code
(More or less complete)

```
nextGcAction(){
    for each vat (non deterministic order)
        in priority order, foreach, dropExport > retireExport > retireImport
            filter out invalid action
            if there's a valid one, return it
        
    isValid():
        dropExport
            reachableFlag set
            reachable 0
            kernel obj
            clist for vat
        retireExport
            reachable 0
            recognizable 0
            kernel obj
            clist for vat
        retireImport
            clist for vat 
}


dropImportSyscall() {
    assert kref in clist
    set reachableFlag false
    if reachableFlag WAS true, and kernel obj exists
        reachable -= 1
        if reachable 0
            enable maybeFreeKRef
}
retireImportSyscall() {
    assert kref in clist
    assert reachableFlag not set
    if kernel obj
        recognizable -= 1
        if recognizable 0 OR reach 0
            enable maybeFreeKRef
    delete clist for vat
}
dropThenRetireImportSyscall() {
    assert kref in clist
    set reachableFlag false
    if reachableFlag WAS true and kernel obj
        reachable -= 1
    if kernel obj
        recognizable -= 1
        if recognizable 0 or reach 0
            enable maybeFreeKRef
    delete clist for vat
}
retireExportSyscall() {
    assert reachableFlag not set
    add retireImport to gcActions
    delete kernel obj
    delete clist for vat
}

while nextGCActionOrNextMessage(){

    if dropExport action
        clear reachableFlag for vat
        clear exportedRemotable (inside vat)
    if retireExport action
        clear reachableFlag for vat
        delete kernel obj
        delete clist for vat
        (inside vat: liveSlots will clear out slot to val)
    if retireImport action
        clear reachableFlag for vat
        recognizable -= 1
        if reachable 0 OR recognizable 0
            enable maybeFreeKref
        delete clist for vat
        (code does nothing in liveslots but maybe it should)

    maybe do dropImport syscall
    maybe do dropImport and then retireImport syscall
    maybe do retireExport syscall

    if maybeFreeKRef and reachable 0
        if exporter has reachableFlag
            add dropExport to gcActions
        if recognizable 0
            add retireExport to gcActions
    clear maybeFreeKRef

}
```

