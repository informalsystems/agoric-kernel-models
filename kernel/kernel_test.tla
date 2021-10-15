------------------------------------ MODULE kernel_test -----------------------------
(*
  The model of the Agoric SwingSet kernel.
  (https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel)

  For the main model file please see kernel.tla.
  This file defines unit tests for the model.

  The model has been constructed in the scope of audit & verification services
  provided by Informal Systems (https://informal.systems)
  to Agoric (https://agoric.com).

  In case of any questions please feel free to contact
  Andrey Kuprianov <andrey@informal.systems>

  v.1.0
  07.07.2021
*)

EXTENDS kernel_exec

TestCreateUnknownVatCInit == CInit
TestCreateUnknownVatBefore ==
  InitDefaultsExcept([
    vats |-> [ id \in {"a", "b"} |-> NEW_VAT(FALSE)]
  ])
TestCreateUnknownVatAction == CreateVatAction("c", TRUE)
TestCreateUnknownVatAssert ==
  /\ "c" \in DOMAIN vats
  /\ "c" \in DOMAIN vatToKernel
  /\ "c" \in DOMAIN kernelToVat


TestCreateKnownVatCInit == CInit
TestCreateKnownVatBefore ==
  InitDefaultsExcept([
    vats |-> [ id \in {"a", "b"} |-> NEW_VAT(FALSE)]
  ])
TestCreateKnownVatAction == CreateVatAction("a", TRUE)
TestCreateKnownVatAssert ==
  /\ error = "CreateVat"

TestExportPreCInit == CInit
TestExportPreBefore == DefaultInit
TestExportPreAction == ExportStep
TestExportPreAssert ==
  LET vatID == action.vatID
      vatSlot == action.vatSlot IN
  \/ error = NULL 
  \/ UnknownVat(vatID)
  \/ vatSlot.exported = FALSE
  \/ vatSlot.type = VAT_DEVICE
  \/ vatSlot \in DOMAIN vatToKernel[vatID]

TestExportCInit == CInit
TestExportBefore == DefaultInit
TestExportAction == ExportStep
TestExportAssert ==
  LET vatID == action.vatID
      vatSlot == action.vatSlot IN
  \/ error /= NULL 
  \/ \E kernelSlot \in KERNEL_SLOTS: 
        /\ vatToKernel[vatID][vatSlot] = kernelSlot
        /\ kernelToVat[vatID][kernelSlot] = vatSlot
        /\ kernelSlot \in vatReachSlots[vatID]
        /\ \/ (vatSlot.type = VAT_OBJECT /\ kernelSlot.type = KERNEL_OBJECT
               /\ kernelObjects[kernelSlot] = NEW_OBJECT(vatID))
           \/ (vatSlot.type = VAT_PROMISE /\ kernelSlot.type = KERNEL_PROMISE 
               /\ kernelPromises[kernelSlot] = NEW_PROMISE(vatID))


TestImportPreCInit == CInit
TestImportPreBefore == DefaultInit
TestImportPreAction == ImportStep
TestImportPreAssert ==
  LET vatID == action.vatID
      kernelSlot == action.kernelSlot IN
  \/ error = NULL 
  \/ UnknownVat(vatID)
  \/ kernelSlot.type = KERNEL_DEVICE
  \/ kernelSlot \in DOMAIN kernelToVat[vatID]


\* The tests below are trivial, and serve only to check 
\* that all variables are updated appropriately

TestTerminateVatPreCInit == CInit
TestTerminateVatPreBefore == DefaultInit
TestTerminateVatPreAction == TerminateVatStep
TestTerminateVatPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestSendPreCInit == CInit
TestSendPreBefore == DefaultInit
TestSendPreAction == SendStep
TestSendPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 


TestProcessNotifyPreCInit == CInit
TestProcessNotifyPreBefore == DefaultInit
TestProcessNotifyPreAction == ProcessNotifyStep
TestProcessNotifyPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestDeliverToTargetPreCInit == CInit
TestDeliverToTargetPreBefore == DefaultInit
TestDeliverToTargetPreAction == DeliverToTargetStep
TestDeliverToTargetPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestDeliverToVatPreCInit == CInit
TestDeliverToVatPreBefore == DefaultInit
TestDeliverToVatPreAction == DeliverToVatStep
TestDeliverToVatPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestExitPreCInit == CInit
TestExitPreBefore == DefaultInit
TestExitPreAction == ExitStep
TestExitPreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestSubscribePreCInit == CInit
TestSubscribePreBefore == DefaultInit
TestSubscribePreAction == SubscribeStep
TestSubscribePreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

TestProcessQueueMessagePreCInit == CInit
TestProcessQueueMessagePreBefore == DefaultInit
TestProcessQueueMessagePreAction == ProcessQueueMessageStep
TestProcessQueueMessagePreAssert ==
  \/ error = NULL 
  \/ error /= NULL 

===============================================================================

