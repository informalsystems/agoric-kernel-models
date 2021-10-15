# TLA+ models for Agoric Swingset Kernel

This repository contains TLA+ models of the [Agoric SwingSet kernel](https://github.com/Agoric/agoric-sdk/tree/master/packages/SwingSet/src/kernel).


The models are being constructed in the scope of [audit & verification services](https://informal.systems/services/security-audits)
provided by [Informal Systems](https://informal.systems)
to [Agoric](https://agoric.com).

The current set of models include:
 - [Model for object and promise management in the kernel](./kernel/kernel.tla)
 - [Model of the userspace VAT interactions via kernel](./userspace/userspace.tla)
 - [Model of garbage collection in the kernel](./kernel_gc/kernel_gc.tla)

