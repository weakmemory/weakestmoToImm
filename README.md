# Weakestmo Memory Model and compilation correctness proofs for it

This repository contains Coq code supplementing the paper 
*Reconciling Event Structures with Modern Multiprocessors*
by Evgenii Moiseenko, Anton Podkopaev, Ori Lahav, Orestis Melkonian, and Viktor Vafeiadis.

## Building the Project

### Requirements
* [Coq 8.9.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [Utility library from the Promising semantics development](https://github.com/snu-sf/promising-lib)(`coq-promising-lib`)
* [Intermediate Memory Model](https://github.com/weakmemory/imm)(`coq-imm`)

All required dependencies can be installed via [`opam`](https://opam.ocaml.org/) package manager. 

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

### Building Manually

To build the project just use `make` command (assuming all dependencies were installed as described above). 

## Description of the project's files

* `src/model` --- definitions of the `Weakestmo` memory model.
  - *EventStructure.v* --- definition of the `Weakestmo` event structure and related lemmas.
  - *Consistency.v* --- definition of the consistency predicate and related lemmas.
  - *Execution.v* --- definition of the `extracted` subset of events and related lemmas.

* `src/construction` --- operational semantics of the `Weakestmo`.
  - *ProgES.v* --- construction of the initial event structure for a program.
  - *LblStep.v* --- thread-local sequential semantics, generating labels of events.
  - *BasicStep.v* --- `basic_step` relation, updating set of events, program order and read-modify-write pairs of an event structure.
  - *AddJF.v* --- `add_jf` relation, updating justified-from component of an event structure.
  - *AddEW.v* --- `add_ew` relation, updating equal-writes component of an event structure.
  - *AddCO.v* --- `add_co` relation, updating coherence component of an event structure.
  - *Step.v* --- `step_` and `step` relations, updating whole event structure.
  - *StepWf.v* --- preservation of the event structure's well-formdness property by `step_` relation.

* `src/imm_aux` --- auxiliary definition related to `IMM`.
  - *EventToAction.v* --- definition of the function, relating events in the event structure and execution graph.
  - *ImmProperties.v* --- some auxiliary properties of `IMM` model.

* `src/compilation` --- proof of compilation correctness to `IMM`.
  - *CertRF.v* --- definition of `cert_rf` relation.
  - *CertGraph.v* --- construction of the certification branch.
  - *SimRelCont.v* --- part of simulation relation, related to thread states stored in the event structure.
  - *SimRelEventToAction.v* --- part of simulation relation, relating some components of the event structure and the execution graph.
  - *SimRel.v* --- whole simulation relation.
  - *SimRelInit.v* --- proof that the initial event structure satisfies simulation relation.
  - *SimRelCert.v* --- intermediate simulation relation, preserved during the construction of certification branch.
  - *SimRelCertBasicStep.v* --- lemmas related to performing a basic step during certification.
  - *SimRelCertAddJF.v* --- lemmas related to updating justified-from during certification.
  - *SimRelCertAddEW.v* --- lemmas related to updating equal-writes during certification.
  - *SimRelCertAddCO.v* --- lemmas related to updating coherence order during certification.
  - *SimRelCertStep.v* --- lemmas related to performing (whole) step during certification.
  - *SimRelCertStepCoh.v* --- proof that the event structure is consistent after a certification step.
  - *SimRelCertStepLemma.v* --- proof that the event structure satisfies `simrel_cert` after a certification step.
  - *SimRelCertForwarding.v* --- performing forwarding (i.e. no step) during certification.
  - *SimRelStep.v* --- simulation of the traversal step.
  - *Compilation.v* --- proof of the main theorem.

* `src/utils` --- auxiliary definitions and lemmas.
