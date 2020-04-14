# Weakestmo Memory Model and compilation correctness proofs for it

This repository contains Coq code supplementing the paper 
*Reconciling Event Structures with Modern Multiprocessors*
by Evgenii Moiseenko, Anton Podkopaev, Ori Lahav, Orestis Melkonian, and Viktor Vafeiadis.

## Building the Project

### Requirements
* [Coq 8.9.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [Utility library from the Promising semantics development](https://github.com/snu-sf/promising-lib)(`coq-promising-lib`)
* [Intermediate Memory Model](https://github.com/weakmemory/imm)(`coq-imm.1.1`)

All required dependencies can be installed via [`opam`](https://opam.ocaml.org/) package manager. 

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm.1.1
```

### Building Manually

To build the project just use `make -j` command (assuming all dependencies were installed as described above). 

## Description of the project's files

* `src/model` --- definitions of the `Weakestmo` memory model.
  - *EventStructure.v* --- definition of the `Weakestmo` event structure and related lemmas.
  - *Consistency.v* --- definition of the consistency predicate and related lemmas.
  - *Execution.v* --- definition of the `extracted` subset of events and related lemmas.

* `src/construction` --- operational semantics of the `Weakestmo`.
  - *ProgES.v* --- construction of the initial event structure.
  - *LblStep.v* --- thread-local sequential semantics.
  - *BasicStep.v* --- `basic_step` relation used to update set of events, program order and read-modify-write pairs of the event structure.
  - *AddJF.v* --- `add_jf` relation used to update justified-from component of the event structure.
  - *AddEW.v* --- `add_ew` relation used to equal-writes component of the event structure.
  - *AddCO.v* --- `add_co` relation used to update coherence component of the event structure.
  - *Step.v* --- `step_` and `step` relations used to update the event structure.
  - *StepWf.v* --- preservation of the event structure's well-formdness property by the `step_` relation.

* `src/imm_aux` --- auxiliary definition related to `IMM`.
  - *EventToAction.v* --- definition of the function which establish a connection between events of the event structure and the execution graph.
  - *ImmProperties.v* --- some auxiliary properties of the `IMM` model.

* `src/compilation` --- proof of the compilation correctness to `IMM`.
  - *CertRF.v* --- definition of `cert_rf` relation (a.k.a. `stable justification` relation).
  - *CertGraph.v* --- construction of the certification branch.
  - *SimRelCont.v* --- definition of the part of the simulation relation related to thread-local states.
  - *SimRelEventToAction.v* --- definition of the part of the simulation relation which establish a connection between some components of the event structure and the execution graph.
  - *SimRel.v* --- definition of the whole simulation relation.
  - *SimRelInit.v* --- proof that the initial event structure satisfies the simulation relation.
  - *SimRelCert.v* --- intermediate simulation relation which is preserved during the construction of the certification branch.
  - *SimRelCertBasicStep.v* --- lemmas related to performing a basic step during the certification.
  - *SimRelCertAddJF.v* --- lemmas related to updating justified-from component during the certification.
  - *SimRelCertAddEW.v* --- lemmas related to updating equal-writes component during the certification.
  - *SimRelCertAddCO.v* --- lemmas related to updating coherence order component during the certification.
  - *SimRelCertStep.v* --- lemmas related to performing (whole) step during the certification.
  - *SimRelCertStepCoh.v* --- proof that the event structure is consistent after a certification step.
  - *SimRelCertStepLemma.v* --- proof that the event structure satisfies `simrel_cert` after a certification step.
  - *SimRelCertForwarding.v* --- forwarding (i.e. an idle step) of the certification.
  - *SimRelStep.v* --- simulation of the traversal step.
  - *Compilation.v* --- proof of the main theorem.

* `src/utils` --- auxiliary definitions and lemmas.
