# Weakestmo Memory Model and compilation correctness proofs for it

This repository contains Coq code supplementing the paper 
*Reconciling Event Structures with Modern Multiprocessors*
by Evgenii Moiseenko, Anton Podkopaev, Ori Lahav, Orestis Melkonian, and Viktor Vafeiadis.

## Building the Project

### Requirements
* [Coq 8.9.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [Utility library from the Promising semantics development](https://github.com/snu-sf/promising-lib) (`coq-promising-lib`)
* [Intermediate Memory Model](https://github.com/weakmemory/imm) (`coq-imm.1.1`)

All required dependencies can be installed via [`opam`](https://opam.ocaml.org/) package manager. 

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm.1.1
```

### Building Manually

To build the project just use `make -j` command (assuming all dependencies were installed as described above). 

## Relation between code and the paper 

### (§2.3) Weakestmo to IMM compilation correctness. Main theorem and lemmas

* The main theorem of compilation correctness from Weakestmo to IMM (**Theorem 1** from the paper) is represented
  by `compilation_correctness` stated in `src/compilation/Compilation.v`.
* The simulation relation `I` used to prove **Theorem 1** is represented by `simrel_consistent` in `src/compilation/SimRel.v`.
* **Lemma 2** stating that the simulation relation `I` holds for the initial event structure corresponds to 
  `simrel_init` in `src/compilation/SimRelInit.v`.
* **Lemma 3** stating that the simulation relation `I` might be restored after a traversal step is represented by
  `simrel_step` in `src/compilation/SimRelStep.v`.
* **Lemma 4** stating that **TODO**
<!-- from the simulation relation `I` holds for the initial event structure corresponds to  -->
  `simrel_extract` in `src/compilation/Compilation.v`.
  
### (§3) Basic definitions of event structure
* (**§3.1**) Events of event structures are encoded by `eventid` (which is equal to `nat`) defined in `src/model/EventStructure.v`.
  <br />
  Labels (`label` in Coq) are defined in the IMM framework in file [`src/basic/Events.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/basic/Events.v).
* (**§3.2**) Event structures (`ES.t` in Coq) and the well-formedness predicate (`ES.Wf` in Coq) stating basic properties of their components
  are defined in `src/model/EventStructure.v`.
* (**§3.3**) A step of operational semantics of event structure construction (`step` in Coq) is defined in `src/construction/Step.v`.
* (**§3.4**) The Weakestmo event structure consistency predicate along with definitions of relations `hb` and `ecf` and the notion of visible events (predicate `vis` in Coq)
  are defined in `src/model/Consistency.v`.
  <br />
  (The consistency predicate is parameterized by `model` which is either `Weakest` or `Weakestmo`.
   The former represents a version of Weakestmo [Chakraborty-Vafeiadis:POPL19] which is not considered in our paper.)
* (**§3.5**)
  The notion of *execution graph* (**Definition 6**, `execution` in Coq)
  is defined in the IMM framework in file [`src/basic/Execution.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/basic/Execution.v).
  Unlike the paper representation, it is not defined as a special case of event structures.
  Moreover, as mentioned in footnote 11, execution graphs are defined with another type of events
  (`actid` in Coq, file [`src/basic/Events.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/basic/Events.v) in the IMM framework).
  <br />
  The notion of a subset of events *extracted from* an event structure (**Definition 7**, `Execution.t` in Coq) is defined in `src/model/Execution.v`.
  <br />
  The notion of a execution graph *associated with* an extracted subset (`simrel_extract` in Coq) is defined in `src/compilation/Compilation.v`.

### (§4.2) Simulation relation `I`
* Function `s2g(G, S)` from the paper (which maps events of event structure `S` to events of execution graph `G`)
  is represented by function `e2a` (stands for *'`eventid` to `actid`'*) defined in `src/imm_aux/EventToAction.v`.
* In Coq, functions `⌈⌈·⌉⌉` and `⌊⌊·⌋⌋` for lifting `s2g` to sets are represented as `e2a □₁ ·` and `e2a ⋄₁ ·` correspondingly;
  their relational counterparts—`e2a □ ·` and `e2a ⋄ ·`.
* The simulation relation `I` is represented by `simrel_consistent` in `src/compilation/SimRel.v`.
	

TODO: address footnote 9.

## Description of the project's files

* `src/model` — definitions of the `Weakestmo` memory model.
  - *EventStructure.v* — definition of the `Weakestmo` event structure and related lemmas.
  - *Consistency.v* — definition of the consistency predicate and related lemmas.
  - *Execution.v* — definition of the `extracted` subset of events and related lemmas.

* `src/construction` — operational semantics of the `Weakestmo`.
  - *ProgES.v* — construction of the initial event structure.
  - *LblStep.v* — thread-local sequential semantics.
  - *BasicStep.v* — `basic_step` relation used to update set of events, program order and read-modify-write pairs of the event structure.
  - *AddJF.v* — `add_jf` relation used to update justified-from component of the event structure.
  - *AddEW.v* — `add_ew` relation used to equal-writes component of the event structure.
  - *AddCO.v* — `add_co` relation used to update coherence component of the event structure.
  - *Step.v* — `step_` and `step` relations used to update the event structure.
  - *StepWf.v* — preservation of the event structure's well-formedness property by the `step_` relation.

* `src/imm_aux` — auxiliary definition related to `IMM`.
  - *EventToAction.v* — definition of function `e2a`  which maps event structure events to events of execution graphs.
In the paper, its counterpart is `s2g` from §2.2.
  - *ImmProperties.v* — some auxiliary properties of the `IMM` model.

* `src/compilation` — proof of the compilation correctness to `IMM`.
  - *CertRF.v* — definition of `cert_rf` relation (a.k.a. `stable justification` relation).
  - *CertGraph.v* — construction of the certification branch.
  - *SimRelCont.v* — definition of the part of the simulation relation related to thread-local states.
  - *SimRelEventToAction.v* — definition of the part of the simulation relation which establish a connection between some components of the event structure and the execution graph.
  - *SimRel.v* — definition of the whole simulation relation.
  - *SimRelInit.v* — proof that the initial event structure satisfies the simulation relation.
  - *SimRelCert.v* — intermediate simulation relation which is preserved during the construction of the certification branch.
  - *SimRelCertBasicStep.v* — lemmas related to performing a basic step during the certification.
  - *SimRelCertAddJF.v* — lemmas related to updating justified-from component during the certification.
  - *SimRelCertAddEW.v* — lemmas related to updating equal-writes component during the certification.
  - *SimRelCertAddCO.v* — lemmas related to updating coherence order component during the certification.
  - *SimRelCertStep.v* — lemmas related to performing (whole) step during the certification.
  - *SimRelCertStepCoh.v* — proof that the event structure is consistent after a certification step.
  - *SimRelCertStepLemma.v* — proof that the event structure satisfies `simrel_cert` after a certification step.
  - *SimRelCertForwarding.v* — forwarding (i.e. an idle step) of the certification.
  - *SimRelStep.v* — simulation of the traversal step.
  - *Compilation.v* — proof of the main theorem.

* `src/utils` — auxiliary definitions and lemmas.

