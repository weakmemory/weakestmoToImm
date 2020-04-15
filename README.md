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

### Weakestmo to IMM compilation correctness. Main theorem and lemmas (§2.3)

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
  
### Basic definitions of event structure (§3)
* (§3.1) Events of event structures are encoded by `eventid` (which is equal to `nat`) defined in `src/model/EventStructure.v`.
* (§3.1) Labels (`label` in Coq) are defined in the IMM framework in file [`src/basic/Events.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/basic/Events.v).
* (§3.2) Event structures (`ES.t` in Coq) and the well-formedness predicate (`ES.Wf` in Coq) stating basic properties of their components
  are defined in `src/model/EventStructure.v`.
* (§3.3) A step of operational semantics of event structure construction (`step` in Coq) is defined in `src/construction/Step.v`.
* (§3.4) The Weakestmo event structure consistency predicate along with definitions of relations `hb` and `ecf` and the notion of visible events (predicate `vis` in Coq)
  are defined in `src/model/Consistency.v`.
  <br />
  (The consistency predicate is parameterized by `model` which is either `Weakest` or `Weakestmo`.
   The former represents a version of Weakestmo [Chakraborty-Vafeiadis:POPL19] which is not considered in our paper.)

A step of operational semantics of event structure construction (`step` in Coq) is defined in `src/construction/Step.v`.

used for event structures are defined in
  
### Representation of event structures and execution graphs

Events 



In footnote 11, we mention that events of execution graphs, unlike events used for event structures which are represented by natural numbers only,
have different representation in Coq.
In the representation, 
  
comparing 

TODO

In footnote 11, we mention that for a given execution graph `G` and an event structure `S` there exists an unique function `s2g(G, E) : S.E → G.E`,
which maps events of `S` to events of `G` /s.t./ events `es` and `s2g(G, E, es)` belong to the same thread
and have the same `po`-position in the thread of event structure `S` and execution graph `G` correspondigly.
It is the case for this Coq formalization since we use a representation of the execution graphs from the [IMM framework](https://github.com/weakmemory/imm)
(see also §2.2 of [[Podkopaev-al:POPL19]](https://dl.acm.org/doi/10.1145/3290382)).
In the representation, an execution graph event `eg` is encoded as a pair of natural numbers `<t, n>`, where `t` is the corresponding thread and
`n` is the position number of `eg` in the thread `t`.

TODO: address footnote 9.

## Description of the project's files

* `src/model` &mdash; definitions of the `Weakestmo` memory model.
  - *EventStructure.v* &mdash; definition of the `Weakestmo` event structure and related lemmas.
  - *Consistency.v* &mdash; definition of the consistency predicate and related lemmas.
  - *Execution.v* &mdash; definition of the `extracted` subset of events and related lemmas.

* `src/construction` &mdash; operational semantics of the `Weakestmo`.
  - *ProgES.v* &mdash; construction of the initial event structure.
  - *LblStep.v* &mdash; thread-local sequential semantics.
  - *BasicStep.v* &mdash; `basic_step` relation used to update set of events, program order and read-modify-write pairs of the event structure.
  - *AddJF.v* &mdash; `add_jf` relation used to update justified-from component of the event structure.
  - *AddEW.v* &mdash; `add_ew` relation used to equal-writes component of the event structure.
  - *AddCO.v* &mdash; `add_co` relation used to update coherence component of the event structure.
  - *Step.v* &mdash; `step_` and `step` relations used to update the event structure.
  - *StepWf.v* &mdash; preservation of the event structure's well-formedness property by the `step_` relation.

* `src/imm_aux` &mdash; auxiliary definition related to `IMM`.
  - *EventToAction.v* &mdash; definition of function `e2a`  which maps event structure events to events of execution graphs.
In the paper, its counterpart is `s2g` from §2.2.
  - *ImmProperties.v* &mdash; some auxiliary properties of the `IMM` model.

* `src/compilation` &mdash; proof of the compilation correctness to `IMM`.
  - *CertRF.v* &mdash; definition of `cert_rf` relation (a.k.a. `stable justification` relation).
  - *CertGraph.v* &mdash; construction of the certification branch.
  - *SimRelCont.v* &mdash; definition of the part of the simulation relation related to thread-local states.
  - *SimRelEventToAction.v* &mdash; definition of the part of the simulation relation which establish a connection between some components of the event structure and the execution graph.
  - *SimRel.v* &mdash; definition of the whole simulation relation.
  - *SimRelInit.v* &mdash; proof that the initial event structure satisfies the simulation relation.
  - *SimRelCert.v* &mdash; intermediate simulation relation which is preserved during the construction of the certification branch.
  - *SimRelCertBasicStep.v* &mdash; lemmas related to performing a basic step during the certification.
  - *SimRelCertAddJF.v* &mdash; lemmas related to updating justified-from component during the certification.
  - *SimRelCertAddEW.v* &mdash; lemmas related to updating equal-writes component during the certification.
  - *SimRelCertAddCO.v* &mdash; lemmas related to updating coherence order component during the certification.
  - *SimRelCertStep.v* &mdash; lemmas related to performing (whole) step during the certification.
  - *SimRelCertStepCoh.v* &mdash; proof that the event structure is consistent after a certification step.
  - *SimRelCertStepLemma.v* &mdash; proof that the event structure satisfies `simrel_cert` after a certification step.
  - *SimRelCertForwarding.v* &mdash; forwarding (i.e. an idle step) of the certification.
  - *SimRelStep.v* &mdash; simulation of the traversal step.
  - *Compilation.v* &mdash; proof of the main theorem.

* `src/utils` &mdash; auxiliary definitions and lemmas.

