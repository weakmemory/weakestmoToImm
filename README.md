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

All required dependencies can be installed via package manager [`opam`](https://opam.ocaml.org/). 

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
* **Lemma 3** stating that the simulation relation `I` can be restored after a traversal step is represented by
  `simrel_step` in `src/compilation/SimRelStep.v`.
* **Lemma 4** stating that if `I` holds for the final traversal configuration 
  then the graph associated with the extracted subset `X` is isomorphic to the original IMM graph `G` 
  is represented by `simrel_extract` in `src/compilation/Compilation.v`
  
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
  <br />
  In footnote 9, we mention that our Coq formalization uses another definition of visible events (predicate `vis` in Coq) comparing
  to the one in [Chakraborty-Vafeiadis:POPL19].
  Their equivalence is stated by lemma `cc_alt` in `src/model/Consistency.v`.
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

The simulation relation `I` is represented by `simrel_consistent` in `src/compilation/SimRel.v`.
Below, we map elements of the paper's version of `I` to the Coq version.
Most of them are represented by fields in `simrel` or derivable from them:

1. `gcons` (a field in `simrel`).
2. `SCONS` (an entry in `simrel_consistent`).
3. `sr_exec` (a field in `simrel`).
4. `ex_cov_iss` (a field in `simrel`).
5. **(a)** Equality of events' threads and labels up to values for events connected via `e2a` 
   is represented by `sr_e2a` (a field in `simrel`).
   It uses auxiliary definition `simrel_e2a` defined in `src/compilation/SimRelEventToAction.v`.
   <br />
   **(b)** Equality of labels for events and their covered and issued counterparts is represented by `ex_cov_iss_lab` (a field in `simrel`).
6. Derivable from `sr_e2a` via lemma `e2a_sb` stated in `src/imm_aux/EventToAction.v`.
7. Derivable from `sr_e2a` via lemma `e2a_eq_in_cf` stated in `src/imm_aux/EventToAction.v`.
8. **(a)** Field `e2a_jf` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `src/compilation/SimRelEventToAction.v`.
   <br />
   **(b)** Lemma `jf_cov_iv_rf` stated in `src/compilation/SimRel.v` derivable from `jf_ex_in_cert_rf` (a field in `simrel`).
9. `jfe_ex_iss` (a field in `simrel`).
10. Field `e2a_ew` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `src/compilation/SimRelEventToAction.v`.
11. `ew_ex_iss` (a field in `simrel`).
12. Field `e2a_co` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `src/compilation/SimRelEventToAction.v`.

### (§4.3) Simulation step

In our proof, we show that **Lemma 3**, the simulation step (in Coq, `simrel_step` in `src/compilation/SimRelStep.v`),
holds by doing induction on a certification run.
During the induction, we preserve predicate `simrel_cert` defined in `src/compilation/SimRelCert.v`.

* (**§4.3.1**) The `determined` set  (`D` in Coq), relations `vf` and `sjf` (`cert_rf` in Coq) are defined in `src/compilation/CertRf.v`.
  <br />
  The certification run is defined via predicate `cert_graph` and constructed via lemma `cert_graph_start` in `src/compilation/CertGraph.v`.
  <br />
  The proof of `cert_graph_start` uses the receptiveness property (`receptiveness_full` in Coq, defined in file `Receptiveness.v` of the IMM framework)
  which is mentioned in footnote 12.
  
### (§5) Handling SC Accesses (`IMM_SC`)
As mentioned in [Podkopaev-al:POPL19], we have two versions of the `IMM` model being implemented in Coq:
[`IMM`](https://github.com/weakmemory/imm/blob/forweakestmo/src/imm/imm.v) and
[`IMM_S`](https://github.com/weakmemory/imm/blob/forweakestmo/src/imm/imm_s.v).
Paradoxically, `IMM_S` is the one we refer to in the paper and `IMM` is a stronger version of it, which we use as another intermediate
step in compilation correctness proofs to hardware models.
The proof of compilation correctness from `IMM_S` to `IMM` is presented in
[`src/imm/imm_sToimm.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/imm/imm_sToImm.v) of the IMM framework.
<br />
The extension of `IMM_S`-consistency predicate to SC accesses (**Definition 10**) is defined by 
predicate `imm_psc_consistent` in file
[`src/imm/imm_s.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/imm/imm_s.v)
of the IMM framework, whereas the extension for `IMM` is embedded in predicate `imm_consistent` in file
[`src/imm/imm.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/imm/imm.v)
of the IMM framework.
Versions of relations `scb`, `psc_base`, and `psc_f` for both model are defined in the corresponding files. 
  
* (**§5.1.1**) The compilation correctness theorem from `IMM_SC` to `TSO` is represented by lemma `IMM_consistent`
  in [`src/hardware/immToTSO.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/hardware/immToTSO.v)
  of the IMM framework.
  It has a precondition stating that there should be an `mfence` between every SC write and following SC read as mentioned in the paper.

* (**§5.1.2**) **Theorem 12** is represented by lemma `global_sc_ar` in
  [`src/imm/Sc_opt.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/hardware/Sc_opt.v)
  compilation correctness theorem from `IMM_SC` to `POWER` is split to a compilation 
  <br />
  The compilation correctness theorem from `IMM_SC` to `POWER` (assuming the absence of SC accesses which are dealt by **Theorem 12**)
  is represented by lemma `IMM_consistent`
  in [`src/hardware/immToPower.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/hardware/immToPower.v)
  of the IMM framework.

* (**§5.1.4**) The compilation correctness theorem from `IMM_SC` to `ARMv8` is represented by lemma `IMM_consistent`
  in [`src/hardware/immToARM.v`](https://github.com/weakmemory/imm/blob/forweakestmo/src/hardware/immToARM.v)
  of the IMM framework.
  
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

