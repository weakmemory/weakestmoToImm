This is a description of the artifact supplementing the paper 
*Reconciling Event Structures with Modern Multiprocessors*
by Evgenii Moiseenko, Anton Podkopaev, Ori Lahav, Orestis Melkonian, and Viktor Vafeiadis.

The artifact is two Coq packages
([`imm.1.1`](https://github.com/weakmemory/imm/tree/1.1) and [`weakestmoToImm`](https://github.com/weakmemory/weakestmoToImm)) in a VirtualBox image. <br />
The image has been tested with VirtualBox TODO 5.2.18 with Oracle VM VirtualBox Extension pack.

## How to use the artifact
Import the VirtualBox image into VirtualBox, and boot the machine.

TODO: The login is `ecoop` and the password is `ecoop`.

All necessary software is installed, and the `imm` and `weakestmoToImm` projects are checked out to
`/home/ecoop/Desktop/imm` and `/home/ecoop/Desktop/weakestmoToImm` correspondingly.
Additionally, Emacs (with Proof General) and CoqIDE are installed so that you can browse the sources
and TODO the latest version of the paper copied to `/home/ecoop/Desktop/paper.pdf`.

The proofs might be checked by opening a terminal and running
```bash
cd /home/ecoop/Desktop/imm
make clean; make -j2
```
for `imm` and
```bash
cd /home/ecoop/Desktop/weakestmoToImm
make clean; make -j2
```
for `weakestmoToImm`.
There might be some warnings about notations. The build terminating without printing "error" is successful.
Please, note that building of the proofs might take a lot of time (especially, the `imm` project).

## Relation between code and the paper 

The code supplementing the paper is spread over two packages:

* `imm`, where we extended the `IMM` memory model with support for SC accesses comparing to the version from [Podkopaev-al:POPL19];
* `weakestmoToImm`, which contains definitions of the `Weaketmo` memory model and our proof of compilation correctness from `Weakestmo` to `IMM`.

Below, there is a mapping from definitions and statements used in the paper to their counterparts in the Coq code.


### (§2.3) Weakestmo to IMM compilation correctness. Main theorem and lemmas

* The main theorem of compilation correctness from Weakestmo to IMM (**Theorem 1** from the paper) is represented
  by `compilation_correctness` stated in `weakestmoToImm/src/compilation/Compilation.v`.
* The simulation relation `I` used to prove **Theorem 1** is represented by `simrel_consistent` in `weakestmoToImm/src/compilation/SimRel.v`.
* **Lemma 2** stating that the simulation relation `I` holds for the initial event structure corresponds to 
  `simrel_init` in `weakestmoToImm/src/compilation/SimRelInit.v`.
* **Lemma 3** stating that the simulation relation `I` can be restored after a traversal step is represented by
  `simrel_step` in `weakestmoToImm/src/compilation/SimRelStep.v`.
* **Lemma 4** stating that if `I` holds for the final traversal configuration 
  then the graph associated with the extracted subset `X` is isomorphic to the original IMM graph `G` 
  is represented by `simrel_extract` in `weakestmoToImm/src/compilation/Compilation.v`
  
### (§3) Basic definitions of event structure
* (**§3.1**) Events of event structures are encoded by `eventid` (which is equal to `nat`) defined in `weakestmoToImm/src/model/EventStructure.v`.
  <br />
  Labels (`label` in Coq) are defined in file `imm/src/basic/Events.v`.
* (**§3.2**) Event structures (`ES.t` in Coq) and the well-formedness predicate (`ES.Wf` in Coq) stating basic properties of their components
  are defined in `weakestmoToImm/src/model/EventStructure.v`.
* (**§3.3**) A step of operational semantics of event structure construction (`step` in Coq) is defined in `weakestmoToImm/src/construction/Step.v`.
* (**§3.4**) The Weakestmo event structure consistency predicate along with definitions of relations `hb` and `ecf` and the notion of visible events (predicate `vis` in Coq)
  are defined in `weakestmoToImm/src/model/Consistency.v`.
  <br />
  (The consistency predicate is parameterized by `model` which is either `Weakest` or `Weakestmo`.
   The former represents a version of Weakestmo [Chakraborty-Vafeiadis:POPL19] which is not considered in our paper.)
  <br />
  In footnote 9, we mention that our Coq formalization uses another definition of visible events (predicate `vis` in Coq) comparing
  to the one in [Chakraborty-Vafeiadis:POPL19].
  Their equivalence is stated by lemma `cc_alt` in `weakestmoToImm/src/model/Consistency.v`.
* (**§3.5**)
  The notion of *execution graph* (**Definition 6**, `execution` in Coq)
  is defined in file `imm/src/basic/Execution.v`.
  Unlike the paper representation, it is not defined as a special case of event structures.
  Moreover, as mentioned in footnote 11, execution graphs are defined with another type of events
  (`actid` in Coq, file `imm/src/basic/Events.v`).
  <br />
  The notion of a subset of events *extracted from* an event structure (**Definition 7**, `Execution.t` in Coq) is defined in `weakestmoToImm/src/model/Execution.v`.
  <br />
  The notion of a execution graph *associated with* an extracted subset (`simrel_extract` in Coq) is defined in `weakestmoToImm/src/compilation/Compilation.v`.

### (§4.2) Simulation relation `I`
* Function `s2g(G, S)` from the paper (which maps events of event structure `S` to events of execution graph `G`)
  is represented by function `e2a` (stands for *'`eventid` to `actid`'*) defined in `weakestmoToImm/src/imm_aux/EventToAction.v`.
* In Coq, functions `⌈⌈·⌉⌉` and `⌊⌊·⌋⌋` for lifting `s2g` to sets are represented as `e2a □₁ ·` and `e2a ⋄₁ ·` correspondingly;
  their relational counterparts—`e2a □ ·` and `e2a ⋄ ·`.

The simulation relation `I` is represented by `simrel_consistent` (and its part `simrel`) in `weakestmoToImm/src/compilation/SimRel.v`.
Below, we map elements of the paper's version of `I` to the Coq version.
Most of them are represented by fields of `simrel` or derivable from them:

1. `gcons` (a field in `simrel`).
2. `SCONS` (an entry in `simrel_consistent`).
3. `sr_exec` (a field in `simrel`).
4. `ex_cov_iss` (a field in `simrel`).
5. **(a)** Equality of events' threads and labels up to values for events connected via `e2a` 
   is represented by `sr_e2a` (a field in `simrel`).
   It uses auxiliary definition `simrel_e2a` defined in `weakestmoToImm/src/compilation/SimRelEventToAction.v`.
   <br />
   **(b)** Equality of labels for events and their covered and issued counterparts is represented by `ex_cov_iss_lab` (a field in `simrel`).
6. Derivable from `sr_e2a` via lemma `e2a_sb` stated in `weakestmoToImm/src/imm_aux/EventToAction.v`.
7. Derivable from `sr_e2a` via lemma `e2a_eq_in_cf` stated in `weakestmoToImm/src/imm_aux/EventToAction.v`.
8. **(a)** Field `e2a_jf` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `weakestmoToImm/src/compilation/SimRelEventToAction.v`.
   <br />
   **(b)** Lemma `jf_cov_iv_rf` stated in `weakestmoToImm/src/compilation/SimRel.v` derivable from `jf_ex_in_cert_rf` (a field in `simrel`).
9. `jfe_ex_iss` (a field in `simrel`).
10. Field `e2a_ew` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `weakestmoToImm/src/compilation/SimRelEventToAction.v`.
11. `ew_ex_iss` (a field in `simrel`).
12. Field `e2a_co` of `simrel_e2a` (which is represented in `simrel` via field `sr_e2a`) defined in `weakestmoToImm/src/compilation/SimRelEventToAction.v`.

### (§4.3) Simulation step

In our proof, we show that **Lemma 3**, the simulation step (in Coq, `simrel_step` in `weakestmoToImm/src/compilation/SimRelStep.v`),
holds by doing induction on a certification run.
During the induction, we preserve predicate `simrel_cert` defined in `weakestmoToImm/src/compilation/SimRelCert.v`.

* (**§4.3.1**) The `determined` set  (`D` in Coq), relations `vf` and `sjf` (`cert_rf` in Coq) are defined in `weakestmoToImm/src/compilation/CertRf.v`.
  <br />
  The certification run is defined via predicate `cert_graph` and constructed via lemma `cert_graph_start` in `weakestmoToImm/src/compilation/CertGraph.v`.
  <br />
  The proof of `cert_graph_start` uses the receptiveness property
  (`receptiveness_full` in Coq, defined in file `imm/src/promiseToImm/Receptiveness.v`)
  which is mentioned in footnote 12.
  
### (§5) Handling SC accesses (`IMM_SC`)
As mentioned in [Podkopaev-al:POPL19], we have two versions of the `IMM` model being implemented in Coq:
`IMM` (file `imm/src/imm/imm.v`) and `IMM_S` (file `imm/src/imm/imm_s.v`).
Paradoxically, `IMM_S` is the one we refer to in the paper and `IMM` is a stronger version of it, which we use as another intermediate
step in compilation correctness proofs to hardware models.
The proof of compilation correctness from `IMM_S` to `IMM` is presented in
`imm/src/imm/imm_sToimm.v`.
<br />
The extension of `IMM_S`-consistency predicate to SC accesses (**Definition 10**) is defined by 
predicate `imm_psc_consistent` in file `imm/src/imm/imm_s.v`,
whereas the extension for `IMM` is embedded in predicate `imm_consistent` in file `imm/src/imm/imm.v`.
Versions of relations `scb`, `psc_base`, and `psc_f` for both model are defined in the corresponding files. 
  
* (**§5.1.1**) The compilation correctness theorem from `IMM_SC` to `TSO` is represented by lemma `IMM_consistent`
  in `imm/src/hardware/immToTSO.v`.
  It has a precondition stating that there should be an `mfence` between every SC write and following SC read as mentioned in the paper.

* (**§5.1.2**) **Theorem 12** is represented by lemma `global_sc_ar` in
  `imm/src/imm/Sc_opt.v`
  compilation correctness theorem from `IMM_SC` to `POWER` is split to a compilation 
  <br />
  The compilation correctness theorem from `IMM_SC` to `POWER` (assuming the absence of SC accesses which are dealt by **Theorem 12**)
  is represented by lemma `IMM_consistent`
  in `imm/src/hardware/immToPower.v`.

* (**§5.1.4**) The compilation correctness theorem from `IMM_SC` to `ARMv8` is represented by lemma `IMM_consistent`
  in `imm/src/hardware/immToARM.v`.
