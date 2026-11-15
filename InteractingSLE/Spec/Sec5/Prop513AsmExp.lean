/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemCand

/-!
# Proposition 5.9's tips from the stage law of the adaptive construction (any universe)

Packet PROVE-PROP513-ASM. Specification §5.2, proof of Proposition 5.9 (pp. 143–148), as used by the proof of
Proposition 5.13 (p. 150).

PROVE-PROP59T4's experiments (`ProdExp`, `CandExp`) carry the **piece law** `Prop59StagePieceLawStatement` of every
stage and live on `Type`. The experiment itself (`ae_not_isBounded_of_stageLaw`, PROVE-PROP59T2) only consumes the
weaker **stage law** `Prop59StageLawStatement` (the target of PROVE-STAGED5) together with the stage-word conditions,
which follow from the initial word (`hwL_of_isStageInit`, `hwR_of_isStageInit`). This file states the experiments in
that form, with the law as a separate hypothesis on the data, in every universe.

**The adaptive construction is the countable mixture `histSys` of fixed candidates** (`HistExp.system`): at every
stage the realized piece is the candidate indexed by its realized finite list of switching times (PROVE-PROP59T4's
`mixPiece`). This is the simultaneous identification of each realized adaptive prefix with a member of a countable
canonical family that Astra's follow-up 5 (R73; correction L8–L14, (2.2) at L346–L352) requires; it holds here by
construction, and the stage law is asked of this realized construction, not of an arbitrary gluing.

## Main results

* `rootTgt`, `nodeTgt`, `nodeAct`: PROVE-PROP59T4's targets `rootTarget`, `nodeTarget`, `nodeActive` in every universe
  (definitionally equal to them on `Type`);
* `ae_fst_of_ae_prod`: an almost-sure statement about the first coordinate of `P ⊗ Pa` holds `P`-almost surely, for
  every predicate;
* **`ae_not_isBounded_of_prod_stageLaw`**: the experiment on `Ω × Ωa` from the stage law, read on `Ω`;
* `HistExp` (the data of the experiments, PROVE-PROP59-PIECES's target; no law), `HistExp.system`,
  **`HistExp.ae_not_isBounded`**;
* **`tip0UnboundedStatement_of_histExp`**, **`tipUnboundedStatement_of_histExp`**: PROVE-PROP59T's tip statements
  from the data and the stage law;
* `histExpOfCandExp`, `stageLaw_histExpOfCandExp`: PROVE-PROP59T4's candidate experiments are a special case.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.Sec5.Prop513Asm

open QuantumZipper Prop59Stage Prop59Tips Prop59System

/-! ### The targets in every universe -/

section Targets

variable {Ω : Type u}

/-- The root targets: the node points off the counterflow hull at time `r`, in the own-component chart
(PROVE-PROP59T4's `rootTarget`, any universe). -/
def rootTgt (W : ℝ≥0 → Ω → ℝ) (z : ℕ → Ω → ℂ) (r : ℚ) (ω : Ω) : Set ℂ :=
  (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
    (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal))

/-- The descendant targets of a root (PROVE-PROP59T4's `nodeTarget`, any universe). -/
def nodeTgt (W : ℝ≥0 → Ω → ℝ) (S : Ω → Set ℂ) (r : ℚ) (ω : Ω) : Set ℂ :=
  (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
    (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal))

/-- The event that the root `z` is visited after the counterflow time `r` (PROVE-PROP59T4's `nodeActive`). -/
def nodeAct (γ : Ω → ℝ≥0 → ℂ) (z : Ω → ℂ) (r : ℚ) : Set Ω :=
  {ω | (r : ℝ) < traceFirstVisit (γ ω) (z ω)}

theorem rootTgt_eq_rootTarget {Ω : Type} (W : ℝ≥0 → Ω → ℝ) (z : ℕ → Ω → ℂ) :
    rootTgt W z = rootTarget W z := rfl

theorem nodeTgt_eq_nodeTarget {Ω : Type} (W : ℝ≥0 → Ω → ℝ) (S : Ω → Set ℂ) :
    nodeTgt W S = nodeTarget W S := rfl

theorem nodeAct_eq_nodeActive {Ω : Type} (γ : Ω → ℝ≥0 → ℂ) (z : Ω → ℂ) :
    nodeAct γ z = nodeActive γ z := rfl

end Targets

/-! ### The experiment on a product extension, from the stage law -/

section Prod

variable {κ : ℝ} {Ω : Type u} {Ωa : Type v} [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω}
  {Pa : Measure Ωa} [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]

omit [IsProbabilityMeasure P] in
/-- **An almost-sure statement about the first coordinate of `P ⊗ Pa` holds `P`-almost surely**, for every predicate
(`P ⊗ Pa (N × Ωa) = P(N)` for every set `N`; PROVE-PROP59T4's `ae_of_ae_prod_fst` in every universe). -/
theorem ae_fst_of_ae_prod {p : Ω → Prop} (h : ∀ᵐ ω' ∂(P.prod Pa), p ω'.1) : ∀ᵐ ω ∂P, p ω := by
  rw [ae_iff] at h ⊢
  have e : {ω' : Ω × Ωa | ¬ p ω'.1} = {ω | ¬ p ω} ×ˢ (univ : Set Ωa) := by
    ext ω'
    simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]
  rw [e, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

/-- **The alternating construction on a product extension from the stage law, read on `Ω`**: if the experiment on
`Ω × Ωa` obeys the stage law, has the structure of a stage system and an initial word with `IsStageInit`, if its
images are bounded whenever the target sets `D` are, and if it is started almost surely on `A`, then almost surely on
`A` the set `D` is unbounded. -/
theorem ae_not_isBounded_of_prod_stageLaw (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {hnL : 0 < nL}
    {hnR : 0 < nR} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0}
    {sys : StageSys (Ω × Ωa) nL nR} {C : Ω × Ωa → Set ℂ} {D : Ω → Set ℂ} {A : Set Ω}
    (hL : Prop59StageLawStatement κ (P.prod Pa) ρL ρR sys)
    (hS : IsStageSystem (P.prod Pa) hnL hnR Q δ G sys C) (hI : IsStageInit κ ρL ρR)
    (hC : ∀ ω' : Ω × Ωa, Bornology.IsBounded (D ω'.1) → Bornology.IsBounded (C ω'))
    (hA : ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A → ω' ∈ (sys (fun _ => 0) 0).R) :
    ∀ᵐ ω ∂P, ω ∈ A → ¬ Bornology.IsBounded (D ω) := by
  refine ae_fst_of_ae_prod (Pa := Pa) ?_
  filter_upwards [ae_not_isBounded_of_stageLaw hκ hκ4 hL hS (hwL_of_isStageInit hκ hκ4 hI)
    (hwR_of_isStageInit hκ hκ4 hI) (fun _ => 0), hA] with ω' h1 h2 hω hD
  exact h1 (h2 hω) (hC ω' hD)

/-- **The data of the alternating construction's experiments** at every positive rational counterflow time, on the
product extension `Ω × Ωa`, for target sets `D r` and initial events `A r` (PROVE-PROP59-PIECES's target): the stage
words, the switching grids, the fixed candidate pieces `cand r j t` (one per finite list `t` of original switching
times), the initial start, event and revealed history, the node images, the structure of a stage system for the
realized construction `histSys`, the initial word, the bounded images and the initial events. The law of the
construction is not part of the data: it is the separate hypothesis `Prop59StageLawStatement … (X.system r)`
(PROVE-STAGED5's target). -/
structure HistExp (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  /-- The allowed original switching times. -/
  grid : ℚ → Set ℝ≥0
  /-- The meshes. -/
  mesh : ℚ → ℕ → ℝ≥0
  /-- The grids. -/
  times : ℚ → ℕ → ℕ → ℝ≥0
  /-- The fixed candidate pieces, one per finite list of original switching times. -/
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  /-- The initial start (in the dilated joint chart). -/
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + 0) (nR r + 0)
  /-- The initial reached event. -/
  R₀ : ℚ → Set (Ω × Ωa)
  /-- The initial revealed history. -/
  base : ℚ → MeasurableSpace (Ω × Ωa)
  /-- The node images in the dilated joint chart. -/
  image : ℚ → Ω × Ωa → Set ℂ
  /-- The realized construction is a stage system. -/
  stages : ∀ r : ℚ, 0 < r → IsStageSystem (P.prod Pa) (posL r) (posR r) (grid r) (mesh r) (times r)
    (histSys (cand r) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r)) (image r)
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) →
    Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

variable {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω}

/-- The realized (adaptive) construction at the counterflow time `r`: the countable mixture of the fixed candidates
along the realized switching history. -/
def HistExp.system (X : HistExp κ P Pa D A) (r : ℚ) : StageSys (Ω × Ωa) (X.nL r) (X.nR r) :=
  histSys (X.cand r) (X.times r) (X.posL r) (X.posR r) (X.y₀ r) (X.R₀ r) (X.base r)

/-- **The experiment at the counterflow time `r`**, from the stage law of the realized construction. -/
theorem HistExp.ae_not_isBounded (hκ : 0 < κ) (hκ4 : κ < 4) (X : HistExp κ P Pa D A)
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X.rhoL r) (X.rhoR r) (X.system r))
    (r : ℚ) (hr : 0 < r) : ∀ᵐ ω ∂P, ω ∈ A r → ¬ Bornology.IsBounded (D r ω) :=
  ae_not_isBounded_of_prod_stageLaw hκ hκ4 (hL r hr) (X.stages r hr) (X.initialWord r hr) (X.image_bdd r hr)
    (X.active r hr)

/-- **`Tip0UnboundedStatement` from the experiments and the stage law** (root `0`). -/
theorem tip0UnboundedStatement_of_histExp (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (X : HistExp κ P Pa (rootTgt W z) fun _ => univ)
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X.rhoL r) (X.rhoR r) (X.system r)) :
    Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [X.ae_not_isBounded hκ hκ4 hL r hr] with ω hω
  exact hω (mem_univ ω)

/-- **`TipUnboundedStatement` from the experiments and the stage law** (root `z`, descendants `S`). -/
theorem tipUnboundedStatement_of_histExp (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {z : Ω → ℂ} {S : Ω → Set ℂ} (X : HistExp κ P Pa (nodeTgt W S) (nodeAct γ z))
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X.rhoL r) (X.rhoR r) (X.system r)) :
    TipUnboundedStatement P W γ z S :=
  fun r hr => X.ae_not_isBounded hκ hκ4 hL r hr

end Prod

/-! ### PROVE-PROP59T4's candidate experiments are a special case -/

section Cand

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  [StandardBorelSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
  {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω}

/-- **The data of a candidate experiment** (`isStageSystem_histSys` gives the stage systems). -/
def histExpOfCandExp (X : CandExp κ P Pa D A) : HistExp κ P Pa D A where
  nL := X.nL
  nR := X.nR
  posL := X.posL
  posR := X.posR
  rhoL := X.rhoL
  rhoR := X.rhoR
  grid := X.grid
  mesh := X.mesh
  times := X.times
  cand := X.cand
  y₀ := X.y₀
  R₀ := X.R₀
  base := X.base
  image := X.image
  stages r hr := isStageSystem_histSys (X.reg r hr) (X.grid_ok r) (X.mesh_ok r) (X.y₀_meas r hr) (X.base_le r hr)
    (X.R₀_meas r hr) (X.init r hr) (X.chain r hr)
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

/-- **The stage law of a candidate experiment**, from its piece laws (`prop59StageLawStatement_of_pieceLaw`). -/
theorem stageLaw_histExpOfCandExp (X : CandExp κ P Pa D A) (r : ℚ) (hr : 0 < r) :
    Prop59StageLawStatement κ (P.prod Pa) ((histExpOfCandExp X).rhoL r) ((histExpOfCandExp X).rhoR r)
      ((histExpOfCandExp X).system r) :=
  prop59StageLawStatement_of_pieceLaw (X.pieceLaw r hr)

end Cand

end InteractingSLE.Sec5.Prop513Asm
