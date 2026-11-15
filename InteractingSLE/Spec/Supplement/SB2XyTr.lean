/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XyRun

/-!
# The per-time lifts `trLift` at a later stage from the per-stage facts

Packet PROVE-T14-SB2LIFT (round 28; LIFTSET's item 4). **`trLift_of_facts`**: at a launched actual stage of positive
finite lifetime whose relative stage has the per-stage facts of the v3 rule (shift `0`), the per-time lift identities
`trLift` of `RunInputs''` hold — `trLift_concrete` (round 23), with the actual-piece facts from the launch
(`tipSet_newPc_launch`, `tail_of_launch`, `GW1P.isClosed_pieces_run`) and the relative facts read off `StageFacts`
(at shift `0` the v3 stage curve is the v2 one, `stCurvep_zero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep Sec7.PocketTraversal Sec7.Lemma71C

/-- At shift `0` the v3 stage curve is the v2 one. -/
theorem stCurvep_zero (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) :
    stCurvep c m (fun t => pcPt s₁ e₁ ((0 : ℝ≥0) + t)) (e₁.2 - ((0 : ℝ≥0) : ℝ≥0∞)) s₂ = stCurve c m s₁ e₁ s₂ := by
  simp only [zero_add, ENNReal.coe_zero, tsub_zero]
  rfl

/-- At shift `0` the v3 good times are the v2 ones. -/
theorem goodTp_zero (c : Chart) (s₁ : ExplState) (e₁ : Drv) :
    goodTp c (fun t => pcPt s₁ e₁ ((0 : ℝ≥0) + t)) (e₁.2 - ((0 : ℝ≥0) : ℝ≥0∞)) = goodT c s₁ e₁ := by
  simp only [zero_add, ENNReal.coe_zero, tsub_zero]
  rfl

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv} {n : ℕ} {c : Chart} {A : Set ℂ} {R m : ℝ}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The per-time lifts at one stage from the per-stage facts.** -/
theorem trLift_of_facts (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hU : UpperChartOK c) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (he₁ : (D n).2 ≠ ⊤) (hpos : (D n).2 ≠ 0) {s₂ : ExplState} {e₂ : Drv}
    (hF : StageFacts c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) 0 s₂ e₂) :
    (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D n) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ e₂ ∧
      LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (LuM.bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ''
          (LuM.trOf (D n) '' Icc 0 r.toNNReal))) ∧
    (∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ e₂ → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D n) ∧
      LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (LuM.bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ''
          (LuM.trOf (D n) '' Icc 0 r.toNNReal))) := by
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨hρ, he₂, hgen, hrel, hdense, -, hpr₂⟩ := hF
  rw [stCurvep_zero] at hρ he₂ hgen
  rw [goodTp_zero] at hdense
  have hL : (D n).2 - ((0 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by simpa using he₁
  obtain ⟨hfin, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom⟩ := hrel.1 hL
  rw [stCurvep_zero] at hαeq
  rw [goodTp_zero] at hdom
  have hdense' : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆ closure (goodT c s₁ (D n)) := by
    simpa using hdense
  have hdom' : ∀ t ∈ goodT c s₁ (D n), Lk.liftPt c m (pcPt s₁ (D n) t) ∈ (stChart s₂).2.1 '' H := by
    simpa using hdom
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htail := tail_of_launch hl hβr hK hDom
  have hbe₁ := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) _ D hP n).1
  exact trLift_concrete hγ hβ hcH hc1 hoff hbe₁ (LuM.pieceRegular_of_launch hP hl) he₁ hpos htip htail hρ he₂
    hgen hfin hW hpr₂.1 hαeq hα0 hαc hc hgc hcH₂ hc1₂ hdom' hdense'

end InteractingSLE.Theorem14.SB.Mn
