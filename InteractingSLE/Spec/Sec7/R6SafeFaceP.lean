/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeFinal
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# R.6's face description in positional form

PROVE-R6-SAFE. In `R6Face` the side, jump and height conditions at the shared-side point `y₀` and the exposed point `ξ`
(and at their transition images `η₀`, `η`) follow from positions alone, since the two-seed words have canonical
heights (`R6Rel.forceBoundaryData_one_*`) and the current marks are ordered around the driver at every live relative
capacity (`segDriver_le_geomRW`, `geomLW_le_segDriver`, from `MartChar.RealFlow.le_rightImg` and
`Supp8.GB6.rightImg_congr`). This file states the positional face `R6FaceP` (shared side: beyond the right marks with
equal right weights, or before the left marks with equal left weights; exposed side: strictly inside the right or the
left exposed interval in both charts) and proves

* **`r6Face_of_faceP`** (deterministic), and on R.7 configurations **`r6Face*Remaining_of_faceP`** (six shapes);
* **`r7OuterPhaseSideRemaining_of_cont_faceP_safe`**: the final drop-in with positional faces.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R6Fin R6Rel PocketStopSide PocketTraversal Lemma71C
open InteractingSLE.MartChar.RealFlow (rightImg le_rightImg)

/-! ### The current marks are ordered around the driver -/

section Marks

variable {Ω : Type*} {nL nR : ℕ}

/-- The capacity driver of a driven curve, read on `ℝ`, agrees on `[0, q]` (`q` live) with a continuous function. -/
theorem exists_continuous_eqOn_segDriver {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife γ) :
    ∃ w' : ℝ → ℝ, Continuous w' ∧ ∀ r ∈ Icc (0 : ℝ) q, segDriver γ r.toNNReal = w' r := by
  have hcont : ContinuousOn (fun s : ℝ => segDriver γ s.toNNReal) (Icc 0 (q : ℝ)) := by
    refine hγ.segDriver_spec.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife γ
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hq
    exact (Real.toNNReal_le_iff_le_coe).2 hs.2
  refine ⟨fun s => segDriver γ ((projIcc 0 (q : ℝ) q.coe_nonneg s : ℝ)).toNNReal,
    hcont.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc _ _ _ s).2,
    fun r hr => ?_⟩
  simp only [projIcc_of_mem q.coe_nonneg hr]

/-- **The right current marks lie right of the driver** at every live relative capacity of a driven curve. -/
theorem segDriver_le_geomRW {γ : Ω → ℝ → ℂ} {ω : Ω} (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (xR : Ω → Fin nR → ℝ) (j : Fin nR) :
    segDriver (γ ω) q ≤ geomRW (fun t ω => segDriver (γ ω) t) xR j q ω := by
  obtain ⟨w', hw', he⟩ := exists_continuous_eqOn_segDriver hγ hq
  change segDriver (γ ω) q ≤ rightImg (fun s : ℝ => segDriver (γ ω) s.toNNReal) (xR ω j) q
  rw [Supp8.GB6.rightImg_congr hw' q.coe_nonneg he]
  have h := le_rightImg hw' (xR ω j) q.coe_nonneg
  rwa [← he q ⟨q.coe_nonneg, le_rfl⟩, Real.toNNReal_coe] at h

/-- **The left current marks lie left of the driver** at every live relative capacity of a driven curve. -/
theorem geomLW_le_segDriver {γ : Ω → ℝ → ℂ} {ω : Ω} (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (xL : Ω → Fin nL → ℝ) (i : Fin nL) :
    geomLW (fun t ω => segDriver (γ ω) t) xL i q ω ≤ segDriver (γ ω) q := by
  obtain ⟨w', hw', he⟩ := exists_continuous_eqOn_segDriver hγ hq
  change -rightImg (fun s : ℝ => -segDriver (γ ω) s.toNNReal) (-xL ω i) q ≤ segDriver (γ ω) q
  rw [Supp8.GB6.rightImg_congr (w' := fun s => -w' s) hw'.neg q.coe_nonneg fun r hr => by rw [he r hr]]
  have h : -w' q ≤ rightImg (fun s => -w' s) (-xL ω i) q := le_rightImg hw'.neg (-xL ω i) q.coe_nonneg
  rw [← he q ⟨q.coe_nonneg, le_rfl⟩, Real.toNNReal_coe] at h
  linarith

end Marks






/-! ### The positional face -/

section Det

/-- A non-zero point off both marks of a two-seed word is not a jump. -/
theorem notMem_forceJumpSet_one {v w : Fin 1 → ℝ} {x : ℝ} (h0 : x ≠ 0) (hv : x ≠ v 0) (hw : x ≠ w 0) :
    x ∉ forceJumpSet v w := by
  rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
  · exact h0 h
  · exact hv (by rw [← hi, Subsingleton.elim i 0])
  · exact hw (by rw [← hj, Subsingleton.elim j 0])

/-- **The shared-side conditions from positions** (marks ordered around the driver): beyond the right marks with equal
right weights, or before the left marks with equal left weights. -/
theorem shared_conditions {κ : ℝ} {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ} {y₀ η₀ : ℝ}
    (hv : vL 0 ≤ 0 ∧ 0 ≤ vR 0) (hw : wL 0 ≤ 0 ∧ 0 ≤ wR 0)
    (hs : (vR 0 < y₀ ∧ wR 0 < η₀ ∧ ρR 0 = σR 0) ∨ (y₀ < vL 0 ∧ η₀ < wL 0 ∧ ρL 0 = σL 0)) :
    y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧ η₀ ∉ forceJumpSet wL wR ∧
      η₀ ∉ Ioo (wL 0) (wR 0) ∧ forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀ := by
  rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), fun h => by linarith [h.2],
      notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), fun h => by linarith [h.2], ?_⟩
    rw [forceBoundaryData_one_of_vR_le hv.2 h1.le, forceBoundaryData_one_of_vR_le hw.2 h2.le, h3]
  · refine ⟨notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), fun h => by linarith [h.1],
      notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), fun h => by linarith [h.1], ?_⟩
    rw [forceBoundaryData_one_of_lt_vL hv.1 h1, forceBoundaryData_one_of_lt_vL hw.1 h2, h3]

/-- **The exposed-side conditions from positions**: strictly inside the right (or the left) exposed interval in both
charts. -/
theorem exposed_conditions {κ : ℝ} {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ} {ξ η : ℝ}
    (hv : vL 0 ≤ 0 ∧ 0 ≤ vR 0) (hw : wL 0 ≤ 0 ∧ 0 ≤ wR 0)
    (he : (0 < ξ ∧ ξ < vR 0 ∧ 0 < η ∧ η < wR 0) ∨ (vL 0 < ξ ∧ ξ < 0 ∧ wL 0 < η ∧ η < 0)) :
    ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧ η ∉ forceJumpSet wL wR ∧ η ∈ Ioo (wL 0) (wR 0) ∧
      forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η := by
  rcases he with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine ⟨notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), ⟨by linarith, h2⟩,
      notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), ⟨by linarith, h4⟩, ?_⟩
    rw [forceBoundaryData_one_exposedRight h1.le h2, forceBoundaryData_one_exposedRight h3.le h4]
  · refine ⟨notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), ⟨h1, by linarith⟩,
      notMem_forceJumpSet_one (by linarith) (by linarith) (by linarith), ⟨h3, by linarith⟩, ?_⟩
    rw [forceBoundaryData_one_exposedLeft h1.le h2, forceBoundaryData_one_exposedLeft h3.le h4]

/-- **The positional face of R.6**: `R6Face` with the side, jump and height conditions replaced by positions — the
shared-side point `y₀` beyond the right marks (equal right weights) or before the left marks (equal left weights) in
both charts, and the exposed point `ξ` strictly inside the same exposed interval in both charts. -/
def R6FaceP (ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ) (outer inner : Chart) (EC EU : Set ℂ) : Prop :=
  (inner.dom : Set ℂ) ⊆ outer.dom ∧ ∃ (J : Set ℝ) (y₀ η₀ ξ η : ℝ), IsOpen J ∧ IsPreconnected J ∧
    (∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ)) ∧
    (∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M) ∧
    y₀ ∈ J ∧ ξ ∈ J ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y₀ : ℂ)) (𝓝 (η₀ : ℂ)) ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (ξ : ℂ)) (𝓝 (η : ℂ)) ∧
    ((vR 0 < y₀ ∧ wR 0 < η₀ ∧ ρR 0 = σR 0) ∨ (y₀ < vL 0 ∧ η₀ < wL 0 ∧ ρL 0 = σL 0)) ∧
    ((0 < ξ ∧ ξ < vR 0 ∧ 0 < η ∧ η < wR 0) ∨ (vL 0 < ξ ∧ ξ < 0 ∧ wL 0 < η ∧ η < 0)) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (y₀ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC)

/-- **`R6Face` from the positional face** when the marks of both words are ordered around the driver. -/
theorem r6Face_of_faceP {κ : ℝ} {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ} {outer inner : Chart} {EC EU : Set ℂ}
    (hv : vL 0 ≤ 0 ∧ 0 ≤ vR 0) (hw : wL 0 ≤ 0 ∧ 0 ≤ wR 0)
    (h : R6FaceP ρL ρR σL σR vL vR wL wR outer inner EC EU) :
    R6Face κ ρL ρR σL σR vL vR wL wR outer inner EC EU := by
  obtain ⟨hIncl, J, y₀, η₀, ξ, η, hJo, hJ, hcol, hb, hy₀, hξ, hl₀, hl, hs, he, ha₀, ha⟩ := h
  exact ⟨hIncl, J, y₀, η₀, ξ, η, hJo, hJ, hcol, hb, hy₀, hξ, hl₀, hl, shared_conditions hv hw hs,
    exposed_conditions hv hw he, ha₀, ha⟩

end Det

/-! ### The positional faces on R.7 configurations -/

section R7

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open WholeField R7Outer R7Leaves R6Nest R6Cert HOuter PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketCoupling PocketStopField Lemma71I PocketStop PocketSeedOpen

/-- **Named, unproved: R.6's positional face, shape `Mixed`**:
`R6FaceMixedRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceMixedRemaining_of_faceP`). -/
def R6FacePMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's positional face, shape `MixedInf`**:
`R6FaceMixedInfRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceMixedInfRemaining_of_faceP`). -/
def R6FacePMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's positional face, shape `MixedInfInf`**:
`R6FaceMixedInfInfRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceMixedInfInfRemaining_of_faceP`). -/
def R6FacePMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's positional face, shape `Two`**:
`R6FaceTwoRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceTwoRemaining_of_faceP`). -/
def R6FacePTwoRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's positional face, shape `TwoInf`**:
`R6FaceTwoInfRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceTwoInfRemaining_of_faceP`). -/
def R6FacePTwoInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's positional face, shape `TwoInfInf`**:
`R6FaceTwoInfInfRemaining` with `R6FaceP` in place of `R6Face` (`r6FaceTwoInfInfRemaining_of_faceP`). -/
def R6FacePTwoInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfgInf (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf R ML (StripSys.rt s) η ψ' ω) ∧
          R6FaceP (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FaceMixedRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceMixedRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePMixedRemaining.{u} k rL rR c c') : R6FaceMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAll R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAll R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

/-- **`R6FaceMixedInfRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceMixedInfRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePMixedInfRemaining.{u} k rL rR c c') : R6FaceMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

/-- **`R6FaceMixedInfInfRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceMixedInfInfRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePMixedInfInfRemaining.{u} k rL rR c c') : R6FaceMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

/-- **`R6FaceTwoRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceTwoRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePTwoRemaining.{u} k rL rR c c') : R6FaceTwoRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.props (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAll R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAll R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAll R ML (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAll R ML (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

/-- **`R6FaceTwoInfRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceTwoInfRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePTwoInfRemaining.{u} k rL rR c c') : R6FaceTwoInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.props (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAll R ML (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAll R ML (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

/-- **`R6FaceTwoInfInfRemaining` from the positional face** (`r6Face_of_faceP`; the marks of both live current charts
are ordered around their drivers, `segDriver_le_geomRW`, `geomLW_le_segDriver`). -/
theorem r6FaceTwoInfInfRemaining_of_faceP {k rL rR c c' : ℝ}
    (hP : R6FacePTwoInfInfRemaining.{u} k rL rR c c') : R6FaceTwoInfInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hP hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hγ := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγ' := ((hA' ω hωA').1.props (hA' ω hωA').2).1
  exact ⟨q', hq', r6Face_of_faceP
    ⟨sub_nonpos.2 (geomLW_le_segDriver (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0),
      sub_nonneg.2 (segDriver_le_geomRW (γ := travAllInf R L r η ψ) hγ hωN.2.1 _ 0)⟩
    ⟨sub_nonpos.2 (geomLW_le_segDriver
        (γ := travAllInf R ML (StripSys.rt s) η ψ') hγ' hq' _ 0),
      sub_nonneg.2 (segDriver_le_geomRW
        (γ := travAllInf R ML (StripSys.rt s) η ψ') hγ' hq' _ 0)⟩ hf⟩

end R7

/-! ### The final drop-in with positional faces -/

section Final

open R7Outer R7Leaves R6Nest

variable {k rL rR : ℝ}

/-- **The named inputs of R.6's two-outer-arm case in positional-face form.** -/
def TwoOuterFacePInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FacePMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FacePMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FacePMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FacePTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FacePTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FacePTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The positional form of the two-outer-arm inputs gives `TwoOuterFaceInputs`. -/
theorem twoOuterFaceInputs_of_faceP (h : TwoOuterFacePInputs.{u} k rL rR) : TwoOuterFaceInputs.{u} k rL rR :=
  ⟨h.1, r6FaceMixedRemaining_of_faceP h.2.1, r6FaceMixedInfRemaining_of_faceP h.2.2.1,
    r6FaceMixedInfInfRemaining_of_faceP h.2.2.2.1, h.2.2.2.2.1, r6FaceTwoRemaining_of_faceP h.2.2.2.2.2.1,
    r6FaceTwoInfRemaining_of_faceP h.2.2.2.2.2.2.1, r6FaceTwoInfInfRemaining_of_faceP h.2.2.2.2.2.2.2⟩

/-- **The outer phase input from R.5 and R.6's positional faces** (drop-in for
`R6Fin.r7OuterPhaseSideRemaining_of_cont_core`, without `hstrip` and `htwo`). -/
theorem r7OuterPhaseSideRemaining_of_cont_faceP_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FacePMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FacePMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FacePMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterFacePInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_face_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FaceMixedRemaining_of_faceP hface) (r6FaceMixedInfRemaining_of_faceP hfaceI)
    (r6FaceMixedInfInfRemaining_of_faceP hfaceII) hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceInputs_of_faceP (htwoIn hdL hdR)

end Final

/-! ### A tool for the inclusion of the two current domains -/

section Incl

/-- **The inner current domain lies in the outer one** as soon as it meets it and avoids its frontier (the inner
domain of a conformal chart is connected). For R.6 the frontier of the outer current domain inside the pocket lies in
the outer hull, so this reduces `R6FaceP`'s inclusion to the time ordering of the two hulls and one common point. -/
theorem dom_subset_of_frontier_disjoint {outer inner : Chart} (hI : inner.IsConformal)
    (hfr : Disjoint (inner.dom : Set ℂ) (frontier (outer.dom : Set ℂ)))
    (hmeet : ((inner.dom : Set ℂ) ∩ outer.dom).Nonempty) : (inner.dom : Set ℂ) ⊆ outer.dom := by
  have hpre : IsPreconnected (inner.dom : Set ℂ) := by
    rw [hI.coe_dom]
    exact convex_H.isPreconnected.image _ hI.1.continuousOn
  have hcover : (inner.dom : Set ℂ) ⊆ (outer.dom : Set ℂ) ∪ (closure (outer.dom : Set ℂ))ᶜ := by
    intro z hz
    by_cases hc : z ∈ closure (outer.dom : Set ℂ)
    · left
      by_contra hno
      exact disjoint_left.1 hfr hz ⟨hc, by rwa [outer.dom.isOpen.interior_eq]⟩
    · exact Or.inr hc
  exact hpre.subset_left_of_subset_union outer.dom.isOpen isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) hcover hmeet

end Incl

end InteractingSLE.Sec7.R6Safe
