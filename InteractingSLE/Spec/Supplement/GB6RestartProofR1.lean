/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RestartProofData

/-!
# Proposition GB6, step (d): the record of the flow prefix and (R1)

Packet PROVE-GB6-RESTART. GB6 (supplement p. 519: "Thus the conditional Poisson mean is exactly the evolving finite
word, and its covariance is the zero-boundary Green kernel") in the form of GB6's (d): conditionally on the record of
the flow prefix at the own time `s`, the field read in the chart of `U` is the GFF of the returned stop word.

The record is that of the regularized flow driver (`Theorem14.GW2JointKernel.cfE`,
`Theorem14.StagedReg.regularize`), read at `s` (`recOf`). The chart of `U` is
`ownComponentChart w s = (Chart.id.loewner w s).trans R`, so the field read in it
with the counterflow coefficients `(−1, −πχ, χ(16/κ))` is the record field (the field read in the flow's Loewner chart
with `(1, 0, χ)`, `recField`) returned through `R` with the constant `πχ` and lift coefficient `χ`
(`isChartTransport_ownComponentChart_returnField`); its conditional law is the returned stop word
(`ae_condExp_returnRecField`, from PROVE-STAGEDLAW3's `ae_condExp_recField_of_admissible` and `gaussCF_retWord`).
This is PROVE-T14-TIP10's `exists_jointKernel_r1` with the roles of the two curves exchanged.

## Main results

* `isChartTransport_ownComponentChart_returnField`;
* `recOf_cfE_eq`, `rtime_recOf_cfE`, `rdrv_recOf_cfE`, `flag_recOf_cfE`: the record before the lifetime;
* `measurable_recOf_cfE`;
* **`ae_condExp_returnRecField`**: (R1) for the returned record field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField Theorem14.GW2JointKernel

/-! ### The chart of `U` reads the returned record field -/

/-- **The field read in the chart of `U` is the returned field of the flow's Loewner chart**: if `Y` is `h` read in
the Loewner chart `f_s` with `(1, 0, χ)`, then `returnField πχ χ Y` is `h` read in `ownComponentChart w s` with the
counterflow coefficients `(−1, −πχ, χ(16/κ))`. -/
theorem isChartTransport_ownComponentChart_returnField {κ : ℝ} (hκ : 0 < κ) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) {h Y : DistOn upperHalfPlaneOpens}
    (h₂ : IsChartTransport (Chart.id.loewner w s) 1 0 (chiC κ) h Y) :
    IsChartTransport (ownComponentChart w s) (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h
      (returnField (Real.pi * chiC κ) (chiC κ) Y) := by
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  have h₃ := isChartTransport_infinitySourceChart_returnField (Real.pi * chiC κ) (chiC κ) Y
  have e₂ : -chiC κ = -1 * chiC κ := by ring
  rw [e₂] at h₃
  have h₄ := isChartTransport_trans_sign hL hR hℓL hℓR h₂ h₃
  have e₃ : (-1 : ℝ) * 1 = -1 := by ring
  have e₄ : (-1 : ℝ) * 0 + (Real.pi * chiC κ - 2 * Real.pi * chiC κ) = -(Real.pi * chiC κ) := by ring
  have e₅ : (-1 : ℝ) * chiC κ = chiC (16 / κ) := by
    rw [Sec4.chiC_sixteen_div hκ]
    ring
  rw [e₃, e₄, e₅] at h₄
  exact h₄

theorem isConformal_ownComponentChart {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    (ownComponentChart w s).IsConformal :=
  (isConformal_loewner hw hw0 hs).trans Chart.isConformal_infinitySourceChart

/-! ### The record before the lifetime -/

section Record

variable {Ω : Type*} (s : ℝ≥0) {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- Before the lifetime the regularized driver is the driver. -/
theorem cfE_fst_of_lt (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) : (cfE s W ζ ω).1 t = W t ω := by
  have h0 : (fun t => cfKW W ζ t ω) 0 = 0 := by
    simp only [cfKW]
    split_ifs <;> simp [hW0]
  have hc : ContinuousOn (fun t => cfKW W ζ t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    hWc.congr fun t ht => by simp only [cfKW, show (t : ℝ≥0∞) < ζ ω from ht, ↓reduceIte]
  change (Theorem14.StagedReg.regularize (s : ℝ≥0∞) (fun t => cfKW W ζ t ω, ζ ω)).1 t = W t ω
  rw [Theorem14.StagedReg.regularize_eq_of_lt _ h0 hc ht]
  simp only [cfKW, ht, ↓reduceIte]

/-- **Before the lifetime the record is that of the driver**, read with an infinite lifetime. -/
theorem recOf_cfE_eq (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hs : (s : ℝ≥0∞) < ζ ω) : recOf (s : ℝ≥0∞) (cfE s W ζ ω) = recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤) := by
  have hmin : min (s : ℝ≥0∞) (cfE s W ζ ω).2 = s := by rw [cfE_snd]; exact min_eq_left hs.le
  have hmin' : min (s : ℝ≥0∞) (⊤ : ℝ≥0∞) = s := min_eq_left le_top
  unfold recOf
  congr 1
  unfold retOf
  refine Prod.ext (funext fun r => ?_) (Prod.ext ?_ ?_)
  · simp only [hmin, hmin']
    refine cfE_fst_of_lt s hW0 hWc ?_
    have hne : min (r : ℝ≥0∞) (s : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    rw [ENNReal.coe_toNNReal hne]
    exact (min_le_right _ _).trans_lt hs
  · simp only [hmin, hmin']
  · simp only [cfE_snd, decide_eq_false (not_le.2 hs), decide_eq_false (not_le.2 (ENNReal.coe_lt_top (r := s)))]

theorem rtime_recOf_cfE (hs : (s : ℝ≥0∞) < ζ ω) : rtime (recOf (s : ℝ≥0∞) (cfE s W ζ ω)) = s := by
  rw [rtime_recOf_coe, cfE_snd, min_eq_left hs.le, ENNReal.toNNReal_coe]

/-- **The record driver is the driver on `[0, s]`.** -/
theorem rdrv_recOf_cfE (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hs : (s : ℝ≥0∞) < ζ ω) {x : ℝ} (hx : x ≤ s) : rdrv (recOf (s : ℝ≥0∞) (cfE s W ζ ω)) x = W x.toNNReal ω := by
  have hreg : IsRegularDriver (cfE s W ζ ω) :=
    Theorem14.StagedReg.isRegularDriver_regularize (s : ℝ≥0∞) (fun t => cfKW W ζ t ω, ζ ω)
  have hfin : min (s : ℝ≥0∞) (cfE s W ζ ω).2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hmin : min (s : ℝ≥0∞) (cfE s W ζ ω).2 = s := by rw [cfE_snd]; exact min_eq_left hs.le
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (s : ℝ≥0∞) (cfE s W ζ ω).2 → (t : ℝ≥0∞) < ζ ω := fun t ht =>
    (ht.trans_eq hmin).trans_lt hs
  have hc : ContinuousOn (cfE s W ζ ω).1 {t | (t : ℝ≥0∞) ≤ min (s : ℝ≥0∞) (cfE s W ζ ω).2} :=
    (hWc.mono fun t ht => hle t ht).congr fun t ht => cfE_fst_of_lt s hW0 hWc (hle t ht)
  have hg := isDrvGood_of_continuousOn_le hreg hfin hc
  rw [rdrv_recOf_eq hreg hg hfin (by rw [rtime_recOf_cfE s hs]; exact hx)]
  refine cfE_fst_of_lt s hW0 hWc ((ENNReal.coe_le_coe.2 ?_).trans_lt hs)
  rcases le_or_gt x 0 with h | h
  · rw [Real.toNNReal_of_nonpos h]; exact zero_le
  · exact (Real.toNNReal_le_iff_le_coe).2 hx

/-- The record's flag reads the event `s < ζ`. -/
theorem flag_recOf_cfE : (recOf (s : ℝ≥0∞) (cfE s W ζ ω)).2.2 = false ↔ (s : ℝ≥0∞) < ζ ω := by
  change decide ((cfE s W ζ ω).2 ≤ (s : ℝ≥0∞)) = false ↔ _
  rw [cfE_snd, decide_eq_false_iff_not, not_le]

end Record

/-- **The record of a flow driver is measurable.** -/
theorem measurable_recOf_cfE {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (s : ℝ≥0) :
    Measurable (fun ω => cfE s Wα ζα ω) ∧ Measurable fun ω => recOf (s : ℝ≥0∞) (cfE s Wα ζα ω) := by
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hfl
  have hWa : AdaptedBefore 𝓕 ζα Wα := hC.1.2.1
  have hζm : Measurable ζα := Sec2.Assembly.measurable_lifetime hWa
  have hKm : ∀ t, Measurable (cfKW Wα ζα t) := fun t => Restart.measurable_ite_of_adaptedBefore hWa t
  have hEm : Measurable fun ω => cfE s Wα ζα ω :=
    (Theorem14.StagedReg.measurable_regularize _).comp ((measurable_pi_iff.2 hKm).prodMk hζm)
  exact ⟨hEm, measurable_recOf hEm (fun ω => Theorem14.StagedReg.isRegularDriver_regularize _ _) _⟩

/-! ### (R1): the conditional law of the returned record field -/

/-- **(R1) for the returned record field** (GB6: "the conditional Poisson mean is exactly the evolving finite word,
and its covariance is the zero-boundary Green kernel"). For a flow line of `h` with the data of the word `c` and an
admissible seed, conditionally on the record at the own time `s`, the record field returned through `R` (constant
`πχ`, lift coefficient `χ`) has the Gaussian characteristic functional of the conditional word. -/
theorem ae_condExp_returnRecField {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {c : BoundaryWord} (hfl : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    (s : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (returnField (Real.pi * chiC κ) (chiC κ)
        (recField κ (recOf (s : ℝ≥0∞) (cfE s Wα ζα ω')) (h ω')) φ : ℂ)) |
        MeasurableSpace.comap (fun ω' => recOf (s : ℝ≥0∞) (cfE s Wα ζα ω')) inferInstance] ω =
      gaussCF (gb6WordOfRec κ θ c (recOf (s : ℝ≥0∞) (cfE s Wα ζα ω))) φ := by
  set E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => cfE s Wα ζα ω with hEdef
  obtain ⟨hEm, -⟩ := measurable_recOf_cfE hfl s
  have hEreg : ∀ ω, IsRegularDriver (E ω) := fun ω => Theorem14.StagedReg.isRegularDriver_regularize _ _
  have hdrv := ae_driver_zero_continuousOn hfl
  have hfl₂ : IsFlowLineDriver κ c.fn c.jumps θ P h (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
    have e : (fun ω => (E ω).2) = ζα := funext fun ω => cfE_snd s Wα ζα ω
    rw [e]
    refine Theorem14.StagedReg.isFlowLineDriver_congr_ae hfl
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hEm)) ?_
    filter_upwards [hdrv] with ω hω
    exact ⟨(hEreg ω).2.1.trans hω.1.symm, fun t ht => cfE_fst_of_lt s hω.1 hω.2 ht⟩
  set φ' : TestOn upperHalfPlaneOpens := Chart.pushTest isConformal_infinityReturnChart φ with hφ'
  set C : ℂ := Complex.exp (Complex.I *
    ((Real.pi * chiC κ * (∫ w, φ w) + chiC κ * ∫ w, infinitySourceChart.2.2 w * φ w : ℝ) : ℂ)) with hC
  have h3 := ae_condExp_recField_of_admissible hκ c θ (s : ℝ≥0∞) P h E hEm hEreg hfl₂ hseed (-φ')
  have e : (fun ω' => Complex.exp (Complex.I * (returnField (Real.pi * chiC κ) (chiC κ)
      (recField κ (recOf (s : ℝ≥0∞) (E ω')) (h ω')) φ : ℂ))) =
      C • fun ω' => Complex.exp (Complex.I * (recField κ (recOf (s : ℝ≥0∞) (E ω')) (h ω') (-φ') : ℂ)) := by
    funext ω'
    rw [Pi.smul_apply, smul_eq_mul, hC, returnField_apply, map_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 := condExp_smul (μ := P)
    (m := MeasurableSpace.comap (fun ω' => recOf (s : ℝ≥0∞) (E ω')) inferInstance) C
    (fun ω' => Complex.exp (Complex.I * (recField κ (recOf (s : ℝ≥0∞) (E ω')) (h ω') (-φ') : ℂ)))
  filter_upwards [h3, h2] with ω e3 e2
  have hne : min (s : ℝ≥0∞) (E ω).2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [e, e2, Pi.smul_apply, smul_eq_mul, e3 hne]
  exact (gaussCF_retWord (isSorted_stopWord _ _) (Real.pi * chiC κ) (chiC κ) φ).symm

end GB6

end Supp8

end InteractingSLE
