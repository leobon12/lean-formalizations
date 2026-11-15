/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawStmt
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# The staged conditional law: boundary data of the conditional fields

Packet PROVE-STAGEDLAW. The conditional field of a stage is described twice: through the induction (a GFF with the data
of a word read off the past) and through the flow-line coupling of the stage (`IsFlowLineDriver` with some data `b'`).
This file shows that the two data agree off a finite set, so that the flow-line coupling may be read with the word.

## Main results

* **`eq_of_isGFFWithBoundaryData`**: two piecewise-constant data of the same GFF agree off their jump candidates (the
  means agree as distributions, hence as harmonic functions, hence in their boundary limits);
* `flowDrvOf`, `isFlowLineDriver_eq_flowDrvOf`, **`isFlowLineDriver_congr_of_eqOn`**: `IsFlowLineDriver` sees the data
  only through its genuine jumps and one-sided limits;
* `BoundaryWord.shiftW`, `isGFFWithBoundaryData_shiftW`: recentring a word GFF;
* `integral_cexp_eq_gaussCF`: the characteristic functional of a word GFF.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart PiecewiseConstantBoundaryData

/-! ### One-sided limits of piecewise-constant data -/

theorem neBot_nhdsWithin_H_real (x : ℝ) : (𝓝[QuantumZipper.H] (x : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨x + (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
  · change 0 < ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, zero_add, mul_one]
    linarith
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

theorem leftLim_eq_of_notMem {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ}
    (hy : y ∉ J) : leftLim b y = b y := by
  have h : Tendsto b (𝓝[<] y) (𝓝 (b y)) :=
    (tendsto_const_nhds.congr' ((hb y hy).mono fun z hz => hz.symm)).mono_left nhdsWithin_le_nhds
  exact h.limUnder_eq

theorem rightLim_eq_of_notMem {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ}
    (hy : y ∉ J) : rightLim b y = b y := by
  have h : Tendsto b (𝓝[>] y) (𝓝 (b y)) :=
    (tendsto_const_nhds.congr' ((hb y hy).mono fun z hz => hz.symm)).mono_left nhdsWithin_le_nhds
  exact h.limUnder_eq

/-- The genuine jump set does not depend on the finite set of candidates. -/
theorem jumpSet_eq_of_subset {b : ℝ → ℝ} {J J' : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hJ : J ⊆ J') : jumpSet b J' = jumpSet b J := by
  ext y
  unfold jumpSet
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hne⟩
    by_cases hyJ : y ∈ J
    · exact ⟨hyJ, hne⟩
    · exact absurd ((leftLim_eq_of_notMem hb hyJ).trans (rightLim_eq_of_notMem hb hyJ).symm) hne
  · rintro ⟨hy, hne⟩
    exact ⟨hJ hy, hne⟩

/-! ### Two data of the same GFF -/

/-- **Two data of the same GFF agree off their exceptional sets**, as soon as both have bounded harmonic extensions. -/
theorem eq_of_isGFFWithBoundaryData' {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {g : Ω → DistOn upperHalfPlaneOpens} {b₁ b₂ : ℝ → ℝ} {S₁ S₂ : Set ℝ} {u₁ u₂ : ℂ → ℝ}
    (hu₁ : IsBoundedHarmonicExtension b₁ S₁ u₁) (hu₂ : IsBoundedHarmonicExtension b₂ S₂ u₂)
    (h₁ : IsGFFWithBoundaryData Q g b₁ S₁) (h₂ : IsGFFWithBoundaryData Q g b₂ S₂) :
    ∀ y : ℝ, y ∉ S₁ → y ∉ S₂ → b₁ y = b₂ y := by
  have X₁ := h₁.2 u₁ hu₁
  have X₂ := h₂.2 u₂ hu₂
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₁ z * φ z = ∫ z, u₂ z * φ z := by
    intro φ
    have i₁ : Integrable (fun ω => g ω φ - ∫ z, u₁ z * φ z) Q :=
      (X₁.gaussian.hasGaussianLaw_eval φ).integrable
    have c₁ := X₁.centered φ
    have c₂ := X₂.centered φ
    have hg : Integrable (fun ω => g ω φ) Q := by
      refine (i₁.add (integrable_const (∫ z, u₁ z * φ z))).congr (Eventually.of_forall fun ω => ?_)
      simp
    rw [integral_sub hg (integrable_const _), integral_const, probReal_univ, one_smul] at c₁ c₂
    linarith
  have heq : EqOn u₁ u₂ QuantumZipper.H :=
    Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hu₁.1 hu₂.1 fun φ _ => hmean φ
  intro y hy₁ hy₂
  have t₁ := hu₁.2.2 y hy₁
  have t₂ := hu₂.2.2 y hy₂
  have t₁' : Tendsto u₂ (𝓝[QuantumZipper.H] (y : ℂ)) (𝓝 (b₁ y)) :=
    t₁.congr' (eventually_nhdsWithin_of_forall fun z hz => heq hz)
  have := neBot_nhdsWithin_H_real y
  exact tendsto_nhds_unique t₁' t₂

/-- **Two piecewise-constant data of the same GFF agree off their jump candidates.** -/
theorem eq_of_isGFFWithBoundaryData {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {g : Ω → DistOn upperHalfPlaneOpens} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}
    (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁) (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂)
    (h₁ : IsGFFWithBoundaryData Q g b₁ J₁) (h₂ : IsGFFWithBoundaryData Q g b₂ J₂) :
    ∀ y ∉ J₁ ∪ J₂, b₁ y = b₂ y := by
  obtain ⟨u₁, hu₁, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb₁
  obtain ⟨u₂, hu₂, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb₂
  intro y hy
  exact eq_of_isGFFWithBoundaryData' hu₁ hu₂ h₁ h₂ y (by exact_mod_cast fun h => hy (Finset.mem_union_left _ h))
    (by exact_mod_cast fun h => hy (Finset.mem_union_right _ h))

/-! ### `IsFlowLineDriver` sees the data through its jumps and one-sided limits -/

/-- The body of the frozen `IsFlowLineDriver`, through the genuine jump set `S` and the one-sided limits `L`, `R`. -/
def flowDrvOf (κ : ℝ) (S : Finset ℝ) (L R : ℝ → ℝ) (θ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
    (VL : Fin ((S.filter (· < 0)).card + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin ((S.filter (0 < ·)).card + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsOptionalHullCoupling κ
      (Fin.cons 0 fun i => (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0)
      (Fin.cons 0 fun i => (S.filter (0 < ·)).orderEmbOfFin rfl i - 0)
      (Fin.cons (-(L 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
        let y := (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i)
        (R y - L y) / sleLambda κ)
      (Fin.cons ((R 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
        let y := (S.filter (0 < ·)).orderEmbOfFin rfl i
        (R y - L y) / sleLambda κ)
      P 𝓕 W VL VR B ζ h'

theorem isFlowLineDriver_eq_flowDrvOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) :
    IsFlowLineDriver κ b jumps θ P h W ζ = flowDrvOf κ (jumpSet b jumps) (leftLim b) (rightLim b) θ P h W ζ :=
  rfl

/-- **`IsFlowLineDriver` for data agreeing off a finite set.** -/
theorem isFlowLineDriver_congr_of_eqOn {κ θ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hb' : IsPiecewiseConstantBoundaryData b' J') (F : Finset ℝ)
    (heq : ∀ y ∉ F, b' y = b y) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    IsFlowLineDriver κ b' J' θ P h W ζ ↔ IsFlowLineDriver κ b J θ P h W ζ := by
  have hL : leftLim b' = leftLim b := Restart.leftLim_congr heq
  have hR : rightLim b' = rightLim b := Restart.rightLim_congr heq
  have hS : jumpSet b' J' = jumpSet b J := by
    rw [← jumpSet_eq_of_subset hb' (show J' ⊆ J ∪ J' from Finset.subset_union_right),
      ← jumpSet_eq_of_subset hb (show J ⊆ J ∪ J' from Finset.subset_union_left)]
    unfold jumpSet
    rw [hL, hR]
  rw [isFlowLineDriver_eq_flowDrvOf, isFlowLineDriver_eq_flowDrvOf, hS, hL, hR]

/-! ### Recentred words -/

namespace BoundaryWord

/-- The word of the data read after recentring at `a` (`y ↦ c.fn (y + a)`): positions moved by `-a`. -/
def shiftW (a : ℝ) (c : BoundaryWord) : BoundaryWord := (c.1, fun i => c.2.1 i - a, c.2.2)

theorem measurable_shiftW : Measurable fun p : ℝ × BoundaryWord => shiftW p.1 p.2 := by
  refine Measurable.prodMk (measurable_fst.comp measurable_snd) (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))).sub measurable_fst
  · exact measurable_snd.comp (measurable_snd.comp measurable_snd)

theorem fn_shiftW (a : ℝ) (c : BoundaryWord) (y : ℝ) : (shiftW a c).fn y = c.fn (y + a) := by
  unfold shiftW Restart.BoundaryWord.fn Restart.BoundaryWord.index
  simp only [sub_lt_iff_lt_add]

theorem jumps_shiftW (a : ℝ) (c : BoundaryWord) : (shiftW a c).jumps = c.jumps.image (· - a) := by
  unfold shiftW Restart.BoundaryWord.jumps
  rw [Finset.image_image]
  rfl

theorem isSorted_shiftW {c : BoundaryWord} (hc : c.IsSorted) (a : ℝ) : (shiftW a c).IsSorted := fun i j hij hj =>
  sub_le_sub_right (hc i j hij hj) a

end BoundaryWord

/-- **Recentring a word GFF.** -/
theorem isGFFWithBoundaryData_shiftW {c : BoundaryWord} (a : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : IsGFFWithBoundaryData P Y c.fn c.jumps) :
    IsGFFWithBoundaryData P (fun ω => flowField a 0 (Y ω)) (BoundaryWord.shiftW a c).fn
      (BoundaryWord.shiftW a c).jumps := by
  have h := Supp9.IsGFFWithBoundaryData.recenter c.isPiecewiseConstantBoundaryData a hY
  rw [BoundaryWord.jumps_shiftW]
  have e : (BoundaryWord.shiftW a c).fn = fun y => c.fn (y + a) := funext (BoundaryWord.fn_shiftW a c)
  rw [e]
  exact h

/-- **The characteristic functional of a GFF with a sorted word datum.** -/
theorem integral_cexp_eq_gaussCF {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} (hc : c.IsSorted)
    (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps) (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (Y ω φ : ℂ)) ∂Q = gaussCF c φ := by
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hmap := map_eq_of_isGFFWithBoundaryData hY (c.isGFFWithBoundaryData_gffLaw hc) hu
  rw [Measure.map_id] at hmap
  have hm : Measurable fun g : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (g φ : ℂ)) :=
    GFF.measurable_exp_I_mul (measurable_distOn_apply φ)
  rw [gaussCF_eq_integral, ← hmap, integral_map hY.1.aemeasurable hm.aestronglyMeasurable]

end StagedLaw

end Exist

end InteractingSLE
