/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Cond

/-!
# The local comparison of Aux. lemma 55: the Loewner Green cross energy

Packet PROVE-LOCEXT-A3 (step 5's kernel input). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L206,
p. 250): the conditional covariance of `(h(φ), (h, v))` off the hull is `G_{ℍ∖K_t}(φ, v) = ∫ φ · G_{ℍ∖K_t} v`.

For a continuous driver `W`, a time `t ≥ 0` and functions that are measurable, bounded, vanish off a compact subset
of `H̄` and off `ℍ ∖ K_t` (`IsGreenTest`):

* `greenCross W t φ ψ = ∬ φ(y) G(f_t y, f_t z) ψ(z)` (so `loewnerGreenEnergy W t φ = greenCross W t φ φ`);
* `greenH_fwdMap_mem_Icc`: `0 ≤ G(f_t y, f_t z) ≤ G_ℍ(y, z)` for distinct points alive at `t`;
* `integrable_crossKer`, `greenCross_eq_integral_crossKer`: the integrand is integrable on `ℂ × ℂ`;
* `greenCross_comm`, **`greenCross_combo`**: `E_t(aφ + bψ) = a² E_t(φ) + 2ab E_t(φ, ψ) + b² E_t(ψ)`;
* **`tendsto_greenCross`**: dominated convergence in the second slot;
* `isGreenTest_of_testOn`: test functions whose support avoids `K_t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn)

section Cross

variable {W : ℝ → ℝ} {t : ℝ} {φ ψ : ℂ → ℝ}

/-- **The Loewner Green cross energy** `E_t(φ, ψ) = ∬ φ(y) G_ℍ(f_t y, f_t z) ψ(z)`. -/
def greenCross (W : ℝ → ℝ) (t : ℝ) (φ ψ : ℂ → ℝ) : ℝ :=
  ∫ y, ∫ z, φ y * greenH (fwdMap W t y) (fwdMap W t z) * ψ z

theorem loewnerGreenEnergy_eq_greenCross (W : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) :
    loewnerGreenEnergy W t φ = greenCross W t φ φ := rfl

theorem greenCross_eq_integral_mul (W : ℝ → ℝ) (t : ℝ) (φ ψ : ℂ → ℝ) :
    greenCross W t φ ψ = ∫ y, φ y * ∫ z, greenH (fwdMap W t y) (fwdMap W t z) * ψ z := by
  unfold greenCross
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext z
  ring

/-- The functions handled by the cross energy: measurable, bounded, vanishing off a compact subset of `H̄` and off
`ℍ ∖ K_t`. -/
structure IsGreenTest (W : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) : Prop where
  measurable : Measurable φ
  bdd : ∃ C, ∀ z, |φ z| ≤ C
  compact : ∃ K, IsCompact K ∧ K ⊆ Hbar ∧ ∀ z, φ z ≠ 0 → z ∈ K
  alive : ∀ z, φ z ≠ 0 → z ∈ H \ fwdHull W t

theorem IsGreenTest.combo (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ) (a b : ℝ) :
    IsGreenTest W t fun z => a * φ z + b * ψ z := by
  obtain ⟨C₁, hC₁⟩ := hφ.bdd
  obtain ⟨C₂, hC₂⟩ := hψ.bdd
  obtain ⟨K₁, hK₁, hK₁H, hK₁s⟩ := hφ.compact
  obtain ⟨K₂, hK₂, hK₂H, hK₂s⟩ := hψ.compact
  have hor : ∀ z, a * φ z + b * ψ z ≠ 0 → φ z ≠ 0 ∨ ψ z ≠ 0 := fun z hz => by
    by_contra h
    push Not at h
    exact hz (by rw [h.1, h.2]; ring)
  refine ⟨(hφ.measurable.const_mul a).add (hψ.measurable.const_mul b), ⟨|a| * C₁ + |b| * C₂, fun z => ?_⟩,
    ⟨K₁ ∪ K₂, hK₁.union hK₂, union_subset hK₁H hK₂H, fun z hz => ?_⟩, fun z hz => ?_⟩
  · calc |a * φ z + b * ψ z| ≤ |a * φ z| + |b * ψ z| := abs_add_le _ _
      _ = |a| * |φ z| + |b| * |ψ z| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * C₁ + |b| * C₂ := add_le_add (mul_le_mul_of_nonneg_left (hC₁ z) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (hC₂ z) (abs_nonneg b))
  · rcases hor z hz with h | h
    · exact Or.inl (hK₁s z h)
    · exact Or.inr (hK₂s z h)
  · rcases hor z hz with h | h
    · exact hφ.alive z h
    · exact hψ.alive z h

/-- **Test functions avoiding the hull.** -/
theorem isGreenTest_of_testOn (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull W t)) :
    IsGreenTest W t φ := by
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  refine ⟨φ.continuous.measurable, ⟨C, fun z => ?_⟩, ⟨tsupport φ, φ.hasCompactSupport.isCompact,
    fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (Coupling.tsupport_subset_H φ hz),
    fun z hz => subset_tsupport _ hz⟩, fun z hz => ?_⟩
  · rw [← Real.norm_eq_abs]; exact hC z
  · have hz' := subset_tsupport _ hz
    exact ⟨Coupling.tsupport_subset_H φ hz', fun h => hφ.ne_of_mem hz' h rfl⟩

/-- **`0 ≤ G(f_t y, f_t z) ≤ G_ℍ(y, z)`** for distinct points alive at `t` (the Loewner Green identity (3.16) with
its nonnegative integrand). -/
theorem greenH_fwdMap_mem_Icc (hW : Continuous W) (ht : 0 ≤ t) {y z : ℂ} (hy : y ∈ H \ fwdHull W t)
    (hz : z ∈ H \ fwdHull W t) (hyz : y ≠ z) :
    0 ≤ greenH (fwdMap W t y) (fwdMap W t z) ∧ greenH (fwdMap W t y) (fwdMap W t z) ≤ greenH y z := by
  have hfy := Ito.im_fwdMap_pos hW ht hy ⟨ht, le_rfl⟩
  have hfz := Ito.im_fwdMap_pos hW ht hz ⟨ht, le_rfl⟩
  have hne : fwdMap W t y ≠ fwdMap W t z := fun he =>
    hyz (QuantumZipper.FwdHolo.injOn_fwdMap hW ht hy hz he)
  refine ⟨QuantumZipper.greenH_nonneg (le_of_lt hfy) (le_of_lt hfz) hne, ?_⟩
  rw [Ito.greenH_fwdMap_eq_sub_integral hW ht hy hz hyz, sub_le_self_iff]
  refine intervalIntegral.integral_nonneg ht fun u hu => ?_
  exact mul_nonneg_of_nonpos_of_nonpos (im_two_div_nonpos (Ito.im_fwdMap_pos hW ht hy hu).le)
    (im_two_div_nonpos (Ito.im_fwdMap_pos hW ht hz hu).le)

open Classical in
/-- `f_t` on `ℍ ∖ K_t`, `0` elsewhere (a measurable version). -/
def fwdAlive (W : ℝ → ℝ) (t : ℝ) : ℂ → ℂ := (H \ fwdHull W t).piecewise (fwdMap W t) fun _ => 0

theorem measurable_fwdAlive (hW : Continuous W) (ht : 0 ≤ t) : Measurable (fwdAlive W t) := by
  classical
  exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn.measurable_piecewise
    continuousOn_const (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).measurableSet

/-- The cross-energy integrand on `ℂ × ℂ` (with the measurable version of `f_t`). -/
def crossKer (W : ℝ → ℝ) (t : ℝ) (φ ψ : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  φ p.1 * greenH (fwdAlive W t p.1) (fwdAlive W t p.2) * ψ p.2

theorem crossKer_eq (hφ : ∀ z, φ z ≠ 0 → z ∈ H \ fwdHull W t) (hψ : ∀ z, ψ z ≠ 0 → z ∈ H \ fwdHull W t)
    (y z : ℂ) : φ y * greenH (fwdMap W t y) (fwdMap W t z) * ψ z = crossKer W t φ ψ (y, z) := by
  classical
  by_cases hy : φ y = 0
  · simp [crossKer, hy]
  by_cases hz : ψ z = 0
  · simp [crossKer, hz]
  simp only [crossKer, fwdAlive, Set.piecewise_eq_of_mem _ _ _ (hφ y hy), Set.piecewise_eq_of_mem _ _ _ (hψ z hz)]

theorem measurable_crossKer (hW : Continuous W) (ht : 0 ≤ t) (hφ : Measurable φ) (hψ : Measurable ψ) :
    Measurable (crossKer W t φ ψ) :=
  ((hφ.comp measurable_fst).mul (QuantumZipper.measurable_greenH.comp
    (((measurable_fwdAlive hW ht).comp measurable_fst).prodMk ((measurable_fwdAlive hW ht).comp measurable_snd)))).mul
    (hψ.comp measurable_snd)

/-- `|φ(y)| |ψ(z)| G_ℍ(y, z)` is integrable on `ℂ × ℂ`. -/
theorem integrable_abs_mul_abs_mul_greenH (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ) :
    Integrable (fun p : ℂ × ℂ => |φ p.1| * |ψ p.2| * greenH p.1 p.2) ((volume : Measure ℂ).prod volume) := by
  obtain ⟨C₁, hC₁⟩ := hφ.bdd
  obtain ⟨C₂, hC₂⟩ := hψ.bdd
  obtain ⟨K₁, hK₁, hK₁H, hK₁s⟩ := hφ.compact
  obtain ⟨K₂, hK₂, hK₂H, hK₂s⟩ := hψ.compact
  set g₁ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |φ z| with hg₁
  set g₂ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |ψ z| with hg₂
  have hg₁m : Measurable g₁ := ENNReal.measurable_ofReal.comp hφ.measurable.abs
  have hg₂m : Measurable g₂ := ENNReal.measurable_ofReal.comp hψ.measurable.abs
  have hadm₁ : QuantumZipper.IsAdmissibleH (volume.withDensity g₁) :=
    QuantumZipper.isAdmissibleH_withDensity hg₁m (M := ENNReal.ofReal C₁) ENNReal.ofReal_lt_top
      (fun z => ENNReal.ofReal_le_ofReal (hC₁ z)) hK₁ hK₁H fun z hz => by
        by_contra hne
        exact hz (hK₁s z fun h0 => hne (by simp [hg₁, h0]))
  have hadm₂ : QuantumZipper.IsAdmissibleH (volume.withDensity g₂) :=
    QuantumZipper.isAdmissibleH_withDensity hg₂m (M := ENNReal.ofReal C₂) ENNReal.ofReal_lt_top
      (fun z => ENNReal.ofReal_le_ofReal (hC₂ z)) hK₂ hK₂H fun z hz => by
        by_contra hne
        exact hz (hK₂s z fun h0 => hne (by simp [hg₂, h0]))
  have hI := QuantumZipper.integrable_greenH_prod hadm₁ hadm₂
  have hgg : Measurable fun p : ℂ × ℂ => g₁ p.1 * g₂ p.2 := (hg₁m.comp measurable_fst).mul (hg₂m.comp measurable_snd)
  rw [prod_withDensity hg₁m hg₂m] at hI
  have hI2 := (integrable_withDensity_iff hgg
    (ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).1 hI
  refine hI2.congr (ae_of_all _ fun p => ?_)
  show greenH p.1 p.2 * (g₁ p.1 * g₂ p.2).toReal = |φ p.1| * |ψ p.2| * greenH p.1 p.2
  rw [ENNReal.toReal_mul, hg₁, hg₂, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

theorem abs_crossKer_le (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ)
    {p : ℂ × ℂ} (hp : p.1 ≠ p.2) : |crossKer W t φ ψ p| ≤ |φ p.1| * |ψ p.2| * greenH p.1 p.2 := by
  by_cases hy : φ p.1 = 0
  · simp [crossKer, hy]
  by_cases hz : ψ p.2 = 0
  · simp [crossKer, hz]
  have hy' := hφ.alive _ hy
  have hz' := hψ.alive _ hz
  rw [← crossKer_eq hφ.alive hψ.alive p.1 p.2]
  obtain ⟨g0, g1⟩ := greenH_fwdMap_mem_Icc hW ht hy' hz' hp
  rw [abs_mul, abs_mul, abs_of_nonneg g0]
  calc |φ p.1| * greenH (fwdMap W t p.1) (fwdMap W t p.2) * |ψ p.2|
      ≤ |φ p.1| * greenH p.1 p.2 * |ψ p.2| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left g1 (abs_nonneg _)) (abs_nonneg _)
    _ = |φ p.1| * |ψ p.2| * greenH p.1 p.2 := by ring

theorem integrable_crossKer (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ) :
    Integrable (crossKer W t φ ψ) ((volume : Measure ℂ).prod volume) :=
  (integrable_abs_mul_abs_mul_greenH hφ hψ).mono'
    (measurable_crossKer hW ht hφ.measurable hψ.measurable).aestronglyMeasurable
    (ae_ne_prod.mono fun p hp => by rw [Real.norm_eq_abs]; exact abs_crossKer_le hW ht hφ hψ hp)

/-- **The cross energy as a product integral.** -/
theorem greenCross_eq_integral_crossKer (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ)
    (hψ : IsGreenTest W t ψ) :
    greenCross W t φ ψ = ∫ p, crossKer W t φ ψ p ∂((volume : Measure ℂ).prod volume) := by
  rw [integral_prod _ (integrable_crossKer hW ht hφ hψ), greenCross]
  congr 1; funext y; congr 1; funext z
  exact crossKer_eq hφ.alive hψ.alive y z

/-- **Symmetry of the cross energy.** -/
theorem greenCross_comm (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ) :
    greenCross W t φ ψ = greenCross W t ψ φ := by
  rw [greenCross_eq_integral_crossKer hW ht hφ hψ, greenCross_eq_integral_crossKer hW ht hψ hφ,
    ← integral_prod_swap]
  congr 1; funext p
  simp only [crossKer, Prod.fst_swap, Prod.snd_swap, QuantumZipper.greenH_symm (fwdAlive W t p.2)]
  ring

/-- **The quadratic expansion of the Loewner Green energy**:
`E_t(aφ + bψ) = a² E_t(φ) + 2ab E_t(φ, ψ) + b² E_t(ψ)`. -/
theorem greenCross_combo (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ) (hψ : IsGreenTest W t ψ)
    (a b : ℝ) :
    greenCross W t (fun z => a * φ z + b * ψ z) (fun z => a * φ z + b * ψ z) =
      a ^ 2 * greenCross W t φ φ + 2 * a * b * greenCross W t φ ψ + b ^ 2 * greenCross W t ψ ψ := by
  have hc := hφ.combo hψ a b
  have e : crossKer W t (fun z => a * φ z + b * ψ z) (fun z => a * φ z + b * ψ z) = fun p =>
      a ^ 2 * crossKer W t φ φ p + (a * b * crossKer W t φ ψ p + a * b * crossKer W t ψ φ p) +
        b ^ 2 * crossKer W t ψ ψ p := by
    funext p; simp only [crossKer]; ring
  have i1 := integrable_crossKer hW ht hφ hφ
  have i2 := integrable_crossKer hW ht hφ hψ
  have i3 := integrable_crossKer hW ht hψ hφ
  have i4 := integrable_crossKer hW ht hψ hψ
  have j1 : Integrable (fun p => a ^ 2 * crossKer W t φ φ p) ((volume : Measure ℂ).prod volume) := i1.const_mul _
  have j2 : Integrable (fun p => a * b * crossKer W t φ ψ p) ((volume : Measure ℂ).prod volume) := i2.const_mul _
  have j3 : Integrable (fun p => a * b * crossKer W t ψ φ p) ((volume : Measure ℂ).prod volume) := i3.const_mul _
  have j4 : Integrable (fun p => b ^ 2 * crossKer W t ψ ψ p) ((volume : Measure ℂ).prod volume) := i4.const_mul _
  have j23 : Integrable (fun p => a * b * crossKer W t φ ψ p + a * b * crossKer W t ψ φ p)
      ((volume : Measure ℂ).prod volume) := j2.add j3
  have j123 : Integrable (fun p => a ^ 2 * crossKer W t φ φ p +
      (a * b * crossKer W t φ ψ p + a * b * crossKer W t ψ φ p)) ((volume : Measure ℂ).prod volume) := j1.add j23
  rw [greenCross_eq_integral_crossKer hW ht hc hc, e, integral_add j123 j4, integral_add j1 j23,
    integral_add j2 j3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, ← greenCross_eq_integral_crossKer hW ht hφ hφ, ← greenCross_eq_integral_crossKer hW ht hφ hψ,
    ← greenCross_eq_integral_crossKer hW ht hψ hφ, ← greenCross_eq_integral_crossKer hW ht hψ hψ,
    greenCross_comm hW ht hψ hφ]
  ring

/-- **Dominated convergence in the second slot of the cross energy.** -/
theorem tendsto_greenCross (hW : Continuous W) (ht : 0 ≤ t) (hφ : IsGreenTest W t φ) {ψs : ℕ → ℂ → ℝ}
    {g : ℂ → ℝ} (hg : IsGreenTest W t g) (hψs : ∀ k, IsGreenTest W t (ψs k)) (hψ : IsGreenTest W t ψ)
    (hle : ∀ k z, |ψs k z| ≤ |g z|) (hlim : ∀ z, Tendsto (fun k => ψs k z) atTop (𝓝 (ψ z))) :
    Tendsto (fun k => greenCross W t φ (ψs k)) atTop (𝓝 (greenCross W t φ ψ)) := by
  simp_rw [greenCross_eq_integral_crossKer hW ht hφ (hψs _), greenCross_eq_integral_crossKer hW ht hφ hψ]
  refine tendsto_integral_of_dominated_convergence (fun p => |φ p.1| * |g p.2| * greenH p.1 p.2)
    (fun k => (measurable_crossKer hW ht hφ.measurable (hψs k).measurable).aestronglyMeasurable)
    (integrable_abs_mul_abs_mul_greenH hφ hg) (fun k => ae_ne_prod.mono fun p hp => ?_) (ae_of_all _ fun p => ?_)
  · rw [Real.norm_eq_abs]
    refine (abs_crossKer_le hW ht hφ (hψs k) hp).trans ?_
    by_cases hz : ψs k p.2 = 0
    · rw [hz, abs_zero, mul_zero, zero_mul]
      have hz' : g p.2 = 0 ∨ g p.2 ≠ 0 := em _
      rcases hz' with h0 | h0
      · rw [h0, abs_zero, mul_zero, zero_mul]
      by_cases hy : φ p.1 = 0
      · rw [hy, abs_zero, zero_mul, zero_mul]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (QuantumZipper.greenH_nonneg
        (show (0 : ℝ) ≤ p.1.im from le_of_lt (hφ.alive _ hy).1)
        (show (0 : ℝ) ≤ p.2.im from le_of_lt (hg.alive _ h0).1) hp)
    · have hg0 : g p.2 ≠ 0 := fun h0 => hz (abs_nonpos_iff.1 (h0 ▸ hle k p.2 |>.trans (by simp)))
      by_cases hy : φ p.1 = 0
      · rw [hy, abs_zero, zero_mul, zero_mul, zero_mul, zero_mul]
      have hG := QuantumZipper.greenH_nonneg (show (0 : ℝ) ≤ p.1.im from le_of_lt (hφ.alive _ hy).1)
        (show (0 : ℝ) ≤ p.2.im from le_of_lt (hg.alive _ hg0).1) hp
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle k p.2) (abs_nonneg _)) hG
  · exact (tendsto_const_nhds.mul (hlim p.2))

end Cross

end LocalExt

end InteractingSLE
