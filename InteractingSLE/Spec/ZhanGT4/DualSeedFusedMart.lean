/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedDrift
import InteractingSLE.Spec.ZhanGT4.DualSeedLimitVersions

/-!
# The fused field's martingale and its entrance normalization

Packet PROVE-ZHAN-GT4-A22. Reuse the landed martingale of the shifted
random field. The initial logarithm is bounded and measurable at time
zero, so subtracting it gives a density with literal initial value one.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsDriftLogField
variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ}
  {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
  (h : IsDriftLogField 𝓕 σ ρ K B D b 0 S ℓ ℓx ℓxx ℓxxx ℓt)
include h

/-- The stopped exponential of a regular drifted log-field starting at
zero is a true martingale. This specializes the shifted-field theorem. -/
theorem martingale_exp_stopped_zero {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Martingale (fun (t : ℝ≥0) ω => Real.exp (ℓ ω (min t (S ω))
      (driftDriver σ B D ω (min t (S ω))))) 𝓕 P := by
  have h𝓕 : LP.LP4HB.shiftFiltration 𝓕 0 = 𝓕 := by
    apply Filtration.ext
    funext u
    exact congrArg 𝓕 (zero_add u)
  have hB' := LP.LP4HB.isFilteredBrownianReal_shift hB 0
  have hBc' : ∀ ω, Continuous (shiftBM B 0 · ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hS' : IsStoppingTime (LP.LP4HB.shiftFiltration 𝓕 0)
      (fun ω => ((S ω - 0 : ℝ≥0) : WithTop ℝ≥0)) := by simpa only [h𝓕, tsub_zero] using hS
  have hm := (h.isDriverLogField_shift hBc hρ).martingale_logFieldExp_stopped hB' hBc' hσ hρ hS'
  have he : (fun (t : ℝ≥0) ω => logFieldExp σ (shiftBM B 0) (shiftField ℓ σ B D 0)
      (min t (S ω - 0)) ω) = fun (t : ℝ≥0) ω => Real.exp (ℓ ω (min t (S ω))
        (driftDriver σ B D ω (min t (S ω)))) := by
    funext t ω
    simpa only [tsub_zero] using h.logFieldExp_shift (r := t) bot_le ω
  rw [he, h𝓕] at hm
  exact hm

/-- Normalize the entrance using its actual bounded time-zero value.
The initial value need only be measurable at time zero. -/
theorem sub_initial (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsDriftLogField 𝓕 σ ρ (2 * K) B D b 0 S
      (fun ω t x => ℓ ω t x - ℓ ω 0 (driftDriver σ B D ω 0)) ℓx ℓxx ℓxxx ℓt := by
  have hi (ω : Ω) : |ℓ ω 0 (driftDriver σ B D ω 0)| ≤ K :=
    (h.bound ω (0, driftDriver σ B D ω 0) ⟨⟨le_rfl, (S ω).coe_nonneg⟩, by
      simp only [sub_self, abs_zero]; positivity⟩).1
  have hm : Measurable[𝓕 0] fun ω => ℓ ω 0 (driftDriver σ B D ω 0) := by
    simpa only [zero_le, Set.ofPred_true, indicator_univ, NNReal.coe_zero] using h.meas0 0 bot_le
  have hK : K ≤ 2 * K := by linarith only [h.Knonneg]
  refine ⟨h.le, mul_nonneg (by norm_num) h.Knonneg, h.dD, h.contb, fun ω t ht => (h.bound_b ω t ht).trans hK,
    fun ω z hz => (h.dx ω z hz).sub_const _, h.dxx, h.dxxx,
    fun ω z hz => (h.dt ω z hz).sub_const _,
    fun ω => (h.cont ω).sub continuousOn_const, h.contX, h.contXX, h.contT, ?_, h.gen,
    ?_, h.meas1, h.meas2⟩
  · intro ω z hz
    obtain ⟨b0, b1, b2, b3, bt⟩ := h.bound ω z hz
    exact ⟨(abs_sub _ _).trans ((add_le_add b0 (hi ω)).trans_eq (by ring)),
      b1.trans hK, b2.trans hK, b3.trans hK, bt.trans hK⟩
  · intro u hu
    have hh := (h.meas0 u hu).sub
      ((hm.mono (𝓕.mono bot_le) le_rfl).indicator (measurableSet_ge_of_isStoppingTime hS u))
    convert hh using 1
    funext ω
    by_cases hω : ω ∈ {ω | u ≤ S ω}
    · simp only [indicator_of_mem hω, Pi.sub_apply]
    · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_self]

/-- The normalized exponential is a martingale with literal entrance one. -/
theorem normalized_martingale_zero {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Martingale (fun (t : ℝ≥0) ω => Real.exp (ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))) -
      ℓ ω 0 (driftDriver σ B D ω 0))) 𝓕 P ∧
      ∀ ω, Real.exp (ℓ ω (min (0 : ℝ≥0) (S ω)) (driftDriver σ B D ω (min (0 : ℝ≥0) (S ω))) -
        ℓ ω 0 (driftDriver σ B D ω 0)) = 1 := by
  exact ⟨(h.sub_initial hρ hS).martingale_exp_stopped_zero hB hBc hσ hρ hS,
    fun ω => by
      rw [NNReal.coe_zero, min_eq_left (S ω).coe_nonneg, sub_self, Real.exp_zero]⟩

/-- The normalized stopped exponential has continuous paths and a
deterministic bound, uniformly in time and sample. -/
theorem normalized_path_facts (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) :
    (∀ ω, Continuous (fun t : ℝ≥0 => Real.exp
      (ℓ ω (min (t : ℝ) (S ω)) (driftDriver σ B D ω (min (t : ℝ) (S ω))) -
        ℓ ω 0 (driftDriver σ B D ω 0)))) ∧
    ∀ (t : ℝ≥0) ω, |Real.exp
      (ℓ ω (min (t : ℝ) (S ω)) (driftDriver σ B D ω (min (t : ℝ) (S ω))) -
        ℓ ω 0 (driftDriver σ B D ω 0))| ≤ Real.exp (2 * K) := by
  have hmem (ω : Ω) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (S ω)) :
      (u, driftDriver σ B D ω u) ∈ driftTube σ B D 0 (S ω) (4 * ρ) ω :=
    ⟨hu, by simp only [sub_self, abs_zero]; positivity⟩
  have hpath (ω : Ω) : ContinuousOn
      (fun u : ℝ => ℓ ω u (driftDriver σ B D ω u)) (Icc 0 (S ω)) :=
    (h.cont ω).comp (continuousOn_id.prodMk (h.continuousOn_driftDriver hBc ω)) (hmem ω)
  refine ⟨fun ω => Real.continuous_exp.comp
    ((continuous_stopped_of_continuousOn hpath ω).sub continuous_const), ?_⟩
  intro t ω
  have hmin : min (t : ℝ) (S ω : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨le_min t.coe_nonneg (S ω).coe_nonneg, min_le_right _ _⟩
  have h0 := (h.bound ω (0, driftDriver σ B D ω 0) (hmem ω 0 ⟨le_rfl, (S ω).coe_nonneg⟩)).1
  have ht := (h.bound ω _ (hmem ω _ hmin)).1
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  exact (le_abs_self _).trans ((abs_sub _ _).trans ((add_le_add ht h0).trans_eq (by ring)))

end IsDriftLogField
end InteractingSLE.ZhanGT4
