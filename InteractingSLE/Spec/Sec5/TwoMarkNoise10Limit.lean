/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Regular

/-!
# Finite endpoints from announced noise martingales

Extract the existing target-change convergence argument from its maximal-path
wrapper. The abstract oscillation estimate is reused without modification.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓘 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {Q : ℕ → Ω → ℝ≥0}

/-- A bounded stopped noise with unit quadratic martingale has the expected second-moment bound. -/
theorem integral_sq_le_of_quadratic
    (hN : ∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω) 𝓘 P)
    (hN2 : ∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω ^ 2 - ((min u (Q n ω) : ℝ≥0) : ℝ)) 𝓘 P)
    (h0 : ∀ ω, N 0 ω = 0)
    (hb : ∀ n, ∃ C, ∀ u ω, |N (min u (Q n ω)) ω| ≤ C) (n : ℕ) (U : ℝ≥0) :
    ∫ ω, N (min U (Q n ω)) ω ^ 2 ∂P ≤ U := by
  have hM := hN2 n
  have hM1 := hN n
  let Y : Ω → ℝ := fun ω => N (min U (Q n ω)) ω
  let S : Ω → ℝ := fun ω => ((min U (Q n ω) : ℝ≥0) : ℝ)
  have hzero := hM.setIntegral_eq (zero_le (a := U)) (@MeasurableSet.univ _ (𝓘 0))
  simp only [Measure.restrict_univ, zero_min, h0, NNReal.coe_zero, sub_zero] at hzero
  obtain ⟨C, hC⟩ := hb n
  have hYm : StronglyMeasurable Y := (hM1.stronglyAdapted U).mono (𝓘.le U)
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
    refine Integrable.of_bound (hYm.aestronglyMeasurable.pow 2) (C ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC U ω) 2
  have hdiff : Integrable (fun ω => Y ω ^ 2 - S ω) P := hM.integrable U
  have hSi : Integrable S P := (hY2.sub hdiff).congr (ae_of_all _ fun ω => by
    dsimp only [Pi.sub_apply]
    ring)
  have hsplit : ∫ ω, Y ω ^ 2 ∂P = (∫ ω, (Y ω ^ 2 - S ω) ∂P) + ∫ ω, S ω ∂P := by
    rw [← integral_add hdiff hSi]
    congr 1
    funext ω
    ring
  have hz : ∫ ω, (Y ω ^ 2 - S ω) ∂P = 0 := by
    rw [← hzero]
    norm_num
  have hSle : ∫ ω, S ω ∂P ≤ U := by
    have h : ∫ ω, S ω ∂P ≤ ∫ _ω, (U : ℝ) ∂P :=
      integral_mono hSi (integrable_const _) fun ω => by exact_mod_cast min_le_left U (Q n ω)
    simpa using h
  rw [hsplit, hz, zero_add]
  exact hSle

/-- Announced continuous bounded noise martingales have a finite left limit at a finite lifetime. -/
theorem ae_tendsto_of_announced_noise {τ : Ω → ℝ≥0∞}
    (hQ : Coupling.IsAnnouncingSeq 𝓘 P τ Q)
    (hN : ∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω) 𝓘 P)
    (hN2 : ∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω ^ 2 - ((min u (Q n ω) : ℝ≥0) : ℝ)) 𝓘 P)
    (h0 : ∀ ω, N 0 ω = 0)
    (hc : ∀ n ω, Continuous fun u => N (min u (Q n ω)) ω)
    (hb : ∀ n, ∃ C, ∀ u ω, |N (min u (Q n ω)) ω| ≤ C) :
    ∀ᵐ ω ∂P, τ ω ≠ ⊤ → ∃ L : ℝ, Tendsto (N · ω) (𝓝[<] (τ ω).toNNReal) (𝓝 L) := by
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n u ω => N (min u (Q n ω)) ω
  have hYS : ∀ n t ω, Y n t ω = Y n (min t (Q n ω)) ω := fun n t ω => by
    simp only [Y, min_assoc, min_self]
  have hcons : ∀ n m, n ≤ m → ∀ t ω, Y n t ω = Y m (min t (Q n ω)) ω := by
    intro n m hnm t ω
    simp only [Y, min_assoc, min_eq_left (hQ.2.1 ω hnm)]
  have hosc : ∀ U : ℕ, ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m, n ≤ m →
      ⨆ i : Iic (U : ℝ≥0), ‖Y m i ω - Y n i ω‖ < 1 / ((k : ℝ) + 1) := fun U =>
    ae_osc_small hN hc hb hQ.1 hQ.2.1 hYS hcons (U : ℝ≥0)
      (fun n => integral_sq_le_of_quadratic hN hN2 h0 hb n U)
  filter_upwards [ae_all_iff.2 hosc, ae_all_iff.2 hQ.2.2.1, hQ.2.2.2] with ω hω hstrict hcof hfin
  let h := (τ ω).toNNReal
  have hhc : ((h : ℝ≥0) : ℝ≥0∞) = τ ω := ENNReal.coe_toNNReal hfin
  have hρ : ∀ n, Q n ω < h := fun n => by
    have hn := hstrict n
    rw [← hhc] at hn
    exact_mod_cast hn
  obtain ⟨U, hU⟩ := exists_nat_gt (h : ℝ)
  refine WangWu.exists_tendsto_nhdsLT_of_osc (f := (N · ω)) hρ fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hω U k
  refine ⟨n, fun r hr hrh => ?_⟩
  have hrτ : (r : ℝ≥0∞) < τ ω := by rw [← hhc]; exact_mod_cast hrh
  obtain ⟨m₀, hm₀⟩ := hcof r hrτ
  let m := max n m₀
  have hrm : r ≤ Q m ω := hm₀.trans (hQ.2.1 ω (le_max_right _ _))
  have h1 : Y m r ω = N r ω := by simp only [Y, min_eq_left hrm]
  have h2 : Y n r ω = N (Q n ω) ω := by simp only [Y, min_eq_right hr]
  have hrU : r ≤ (U : ℝ≥0) := by
    have hru : (r : ℝ) < U := lt_trans (by exact_mod_cast hrh) hU
    exact_mod_cast hru.le
  obtain ⟨C₁, hC₁⟩ := hb m
  obtain ⟨C₂, hC₂⟩ := hb n
  have hbdd : BddAbove (range fun i : Iic (U : ℝ≥0) => ‖Y m i ω - Y n i ω‖) :=
    ⟨C₁ + C₂, by
      rintro _ ⟨i, rfl⟩
      show ‖Y m i ω - Y n i ω‖ ≤ C₁ + C₂
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hC₁ i ω) (hC₂ i ω))⟩
  have hle : ‖Y m r ω - Y n r ω‖ ≤ ⨆ i : Iic (U : ℝ≥0), ‖Y m i ω - Y n i ω‖ :=
    le_ciSup (f := fun i : Iic (U : ℝ≥0) => ‖Y m i ω - Y n i ω‖) hbdd ⟨r, hrU⟩
  rw [h1, h2, Real.norm_eq_abs] at hle
  exact (hle.trans (hn m (le_max_left _ _)).le).trans hk.le

end InteractingSLE.Sec5.TwoMark.Noise10
