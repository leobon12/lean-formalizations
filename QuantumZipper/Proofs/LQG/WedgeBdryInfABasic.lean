import QuantumZipper.Proofs.LQG.InfiniteMass

/-!
# WEDGE-BDRY 4 (a): tools

* `ae_frequently_one_le_of_prob_small` (reverse Fatou for events, outer-measure form): if
  `P{a_n < 1}` is small for arbitrarily large `n`, then a.s. `a_n ≥ 1` for infinitely many `n`.
  No measurability of `a_n` is needed (`P` is an outer measure).
* `lintegral_Ici_one_eq_top_of_frequently`: if the dyadic windows `(2^n, 2^{n+1})` carry mass
  `≥ 1` infinitely often, the integral over `[1,∞)` is infinite.
* `tendsto_prob_drift`: for the free field and a drift `q > 0`,
  `P{X(fc(0,2^n)) − X(fc(0,1)) + q n log 2 ≤ L} → 0` (Chebyshev, variance `2 n log 2`); this
  generalizes `InfMass.tendsto_prob_Y` (drift `Q`) to an arbitrary positive drift.

All three are own elementary arguments (the route of handoff/WEDGE-BDRY.md item 4 (a)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper

namespace WedgeBdry

/-- Reverse Fatou for events, outer-measure form (own elementary proof). -/
theorem ae_frequently_one_le_of_prob_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (a : ℕ → Ω → ℝ≥0∞)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, P {ω | a n ω < 1} ≤ ε) :
    ∀ᵐ ω ∂P, ∃ᶠ n in atTop, 1 ≤ a n ω := by
  rw [ae_iff]
  have hsub : {ω | ¬ ∃ᶠ n in atTop, 1 ≤ a n ω} ⊆ ⋃ N : ℕ, ⋂ n ≥ N, {ω | a n ω < 1} := by
    intro ω hω
    simp only [mem_setOf_eq, not_frequently, not_le, eventually_atTop] at hω
    obtain ⟨N, hN⟩ := hω
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => hN n hn⟩
  refine measure_mono_null hsub (measure_iUnion_null fun N => ?_)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  obtain ⟨n, hn, hP⟩ := h ε (by exact_mod_cast hε) N
  rw [zero_add]
  exact (measure_mono (biInter_subset_of_mem (show n ∈ {n | n ≥ N} from hn))).trans hP

/-- Infinitely many dyadic windows of mass `≥ 1` force infinite mass on `[1,∞)`. -/
theorem lintegral_Ici_one_eq_top_of_frequently {ν : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (h : ∃ᶠ n in atTop, 1 ≤ ∫⁻ t in Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1)), f t ∂ν) :
    ∫⁻ t in Ici (1 : ℝ), f t ∂ν = ⊤ := by
  set A : ℕ → Set ℝ := fun n => Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1)) with hA
  have hd : Pairwise (Function.onFun Disjoint A) := by
    refine (pairwise_disjoint_on A).2 fun m n hmn => ?_
    refine Set.disjoint_left.2 fun t ht1 ht2 => ?_
    have : (2 : ℝ) ^ (m + 1) ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hmn
    simp only [hA, mem_Ioo] at ht1 ht2
    linarith [ht1.2, ht2.1]
  have hsub : (⋃ n, A n) ⊆ Ici 1 := iUnion_subset fun n t ht =>
    mem_Ici.2 ((one_le_pow₀ one_le_two).trans ht.1.le)
  have htsum : ∑' n, ∫⁻ t in A n, f t ∂ν = ⊤ := by
    by_contra hne
    have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
    have hev := ht.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))
    obtain ⟨n, h1, h2⟩ := (h.and_eventually hev).exists
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  rw [eq_top_iff, ← htsum, ← lintegral_iUnion (fun n => measurableSet_Ioo) hd]
  exact lintegral_mono_set hsub

section FreeField

open InfMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- Chebyshev bound for the dyadic circle-average increment with a positive drift `q`
(own elementary proof; the case `q = Q` is `InfMass.tendsto_prob_Y`). -/
theorem tendsto_prob_drift (hX : IsFreeGFFModConstH X P) {q : ℝ} (hq : 0 < q) (L : ℝ) :
    Tendsto (fun n : ℕ => P {ω | X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) -
      X ω fc01 + q * (n * Real.log 2) ≤ L}) atTop (𝓝 0) := by
  set a : ℝ := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos one_lt_two
  set d : ℝ := -L with hd
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|d| / (q * a))
  have hcpos : ∀ n : ℕ, N0 ≤ n → 0 < q * (n * a) + d := by
    intro n hn
    have h1 : |d| / (q * a) < n := hN0.trans_le (by exact_mod_cast hn)
    rw [div_lt_iff₀ (by positivity)] at h1
    have := neg_abs_le d
    nlinarith
  have hbound : ∀ n : ℕ, N0 ≤ n → P {ω | X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) -
      X ω fc01 + q * (n * a) ≤ L} ≤ ENNReal.ofReal (2 * (n * a) / (q * (n * a) + d) ^ 2) := by
    intro n hn
    have hb0 : (0 : ℝ) < 2 ^ n := by positivity
    have hb1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    set D : Ω → ℝ := WedgeTK.gaussFam X (dPair hb0) () with hD
    have hmem := WedgeTK.memLp_gaussFam hX (dPair hb0) ()
    have hmean : ∫ ω, D ω ∂P = 0 := WedgeTK.integral_gaussFam hX (dPair hb0) ()
    have hvar : variance D P = 2 * (n * a) := by
      rw [← covariance_self hmem.aemeasurable, WedgeTK.cov_gaussFam hX,
        kernelCov2_dPair hb1, ha, Real.log_pow]
    have hc := hcpos n hn
    have hcheb := meas_ge_le_variance_div_sq hmem hc
    rw [hmean, hvar] at hcheb
    refine le_trans (measure_mono fun ω hω => ?_) hcheb
    simp only [mem_setOf_eq] at hω ⊢
    have hDω : D ω = X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) - X ω fc01 := rfl
    rw [sub_zero, show WedgeTK.gaussFam X (dPair hb0) () ω = D ω from rfl, hDω,
      abs_of_nonpos (by rw [hd] at hc; linarith)]
    rw [hd]; linarith
  have hreal : Tendsto (fun n : ℕ => 2 * (n * a) / (q * (n * a) + d) ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have ht : Tendsto (fun n : ℕ => 2 * a * (1 / (n : ℝ)) / (q * a + d * (1 / (n : ℝ))) ^ 2)
        atTop (𝓝 (2 * a * 0 / (q * a + d * 0) ^ 2)) :=
      ((tendsto_const_nhds.mul hinv).div ((tendsto_const_nhds.add
        (tendsto_const_nhds.mul hinv)).pow 2)
        (by rw [mul_zero, add_zero]; exact pow_ne_zero _ (mul_pos hq ha0).ne'))
    simp only [mul_zero, zero_div] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop (max N0 1)] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hc := hcpos n ((le_max_left _ _).trans hn)
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hc0 : q * (n * a) + d ≠ 0 := hc.ne'
    have e1 : q * a + d * (1 / (n : ℝ)) = (q * (n * a) + d) / n := by field_simp
    rw [e1, div_pow]
    field_simp
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (n * a) / (q * (n * a) + d) ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨N0, hbound⟩)

end FreeField

end WedgeBdry

end QuantumZipper
