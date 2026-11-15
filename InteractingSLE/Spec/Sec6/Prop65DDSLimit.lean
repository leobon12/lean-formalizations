/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSDoob

/-!
# Proposition 6.5, Brownian representation, part 5: the limit over the localizations

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–159).

From the Doob bound of `Prop65DDSDoob`: along a fast subsequence `φ` of levels (chosen so that
`E[ℓ^∞_U] − E[ℓ^{φ k}_U] ≤ 32^{-k}` for all `U ≤ k`), Borel–Cantelli gives, almost surely, for every
`U`, eventually `sup_{u ≤ U} |N^{φ(k+1)}_u − N^{φ k}_u| ≤ 2^{-k}` (`exists_subseq_ae_cauchy`), hence
uniform convergence on compact time intervals to a continuous limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

/-- Uniform convergence on `s` from eventually geometric increments; the limit is `limUnder`. -/
lemma tendstoUniformlyOn_limUnder_of_geometric {f : ℕ → ℝ≥0 → ℝ} {s : Set ℝ≥0}
    (h : ∀ᶠ k in atTop, ∀ u ∈ s, |f (k + 1) u - f k u| ≤ (1 / 2 : ℝ) ^ k) :
    (∀ u ∈ s, Tendsto (fun k => f k u) atTop (𝓝 (limUnder atTop fun k => f k u))) ∧
      TendstoUniformlyOn f (fun u => limUnder atTop fun k => f k u) atTop s := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 h
  have hgeo : ∀ u ∈ s, ∀ n, dist (f (n + k₀) u) (f (n + 1 + k₀) u) ≤
      (1 / 2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n := by
    intro u hu n
    rw [Real.dist_eq, abs_sub_comm, show n + 1 + k₀ = (n + k₀) + 1 by ring, ← pow_add,
      add_comm k₀ n]
    exact hk₀ (n + k₀) (by omega) u hu
  have hconv : ∀ u ∈ s, Tendsto (fun k => f k u) atTop (𝓝 (limUnder atTop fun k => f k u)) := by
    intro u hu
    have hc := cauchySeq_of_le_geometric (1 / 2) ((1 / 2 : ℝ) ^ k₀) (by norm_num) (hgeo u hu)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL' : Tendsto (fun k => f k u) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat k₀).1 hL
    rwa [hL'.limUnder_eq]
  refine ⟨hconv, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  have hbd : ∀ u ∈ s, ∀ n, dist (f (n + k₀) u) (limUnder atTop fun k => f k u) ≤
      2 * (1 / 2 : ℝ) ^ (n + k₀) := by
    intro u hu n
    have := dist_le_of_le_geometric_of_tendsto (1 / 2) ((1 / 2 : ℝ) ^ k₀) (by norm_num)
      (hgeo u hu) ((tendsto_add_atTop_iff_nat k₀).2 (hconv u hu)) n
    refine this.trans (le_of_eq ?_)
    rw [pow_add]
    ring
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (N + k₀)] with k hk u hu
  obtain ⟨n, rfl⟩ : ∃ n, k = n + k₀ := ⟨k - k₀, by omega⟩
  rw [dist_comm]
  have h1 : (1 / 2 : ℝ) ^ (n + k₀) ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith [hbd u hu n]

section Levels

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

namespace IsDDSLevels

variable {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0 → Ω → ℝ} {ρ : ℕ → Ω → ℝ≥0} {K : ℕ → ℝ} {G : ℕ → Set Ω}
  {Y : ℕ → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ} {M : ℝ≥0 → Ω → ℝ}

/-- The flatness property of level `n` along `ω`. -/
def FlatAt (v : ℕ → ℝ≥0 → Ω → ℝ) (ρ : ℕ → Ω → ℝ≥0) (Y : ℕ → ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Prop :=
  ∀ s t, s ≤ t → clockA (v n) (ρ n) s ω = clockA (v n) (ρ n) t ω → Y n s ω = Y n t ω

/-- On flat paths of level `n` along which the path relations hold, the Doob process of `m ≤ n` is
the difference of the time-changed means. -/
theorem ae_doobD_eq (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {S : Set Ω} {m n : ℕ}
    (hmn : m ≤ n) :
    ∀ᵐ ω ∂P, ω ∈ G m → FlatAt v ρ Y n ω → ∀ u, doobD v ρ Y S m n u ω =
      S.indicator (fun ω => tcN (G n) (Y n) (v n) (ρ n) u ω - tcN (G m) (Y m) (v m) (ρ m) u ω) ω := by
  filter_upwards [L.path m, L.path n] with ω hm hn hGm hflat u
  have hGn : ω ∈ G n := L.mono_G hmn hGm
  by_cases hS : ω ∈ S
  · simp only [doobD, tcN, indicator_of_mem hS, indicator_of_mem hGm, indicator_of_mem hGn]
    set σn := lvlTime (v n) (ρ n) u ω
    set σm := lvlTime (v m) (ρ m) u ω
    have hσm : σm ≤ ρ m ω := IsGaussianExploration.lvlTime_le u ω
    have e1 : Y m σm ω - Y m 0 ω = Y n σm ω - Y n 0 ω := by
      rw [← hm hGm σm hσm, hn hGn σm (hσm.trans (L.mono_ρ ω hmn))]
    have hA1 := L.clockA_min_lvlTime hmn u ω
    have hA2 := L.clockA_lvlTime_level hmn u ω
    have e2 : Y n (min σn (ρ m ω)) ω = Y n σm ω := by
      rcases le_total (min σn (ρ m ω)) σm with h | h
      · exact hflat _ _ h (hA1.trans hA2.symm)
      · exact (hflat _ _ h (hA2.trans hA1.symm)).symm
    rw [e1, e2]
    ring
  · simp only [doobD, indicator_of_notMem hS]

theorem integrable_tcL (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) [IsProbabilityMeasure P] (k : ℕ)
    (U : ℝ≥0) : Integrable (tcL (v k) (ρ k) U) P :=
  Integrable.of_bound ((L.gauss k).measurable_tcL U |>.mono ((L.gauss k).tcFilt.le U)
    le_rfl).aestronglyMeasurable U (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((L.gauss k).tcL_nonneg U ω)]
      exact (L.gauss k).tcL_le U ω)

/-- `E[ℓ^k_U]`. -/
def cLev (v : ℕ → ℝ≥0 → Ω → ℝ) (ρ : ℕ → Ω → ℝ≥0) (P : Measure Ω) (U : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ ω, tcL (v k) (ρ k) U ω ∂P

theorem cLev_mono (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) [IsProbabilityMeasure P] (U : ℝ≥0) :
    Monotone (cLev v ρ P U) := fun m n hmn =>
  integral_mono (L.integrable_tcL m U) (L.integrable_tcL n U) fun ω => L.tcL_mono_level hmn U ω

theorem cLev_le (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) [IsProbabilityMeasure P] (U : ℝ≥0)
    (k : ℕ) : cLev v ρ P U k ≤ U := by
  have := integral_mono (L.integrable_tcL k U) (integrable_const (U : ℝ))
    fun ω => (L.gauss k).tcL_le U ω
  simpa [cLev] using this

/-- A fast subsequence of levels: `E[ℓ^n_U] − E[ℓ^{φ k}_U] ≤ 32^{-k}` for `U ≤ k ≤ φ k ≤ n`. -/
theorem exists_fast_subseq (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) [IsProbabilityMeasure P] :
    ∃ φ : ℕ → ℕ, Monotone φ ∧ (∀ k, k ≤ φ k) ∧ ∀ k (U : ℕ), U ≤ k → ∀ n, φ k ≤ n →
      cLev v ρ P U n - cLev v ρ P U (φ k) ≤ (1 / 32 : ℝ) ^ k := by
  classical
  set c : ℕ → ℕ → ℝ := fun U k => cLev v ρ P U k with hc
  have hbdd : ∀ U : ℕ, BddAbove (range (c U)) := fun U =>
    ⟨U, by rintro _ ⟨k, rfl⟩; exact L.cLev_le U k⟩
  set cI : ℕ → ℝ := fun U => ⨆ k, c U k with hcI
  have hlim : ∀ U : ℕ, Tendsto (c U) atTop (𝓝 (cI U)) := fun U =>
    tendsto_atTop_ciSup (L.cLev_mono U) (hbdd U)
  have hle : ∀ (U : ℕ) n, c U n ≤ cI U := fun U n => le_ciSup (hbdd U) n
  set Q : ℕ → ℕ → Prop := fun k n => ∀ U : ℕ, U ≤ k → cI U - c U n ≤ (1 / 32 : ℝ) ^ k with hQ
  have hQex : ∀ k, ∃ n, Q k n := by
    intro k
    have h1 : ∀ U : ℕ, ∀ᶠ n in atTop, cI U - c U n ≤ (1 / 32 : ℝ) ^ k := by
      intro U
      filter_upwards [(hlim U).eventually (lt_mem_nhds (sub_lt_self (cI U)
        (pow_pos (by norm_num : (0 : ℝ) < 1 / 32) k)))] with n hn
      linarith
    have h2 := (eventually_all_finset (Finset.range (k + 1))).2 fun U _ => h1 U
    obtain ⟨n, hn⟩ := h2.exists
    exact ⟨n, fun U hU => hn U (Finset.mem_range.2 (Nat.lt_succ_of_le hU))⟩
  have hQup : ∀ k n n', Q k n → n ≤ n' → Q k n' := fun k n n' hkn hnn' U hU => by
    have := L.cLev_mono U hnn'
    have h := hkn U hU
    simp only [hc] at this h ⊢
    linarith
  set ψ : ℕ → ℕ := fun k => Nat.find (hQex k) with hψ
  refine ⟨fun k => max k (ψ k), fun k k' hkk' => max_le_max hkk' (Nat.find_mono fun n hn U hU =>
    (hn U (hU.trans hkk')).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk')),
    fun k => le_max_left _ _, fun k U hU n hn => ?_⟩
  have hQk : Q k (max k (ψ k)) := hQup k _ _ (Nat.find_spec (hQex k)) (le_max_right _ _)
  have := hQk U hU
  have h2 := hle U n
  simp only [hc] at this h2 ⊢
  linarith

/-- **Almost sure uniform Cauchy property** of the time-changed means along a subsequence of
levels: almost surely, for every `U`, eventually `sup_{u ≤ U} |N^{φ(k+1)}_u − N^{φ k}_u| ≤ 2^{-k}`. -/
theorem exists_subseq_ae_cauchy [IsProbabilityMeasure P] (L : IsDDSLevels P 𝓕 X v ρ K G Y a M)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) :
    ∃ φ : ℕ → ℕ, Monotone φ ∧ (∀ k, k ≤ φ k) ∧ ∀ᵐ ω ∂P, ∀ U : ℕ, ∀ᶠ k in atTop,
      ∀ u : ℝ≥0, u ≤ U →
        |tcN (G (φ (k + 1))) (Y (φ (k + 1))) (v (φ (k + 1))) (ρ (φ (k + 1))) u ω -
          tcN (G (φ k)) (Y (φ k)) (v (φ k)) (ρ (φ k)) u ω| ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨φ, hφm, hφk, hφc⟩ := L.exists_fast_subseq
  have hflatE : ∀ n, ∃ E : Set Ω, MeasurableSet[𝓕 0] E ∧ P Eᶜ = 0 ∧
      ∀ ω ∈ E, FlatAt v ρ Y n ω :=
    fun n => exists_measurableSet_zero_of_ae hnull ((L.gauss n).ae_flat (L.version n))
  choose E hEm hE0 hEf using hflatE
  set S : ℕ → Set Ω := fun k => G (φ k) ∩ E (φ (k + 1)) with hS
  have hSm : ∀ k, MeasurableSet[𝓕 0] (S k) := fun k => (L.measurableSet_G _).inter (hEm _)
  have hmn : ∀ k, φ k ≤ φ (k + 1) := fun k => hφm (Nat.le_succ k)
  have hSflat : ∀ k, ∀ ω ∈ S k, FlatAt v ρ Y (φ (k + 1)) ω := fun k ω hω => hEf _ ω hω.2
  set D : ℕ → ℝ≥0 → Ω → ℝ := fun k => doobD v ρ Y (S k) (φ k) (φ (k + 1)) with hD
  have hsupm : ∀ k (U : ℕ), Measurable fun ω => ⨆ u : Icc (0 : ℝ≥0) U, ‖D k u ω‖ₑ :=
    fun k U => measurable_iSup_Icc
      (fun ω => continuous_enorm.comp (L.continuous_doobD (hmn k) (hSflat k) ω))
      (fun u => (((L.martingale_doobD hnull (hSm k) (hmn k)).stronglyAdapted u).measurable.mono
        ((L.gauss _).tcFilt.le u) le_rfl).enorm) U
  set Bad : ℕ → ℕ → Set Ω := fun U k =>
    {ω | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) < ⨆ u : Icc (0 : ℝ≥0) U, ‖D k u ω‖ₑ} with hBad
  -- the probability of a bad event
  have hbad : ∀ (U : ℕ) k, U ≤ k → P (Bad U k) ≤ ENNReal.ofReal (24 * U * (1 / 2 : ℝ) ^ k) := by
    intro U k hUk
    have hε0 : (0 : ℝ) < ((1 / 2 : ℝ) ^ k) ^ 4 := by positivity
    have hsub : Bad U k ⊆ {ω | ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ 4) ≤
        (⨆ u : Icc (0 : ℝ≥0) U, ‖D k u ω‖ₑ) ^ (4 : ℝ)} := by
      intro ω hω
      simp only [hBad, mem_ofPred_eq] at hω ⊢
      rw [show ((1 / 2 : ℝ) ^ k) ^ 4 = ((1 / 2 : ℝ) ^ k) ^ (4 : ℝ) by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      exact ENNReal.rpow_le_rpow hω.le (by norm_num)
    have hmark := meas_ge_le_lintegral_div (μ := P)
      (((hsupm k U).pow_const (4 : ℝ)).aemeasurable)
      (ENNReal.ofReal_pos.2 hε0).ne' ENNReal.ofReal_ne_top
    have hdoob := L.lintegral_iSup_doobD_le hnull (hSm k) (hmn k) (hSflat k) U
    have hδ : cLev v ρ P U (φ (k + 1)) - cLev v ρ P U (φ k) ≤ (1 / 32 : ℝ) ^ k :=
      hφc k U hUk _ (hmn k)
    have hδ0 : 0 ≤ cLev v ρ P U (φ (k + 1)) - cLev v ρ P U (φ k) :=
      sub_nonneg.2 (L.cLev_mono U (hmn k))
    refine (measure_mono hsub).trans (hmark.trans ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), ← ENNReal.ofReal_mul
      (by positivity)] at hdoob
    refine (ENNReal.div_le_div_right hdoob _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hε0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hε0]
    have h43 : (4 / 3 : ℝ) ^ (4 : ℝ) ≤ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg U
    have hkey : (1 / 32 : ℝ) ^ k = (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ 4 := by
      rw [← pow_mul, ← pow_add]
      rw [show (1 / 32 : ℝ) = (1 / 2) ^ 5 by norm_num, ← pow_mul]
      ring_nf
    calc (4 / 3 : ℝ) ^ (4 : ℝ) * (6 * U * (cLev v ρ P U (φ (k + 1)) - cLev v ρ P U (φ k)))
        ≤ 4 * (6 * U * (1 / 32 : ℝ) ^ k) := by gcongr
      _ = 24 * U * (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ 4 := by rw [hkey]; ring
  -- Borel–Cantelli, for each `U`
  have hBC : ∀ U : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Bad U k := by
    intro U
    have hsum : ∑' k, P (Bad U (k + U)) ≠ ∞ := by
      have hle : ∀ k, P (Bad U (k + U)) ≤ ENNReal.ofReal (24 * U * (1 / 2 : ℝ) ^ k) := by
        intro k
        refine (hbad U (k + U) (Nat.le_add_left U k)).trans (ENNReal.ofReal_le_ofReal ?_)
        have h1 : (1 / 2 : ℝ) ^ (k + U) ≤ (1 / 2) ^ k :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right k U)
        have hU0 : (0 : ℝ) ≤ 24 * U := by positivity
        exact mul_le_mul_of_nonneg_left h1 hU0
      have hsum' : Summable fun k : ℕ => 24 * (U : ℝ) * (1 / 2 : ℝ) ^ k :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum']
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hω
    filter_upwards [eventually_ge_atTop (k₀ + U)] with k hk
    have := hk₀ (k - U) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hBC' : ∀ᵐ ω ∂P, ∀ U : ℕ, ∀ᶠ k in atTop, ω ∉ Bad U k := ae_all_iff.2 hBC
  have hcons : ∀ᵐ ω ∂P, ∀ k, ω ∈ G (φ k) → FlatAt v ρ Y (φ (k + 1)) ω → ∀ u, D k u ω =
      (S k).indicator (fun ω => tcN (G (φ (k + 1))) (Y (φ (k + 1))) (v (φ (k + 1)))
        (ρ (φ (k + 1))) u ω - tcN (G (φ k)) (Y (φ k)) (v (φ k)) (ρ (φ k)) u ω) ω :=
    ae_all_iff.2 fun k => L.ae_doobD_eq (S := S k) (hmn k)
  have hEall : ∀ᵐ ω ∂P, ∀ n, ω ∈ E n := ae_all_iff.2 fun n => ae_iff.2 (hE0 n)
  refine ⟨φ, hφm, hφk, ?_⟩
  filter_upwards [hBC', hcons, hEall] with ω hBCω hconsω hEω U
  by_cases hω : ∃ n₀, ω ∈ G n₀
  · obtain ⟨n₀, hn₀⟩ := hω
    filter_upwards [hBCω U, eventually_ge_atTop n₀] with k hk hkn u hu
    have hGk : ω ∈ G (φ k) := L.mono_G (hkn.trans (hφk k)) hn₀
    have hSk : ω ∈ S k := ⟨hGk, hEω _⟩
    have hDeq := hconsω k hGk (hEf _ ω (hEω _)) u
    rw [indicator_of_mem hSk] at hDeq
    rw [← hDeq]
    simp only [hBad, mem_ofPred_eq, not_lt] at hk
    have h1 : ‖D k u ω‖ₑ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
      (le_iSup (fun u' : Icc (0 : ℝ≥0) U => ‖D k u' ω‖ₑ) ⟨u, zero_le, hu⟩).trans hk
    rw [Real.enorm_eq_ofReal_abs] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  · push Not at hω
    refine Eventually.of_forall fun k u _ => ?_
    simp [tcN, indicator_of_notMem (hω _)]

end IsDDSLevels

end Levels

end InteractingSLE.Sec6.Prop65
