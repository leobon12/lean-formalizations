import GaussianLQG.LQG.Localization.Deterministic

/-!
# Tail of the localization radius `T` (blueprint Lemma `lem:T-B`, moments, first part)

Generic tools for `ℝ≥0∞`-valued random variables:

* `measure_le_le_of_moments`: if `E[Y^{4N}] ≤ C_Y` and `E[X^{-4N}] ≤ C_X R^{-2N}`, then
  `P[X ≤ Y] ≤ (C_Y + C_X) R^{-N}` (split at `R^{1/4}` and use Markov's inequality twice);
* the Cauchy–Schwarz inequalities `lintegral_rpow_mul_rpow_le`, `lintegral_mul_indicator_one_le` and
  `lintegral_le_rpow_lintegral_sq`;
* geometric series bounds `tsum_mul_pow_ne_top`, `ofReal_two_pow_mul_rpow`, `sqrt_mul_pow_mul`.

Specific to the localization lemma: `U ≤ diam(K)^{1/2} A_γ(K)` (`Setup.locU_le_holderConst_mul`),
the tail bound `P[L_R ≤ U] ≤ C R^{-N}` (`Setup.measure_annulusCross_le_locU`), and the pointwise
dyadic decompositions of `T^p` and of `A_γ(B̄_T(0))^q` (`Setup.locT_rpow_le`,
`Setup.holderConst_locT_rpow_le`), as in the blueprint proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-! ## Real-exponent bookkeeping -/

theorem two_pow_rpow_comm (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm, Real.rpow_mul zero_le_two,
    Real.rpow_natCast]

/-- `(2^j a)^q = a^q (2^q)^j` inside `ofReal`. -/
theorem ofReal_two_pow_mul_rpow (j : ℕ) {a : ℝ} (ha : 0 ≤ a) (q : ℝ) :
    ENNReal.ofReal (((2 : ℝ) ^ j * a) ^ q) =
      ENNReal.ofReal (a ^ q) * ENNReal.ofReal (2 ^ q) ^ j := by
  rw [Real.mul_rpow (by positivity) ha, two_pow_rpow_comm, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), mul_comm]

/-- `(r^j)^z = (r^z)^j` in `ℝ≥0∞`. -/
theorem ENNReal_pow_rpow_comm (r : ℝ≥0∞) (j : ℕ) (z : ℝ) : (r ^ j) ^ z = (r ^ z) ^ j := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm, ENNReal.rpow_mul, ENNReal.rpow_natCast]

/-- `(a r^j)^{1/2} (b s^j)^{1/2} = (ab)^{1/2} ((rs)^{1/2})^j`. -/
theorem sqrt_mul_pow_mul (a b r s : ℝ≥0∞) (j : ℕ) :
    (a * r ^ j) ^ (1 / 2 : ℝ) * (b * s ^ j) ^ (1 / 2 : ℝ) =
      (a * b) ^ (1 / 2 : ℝ) * ((r * s) ^ (1 / 2 : ℝ)) ^ j := by
  have h : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ h, ENNReal.mul_rpow_of_nonneg _ _ h,
    ENNReal.mul_rpow_of_nonneg a b h, ENNReal.mul_rpow_of_nonneg r s h, mul_pow,
    ENNReal_pow_rpow_comm r, ENNReal_pow_rpow_comm s]
  ring

/-- A geometric series with ratio `< 1` and finite coefficient is finite. -/
theorem tsum_mul_pow_ne_top {c r : ℝ≥0∞} (hc : c ≠ ⊤) (hr : r < 1) :
    ∑' j : ℕ, c * r ^ j ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top hc (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')

/-- `ofReal (2^a) < 1` for `a < 0`. -/
theorem ofReal_two_rpow_lt_one {a : ℝ} (ha : a < 0) : ENNReal.ofReal ((2 : ℝ) ^ a) < 1 :=
  ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two ha)

/-- `ofReal (2^a) ofReal (2^b) = ofReal (2^{a+b})`. -/
theorem ofReal_two_rpow_mul (a b : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ a) * ENNReal.ofReal ((2 : ℝ) ^ b) =
      ENNReal.ofReal ((2 : ℝ) ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos]

/-! ## Generic probabilistic tools -/

section generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `ofReal (R^{1/4})^{4N} = ofReal (R^N)`. -/
theorem ofReal_rpow_quarter_rpow {R : ℝ} (hR : 0 ≤ R) {N : ℝ} (hN : 0 ≤ N) :
    ENNReal.ofReal (R ^ (1 / 4 : ℝ)) ^ (4 * N) = ENNReal.ofReal (R ^ N) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hR]
  congr 2
  ring

/-- **Comparison through moments.** If `E[Y^{4N}] ≤ C_Y` and `E[X^{-4N}] ≤ C_X R^{-2N}`, then
`P[X ≤ Y] ≤ (C_Y + C_X) R^{-N}` (blueprint, proof of Lemma `lem:T-B`: split at `R^{1/4}`). -/
theorem measure_le_le_of_moments {X Y : Ω → ℝ≥0∞} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {N R : ℝ} (hN : 0 < N) (hR : 0 < R) {CY : ℝ≥0∞} (hYm : ∫⁻ ω, Y ω ^ (4 * N) ∂μ ≤ CY)
    {CX : ℝ} (hCX : 0 ≤ CX)
    (hXm : ∫⁻ ω, (X ω)⁻¹ ^ (4 * N) ∂μ ≤ ENNReal.ofReal (CX * R ^ (-(2 * N)))) :
    μ {ω | X ω ≤ Y ω} ≤ (CY + ENNReal.ofReal CX) * ENNReal.ofReal (R ^ (-N)) := by
  set t := ENNReal.ofReal (R ^ (1 / 4 : ℝ)) with ht
  have htpos : 0 < R ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hR _
  have ht0 : t ≠ 0 := by rw [ht, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact htpos
  have htt : t ^ (4 * N) = ENNReal.ofReal (R ^ N) := ofReal_rpow_quarter_rpow hR.le hN.le
  have h4N : 0 < 4 * N := by linarith
  have hsub : {ω | X ω ≤ Y ω} ⊆ {ω | t ≤ Y ω} ∪ {ω | X ω ≤ t} := by
    intro ω (hω : X ω ≤ Y ω)
    by_cases h : t ≤ Y ω
    · exact Or.inl h
    · exact Or.inr (hω.trans (not_le.1 h).le)
  have h1 : μ {ω | t ≤ Y ω} ≤ CY * ENNReal.ofReal (R ^ (-N)) := by
    refine (measure_ge_le_inv_rpow_mul_lintegral_rpow hY h4N ht0 ENNReal.ofReal_ne_top).trans ?_
    rw [htt, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR N), ← Real.rpow_neg hR.le,
      mul_comm]
    gcongr
  have h2 : μ {ω | X ω ≤ t} ≤ ENNReal.ofReal CX * ENNReal.ofReal (R ^ (-N)) := by
    refine (measure_le_le_rpow_mul_lintegral_inv_rpow hX h4N ht0 ENNReal.ofReal_ne_top).trans ?_
    rw [htt]
    calc ENNReal.ofReal (R ^ N) * ∫⁻ ω, (X ω)⁻¹ ^ (4 * N) ∂μ
        ≤ ENNReal.ofReal (R ^ N) * ENNReal.ofReal (CX * R ^ (-(2 * N))) := by gcongr
      _ = ENNReal.ofReal CX * ENNReal.ofReal (R ^ (-N)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCX]
        congr 1
        rw [mul_left_comm, ← Real.rpow_add hR]
        congr 2
        ring
  calc μ {ω | X ω ≤ Y ω} ≤ μ ({ω | t ≤ Y ω} ∪ {ω | X ω ≤ t}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ Y ω} + μ {ω | X ω ≤ t} := measure_union_le _ _
    _ ≤ CY * ENNReal.ofReal (R ^ (-N)) + ENNReal.ofReal CX * ENNReal.ofReal (R ^ (-N)) :=
        add_le_add h1 h2
    _ = (CY + ENNReal.ofReal CX) * ENNReal.ofReal (R ^ (-N)) := by ring

/-- **Cauchy–Schwarz**: `E[f^q g^q] ≤ E[f^{2q}]^{1/2} E[g^{2q}]^{1/2}`. -/
theorem lintegral_rpow_mul_rpow_le {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {q : ℝ} :
    ∫⁻ ω, f ω ^ q * g ω ^ q ∂μ ≤
      (∫⁻ ω, f ω ^ (2 * q) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ ω, g ω ^ (2 * q) ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (hf.pow_const q)
    (hg.pow_const q)
  have e : ∀ x : ℝ≥0∞, (x ^ q) ^ (2 : ℝ) = x ^ (2 * q) := fun x => by
    rw [← ENNReal.rpow_mul, mul_comm]
  simp only [Pi.mul_apply, e] at h
  exact h

/-- **Cauchy–Schwarz with an indicator**: `E[f 1_s] ≤ E[f²]^{1/2} P(s)^{1/2}`. -/
theorem lintegral_mul_indicator_one_le {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {s : Set Ω}
    (hs : MeasurableSet s) :
    ∫⁻ ω, f ω * s.indicator 1 ω ∂μ ≤
      (∫⁻ ω, f ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ s ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    ((measurable_one.indicator hs).aemeasurable)
  have e : ∀ ω, (s.indicator (1 : Ω → ℝ≥0∞) ω) ^ (2 : ℝ) = s.indicator 1 ω := fun ω => by
    by_cases hω : ω ∈ s
    · rw [indicator_of_mem hω, Pi.one_apply, ENNReal.one_rpow]
    · rw [indicator_of_notMem hω, ENNReal.zero_rpow_of_pos two_pos]
  simp only [Pi.mul_apply, e, lintegral_indicator_one hs] at h
  exact h

/-- **Jensen / Cauchy–Schwarz** for a probability measure: `E[f] ≤ E[f²]^{1/2}`. -/
theorem lintegral_le_rpow_lintegral_sq [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f ω ∂μ ≤ (∫⁻ ω, f ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h := lintegral_mul_indicator_one_le hf (s := univ) MeasurableSet.univ
  simp only [indicator_univ, Pi.one_apply, mul_one, measure_univ, ENNReal.one_rpow] at h
  exact h

/-- `max (a, b)^p ≤ a^p + b^p`. -/
theorem max_rpow_le_add (a b : ℝ≥0∞) (p : ℝ) : max a b ^ p ≤ a ^ p + b ^ p := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_self
  · rw [max_eq_left h]
    exact le_self_add

end generic

/-! ## The tail of `T` -/

theorem locR0_mul_lt (K : Set ℂ) (j : ℕ) :
    2 * (2 ^ j * locR0 K) < 2 * (2 ^ (j + 1) * locR0 K) := by
  have h1 : (2 : ℝ) ^ j < 2 ^ (j + 1) := pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self j)
  have h2 := locR0_pos K
  nlinarith

theorem one_le_two_mul_locR0 (K : Set ℂ) (j : ℕ) : 1 ≤ 2 * (2 ^ j * locR0 K) := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have h2 := one_le_locR0 K
  nlinarith

namespace Setup

variable {S : Setup} {γ : ℝ} {K : Set ℂ} {δ : ℝ}

/-- `U ≤ A_γ(K) diam(K)^{1/2}` (blueprint, proof of Lemma `lem:T-B`). -/
theorem locU_le_holderConst_mul (hK : Bornology.IsBounded K) (ω : Coord) :
    S.locU γ K ω ≤ holderConst (S.D γ ω).1 K * ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) := by
  refine iSup₂_le fun z hz => iSup₂_le fun w hw => ?_
  refine (ofReal_le_holderConst_mul (S.D γ ω) hz hw).trans ?_
  gcongr
  rw [← dist_eq_norm]
  exact Metric.dist_le_diam_of_mem hK hz hw

/-- **Tail bound** (blueprint, proof of Lemma `lem:T-B`): if `E[A_γ(K)^{4N}] ≤ C₆` and
`E[L_R^{-4N}] ≤ C_L R^{-2N}`, then `P[L_R ≤ U] ≤ (diam(K)^{2N} C₆ + C_L) R^{-N}`. -/
theorem measure_annulusCross_le_locU (hK : Bornology.IsBounded K) {N R : ℝ} (hN : 0 < N)
    (hR : 0 < R) {C6 : ℝ≥0∞} (h6 : ∫⁻ ω, holderConst (S.D γ ω).1 K ^ (4 * N) ∂stdP ≤ C6)
    {CL : ℝ} (hCL : 0 ≤ CL)
    (hLm : ∫⁻ ω, (annulusCross (S.D γ ω).1 R)⁻¹ ^ (4 * N) ∂stdP ≤
      ENNReal.ofReal (CL * R ^ (-(2 * N)))) :
    stdP {ω | annulusCross (S.D γ ω).1 R ≤ S.locU γ K ω} ≤
      (ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) * C6 + ENNReal.ofReal CL) *
        ENNReal.ofReal (R ^ (-N)) := by
  have h4N : (0 : ℝ) ≤ 4 * N := by linarith
  have hU : ∫⁻ ω, S.locU γ K ω ^ (4 * N) ∂stdP ≤
      ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) * C6 := by
    calc ∫⁻ ω, S.locU γ K ω ^ (4 * N) ∂stdP
        ≤ ∫⁻ ω, holderConst (S.D γ ω).1 K ^ (4 * N) *
            ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) ∂stdP := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ h4N]
          exact ENNReal.rpow_le_rpow (locU_le_holderConst_mul hK ω) h4N
      _ = (∫⁻ ω, holderConst (S.D γ ω).1 K ^ (4 * N) ∂stdP) *
            ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) :=
          lintegral_mul_const _ ((S.measurable_holderConst γ K).pow_const _)
      _ ≤ C6 * ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) := by gcongr
      _ = ENNReal.ofReal (Metric.diam K ^ (1 / 2 : ℝ)) ^ (4 * N) * C6 := mul_comm _ _
  exact measure_le_le_of_moments (S.measurable_annulusCross γ R).aemeasurable
    (S.measurable_locU γ K).aemeasurable hN hR hU hCL hLm

/-- `P[T > 2 · 2^j R₀] ≤ P[L_{2^j R₀} ≤ U]`. -/
theorem measure_lt_locT_le (j : ℕ) :
    stdP {ω | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω} ≤
      stdP {ω | annulusCross (S.D γ ω).1 (2 ^ j * locR0 K) ≤ S.locU γ K ω} :=
  measure_mono fun _ hω => annulusCross_le_locU_of_lt_locT hω

theorem measurableSet_lt_locT (S : Setup) (γ : ℝ) (K : Set ℂ) (c : ℝ≥0∞) :
    MeasurableSet {ω | c < S.locT γ K ω} :=
  measurableSet_lt measurable_const (S.measurable_locT γ K)

/-! ## Dyadic decompositions -/

/-- `T^p ≤ (2R₀)^p + ∑_j (2 · 2^{j+1} R₀)^p 1{T > 2 · 2^j R₀}` (all `ω`, `p > 0`). -/
theorem locT_rpow_le {p : ℝ} (hp : 0 < p) (ω : Coord) :
    S.locT γ K ω ^ p ≤ ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
      ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'}.indicator 1 ω := by
  by_cases hT : S.locT γ K ω = ⊤
  · have h1 : ∀ j : ℕ, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'}.indicator 1 ω := by
      intro j
      have hmem : ω ∈ {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'} := by
        show ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω
        rw [hT]
        exact ENNReal.ofReal_lt_top
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
      refine ENNReal.one_le_rpow ?_ hp
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_two_mul_locR0 K (j + 1))
    have hsum : ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'}.indicator 1 ω = ⊤ :=
      top_le_iff.1 ((ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm.le.trans
        (ENNReal.tsum_le_tsum h1))
    rw [hsum, add_top]
    exact le_top
  · obtain ⟨k, -, hk⟩ := exists_eq_locT hT
    rw [hk]
    rcases k with _ | j
    · exact le_self_add
    · refine le_add_left (le_trans ?_ (ENNReal.le_tsum j))
      have hmem : ω ∈ {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'} := by
        show ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω
        rw [hk]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [one_le_two_mul_locR0 K (j + 1)])).2
          (locR0_mul_lt K j)
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one]

/-- `A_γ(B̄_T(0))^q ≤ A_γ(B̄_{2R₀})^q + ∑_j A_γ(B̄_{2 · 2^{j+1} R₀})^q 1{T > 2 · 2^j R₀}` when
`T < ∞`. -/
theorem holderConst_locT_rpow_le (q : ℝ) {ω : Coord} (hT : S.locT γ K ω ≠ ⊤) :
    holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ q ≤
      holderConst (S.D γ ω).1 (Metric.closedBall (0 : ℂ) (2 * (2 ^ 0 * locR0 K))) ^ q +
      ∑' j : ℕ,
        holderConst (S.D γ ω).1 (Metric.closedBall (0 : ℂ) (2 * (2 ^ (j + 1) * locR0 K))) ^ q *
        {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'}.indicator 1 ω := by
  obtain ⟨k, -, hk⟩ := exists_eq_locT hT
  have hball : Metric.closedEBall (0 : ℂ) (S.locT γ K ω) =
      Metric.closedBall 0 (2 * (2 ^ k * locR0 K)) := by
    rw [hk]
    exact Metric.closedEBall_ofReal (by linarith [one_le_two_mul_locR0 K k])
  rw [hball]
  rcases k with _ | j
  · exact le_self_add
  · refine le_add_left (le_trans ?_ (ENNReal.le_tsum j))
    have hmem : ω ∈ {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'} := by
      show ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω
      rw [hk]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [one_le_two_mul_locR0 K (j + 1)])).2
        (locR0_mul_lt K j)
    rw [indicator_of_mem hmem, Pi.one_apply, mul_one]

end Setup

end GaussianLQG
