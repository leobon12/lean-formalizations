import GaussianLQG.LQG.Localization.Tail

/-!
# Moments of `T`, `B`, `Θ` (blueprint Lemma `lem:T-B`, moments)

Blueprint Lemma `lem:T-B`: for every `p ∈ [1, ∞)` there is `γ_* = γ_*(p) > 0` such that
`P[T < ∞] = 1` and `sup_{γ ≤ γ_*} E[T^p + B^p + Θ^p] ≤ C_{p,K,δ}` (`Setup.exists_locMoments`;
`γ_*` depends only on `p`, the constant on `p, K, δ`). The hypotheses are the interface lemmas
`Setup.HolderScaling` and `Setup.AnnulusScaling` (Lemma `lem:scaling`(c),(d)), together with
(S1) and (S6) from the `Setup`.

Proof (blueprint): put `N = 4p + 4` and take `γ_*` so small that `|ξQ - 1| ≤ 1/(4N)` and
`ξ ≤ 1/(4N)`. Then `E[L_R^{-4N}] ≤ C R^{-2N}` and `E[U^{4N}] ≤ C`, so
`P[L_R ≤ U] ≤ C R^{-N}` (`Setup.measure_annulusCross_le_locU`) and
`P[T > 2 · 2^j R₀] ≤ C (2^j R₀)^{-N}`. The dyadic decomposition of `T^p` gives `E[T^p] < ∞`
(`Setup.lintegral_locT_rpow_le`), hence `T < ∞` a.s. With `E[A_γ(B̄_R)^{4p}] ≤ C R^{2p+2}`, the
dyadic decomposition of `A_γ(B̄_T)^{2p}` and Cauchy–Schwarz give `E[A_γ(B̄_T)^{2p}] < ∞`
(`Setup.lintegral_holderConst_locT_le`). Then `B^p ≤ 1 + 2^{p/2} A^p I^{-p}` and Cauchy–Schwarz give
`E[B^p] < ∞` (`Setup.lintegral_locB_rpow_le`), and `Θ ≤ 2 max {B, T}` gives `E[Θ^p] < ∞`
(`Setup.lintegral_locTheta_rpow_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- `ofReal (C R^e) ≤ ofReal (max C 0 · R^{e'})` for `R ≥ 1`, `e ≤ e'`. -/
theorem ofReal_mul_rpow_le_max {C R e e' : ℝ} (hR : 1 ≤ R) (he : e ≤ e') :
    ENNReal.ofReal (C * R ^ e) ≤ ENNReal.ofReal (max C 0 * R ^ e') := by
  refine ENNReal.ofReal_le_ofReal ?_
  calc C * R ^ e ≤ max C 0 * R ^ e :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * R ^ e' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR he) (le_max_right C 0)

/-- `(x^q)² = x^{2q}` in `ℝ≥0∞`. -/
theorem rpow_rpow_two (x : ℝ≥0∞) (q : ℝ) : (x ^ q) ^ (2 : ℝ) = x ^ (2 * q) := by
  rw [← ENNReal.rpow_mul, mul_comm]

namespace Setup

variable {S : Setup} {γ : ℝ} {K : Set ℂ} {δ : ℝ}

/-! ## The moment of `T` -/

/-- The terms of the dyadic bound for `E[T^p]` form a geometric sequence. -/
theorem locT_term_eq (K : Set ℂ) {p : ℝ} (hp : 0 ≤ p) (N : ℝ) (C : ℝ≥0∞) (j : ℕ) :
    ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) =
      C * (ENNReal.ofReal ((4 * locR0 K) ^ p) * ENNReal.ofReal (locR0 K ^ (-N))) *
        ENNReal.ofReal ((2 : ℝ) ^ (p + -N)) ^ j := by
  have hR := (locR0_pos K).le
  have e : 2 * (2 ^ (j + 1) * locR0 K) = 2 ^ j * (4 * locR0 K) := by ring
  rw [e, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
    ofReal_two_pow_mul_rpow j (by positivity) p, ofReal_two_pow_mul_rpow j hR (-N),
    ← ofReal_two_rpow_mul, mul_pow]
  ring

/-- The dyadic bound for `E[T^p]` is finite when `p < N`. -/
theorem locT_bound_ne_top (K : Set ℂ) {p N : ℝ} (hp : 0 ≤ p) (hpN : p < N) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) :
    ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
      ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ≠ ⊤ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top, ?_⟩
  simp_rw [locT_term_eq K hp N C]
  exact tsum_mul_pow_ne_top (ENNReal.mul_ne_top hC (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top)) (ofReal_two_rpow_lt_one (by linarith))

/-- **`E[T^p]`** through the tail bound `P[L_{2^j R₀} ≤ U] ≤ C (2^j R₀)^{-N}`. -/
theorem lintegral_locT_rpow_le {p N : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (htail : ∀ j : ℕ, stdP {ω | annulusCross (S.D γ ω).1 (2 ^ j * locR0 K) ≤ S.locU γ K ω} ≤
      C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) :
    ∫⁻ ω, S.locT γ K ω ^ p ∂stdP ≤ ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
      ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) := by
  set s : ℕ → Set Coord := fun j =>
    {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'} with hs
  have hsm : ∀ j, MeasurableSet (s j) := fun j => S.measurableSet_lt_locT γ K _
  calc ∫⁻ ω, S.locT γ K ω ^ p ∂stdP
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
          ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p * (s j).indicator 1 ω)
          ∂stdP := lintegral_mono fun ω => locT_rpow_le hp ω
    _ = ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
          ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p * stdP (s j) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun j => ((measurable_one.indicator (hsm j)).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun j => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hsm j)),
          lintegral_indicator_one (hsm j)]
    _ ≤ ENNReal.ofReal (2 * (2 ^ 0 * locR0 K)) ^ p +
          ∑' j : ℕ, ENNReal.ofReal (2 * (2 ^ (j + 1) * locR0 K)) ^ p *
            (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun j => ?_)
        exact mul_le_mul_right ((measure_lt_locT_le j).trans (htail j)) _

/-! ## The moment of `A_γ(B̄_T(0))` -/

/-- The terms of the dyadic bound for `E[A_γ(B̄_T)^{q}]` form a geometric sequence. -/
theorem holder_term_eq (K : Set ℂ) {CA : ℝ} (hCA : 0 ≤ CA) (eA N : ℝ) (C : ℝ≥0∞) (j : ℕ) :
    ENNReal.ofReal (CA * (2 * (2 ^ (j + 1) * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ^ (1 / 2 : ℝ) =
      (ENNReal.ofReal CA * ENNReal.ofReal ((4 * locR0 K) ^ eA) *
          (C * ENNReal.ofReal (locR0 K ^ (-N)))) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ((2 : ℝ) ^ (eA + -N)) ^ (1 / 2 : ℝ)) ^ j := by
  have hR := (locR0_pos K).le
  have e : 2 * (2 ^ (j + 1) * locR0 K) = 2 ^ j * (4 * locR0 K) := by ring
  rw [e, ENNReal.ofReal_mul hCA, ofReal_two_pow_mul_rpow j (by positivity) eA,
    ofReal_two_pow_mul_rpow j hR (-N), ← mul_assoc, ← mul_assoc C, sqrt_mul_pow_mul,
    ofReal_two_rpow_mul]

/-- The dyadic bound for `E[A_γ(B̄_T)^{q}]` is finite when `e_A < N`. -/
theorem holder_bound_ne_top (K : Set ℂ) {CA : ℝ} (hCA : 0 ≤ CA) {eA N : ℝ} (heN : eA < N)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    ENNReal.ofReal (CA * (2 * (2 ^ 0 * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) +
      ∑' j : ℕ, ENNReal.ofReal (CA * (2 * (2 ^ (j + 1) * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ^ (1 / 2 : ℝ) ≠ ⊤ := by
  refine ENNReal.add_ne_top.2
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top, ?_⟩
  simp_rw [holder_term_eq K hCA eA N C]
  refine tsum_mul_pow_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top))) ?_
  exact ENNReal.rpow_lt_one (ofReal_two_rpow_lt_one (by linarith)) (by norm_num)

/-- **`E[A_γ(B̄_T(0))^q]`** through the tail bound and the moments
`E[A_γ(B̄_R)^{2q}] ≤ C_A R^{e_A}` (`R ≥ 1`), given `T < ∞` a.s. -/
theorem lintegral_holderConst_locT_le {q N : ℝ} {C : ℝ≥0∞}
    (hTfin : ∀ᵐ ω ∂stdP, S.locT γ K ω ≠ ⊤)
    (htail : ∀ j : ℕ, stdP {ω | annulusCross (S.D γ ω).1 (2 ^ j * locR0 K) ≤ S.locU γ K ω} ≤
      C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N)))
    {CA eA : ℝ} (hAm : ∀ R : ℝ, 1 ≤ R →
      ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedBall 0 R) ^ (2 * q) ∂stdP ≤
        ENNReal.ofReal (CA * R ^ eA)) :
    ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ q ∂stdP ≤
      ENNReal.ofReal (CA * (2 * (2 ^ 0 * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) +
      ∑' j : ℕ, ENNReal.ofReal (CA * (2 * (2 ^ (j + 1) * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) *
        (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ^ (1 / 2 : ℝ) := by
  set s : ℕ → Set Coord := fun j =>
    {ω' | ENNReal.ofReal (2 * (2 ^ j * locR0 K)) < S.locT γ K ω'} with hs
  have hsm : ∀ j, MeasurableSet (s j) := fun j => S.measurableSet_lt_locT γ K _
  set A : ℝ → Coord → ℝ≥0∞ := fun R ω => holderConst (S.D γ ω).1 (Metric.closedBall 0 R) with hA
  have hAmeas : ∀ R, Measurable (A R) := fun R => S.measurable_holderConst γ _
  calc ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ q ∂stdP
      ≤ ∫⁻ ω, (A (2 * (2 ^ 0 * locR0 K)) ω ^ q +
          ∑' j : ℕ, A (2 * (2 ^ (j + 1) * locR0 K)) ω ^ q * (s j).indicator 1 ω) ∂stdP := by
        refine lintegral_mono_ae ?_
        filter_upwards [hTfin] with ω hω using holderConst_locT_rpow_le q hω
    _ = ∫⁻ ω, A (2 * (2 ^ 0 * locR0 K)) ω ^ q ∂stdP +
          ∑' j : ℕ, ∫⁻ ω, A (2 * (2 ^ (j + 1) * locR0 K)) ω ^ q * (s j).indicator 1 ω ∂stdP := by
        have hmeas : ∀ j : ℕ, AEMeasurable (fun ω => A (2 * (2 ^ (j + 1) * locR0 K)) ω ^ q *
            (s j).indicator 1 ω) stdP := fun j =>
          (((hAmeas _).pow_const q).mul (measurable_one.indicator (hsm j))).aemeasurable
        rw [lintegral_add_left ((hAmeas _).pow_const q), lintegral_tsum hmeas]
    _ ≤ (∫⁻ ω, A (2 * (2 ^ 0 * locR0 K)) ω ^ (2 * q) ∂stdP) ^ (1 / 2 : ℝ) +
          ∑' j : ℕ, (∫⁻ ω, A (2 * (2 ^ (j + 1) * locR0 K)) ω ^ (2 * q) ∂stdP) ^ (1 / 2 : ℝ) *
            stdP (s j) ^ (1 / 2 : ℝ) := by
        refine add_le_add ?_ (ENNReal.tsum_le_tsum fun j => ?_)
        · have h := lintegral_le_rpow_lintegral_sq (μ := stdP)
            ((hAmeas (2 * (2 ^ 0 * locR0 K))).pow_const q).aemeasurable
          simp only [rpow_rpow_two] at h
          exact h
        · have h := lintegral_mul_indicator_one_le (μ := stdP)
            ((hAmeas (2 * (2 ^ (j + 1) * locR0 K))).pow_const q).aemeasurable (hsm j)
          simp only [rpow_rpow_two] at h
          exact h
    _ ≤ ENNReal.ofReal (CA * (2 * (2 ^ 0 * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) +
          ∑' j : ℕ, ENNReal.ofReal (CA * (2 * (2 ^ (j + 1) * locR0 K)) ^ eA) ^ (1 / 2 : ℝ) *
            (C * ENNReal.ofReal ((2 ^ j * locR0 K) ^ (-N))) ^ (1 / 2 : ℝ) := by
        refine add_le_add (ENNReal.rpow_le_rpow (hAm _ (one_le_two_mul_locR0 K 0)) (by norm_num))
          (ENNReal.tsum_le_tsum fun j => ?_)
        gcongr
        · exact hAm _ (one_le_two_mul_locR0 K (j + 1))
        · exact (measure_lt_locT_le j).trans (htail j)

/-! ## The moments of `B` and `Θ` -/

/-- `B^p ≤ 1 + 2^{p/2} A_γ(B̄_T)^p I_γ(K,δ)^{-p}`. -/
theorem locB_rpow_le {p : ℝ} (hp : 0 ≤ p) (ω : Coord) :
    S.locB γ K δ ω ^ p ≤ 1 + ENNReal.ofReal (Real.sqrt 2) ^ p *
      (holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ p *
        (sepInf (S.D γ ω).1 K δ)⁻¹ ^ p) := by
  unfold locB
  refine (max_rpow_le_add _ _ p).trans ?_
  rw [ENNReal.one_rpow, div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hp,
    ENNReal.mul_rpow_of_nonneg _ _ hp, mul_assoc]

/-- **`E[B^p]`** by Cauchy–Schwarz. -/
theorem lintegral_locB_rpow_le {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP ≤ 1 + ENNReal.ofReal (Real.sqrt 2) ^ p *
      ((∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ (2 * p)
          ∂stdP) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, (sepInf (S.D γ ω).1 K δ)⁻¹ ^ (2 * p) ∂stdP) ^ (1 / 2 : ℝ)) := by
  have hA := S.measurable_holderConst_locT γ K
  have hI := (S.measurable_sepInf γ K δ).inv
  calc ∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (Real.sqrt 2) ^ p *
          (holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ p *
            (sepInf (S.D γ ω).1 K δ)⁻¹ ^ p)) ∂stdP := lintegral_mono fun ω => locB_rpow_le hp ω
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) ^ p *
          ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ p *
            (sepInf (S.D γ ω).1 K δ)⁻¹ ^ p ∂stdP := by
        have hF : Measurable fun ω =>
            holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) ^ p *
              (sepInf (S.D γ ω).1 K δ)⁻¹ ^ p := (hA.pow_const p).mul (hI.pow_const p)
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hF]
    _ ≤ _ := by
        gcongr
        exact lintegral_rpow_mul_rpow_le hA.aemeasurable hI.aemeasurable

/-- **`E[Θ^p]`** from `Θ ≤ 2 max {B, T}`. -/
theorem lintegral_locTheta_rpow_le {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, S.locTheta γ K δ ω ^ p ∂stdP ≤
      2 ^ p * (∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP + ∫⁻ ω, S.locT γ K ω ^ p ∂stdP) := by
  have hB := (S.measurable_locB γ K δ).pow_const p
  have hT := (S.measurable_locT γ K).pow_const p
  calc ∫⁻ ω, S.locTheta γ K δ ω ^ p ∂stdP
      ≤ ∫⁻ ω, 2 ^ p * (S.locB γ K δ ω ^ p + S.locT γ K ω ^ p) ∂stdP := by
        refine lintegral_mono fun ω => ?_
        calc S.locTheta γ K δ ω ^ p ≤ (2 * max (S.locB γ K δ ω) (S.locT γ K ω)) ^ p :=
              ENNReal.rpow_le_rpow locTheta_le hp
          _ = 2 ^ p * max (S.locB γ K δ ω) (S.locT γ K ω) ^ p :=
              ENNReal.mul_rpow_of_nonneg _ _ hp
          _ ≤ 2 ^ p * (S.locB γ K δ ω ^ p + S.locT γ K ω ^ p) := by
              gcongr
              exact max_rpow_le_add _ _ p
    _ = 2 ^ p * (∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP + ∫⁻ ω, S.locT γ K ω ^ p ∂stdP) := by
        have hBT : Measurable fun ω => S.locB γ K δ ω ^ p + S.locT γ K ω ^ p := hB.add hT
        rw [lintegral_const_mul _ hBT, lintegral_add_left hB]

end Setup

end GaussianLQG
