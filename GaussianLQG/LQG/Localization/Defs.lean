import GaussianLQG.LQG.Localization.Measurability

/-!
# The localization variables `T`, `B`, `Θ` (blueprint Lemma `lem:T-B`): definitions

Fix a compact `K ⊂ ℂ` and `δ > 0`. Blueprint Lemma `lem:T-B` defines

* `R₀ := min {2^k ≥ 2 : K ⊂ B_{2^k}(0)}` (`locR0`),
* `U := sup_{z,w ∈ K} D(z, w)` (`Setup.locU`),
* `T := 2 min {R ∈ {2^k R₀ : k ≥ 0} : L_R > U}` with `min ∅ := ∞` (`Setup.locT`),
* `B := max {1, √2 A_γ(B̄_T(0)) / I_γ(K, δ)}` (`Setup.locB`),
* `Θ := (2 log B + 2 + 2 log T)^{1/2}` (`Setup.locTheta`).

`U`, `T`, `B`, `Θ` take values in `[0, ∞]` (`ℝ≥0∞`). The closed ball `B̄_T(0)` is the extended
closed ball `Metric.closedEBall 0 T`, which is `ℂ` when `T = ∞`; the conventions `inf ∅ = ∞` and
`∞⁻¹ = 0` of blueprint (1.10) are those of `ℝ≥0∞`. `Θ = ∞` when `T = ∞` or `B = ∞`.

This file proves the elementary properties of these variables (`exists_eq_locT`, `locT_le`,
`annulusCross_le_locU_of_lt_locT`, `one_le_locT`, `one_le_locB`, `locTheta_le`) and their
measurability (`measurable_locU`, `measurable_locT`, `measurable_holderConst_locT`,
`measurable_locB`, `measurable_locTheta`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

/-! ## The radius `R₀` -/

/-- `R₀ = min {2^k ≥ 2 : K ⊆ B_{2^k}(0)}` (blueprint Lemma `lem:T-B`). For unbounded `K` the set is
empty and `sInf ∅ = 0` gives the junk value `R₀ = 1`; only bounded `K` are used. -/
def locR0 (K : Set ℂ) : ℝ := 2 ^ sInf {k : ℕ | 1 ≤ k ∧ K ⊆ Metric.ball (0 : ℂ) (2 ^ k)}

theorem locR0_pos (K : Set ℂ) : 0 < locR0 K := by
  unfold locR0
  positivity

theorem one_le_locR0 (K : Set ℂ) : 1 ≤ locR0 K := one_le_pow₀ one_le_two

/-- For bounded `K`, `R₀ ≥ 2` and `K ⊆ B_{R₀}(0)`. -/
theorem locR0_spec {K : Set ℂ} (hK : Bornology.IsBounded K) :
    2 ≤ locR0 K ∧ K ⊆ Metric.ball (0 : ℂ) (locR0 K) := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (one_lt_two : (1 : ℝ) < 2)
  have hne : {k : ℕ | 1 ≤ k ∧ K ⊆ Metric.ball (0 : ℂ) (2 ^ k)}.Nonempty := by
    refine ⟨n + 1, Nat.le_add_left 1 n, fun z hz => ?_⟩
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ r := mem_closedBall_zero_iff.1 (hr hz)
      _ < 2 ^ n := hn
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ one_le_two (Nat.le_succ n)
  obtain ⟨h1, h2⟩ := Nat.sInf_mem hne
  refine ⟨?_, h2⟩
  calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ locR0 K := pow_le_pow_right₀ one_le_two h1

/-- The candidate values `2 R = 2 · 2^k R₀` of `T`. -/
theorem locR0_mul_le (K : Set ℂ) {j k : ℕ} (hjk : j ≤ k) :
    2 * (2 ^ j * locR0 K) ≤ 2 * (2 ^ k * locR0 K) :=
  mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hjk) (locR0_pos K).le) zero_le_two

namespace Setup

variable (S : Setup)

/-! ## Definitions -/

/-- `U = sup_{z,w ∈ K} D^γ(z, w)` (blueprint Lemma `lem:T-B`). -/
def locU (γ : ℝ) (K : Set ℂ) (ω : Coord) : ℝ≥0∞ :=
  ⨆ z ∈ K, ⨆ w ∈ K, ENNReal.ofReal ((S.D γ ω).1 (z, w))

/-- `T = 2 min {R ∈ {2^k R₀ : k ≥ 0} : L_R > U}`, with `min ∅ = ∞` (blueprint Lemma `lem:T-B`). -/
def locT (γ : ℝ) (K : Set ℂ) (ω : Coord) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (_ : S.locU γ K ω < annulusCross (S.D γ ω).1 (2 ^ k * locR0 K)),
    ENNReal.ofReal (2 * (2 ^ k * locR0 K))

/-- `B = max {1, √2 A_γ(B̄_T(0)) / I_γ(K, δ)}` (blueprint Lemma `lem:T-B`), with
`B̄_T(0) = Metric.closedEBall 0 T` (all of `ℂ` if `T = ∞`). -/
def locB (γ : ℝ) (K : Set ℂ) (δ : ℝ) (ω : Coord) : ℝ≥0∞ :=
  max 1 (ENNReal.ofReal (Real.sqrt 2) *
    holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) /
      sepInf (S.D γ ω).1 K δ)

/-- `Θ = (2 log B + 2 + 2 log T)^{1/2}` (blueprint Lemma `lem:T-B`), `= ∞` if `T = ∞` or `B = ∞`. -/
def locTheta (γ : ℝ) (K : Set ℂ) (δ : ℝ) (ω : Coord) : ℝ≥0∞ :=
  if S.locT γ K ω = ⊤ ∨ S.locB γ K δ ω = ⊤ then ⊤ else
    ENNReal.ofReal (Real.sqrt (2 * Real.log (S.locB γ K δ ω).toReal + 2 +
      2 * Real.log (S.locT γ K ω).toReal))

variable {S} {γ : ℝ} {K : Set ℂ} {δ : ℝ} {ω : Coord}

/-! ## Elementary properties -/

/-- `T ≤ 2 · 2^k R₀` whenever `L_{2^k R₀} > U`. -/
theorem locT_le {k : ℕ} (hk : S.locU γ K ω < annulusCross (S.D γ ω).1 (2 ^ k * locR0 K)) :
    S.locT γ K ω ≤ ENNReal.ofReal (2 * (2 ^ k * locR0 K)) :=
  iInf₂_le k hk

/-- If `T > 2 · 2^k R₀`, then `L_{2^k R₀} ≤ U`. -/
theorem annulusCross_le_locU_of_lt_locT {k : ℕ}
    (h : ENNReal.ofReal (2 * (2 ^ k * locR0 K)) < S.locT γ K ω) :
    annulusCross (S.D γ ω).1 (2 ^ k * locR0 K) ≤ S.locU γ K ω := by
  by_contra h'
  push Not at h'
  exact absurd (locT_le h') (not_le.2 h)

/-- If `T < ∞`, the minimum is attained: `T = 2 · 2^k R₀` for some `k` with `L_{2^k R₀} > U`. -/
theorem exists_eq_locT (hT : S.locT γ K ω ≠ ⊤) :
    ∃ k : ℕ, S.locU γ K ω < annulusCross (S.D γ ω).1 (2 ^ k * locR0 K) ∧
      S.locT γ K ω = ENNReal.ofReal (2 * (2 ^ k * locR0 K)) := by
  classical
  have hex : ∃ k : ℕ, S.locU γ K ω < annulusCross (S.D γ ω).1 (2 ^ k * locR0 K) := by
    by_contra hne
    push Not at hne
    exact hT (iInf_eq_top.2 fun k => iInf_neg (not_lt.2 (hne k)))
  refine ⟨Nat.find hex, Nat.find_spec hex,
    le_antisymm (locT_le (Nat.find_spec hex)) (le_iInf₂ fun k hk => ?_)⟩
  exact ENNReal.ofReal_le_ofReal (locR0_mul_le K (Nat.find_min' hex hk))

/-- `T ≥ 2 R₀`. -/
theorem ofReal_two_mul_locR0_le_locT :
    ENNReal.ofReal (2 * locR0 K) ≤ S.locT γ K ω := by
  refine le_iInf₂ fun k _ => ENNReal.ofReal_le_ofReal ?_
  have := locR0_mul_le K (Nat.zero_le k)
  rwa [pow_zero, one_mul] at this

/-- `T ≥ 1`. -/
theorem one_le_locT : 1 ≤ S.locT γ K ω := by
  refine le_trans ?_ ofReal_two_mul_locR0_le_locT
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith [one_le_locR0 K])

/-- `B ≥ 1`. -/
theorem one_le_locB : 1 ≤ S.locB γ K δ ω := le_max_left _ _

/-- The extended closed ball `B̄_T(0)` is the closed ball of radius `T` when `T < ∞`. -/
theorem eclosedBall_locT (hT : S.locT γ K ω ≠ ⊤) :
    Metric.closedEBall (0 : ℂ) (S.locT γ K ω) = Metric.closedBall 0 (S.locT γ K ω).toReal := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hT]
  exact Metric.closedEBall_ofReal ENNReal.toReal_nonneg

/-- `(Θ.toReal)² = 2 log B + 2 + 2 log T` when `T, B < ∞`. -/
theorem toReal_locTheta_sq (hT : S.locT γ K ω ≠ ⊤) (hB : S.locB γ K δ ω ≠ ⊤) :
    (S.locTheta γ K δ ω).toReal ^ 2 =
      2 * Real.log (S.locB γ K δ ω).toReal + 2 + 2 * Real.log (S.locT γ K ω).toReal := by
  have hB1 : 1 ≤ (S.locB γ K δ ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hB one_le_locB
  have hT1 : 1 ≤ (S.locT γ K ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hT one_le_locT
  have hx : 0 ≤ 2 * Real.log (S.locB γ K δ ω).toReal + 2 + 2 * Real.log (S.locT γ K ω).toReal := by
    have := Real.log_nonneg hB1
    have := Real.log_nonneg hT1
    linarith
  rw [locTheta, ite_eq_right (not_or.2 ⟨hT, hB⟩), ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt hx]

/-- `Θ ≤ 2 max {B, T}`: `2 log B + 2 + 2 log T ≤ 4 m ≤ 4 m²` with `m = max {B, T} ≥ 1`. -/
theorem locTheta_le : S.locTheta γ K δ ω ≤ 2 * max (S.locB γ K δ ω) (S.locT γ K ω) := by
  by_cases h : S.locT γ K ω = ⊤ ∨ S.locB γ K δ ω = ⊤
  · rcases h with h | h
    · rw [h, max_top_right, ENNReal.mul_top two_ne_zero]
      exact le_top
    · rw [h, max_top_left, ENNReal.mul_top two_ne_zero]
      exact le_top
  · obtain ⟨hT, hB⟩ := not_or.1 h
    set b := (S.locB γ K δ ω).toReal with hb
    set t := (S.locT γ K ω).toReal with ht
    have hb1 : 1 ≤ b := by
      rw [hb, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hB one_le_locB
    have ht1 : 1 ≤ t := by
      rw [ht, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hT one_le_locT
    set m := max b t with hm
    have hm1 : 1 ≤ m := le_max_of_le_left hb1
    have hlb : Real.log b ≤ m - 1 :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith [le_max_left b t])
    have hlt : Real.log t ≤ m - 1 :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith [le_max_right b t])
    have hx : 2 * Real.log b + 2 + 2 * Real.log t ≤ (2 * m) ^ 2 := by nlinarith
    have hsq : Real.sqrt (2 * Real.log b + 2 + 2 * Real.log t) ≤ 2 * m := by
      calc Real.sqrt (2 * Real.log b + 2 + 2 * Real.log t) ≤ Real.sqrt ((2 * m) ^ 2) :=
            Real.sqrt_le_sqrt hx
        _ = 2 * m := Real.sqrt_sq (by linarith)
    rw [locTheta, ite_eq_right h]
    calc ENNReal.ofReal (Real.sqrt (2 * Real.log b + 2 + 2 * Real.log t))
        ≤ ENNReal.ofReal (2 * m) := ENNReal.ofReal_le_ofReal hsq
      _ = 2 * max (S.locB γ K δ ω) (S.locT γ K ω) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, hm, ENNReal.ofReal_max, hb, ht,
            ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal hT]

/-! ## Measurability -/

variable (S)

theorem measurable_locU (γ : ℝ) (K : Set ℂ) : Measurable (S.locU γ K) :=
  S.measurable_iSup_dist γ K

theorem measurable_locT (γ : ℝ) (K : Set ℂ) : Measurable (S.locT γ K) := by
  classical
  unfold locT
  refine Measurable.iInf fun k => ?_
  simp_rw [iInf_eq_if]
  exact Measurable.ite (measurableSet_lt (S.measurable_locU γ K) (S.measurable_annulusCross γ _))
    measurable_const measurable_const

/-- The values of `T`: `∞` or `2 · 2^k R₀`. -/
def locTVal (K : Set ℂ) : Option ℕ → ℝ≥0∞
  | none => ⊤
  | some k => ENNReal.ofReal (2 * (2 ^ k * locR0 K))

theorem exists_locTVal_eq (γ : ℝ) (K : Set ℂ) (ω : Coord) :
    ∃ o : Option ℕ, locTVal K o = S.locT γ K ω := by
  by_cases hT : S.locT γ K ω = ⊤
  · exact ⟨none, hT.symm⟩
  · obtain ⟨k, -, hk⟩ := exists_eq_locT hT
    exact ⟨some k, hk.symm⟩

/-- `A_γ(B̄_T(0))` as a countable supremum over the possible values of `T`. -/
theorem holderConst_locT_eq_iSup (γ : ℝ) (K : Set ℂ) (ω : Coord) :
    holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) =
      ⨆ o : Option ℕ, {ω' | S.locT γ K ω' = locTVal K o}.indicator
        (fun ω' => holderConst (S.D γ ω').1 (Metric.closedEBall (0 : ℂ) (locTVal K o))) ω := by
  refine le_antisymm ?_ (iSup_le fun o => ?_)
  · obtain ⟨o, ho⟩ := S.exists_locTVal_eq γ K ω
    refine le_iSup_of_le o ?_
    rw [indicator_of_mem (show ω ∈ {ω' | S.locT γ K ω' = locTVal K o} from ho.symm), ho]
  · by_cases ho : ω ∈ {ω' | S.locT γ K ω' = locTVal K o}
    · rw [indicator_of_mem ho]
      rw [show S.locT γ K ω = locTVal K o from ho]
    · rw [indicator_of_notMem ho]
      exact zero_le

/-- `ω ↦ A_γ(B̄_T(0))` is measurable. -/
theorem measurable_holderConst_locT (γ : ℝ) (K : Set ℂ) :
    Measurable fun ω => holderConst (S.D γ ω).1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) := by
  simp_rw [S.holderConst_locT_eq_iSup γ K]
  exact Measurable.iSup fun o => (S.measurable_holderConst γ _).indicator
    (measurableSet_eq_fun (S.measurable_locT γ K) measurable_const)

theorem measurable_locB (γ : ℝ) (K : Set ℂ) (δ : ℝ) : Measurable (S.locB γ K δ) := by
  unfold locB
  have hA := S.measurable_holderConst_locT γ K
  have hI := S.measurable_sepInf γ K δ
  exact measurable_const.max ((measurable_const.mul hA).div hI)

theorem measurable_locTheta (γ : ℝ) (K : Set ℂ) (δ : ℝ) : Measurable (S.locTheta γ K δ) := by
  classical
  have hT := S.measurable_locT γ K
  have hB := S.measurable_locB γ K δ
  have hset : MeasurableSet {ω | S.locT γ K ω = ⊤ ∨ S.locB γ K δ ω = ⊤} := by
    rw [ofPred_or]
    exact (measurableSet_eq_fun hT measurable_const).union
      (measurableSet_eq_fun hB measurable_const)
  unfold locTheta
  refine Measurable.ite hset measurable_const ?_
  exact ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (((measurable_const.mul (Real.measurable_log.comp hB.ennreal_toReal)).add
      measurable_const).add (measurable_const.mul (Real.measurable_log.comp hT.ennreal_toReal))))

end Setup

end GaussianLQG
