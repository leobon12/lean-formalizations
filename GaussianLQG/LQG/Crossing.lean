import GaussianLQG.LQG.Crossing.Lower

/-!
# The crossing distance (blueprint Proposition `prop:crossing`)

For `S : Setup` let `C_γ` be the left–right crossing distance of the unit square and
`𝖸_γ = (log C_γ - b_γ) / ξ_γ` (`Setup.crossY`). Assuming blueprint Lemma `lem:energy-approx`
(`Setup.EnergyApprox`):

* `Setup.crossingConv` (blueprint Proposition `prop:crossing`, source (5.2)–(5.4)): the interface
  proposition `Setup.CrossingConv`, `𝖸_γ → M` in probability as `γ ↓ 0`.

The lower bound `P[𝖸_γ < M - ε] → 0` is `Setup.tendsto_measure_crossY_lt`
(`LQG/Crossing/Lower.lean`). The upper bound `P[𝖸_γ ≥ M + ε] → 0`
(`Setup.tendsto_measure_M_add_le_crossY`) follows the blueprint: for `y ∈ S_n`, `r(y, y) = 1` and
`C_γ ≤ D(iy, 1 + iy)`, so `𝖸_γ ≤ H(y, y) + 𝓡(y, y)` (`Setup.crossY_lt_of_diag`); hence
`P[𝖸_γ ≥ M + ε] ≤ P[M_n ≥ M + ε/2] + P[max_{y ∈ S_n} |𝓡(y, y)| ≥ ε/2]` with
`M_n = min_{y ∈ S_n} H(y, y)`. For fixed `n` the second term tends to `0` by Proposition
`prop:first-order` (here applied at the finitely many points of `S_n`, instead of through the grid
`S_{m(γ)} ⊇ S_n`), and the first term tends to `0` as `n → ∞` because `M_n ↓ M` almost surely
(`Setup.tendsto_measure_diagGapSet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open LQGMetric Crossing

namespace Setup

variable (S : Setup)

/-! ## `M_n ↓ M` -/

/-- The event `{min_{y ∈ S_n} H(y, y) ≥ M + ε}`, `S_n = {k 2^{-n} : k ≤ 2^n}`. -/
def diagGapSet (ε : ℝ) (n : ℕ) : Set Coord :=
  {ω | ∀ k : ℕ, k ≤ 2 ^ n → S.M ω + ε ≤ S.H ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω}

theorem measurableSet_diagGapSet (ε : ℝ) (n : ℕ) : MeasurableSet (S.diagGapSet ε n) := by
  have e : S.diagGapSet ε n = ⋂ k : ℕ, ⋂ (_ : k ≤ 2 ^ n),
      {ω | S.M ω + ε ≤ S.H ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω} := by
    ext ω
    simp only [diagGapSet, mem_ofPred_eq, mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (S.measurable_M'.add_const ε) (S.measurable_H _ _)

/-- `S_n ⊆ S_{n+1}`, so the events `{M_n ≥ M + ε}` decrease. -/
theorem diagGapSet_antitone (ε : ℝ) : Antitone (S.diagGapSet ε) := by
  refine antitone_nat_of_succ_le fun n ω hω k hk => ?_
  have h := hω (2 * k) ((Nat.mul_le_mul_left 2 hk).trans_eq (pow_succ' 2 n).symm)
  have e : ((2 * k : ℕ) : ℝ) / 2 ^ (n + 1) = (k : ℝ) / 2 ^ n := by
    rw [Nat.cast_mul, Nat.cast_ofNat, pow_succ, mul_comm (2 : ℝ) (k : ℝ),
      mul_div_mul_right _ _ (two_ne_zero)]
  rwa [e] at h

/-- `⋂_n {M_n ≥ M + ε}` is null for `ε > 0`: almost surely `{H(y, y) : y ∈ 𝔻}` is bounded below,
and then `M = inf_{y ∈ 𝔻} H(y, y) = inf_n M_n`. -/
theorem measure_iInter_diagGapSet {ε : ℝ} (hε : 0 < ε) :
    stdP (⋂ n, S.diagGapSet ε n) = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 S.ae_bddBelow_H_dyadic)
  intro ω hω hbdd
  rw [mem_iInter] at hω
  have hle : S.M ω + ε ≤ S.M ω := by
    refine le_ciInf fun y => ?_
    obtain ⟨n, k, hk, hy⟩ := y.2
    have h := hω n k hk
    rwa [← hy] at h
  linarith

/-- **`M_n ↓ M`** (blueprint proof of Proposition `prop:crossing`, upper bound):
`P[min_{y ∈ S_n} H(y, y) ≥ M + ε] → 0` as `n → ∞`, for `ε > 0`. -/
theorem tendsto_measure_diagGapSet {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => stdP (S.diagGapSet ε n)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop
    (fun n => (S.measurableSet_diagGapSet ε n).nullMeasurableSet) (S.diagGapSet_antitone ε)
    ⟨0, measure_ne_top stdP _⟩
  rw [S.measure_iInter_diagGapSet hε] at h
  exact h

/-! ## The upper bound -/

/-- **The upper bound on the diagonal** (blueprint proof of Proposition `prop:crossing`): for
`y ∈ [0, 1]`, `r(y, y) = 1` and `C_γ ≤ D(iy, 1 + iy)`, so `𝖸_γ ≤ H(y, y) + 𝓡(y, y)`. Hence
`H(y, y) < M + ε/2` and `|𝓡(y, y)| < ε/2` give `𝖸_γ < M + ε`. -/
theorem crossY_lt_of_diag {γ ε : ℝ} (hξ : 0 < S.ξ γ) {ω : Coord} {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hH : S.H y y ω < S.M ω + ε / 2)
    (hR : |S.residual γ y y ω| < ε / 2) : S.crossY γ ω < S.M ω + ε := by
  have hr : ‖(y : ℂ) * Complex.I - (1 + (y : ℂ) * Complex.I)‖ = 1 := by
    rw [show (y : ℂ) * Complex.I - (1 + (y : ℂ) * Complex.I) = -1 by ring, norm_neg, norm_one]
  have hres : S.residual γ y y ω =
      (Real.log ((S.D γ ω).1 ((y : ℂ) * Complex.I, 1 + (y : ℂ) * Complex.I)) - S.b γ) / S.ξ γ -
        S.H y y ω := by
    unfold residual
    rw [hr, Real.log_one, mul_zero, sub_zero]
  have hle : S.crossY γ ω ≤
      (Real.log ((S.D γ ω).1 ((y : ℂ) * Complex.I, 1 + (y : ℂ) * Complex.I)) - S.b γ) / S.ξ γ :=
    div_le_div_of_nonneg_right (sub_le_sub_right (log_crossFn_le _ hy hy) _) hξ.le
  have h1 := (abs_lt.1 hR).2
  rw [hres] at h1
  linarith

/-- **Blueprint Proposition `prop:crossing`, upper bound**, assuming Lemma `lem:energy-approx`:
for every `ε > 0`, `P[𝖸_γ ≥ M + ε] → 0` as `γ ↓ 0`. -/
theorem tendsto_measure_M_add_le_crossY (hY : S.EnergyApprox) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun γ => stdP {ω | S.M ω + ε ≤ S.crossY γ ω}) (𝓝[>] 0) (𝓝 0) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨γs, C, hγs, hC0, hC⟩ := S.exists_residual_tail hY
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨n, hn⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 (S.tendsto_measure_diagGapSet hε2)) (δ / 2) hδ2).exists
  -- the finitely many diagonal residuals at the points of `S_n`
  have hfin : Tendsto (fun γ => ∑ k ∈ Finset.range (2 ^ n + 1),
      stdP {ω | ε / 2 ≤ |S.residual γ ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω|})
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ k ∈ Finset.range (2 ^ n + 1), (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun k hk => ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (S.tendsto_ofReal_mul_xi_rpow ((C / (ε / 2)) ^ (150 : ℝ))
        (by norm_num : (0 : ℝ) < 150 / 24))
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioc_mem_nhdsGT hγs] with γ hγ
    have hkm : k ≤ 2 ^ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    exact hC γ hγ _ (div_two_pow_mem_Icc hkm) _ (div_two_pow_mem_Icc hkm) (ε / 2) hε2
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hfin) (δ / 2) hδ2, Ioc_mem_nhdsGT one_pos]
    with γ hγ hγ1
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ1.1 (by linarith [hγ1.2])
  have hsub : {ω | S.M ω + ε ≤ S.crossY γ ω} ⊆ S.diagGapSet (ε / 2) n ∪
      ⋃ k ∈ Finset.range (2 ^ n + 1),
        {ω | ε / 2 ≤ |S.residual γ ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω|} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hB, hR⟩ := hcon
    simp only [diagGapSet, mem_ofPred_eq, not_forall, not_le] at hB
    obtain ⟨k, hk, hHk⟩ := hB
    have hRk : |S.residual γ ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω| < ε / 2 :=
      not_le.1 fun h => hR k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) h
    have hlt := S.crossY_lt_of_diag hξ (div_two_pow_mem_Icc hk) hHk hRk
    exact absurd hω (not_le.2 hlt)
  calc stdP {ω | S.M ω + ε ≤ S.crossY γ ω}
      ≤ stdP (S.diagGapSet (ε / 2) n ∪ ⋃ k ∈ Finset.range (2 ^ n + 1),
          {ω | ε / 2 ≤ |S.residual γ ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω|}) :=
        measure_mono hsub
    _ ≤ stdP (S.diagGapSet (ε / 2) n) + ∑ k ∈ Finset.range (2 ^ n + 1),
          stdP {ω | ε / 2 ≤ |S.residual γ ((k : ℝ) / 2 ^ n) ((k : ℝ) / 2 ^ n) ω|} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ δ / 2 + δ / 2 := add_le_add hn hγ
    _ = δ := ENNReal.add_halves δ

/-! ## Proposition `prop:crossing` -/

/-- **Blueprint Proposition `prop:crossing`** (source (5.2)–(5.4)), assuming Lemma
`lem:energy-approx` (`Setup.EnergyApprox`): `𝖸_γ = (log C_γ - b_γ) / ξ_γ → M` in probability as
`γ ↓ 0` (the interface proposition `Setup.CrossingConv`). -/
theorem crossingConv (hY : S.EnergyApprox) : S.CrossingConv := by
  show TendstoInMeasure stdP S.crossY (𝓝[>] 0) S.M
  refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
  have h12 := (S.tendsto_measure_M_add_le_crossY hY hε).add
    (S.tendsto_measure_crossY_lt hY (half_pos hε))
  rw [add_zero] at h12
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12 (fun _ => zero_le)
    fun γ => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, Real.dist_eq] at hω
  rcases le_abs'.1 hω with h | h
  · right
    show S.crossY γ ω < S.M ω - ε / 2
    linarith
  · left
    show S.M ω + ε ≤ S.crossY γ ω
    linarith

end Setup

end GaussianLQG
