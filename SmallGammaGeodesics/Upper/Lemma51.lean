import SmallGammaGeodesics.Upper.SingleProbe

/-!
# Lemma 5.1 and the tail on the good event (packet P-U3)

Blueprint `s5-upper.tex`, Lemma `lem:lemma51` (source Lemma 5.1, (5.11)) and Corollary
`cor:tail-good` (source (5.12)); BP2 detail D11.

* `lemma51`: `P[𝒢 ∩ ℬ(R)] ≤ C₅ (ξ²/R³ + ξ² (m + ξ^{99/100} L)/R⁴ + ξ^{49/32} L²/R²)` for
  `δ ≤ R ≤ 2ξ^{99/200}`. The union bound over `j ≤ J` and `a ∈ 𝒜_j` (`#𝒜_j ≤ 4/ℓ_j`,
  `probeGrid_spec`) and the single-probe bound (`singleProbe`) give the sum of
  `(4/ℓ_j)·(three terms)`; with `p_j = ℓ_j^{1/8} = q^j`, `q = 2^{-1/8}`, the three sums are
  geometric (`sum_probe_terms_le`):
  `Σ_j q^{5j} ≤ 3`, `Σ_j q^{4j} ≤ 4` and `Σ_{j ≤ J} q^{-10 j} ≤ 2 q^{-10 J} = 2 ℓ_J^{-5/4}`, and
  `ξ² ℓ_J^{-5/4} ≤ (5/2) ξ^{49/32}` because `ℓ_J > ξ^{3/8}/2` (`ell_Jxi_bounds`).
* `tail_good_le`: on `𝒢`, a height `M > R ≥ δ` forces a band (`bandEv_of_lt_maxDev`), and
  `M < 2ξ^{99/200}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Geometric sums in `q = 2^{-1/8}` -/

namespace Lemma51

/-- `q = 2^{-1/8}` satisfies `q⁸ = 1/2`. -/
theorem q_pow_eight : ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 8 = 1 / 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem q_pos : 0 < (2 : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos two_pos _

/-- `q⁵ ≤ 2/3`, since `(q⁵)⁸ = 1/32 ≤ (2/3)⁸`. -/
theorem q_pow_five_le : ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 5 ≤ 2 / 3 := by
  have h8 := q_pow_eight
  refine (pow_le_pow_iff_left₀ (pow_nonneg q_pos.le 5) (by norm_num)
    (by norm_num : (8 : ℕ) ≠ 0)).1 ?_
  rw [← pow_mul, show 5 * 8 = 8 * 5 by norm_num, pow_mul, h8]
  norm_num

/-- `q⁴ ≤ 3/4`, since `(q⁴)² = 1/2 ≤ (3/4)²`. -/
theorem q_pow_four_le : ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4 ≤ 3 / 4 := by
  have h8 := q_pow_eight
  refine (pow_le_pow_iff_left₀ (pow_nonneg q_pos.le 4) (by norm_num)
    (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
  rw [← pow_mul, h8]
  norm_num

/-- `q² ≥ 4/5`, since `(q²)⁴ = 1/2 ≥ (4/5)⁴`. -/
theorem q_pow_two_ge : 4 / 5 ≤ ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 := by
  have h8 := q_pow_eight
  refine (pow_le_pow_iff_left₀ (by norm_num) (pow_nonneg q_pos.le 2)
    (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
  rw [← pow_mul, h8]
  norm_num

/-- `Σ_{j<n} x^j ≤ 1/(1-x)` for `0 ≤ x < 1`. -/
theorem geom_sum_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, x ^ j ≤ 1 / (1 - x) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hx0 hx1
  rwa [← Finset.range_eq_Ico, pow_zero] at h

/-- `Σ_{j ≤ J} x^j ≤ 2 x^J` for `x ≥ 2`. -/
theorem geom_sum_range_succ_le {x : ℝ} (hx : 2 ≤ x) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), x ^ j ≤ 2 * x ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hxJ : 0 ≤ x ^ J := pow_nonneg (by linarith) J
    nlinarith

end Lemma51

/-- **The union-bound sums** (blueprint, proof of `lem:lemma51`; BP2 detail D11). For `0 < ξ ≤ 1`,
`R > 0`, `M ≥ 0` and `r_j = c_β R ℓ_j^{1/8}`:
`Σ_{j ≤ J(ξ)} (4/ℓ_j) (ξ² ℓ_j²/r_j³ + ξ² M ℓ_j²/r_j⁴ + ξ² L²/r_j²)
  ≤ (12/c_β³) ξ²/R³ + (16/c_β⁴) ξ² M/R⁴ + (20/c_β²) ξ^{49/32} L²/R²`. -/
theorem sum_probe_terms_le {ξ R M L : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hR : 0 < R) (hM : 0 ≤ M) :
    ∑ j ∈ Finset.range (Jxi ξ + 1), 4 / ell j *
      (ξ ^ 2 * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 3 +
        ξ ^ 2 * M * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 4 +
        ξ ^ 2 * L ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 2) ≤
    12 / cBeta ^ 3 * (ξ ^ 2 / R ^ 3) + 16 / cBeta ^ 4 * (ξ ^ 2 * M / R ^ 4) +
      20 / cBeta ^ 2 * (ξ ^ (49 / 32 : ℝ) * L ^ 2 / R ^ 2) := by
  set q : ℝ := (2 : ℝ) ^ (-(1 / 8 : ℝ)) with hq_def
  have hq0 : 0 < q := Lemma51.q_pos
  have hq1 : q < 1 := two_rpow_neg_one_eighth_lt_one
  have h8 : q ^ 8 = 1 / 2 := Lemma51.q_pow_eight
  have hc : 0 < cBeta := cBeta_pos
  set J : ℕ := Jxi ξ with hJ
  set a₁ : ℝ := 4 / cBeta ^ 3 * (ξ ^ 2 / R ^ 3) with ha₁
  set a₂ : ℝ := 4 / cBeta ^ 4 * (ξ ^ 2 * M / R ^ 4) with ha₂
  set a₃ : ℝ := 4 / cBeta ^ 2 * (ξ ^ 2 * L ^ 2 / R ^ 2) with ha₃
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  -- each summand is a combination of three geometric terms
  have hterm : ∀ j : ℕ, 4 / ell j *
      (ξ ^ 2 * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 3 +
        ξ ^ 2 * M * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 4 +
        ξ ^ 2 * L ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 2) =
      a₁ * (q ^ 5) ^ j + a₂ * (q ^ 4) ^ j + a₃ * ((q ^ 10)⁻¹) ^ j := by
    intro j
    have hp : ell j ^ (1 / 8 : ℝ) = q ^ j := ell_rpow_one_eighth j
    have hℓ : ell j = (q ^ j) ^ 8 := by
      rw [← hp, ← Real.rpow_natCast, ← Real.rpow_mul (ell_pos j).le]
      norm_num
    have hpj : 0 < q ^ j := pow_pos hq0 j
    rw [hp, hℓ, ← pow_right_comm q j 5, ← pow_right_comm q j 4, inv_pow, ← pow_right_comm q j 10,
      ha₁, ha₂, ha₃]
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the three geometric sums
  have hs₁ : ∑ j ∈ Finset.range (J + 1), (q ^ 5) ^ j ≤ 3 := by
    refine (Lemma51.geom_sum_range_le (pow_nonneg hq0.le 5) ?_ _).trans ?_
    · linarith [Lemma51.q_pow_five_le]
    · have := Lemma51.q_pow_five_le
      rw [div_le_iff₀ (by linarith)]
      linarith
  have hs₂ : ∑ j ∈ Finset.range (J + 1), (q ^ 4) ^ j ≤ 4 := by
    refine (Lemma51.geom_sum_range_le (pow_nonneg hq0.le 4) ?_ _).trans ?_
    · linarith [Lemma51.q_pow_four_le]
    · have := Lemma51.q_pow_four_le
      rw [div_le_iff₀ (by linarith)]
      linarith
  -- `q^{10} = q²/2 ∈ [2/5, 1/2]`
  have hq10 : q ^ 10 = q ^ 2 / 2 := by
    rw [show (10 : ℕ) = 8 + 2 by norm_num, pow_add, h8]
    ring
  have hq2le : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hx2 : 2 ≤ (q ^ 10)⁻¹ := by
    rw [hq10, inv_div, le_div_iff₀ (by positivity)]
    linarith
  have hs₃ : ∑ j ∈ Finset.range (J + 1), ((q ^ 10)⁻¹) ^ j ≤ 2 * ((q ^ 10)⁻¹) ^ J :=
    Lemma51.geom_sum_range_succ_le hx2 J
  -- `ξ² q^{-10 J} ≤ (5/2) ξ^{49/32}`, from `ℓ_J > ξ^{3/8}/2`
  have hlast : ξ ^ 2 * ((q ^ 10)⁻¹) ^ J ≤ 5 / 2 * ξ ^ (49 / 32 : ℝ) := by
    obtain ⟨hlow, -⟩ := ell_Jxi_bounds hξ hξ1
    set u : ℝ := ξ ^ (3 / 64 : ℝ) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hξ _
    have hu8 : u ^ 8 = ξ ^ (3 / 8 : ℝ) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
      norm_num
    have hu10 : ξ ^ 2 = ξ ^ (49 / 32 : ℝ) * u ^ 10 := by
      rw [hu, ← Real.rpow_natCast (ξ ^ (3 / 64 : ℝ)), ← Real.rpow_mul hξ.le, ← Real.rpow_add hξ,
        ← Real.rpow_natCast]
      norm_num
    have hpJ : ell J ^ (1 / 8 : ℝ) = q ^ J := ell_rpow_one_eighth J
    have hℓJ : ell J = (q ^ J) ^ 8 := by
      rw [← hpJ, ← Real.rpow_natCast, ← Real.rpow_mul (ell_pos J).le]
      norm_num
    -- `q u < q^J`
    have hqu : q * u < q ^ J := by
      refine lt_of_pow_lt_pow_left₀ 8 (pow_nonneg hq0.le J) ?_
      rw [mul_pow, h8, hu8, ← hℓJ]
      linarith
    have hqu10 : (q * u) ^ 10 ≤ (q ^ J) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hqu.le 10
    have hq10pos : 0 < q ^ 10 := pow_pos hq0 10
    have hq10ge : 2 / 5 ≤ q ^ 10 := by
      rw [hq10]
      linarith [Lemma51.q_pow_two_ge]
    rw [inv_pow, pow_right_comm q 10 J, hu10]
    have hξ49 : 0 < ξ ^ (49 / 32 : ℝ) := Real.rpow_pos_of_pos hξ _
    have hqJ10 : 0 < (q ^ J) ^ 10 := by positivity
    rw [mul_inv_le_iff₀ hqJ10]
    calc ξ ^ (49 / 32 : ℝ) * u ^ 10 = ξ ^ (49 / 32 : ℝ) * (q * u) ^ 10 / q ^ 10 := by
          rw [mul_pow]
          field_simp
      _ ≤ ξ ^ (49 / 32 : ℝ) * (q ^ J) ^ 10 / (2 / 5) := by
          gcongr
      _ = 5 / 2 * ξ ^ (49 / 32 : ℝ) * (q ^ J) ^ 10 := by ring
  -- assemble
  have e₃ : a₃ * (2 * ((q ^ 10)⁻¹) ^ J) =
      8 / cBeta ^ 2 * (L ^ 2 / R ^ 2) * (ξ ^ 2 * ((q ^ 10)⁻¹) ^ J) := by
    rw [ha₃]
    ring
  have hL : 0 ≤ 8 / cBeta ^ 2 * (L ^ 2 / R ^ 2) := by positivity
  calc a₁ * ∑ j ∈ Finset.range (J + 1), (q ^ 5) ^ j + a₂ * ∑ j ∈ Finset.range (J + 1), (q ^ 4) ^ j +
        a₃ * ∑ j ∈ Finset.range (J + 1), ((q ^ 10)⁻¹) ^ j
      ≤ a₁ * 3 + a₂ * 4 + a₃ * (2 * ((q ^ 10)⁻¹) ^ J) := by
        gcongr
    _ ≤ a₁ * 3 + a₂ * 4 + 8 / cBeta ^ 2 * (L ^ 2 / R ^ 2) * (5 / 2 * ξ ^ (49 / 32 : ℝ)) := by
        rw [e₃]
        gcongr
    _ = _ := by
        rw [ha₁, ha₂]
        ring

/-! ## Lemma 5.1 -/

/-- **Lemma `lem:lemma51`** (source Lemma 5.1, (5.11); BP2 detail D11): for `γ` small, every
measurable a.s. geodesic `η` and `δ ≤ R ≤ 2ξ^{99/200}`,
`P[𝒢 ∩ ℬ(R)] ≤ C₅ (ξ²/R³ + ξ² (m + ξ^{99/100} L)/R⁴ + ξ^{49/32} L²/R²)`, with `m = E M(η)`. -/
theorem lemma51 (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    ∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) →
      stdP {ω | goodEv G γ ω ∧ bandEv γ R (η ω)} ≤ ENNReal.ofReal (C * (xiGamma γ ^ 2 / R ^ 3 +
        xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) / R ^ 4 +
        xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2)) := by
  obtain ⟨CP, γP, hγP, hsp⟩ := singleProbe G hCC h42
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  set A : ℝ := max CP 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  refine ⟨A * (12 / cBeta ^ 3 + 16 / cBeta ^ 4 + 20 / cBeta ^ 2), min γP γ₀, lt_min hγP hγ₀,
    fun γ hγ η hηm hη R hR1 hR2 => ?_⟩
  have hγP' : γ ∈ Ioc (0:ℝ) γP := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ.1, hγ.2.trans (min_le_right _ _)⟩
  have hξ1 : xiGamma γ ≤ 1 := hξγ.trans ((hγ.2.trans (min_le_right _ _)).trans hγ₀1.le)
  have hR : 0 < R := (Real.rpow_pos_of_pos hξ0 _).trans_le hR1
  have hm0 : 0 ≤ ∫ ω, maxDev (η ω) ∂stdP := integral_nonneg fun ω => maxDev_nonneg _
  have hL0 : 0 ≤ Lg γ := Real.log_nonneg ((one_le_inv₀ hξ0).2 hξ1)
  set M : ℝ := (∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ with hM
  have hM0 : 0 ≤ M := add_nonneg hm0 (mul_nonneg (Real.rpow_nonneg hξ0.le _) hL0)
  -- the bound of one probe at level `j`
  set T : ℕ → ℝ := fun j => xiGamma γ ^ 2 * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 3 +
      xiGamma γ ^ 2 * M * ell j ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 4 +
      xiGamma γ ^ 2 * Lg γ ^ 2 / (cBeta * R * ell j ^ (1 / 8 : ℝ)) ^ 2 with hT
  have hT0 : ∀ j, 0 ≤ T j := fun j => by
    have : 0 < cBeta * R * ell j ^ (1 / 8 : ℝ) :=
      mul_pos (mul_pos cBeta_pos hR) (Real.rpow_pos_of_pos (ell_pos j) _)
    have := ell_pos j
    simp only [hT]
    positivity
  -- the union bound
  have hsub : {ω | goodEv G γ ω ∧ bandEv γ R (η ω)} ⊆
      ⋃ j ∈ Finset.range (Jg γ + 1), ⋃ a ∈ probeGrid j,
        {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath (η ω)) j a|} := by
    rintro ω ⟨hg, j, hj, a, ha, hb⟩
    simp only [mem_iUnion]
    exact ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), a, ha, hg, hb⟩
  have hprobe : ∀ j ∈ Finset.range (Jg γ + 1), ∀ a ∈ probeGrid j,
      stdP {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath (η ω)) j a|} ≤
        ENNReal.ofReal (A * T j) := by
    intro j hj a ha
    refine (hsp γ hγP' η hηm hη R hR1 hR2 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) a
      ((probeGrid_spec j).1 ha)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hT0 j)
  calc stdP {ω | goodEv G γ ω ∧ bandEv γ R (η ω)}
      ≤ stdP (⋃ j ∈ Finset.range (Jg γ + 1), ⋃ a ∈ probeGrid j,
          {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath (η ω)) j a|}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (Jg γ + 1), stdP (⋃ a ∈ probeGrid j,
          {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath (η ω)) j a|}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (Jg γ + 1), ∑ a ∈ probeGrid j,
          stdP {ω | goodEv G γ ω ∧ cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath (η ω)) j a|} :=
        Finset.sum_le_sum fun j _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (Jg γ + 1), ∑ a ∈ probeGrid j, ENNReal.ofReal (A * T j) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun a ha => hprobe j hj a ha
    _ = ∑ j ∈ Finset.range (Jg γ + 1), ENNReal.ofReal ((probeGrid j).card * (A * T j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ j ∈ Finset.range (Jg γ + 1), ENNReal.ofReal (4 / ell j * (A * T j)) := by
        refine Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (probeGrid_spec j).2.1 (mul_nonneg hA0 (hT0 j))
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (Jg γ + 1), 4 / ell j * (A * T j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro j _
        exact mul_nonneg (div_nonneg (by norm_num) (ell_pos j).le) (mul_nonneg hA0 (hT0 j))
    _ ≤ ENNReal.ofReal (A * (12 / cBeta ^ 3 + 16 / cBeta ^ 4 + 20 / cBeta ^ 2) *
          (xiGamma γ ^ 2 / R ^ 3 + xiGamma γ ^ 2 * M / R ^ 4 +
            xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum := sum_probe_terms_le (L := Lg γ) hξ0 hξ1 hR hM0
        have e : ∑ j ∈ Finset.range (Jg γ + 1), 4 / ell j * (A * T j) =
            A * ∑ j ∈ Finset.range (Jxi (xiGamma γ) + 1), 4 / ell j * T j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e]
        have hc := cBeta_pos
        have hx : 0 ≤ xiGamma γ ^ 2 / R ^ 3 := by positivity
        have hy : 0 ≤ xiGamma γ ^ 2 * M / R ^ 4 := by positivity
        have hz : 0 ≤ xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2 := by
          have := Real.rpow_nonneg hξ0.le (49/32 : ℝ)
          positivity
        have hK₁ : 0 ≤ 12 / cBeta ^ 3 := by positivity
        have hK₂ : 0 ≤ 16 / cBeta ^ 4 := by positivity
        have hK₃ : 0 ≤ 20 / cBeta ^ 2 := by positivity
        calc A * ∑ j ∈ Finset.range (Jxi (xiGamma γ) + 1), 4 / ell j * T j
            ≤ A * (12 / cBeta ^ 3 * (xiGamma γ ^ 2 / R ^ 3) +
                16 / cBeta ^ 4 * (xiGamma γ ^ 2 * M / R ^ 4) +
                20 / cBeta ^ 2 * (xiGamma γ ^ (49 / 32 : ℝ) * Lg γ ^ 2 / R ^ 2)) :=
              mul_le_mul_of_nonneg_left hsum hA0
          _ ≤ _ := by
              have e2 : A * (12 / cBeta ^ 3 + 16 / cBeta ^ 4 + 20 / cBeta ^ 2) *
                  (xiGamma γ ^ 2 / R ^ 3 + xiGamma γ ^ 2 * M / R ^ 4 +
                    xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2) =
                  A * (12 / cBeta ^ 3 * (xiGamma γ ^ 2 / R ^ 3) +
                    16 / cBeta ^ 4 * (xiGamma γ ^ 2 * M / R ^ 4) +
                    20 / cBeta ^ 2 * (xiGamma γ ^ (49 / 32 : ℝ) * Lg γ ^ 2 / R ^ 2)) +
                  A * (12 / cBeta ^ 3 * (xiGamma γ ^ 2 * M / R ^ 4 +
                      xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2) +
                    16 / cBeta ^ 4 * (xiGamma γ ^ 2 / R ^ 3 +
                      xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2) +
                    20 / cBeta ^ 2 * (xiGamma γ ^ 2 / R ^ 3 + xiGamma γ ^ 2 * M / R ^ 4)) := by
                ring
              rw [e2]
              have : 0 ≤ A * (12 / cBeta ^ 3 * (xiGamma γ ^ 2 * M / R ^ 4 +
                      xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2) +
                    16 / cBeta ^ 4 * (xiGamma γ ^ 2 / R ^ 3 +
                      xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2) +
                    20 / cBeta ^ 2 * (xiGamma γ ^ 2 / R ^ 3 + xiGamma γ ^ 2 * M / R ^ 4)) := by
                positivity
              linarith
    _ = _ := by rw [mul_assoc]

/-! ## The tail on the good event -/

/-- **Corollary `cor:tail-good`** (source (5.12); BP2 detail D1): on `𝒢`, the probability that the
height exceeds `R ∈ [δ, 2ξ^{99/200}]` is at most the right side of Lemma 5.1, and it is `0` for
`R ≥ 2ξ^{99/200}`. -/
theorem tail_good_le (G : GSetup) (hCC : ∀ γ, 0 < γ → γ < 2 → CC.ConfCovLE γ (G.Dfam γ))
    (h42 : Lemma42) : ∃ C γ₁, 0 < γ₁ ∧ ∀ γ ∈ Ioc (0:ℝ) γ₁,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
    (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
    (∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) →
      stdP {ω | goodEv G γ ω ∧ R < maxDev (η ω)} ≤ ENNReal.ofReal (C * (xiGamma γ ^ 2 / R ^ 3 +
        xiGamma γ ^ 2 * ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99/100:ℝ) * Lg γ) / R ^ 4 +
        xiGamma γ ^ (49/32 : ℝ) * Lg γ ^ 2 / R ^ 2))) ∧
    (∀ R, 2 * xiGamma γ ^ (99/200 : ℝ) ≤ R → stdP {ω | goodEv G γ ω ∧ R < maxDev (η ω)} = 0) := by
  obtain ⟨C₅, γ₅, hγ₅, h51⟩ := lemma51 G hCC h42
  obtain ⟨γb, hγb, hband⟩ := bandEv_of_lt_maxDev G
  refine ⟨C₅, min γ₅ (min γb 1), lt_min hγ₅ (lt_min hγb one_pos), fun γ hγ η hηm hη => ?_⟩
  have hγ0 : 0 < γ := hγ.1
  have hγ5 : γ ∈ Ioc (0:ℝ) γ₅ := ⟨hγ0, hγ.2.trans (min_le_left _ _)⟩
  have hγb' : γ ∈ Ioc (0:ℝ) γb := ⟨hγ0, hγ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hγ2 : γ < 2 := by
    have := hγ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hη' : ∀ᵐ ω ∂stdP, IsGeod01 (G.S.D γ ω) 0 1 (η ω) := by
    filter_upwards [hη] with ω hω
    rw [(G.compat γ ⟨hγ0, hγ2⟩).2 ω]
    exact hω
  refine ⟨fun R hR1 hR2 => ?_, fun R hR => ?_⟩
  · refine (measure_mono_ae ?_).trans (h51 γ hγ5 η hηm hη R hR1 hR2)
    filter_upwards [hη'] with ω hω hωE
    obtain ⟨hg, hM⟩ := hωE
    exact ⟨hg, (hband γ hγb' ω hg (η ω) hω).2 R hR1 hM⟩
  · rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hη'] with ω hω hωE
    obtain ⟨hg, hM⟩ := hωE
    have := (hband γ hγb' ω hg (η ω) hω).1
    linarith

end SmallGammaGeodesics
