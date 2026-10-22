import HigherDimLQGContinuity.Unif4.SelfDiam
import HigherDimLQGContinuity.Unif4.Lemma36
import HigherDimLQGMetric.DGZ.AcrossLower

/-!
# Uniform lower half of DGZ Prop 4.8 (packet U1)

Blueprint Part D, `d:prop-u48` (NA3 §2.3, §2.15 row 6; [8]-bp `r2:prop:48`). Port of
`HigherDimLQGMetric.DGZ.acrossLower_tail` / `DGZ.AcrossLowerShape` (`DGZ/AcrossLower.lean`, MA7 D-4.8).

**Statement** (`acrossLower_unif`). Let `d ≥ 2`, `κ` admissible, `b, μ, δ > 0`. There is `C = C(d, κ, b, μ, δ) > 0`
such that for every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization and every `n`,
`P*[D_n(across B₂(0) \ B₁(0)) < 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n/C}`.

**Proof** (the proof of `DGZ.acrossLower_tail`, `d:prop-u48`):
* `g = μ/4` instead of `ξ(Q - √(2d))/4`; the coarse event is `𝒢_m` at the margin `3g = 3μ/4 < μ`, whose failure is
  bounded uniformly by `prob_G_compl_le_unif` (slope `√(2d) + g/b`);
* `ε = min(1/2, δ²/(32 d b²))` (`≤ δ²/(32 d ξ²)` as `ξ ≤ b`), `δ' = min(g ε, δ/4)`, `m = ⌊ε n⌋`;
* Lemma 3.6 (`lemma36_lower_unif`, `δ'`) and Prop 4.7 (`selfDiamShape_unif`, `g ε`) replace the fixed-`ξ` inputs;
* the deterministic covering (`DGZ.inf'_setDist_le_acrossDist`) and pair bounds are reused;
* the threshold uses `(8bc/δ)²` and the final rate `δ² log 2/(16 b²) ≤ δ² log 2/(16 ξ²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox roundLat convex_obox isOpen_obox
  obox_subset_cbox abs_latPt_roundLat_le abs_latPt_roundLat_sub_lt)
open HigherDimLFPP.Conc (quantileConst)

variable {d : ℕ}

/-- **Uniform DGZ Prop 4.8, lower half** (`d:prop-u48`; port of `DGZ.acrossLower_tail`): for `d ≥ 2`, `κ` admissible
and `b, μ, δ > 0` there is `C > 0` (depending only on `d, κ, b, μ, δ`) such that for every `ξ` with
`UHyp d κ b μ ξ`, every dyadic realization and every `n`,
`P*[D_n(across B₂(0) \ B₁(0)) < 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n/C}`. -/
theorem acrossLower_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 <
            (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + δ) * n)} ≤
              ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  -- the uniform gap `g = μ/4` and the level `η = 3g` of `𝒢_m`
  obtain ⟨g, hg0, hgdef⟩ : ∃ g : ℝ, 0 < g ∧ μ = 4 * g := ⟨μ / 4, by positivity, by ring⟩
  have hη : 3 * g < μ := by linarith
  obtain ⟨CG, hCG, hGb⟩ := prob_G_compl_le_unif (d := d) hκ (b := b) hη
  -- `ε = min(1/2, δ²/(32 d b²))` and `δ' = min(g ε, δ/4)`
  obtain ⟨ε, hε0, hε2, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε ≤ δ ^ 2 / (32 * d * b ^ 2) :=
    ⟨min (1 / 2) (δ ^ 2 / (32 * d * b ^ 2)), lt_min (by norm_num) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ', hδ'0, hδ'g, hδ'δ⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ g * ε ∧ δ' ≤ δ / 4 :=
    ⟨min (g * ε) (δ / 4), lt_min (by positivity) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C₃, hC₃, h36⟩ := lemma36_lower_unif hd hκ hb hδ'0
  obtain ⟨Csd, hCsd, hsd⟩ := selfDiamShape_unif hd hκ hb hμ (δ := g * ε) (by positivity)
  obtain ⟨k₃, hk₃⟩ := exists_mul_exp_neg_div_le hC₃ (θ := 1 / 16) (by norm_num)
  obtain ⟨kG, hkG⟩ := exists_mul_exp_neg_div_le hCG (θ := 1 / 16) (by norm_num)
  obtain ⟨ksd, hksd⟩ := exists_mul_exp_neg_div_le hCsd (θ := 1 / 16) (by norm_num)
  obtain ⟨c, hc0, hcdef⟩ : ∃ c : ℝ, 0 ≤ c ∧ quantileConst (3 / 4) = c :=
    ⟨_, HigherDimLFPP.Conc.quantileConst_nonneg _, rfl⟩
  -- the threshold `n₀` (uniform: `b` in place of `ξ`)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((((((eventually_ge_atTop 1).and
    (eventually_ge_real (1 / ε))).and (eventually_ge_real ((kG + 1) / ε))).and
    (eventually_ge_atTop (2 * ksd))).and (eventually_ge_atTop k₃)).and
    (eventually_ge_real ((3 * g + 2) / (g * ε)))).and
    (eventually_ge_real (((8 * b * c / δ) ^ 2 + 8 * Real.log 2 / δ) / Real.log 2)))
  -- the uniform rate `β = δ² log 2/(16 b²)` and the constant `C`
  obtain ⟨β, hβ0, hβdef⟩ : ∃ β : ℝ, 0 < β ∧ δ ^ 2 * Real.log 2 / (16 * b ^ 2) = β :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K₀, hK₀0, hK₀def⟩ : ∃ K₀ : ℝ, 0 < K₀ ∧ 2 * Real.exp (8 * d * Real.log 2) = K₀ :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C, hCK, hCβ, hCn⟩ : ∃ C : ℝ, K₀ ≤ C ∧ 1 / β ≤ C ∧ (n₀ : ℝ) + 1 ≤ C :=
    ⟨max (max K₀ (1 / β)) (n₀ + 1), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun ξ hξh Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hξb : ξ ≤ b := hξh.le_b
  have hgap : μ ≤ ξ * (distExp d ξ - √(2 * d)) := hξh.gap
  set Q : ℝ := distExp d ξ with hQ
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`: the probability is at most `1 ≤ C e^{-n/C}`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg_div (Nat.cast_nonneg n) ?_)
        have : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hn
        linarith
  obtain ⟨⟨⟨⟨⟨⟨hn1, hnε⟩, hnG⟩, hnsd⟩, hn3⟩, hn6⟩, hn7⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- `ε ≤ δ²/(32 d ξ²)` and the `ξ`-form of the threshold `n₇`
  have hξ2 : ξ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hξ.le hξb 2
  have hεδξ : ε ≤ δ ^ 2 / (32 * d * ξ ^ 2) := by
    refine hεδ.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
    have : (0 : ℝ) ≤ 32 * d := by positivity
    exact mul_le_mul_of_nonneg_left hξ2 this
  have hn7' : ((8 * ξ * c / δ) ^ 2 + 8 * Real.log 2 / δ) / Real.log 2 ≤ n := by
    refine le_trans ?_ hn7
    refine div_le_div_of_nonneg_right ?_ hL0.le
    have h1 : 8 * ξ * c / δ ≤ 8 * b * c / δ := by
      refine div_le_div_of_nonneg_right ?_ hδ.le
      have := mul_le_mul_of_nonneg_right hξb hc0
      linarith
    have h0 : 0 ≤ 8 * ξ * c / δ := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    linarith
  -- the scale `m = ⌊ε n⌋`
  have hεn : 1 ≤ ε * n := by
    rw [div_le_iff₀ hε0] at hnε
    linarith
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, ⌊ε * n⌋₊ = m := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [← hmdef]
    exact Nat.le_floor (by exact_mod_cast hεn)
  have hmle : (m : ℝ) ≤ ε * n := by
    rw [← hmdef]
    exact Nat.floor_le (by positivity)
  have hmge : ε * n < m + 1 := by
    rw [← hmdef]
    exact Nat.lt_floor_add_one _
  have hεn2 : ε * n ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right hε2 hn0.le
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnm : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  -- the bad events have probability `≤ 1/16` each
  have hP3 : C₃ * Real.exp (-(n : ℝ) / C₃) ≤ 1 / 16 := hk₃ n hn3
  have hPG : CG * Real.exp (-(m : ℝ) / CG) ≤ 1 / 16 := by
    refine hkG m ?_
    have h1 : (kG : ℝ) + 1 ≤ ε * n := by
      rw [div_le_iff₀ hε0] at hnG
      linarith
    have : (kG : ℝ) < m + 1 := by linarith
    have : kG < m + 1 := by exact_mod_cast this
    omega
  have hPsd : Csd * Real.exp (-((n - m : ℕ) : ℝ) / Csd) ≤ 1 / 16 := by
    refine hksd (n - m) ?_
    have h1 : (2 * ksd : ℝ) ≤ n := by exact_mod_cast hnsd
    have : (ksd : ℝ) ≤ ((n - m : ℕ) : ℝ) := by rw [hnm]; linarith
    exact_mod_cast this
  -- the grid `s = 2^{-(m+1)}` and the boxes of radius `r = 2^{-m}`
  have hs0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (m + 1) := by positivity
  have hsr : (2 : ℝ)⁻¹ ^ (m + 1) < (2 : ℝ)⁻¹ ^ m :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self m)
  have hr2 : (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 := by
    calc (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
      _ = 1 / 2 := by norm_num
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  -- thresholds `Z = 2^{-(1-ξQ+δ')n}` and `X' = 2^{-(ξQ-3g)m} Z/4`
  obtain ⟨Z, hZ0, hZdef⟩ : ∃ Z : ℝ, 0 < Z ∧ (2 : ℝ) ^ (-(1 - ξ * Q + δ') * n) = Z :=
    ⟨_, Real.rpow_pos_of_pos two_pos _, rfl⟩
  obtain ⟨X', hX'def⟩ : ∃ X' : ℝ,
      (2 : ℝ) ^ (-(1 - ξ * Q + δ') * n) / 4 * (2 : ℝ) ^ (-((ξ * Q - 3 * g) * m)) = X' :=
    ⟨_, rfl⟩
  have hX'Z : (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * X' = Z / 4 := by
    rw [← hX'def, two_rpow_mul_div_four_mul, hZdef]
  have hthr : (2 : ℝ) ^ (-(1 - ξ * Q - g * ε) * ((n - m : ℕ) : ℝ)) ≤
      X' / (2 : ℝ)⁻¹ ^ m := by
    rw [← hX'def]
    refine two_rpow_threshold_le hmn hg0 hε0 hδ'g hmge ?_
    rw [div_le_iff₀ (by positivity)] at hn6
    linarith
  have hE3 : ∀ w : Rd d,
      P {ω | X' < selfDiam ξ (fun z => H n z ω - H m z ω) w ((2 : ℝ)⁻¹ ^ m)} ≤
        ENNReal.ofReal (1 / 16) := by
    intro w
    rw [measure_lt_selfDiam_band_eq hκ hH hmn hG ξ w X']
    refine (measure_mono fun ω hω => ?_).trans ((hsd ξ hξh Ω P W H hH (n - m)).trans
      (ENNReal.ofReal_le_ofReal hPsd))
    exact lt_of_le_of_lt hthr hω
  have hbig := log_two_add_le_of_le hξ hc0 hδ hn7'
  -- the pair estimate
  have hpair : ∀ p ∈ innerSites d (m + 1) ×ˢ outerSites d (m + 1),
      P {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))) <
          (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
        ENNReal.ofReal (2 * Real.exp (-(δ / 2 * (n * Real.log 2)) ^ 2 /
          (2 * ξ ^ 2 * (n * Real.log 2)))) := by
    intro p hp
    obtain ⟨hy, hx⟩ := Finset.mem_product.1 hp
    have ha2 := latPt_inner_mem_cbox hy
    have hb2 := latPt_outer_mem_cbox hx
    have haV := obox_subset_obox_three ha2 hr2
    have hbV := obox_subset_obox_three hb2 hr2
    -- (1) `P[S < Z/2] ≤ 1/4`
    have hE1 : P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3)
        (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) < Z} ≤
        ENNReal.ofReal (1 / 16) := by
      rw [← hZdef]
      exact (h36 ξ hξ hξb Ω P W H hH _ _ ha2 hb2 (exists_half_le_abs_sub (by omega) hy hx) n).trans
        (ENNReal.ofReal_le_ofReal hP3)
    have hbad := (measure_setDist_lt_half_le hξ hH (n := n) hsr hs0.le haV hbV hX'Z).trans
      (add_le_add (add_le_add (add_le_add hE1
        ((hGb ξ Q hξ hξb hgap hH m).trans (ENNReal.ofReal_le_ofReal hPG))) (hE3 _)) (hE3 _))
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hbad
    norm_num at hbad
    -- (2), (3) concentration and the tail at `2^{-(1-ξQ+δ)n}`
    refine measure_setDist_lt_le hκ hξ hH hn1 (isCompact_cbox _ _) ⟨_, fun i => by
      rw [sub_self, abs_zero]; exact hs0.le⟩ (HigherDimLFPP.DGZ.isClosed_cbox _ _) ⟨_, fun i => by
      rw [sub_self, abs_zero]; exact hs0.le⟩ (disjoint_cbox_pair (by omega) hy hx)
      ((cbox_subset_obox hsr).trans haV) ((cbox_subset_obox hsr).trans hbV)
      (div_pos hZ0 two_pos) (by positivity) (by simpa using hbad) ?_
    rw [Real.log_div hZ0.ne' two_ne_zero, ← hZdef, Real.log_rpow two_pos, Real.log_rpow two_pos,
      hcdef]
    have h1 : δ' * (n * Real.log 2) ≤ δ / 4 * (n * Real.log 2) :=
      mul_le_mul_of_nonneg_right hδ'δ (by positivity)
    linarith only [h1, hbig]
  -- (4) the union bound over the pairs
  have hincl : {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 < (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ⊆
      ⋃ p ∈ innerSites d (m + 1) ×ˢ outerSites d (m + 1),
        {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
          (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
          (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))) <
            (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} := by
    intro ω hω
    obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_inf'
      (innerSites_prod_outerSites_nonempty hd1 (m + 1))
      (fun p => lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))))
    have hle := inf'_setDist_le_acrossDist hd1 ((hH.band n).continuous ω) (m + 1) (ξ := ξ)
    have hlt := lt_of_le_of_lt hle hω
    rw [hpeq] at hlt
    exact mem_iUnion₂.2 ⟨p, hp, hlt⟩
  have hexpo : -(δ / 2 * (n * Real.log 2)) ^ 2 / (2 * ξ ^ 2 * (n * Real.log 2)) =
      -(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n) := by
    field_simp
    ring
  rw [hexpo] at hpair
  refine (measure_mono hincl).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum hpair).trans ?_))
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the `ξ`-rate `δ² log 2/(16 ξ²)` is at least the uniform `β`
  have hβξ : β ≤ δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) := by
    rw [← hβdef]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hξ2 (by norm_num)
  have hβC : Real.exp (-(δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n)) ≤ Real.exp (-(n : ℝ) / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hC0]
    have h1 : 1 ≤ β * C := by
      rw [div_le_iff₀ hβ0] at hCβ
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h3 : β * n ≤ δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n :=
      mul_le_mul_of_nonneg_right hβξ (Nat.cast_nonneg n)
    have h4 : (n : ℝ) * (β * C) = β * n * C := by ring
    have h5 : β * n * C ≤ δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n * C :=
      mul_le_mul_of_nonneg_right h3 hC0.le
    linarith only [h2, h4, h5]
  calc ((innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card : ℝ) *
        (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n)))
      ≤ Real.exp (2 * d * (m + 4) * Real.log 2) *
        (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n))) :=
        mul_le_mul_of_nonneg_right (card_innerSites_prod_le m) (by positivity)
    _ ≤ K₀ * Real.exp (-(δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n)) := by
        rw [← hK₀def]
        exact exp_card_mul_le hξ hd1 hεδξ hmle
    _ ≤ C * Real.exp (-(n : ℝ) / C) := mul_le_mul hCK hβC (Real.exp_pos _).le hC0.le

end HigherDimLQGContinuity
