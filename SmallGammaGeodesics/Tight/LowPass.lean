import SmallGammaGeodesics.Upper.Basic
import SmallGammaGeodesics.Tight.Modulus
import SmallGammaGeodesics.Assembly.Transfer

/-!
# §6: the deterministic part of the tightness proof (packet P-T1)

Blueprint `blueprint/sections/s6-tightness.tex` (Lemmas `lem:good-horizontal`, `lem:dyadic-sum`,
`lem:lowpass-holder`, `lem:rescaled-modulus`); statements of `planning/packets/BP2-planned-statements.md`
(§6 block), BP2 details D13–D14, rulings G12 and G27. Everything here is deterministic.

* `horizDev_le_of_approx` (`lem:good-horizontal` (a), source (6.1)/(1.11)): for a `Δ`-Euclidean geodesic with
  `Δ ≤ ξ^{99/100}` and `0 < ξ ≤ γ`, `hd_{γ^{2/3}}(η) ≤ 3 ξ^{97/300}`.
* `lowPass_remainder_le_of_approx` (`lem:good-horizontal` (b), source (6.2)): the high-frequency remainder
  `R_J = y − S_J` at the top level `J = J(ξ)` is at most `13 C₄ ξ^{19/1200} ξ^{2/3}`.
* `sum_ell_rpow_min_le` (`lem:dyadic-sum`, source (6.6)):
  `∑_{j ≤ J} ℓ_j^{1/8} min{1, r/ℓ_j} ≤ 15 r^{1/8}` for `0 ≤ r ≤ 1`.
* `lowPass_holder` (`lem:lowpass-holder`, source (6.5)–(6.7)): band bounds `|B_{j,a}| ≤ b ℓ_j^{1/8}` on the
  grid give `S_J(0) = 0` and the Hölder bound `|S_J(s) − S_J(t)| ≤ C_S b |s − t|^{1/8}` (`C_S = 1050π`).
* `rescaled_mem_modulusSet` (`lem:rescaled-modulus`): under the small-scale lower bound for `d` and the band
  bounds at the scale `K ξ^{2/3}`, the rescaled path `X = (η − id)/γ^{2/3}` has the modulus
  `ω_K(r) = C₁ K r^{1/8} + C₂ r^{1/200} + 3 r^{7/15}`.

Proof of `sum_ell_rpow_min_le` (written out). Let `p = 2^{-1/8}`, so `ℓ_j^{1/8} = p^j` and `p^8 = 1/2`, whence
`10/11 < p < 367/400`. For `0 < r ≤ 1` let `j₀` be the least `j` with `ℓ_j < r`; then `j₀ = k + 1 ≥ 1` with
`ℓ_k ≥ r`. The terms `j < j₀` equal `r (2p)^j`, and `∑_{j < j₀} r (2p)^j ≤ r (2p)^{j₀}/(2p − 1) =
(2p/(2p − 1)) · r ℓ_k^{1/8}/ℓ_k ≤ (2p/(2p − 1)) r^{1/8}`, because `r^{7/8} ≤ ℓ_k^{7/8}`. The terms `j ≥ j₀` are at
most `p^j`, and `∑_{j ≥ j₀} p^j ≤ p^{j₀}/(1 − p) = ℓ_{j₀}^{1/8}/(1 − p) ≤ r^{1/8}/(1 − p)`. Finally
`2p/(2p − 1) ≤ 20/9` (as `p ≥ 10/11`) and `1/(1 − p) ≤ 400/33` (as `p ≤ 367/400`), and `20/9 + 400/33 < 15`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Lemma `lem:good-horizontal`: the horizontal displacement and the high frequencies -/

/-- `ξ^{99/100} = ξ^{97/300} ξ^{2/3}` for `ξ > 0`. -/
theorem Tight.rpow_ninetyNine_hundredths_eq {ξ : ℝ} (hξ : 0 < ξ) :
    ξ ^ (99 / 100 : ℝ) = ξ ^ (97 / 300 : ℝ) * ξ ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_add hξ]
  norm_num

/-- **Lemma `lem:good-horizontal` (a)** (source (6.1), (1.11); BP2 D14), deterministic form: if `η` is a
`Δ`-Euclidean geodesic with `Δ ≤ ξ^{99/100}` and `0 < ξ ≤ γ`, then
`hd_{γ^{2/3}}(η) = sup_t |Re η(t) − t|/γ^{2/3} ≤ 3Δ/ξ^{2/3} ≤ 3 ξ^{97/300}`. -/
theorem horizDev_le_of_approx {γ ξ Δ : ℝ} {d} {η} (hd : ApproxGeod d η Δ) (hΔ : Δ ≤ ξ ^ (99/100 : ℝ))
    (hξ : 0 < ξ) (hξγ : ξ ≤ γ) : horizDev (γ ^ (2/3 : ℝ)) η ≤ 3 * ξ ^ (97/300 : ℝ) := by
  have hγ : 0 < γ := hξ.trans_le hξγ
  have hs : 0 < γ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hγ _
  have hsξ : ξ ^ (2 / 3 : ℝ) ≤ γ ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hξ.le hξγ (by norm_num)
  have he0 : 0 ≤ 3 * ξ ^ (97 / 300 : ℝ) := by positivity
  unfold horizDev
  refine ciSup_le fun t => ?_
  rw [div_le_iff₀ hs]
  calc |(η t).re - (t : ℝ)| ≤ 3 * Δ := hd.abs_re_sub_le t
    _ ≤ 3 * ξ ^ (99 / 100 : ℝ) := by linarith
    _ = 3 * ξ ^ (97 / 300 : ℝ) * ξ ^ (2 / 3 : ℝ) := by
        rw [Tight.rpow_ninetyNine_hundredths_eq hξ]
        ring
    _ ≤ 3 * ξ ^ (97 / 300 : ℝ) * γ ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hsξ he0

/-- The two pieces of (X5) at the top level, separately: for `0 < ξ ≤ 1` and `0 ≤ Δ ≤ ξ^{99/100}`,
`√(ℓ_{J(ξ)} Δ) ≤ ξ^{19/1200} ξ^{2/3}` and `Δ ≤ ξ^{19/1200} ξ^{2/3}` (since `3/16 + 99/200 = 819/1200 ≤ 99/100`
and `819/1200 − 2/3 = 19/1200`). -/
theorem Tight.sqrt_ell_Jxi_mul_le_and_le {ξ Δ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ ξ ^ (99 / 100 : ℝ)) :
    Real.sqrt (ell (Jxi ξ) * Δ) ≤ ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) ∧
      Δ ≤ ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) := by
  have hℓ := (ell_Jxi_bounds h0 h1).2
  have key : ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) = ξ ^ (819 / 1200 : ℝ) := by
    rw [← Real.rpow_add h0]
    norm_num
  rw [key]
  constructor
  · calc Real.sqrt (ell (Jxi ξ) * Δ) ≤ Real.sqrt (ξ ^ (3 / 8 : ℝ) * ξ ^ (99 / 100 : ℝ)) :=
          Real.sqrt_le_sqrt (mul_le_mul hℓ hΔ hΔ0 (by positivity))
      _ = ξ ^ (819 / 1200 : ℝ) := by
          rw [← Real.rpow_add h0, Real.sqrt_eq_rpow, ← Real.rpow_mul h0.le]
          norm_num
  · exact hΔ.trans (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num))

/-- **Lemma `lem:good-horizontal` (b)** (source (6.2)), deterministic form: there is `C₄ ≥ 0` (the constant of
`lemma41_lowPass`, made nonnegative) such that for every `Δ`-Euclidean geodesic `η` with `0 < ξ ≤ 1` and
`Δ ≤ ξ^{99/100}`, the remainder `R_J = y − S_J` at `J = J(ξ)` satisfies
`|R_J(t)| ≤ C₄ (5 √(ℓ_J Δ) + 8Δ) ≤ 13 C₄ ξ^{19/1200} ξ^{2/3}` on `[0,1]`. -/
theorem lowPass_remainder_le_of_approx : ∃ C₄, 0 ≤ C₄ ∧ ∀ {ξ Δ : ℝ} {d} {η}, ApproxGeod d η Δ → 0 < ξ → ξ ≤ 1 →
    Δ ≤ ξ ^ (99/100 : ℝ) → ∀ t ∈ Icc (0:ℝ) 1,
      |yPath η t - lowPass (yPath η) (Jxi ξ) t| ≤ 13 * C₄ * ξ ^ (19/1200 : ℝ) * ξ ^ (2/3 : ℝ) := by
  obtain ⟨C, hC⟩ := lemma41_lowPass
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ Δ d η h h0 h1 hΔ t ht
  have hyc : ContinuousOn (yPath η) (Icc 0 1) := (continuous_yPath η).continuousOn
  have hrem := hC (yPath η) hyc (yPath_zero h.zero) (yPath_one h.one) (Jxi ξ) t ht
  have hmod := h.modulus_yPath_le (ell (Jxi ξ))
  have hmod0 : 0 ≤ modulus (yPath η) (ell (Jxi ξ)) := modulus_nonneg hyc (ell_pos _).le
  obtain ⟨hs, hΔ'⟩ := Tight.sqrt_ell_Jxi_mul_le_and_le h0 h1 h.nonneg hΔ
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc |yPath η t - lowPass (yPath η) (Jxi ξ) t| ≤ C * modulus (yPath η) (ell (Jxi ξ)) := hrem
    _ ≤ max C 0 * modulus (yPath η) (ell (Jxi ξ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmod0
    _ ≤ max C 0 * (5 * Real.sqrt (ell (Jxi ξ) * Δ) + 8 * Δ) :=
        mul_le_mul_of_nonneg_left hmod hC0
    _ ≤ max C 0 * (13 * (ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        linarith
    _ = 13 * max C 0 * ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) := by ring

/-! ## Lemma `lem:dyadic-sum` -/

/-- `p = 2^{-1/8}` satisfies `p^8 = 1/2`. -/
theorem Tight.two_rpow_neg_one_eighth_pow_eight : ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 8 = 1 / 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `10/11 < 2^{-1/8} < 367/400`. -/
theorem Tight.two_rpow_neg_one_eighth_bounds :
    (10 / 11 : ℝ) < (2 : ℝ) ^ (-(1 / 8 : ℝ)) ∧ (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 367 / 400 := by
  have hp0 : 0 ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
  have h8 := Tight.two_rpow_neg_one_eighth_pow_eight
  constructor
  · exact lt_of_pow_lt_pow_left₀ 8 hp0 (by rw [h8]; norm_num)
  · exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) (by rw [h8]; norm_num)

/-- `ℓ_j^{1/8} (r/ℓ_j) = r (2 · 2^{-1/8})^j`. -/
theorem Tight.ell_rpow_one_eighth_mul_div (j : ℕ) (r : ℝ) :
    ell j ^ (1 / 8 : ℝ) * (r / ell j) = r * (2 * (2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ j := by
  rw [ell_rpow_one_eighth, div_eq_mul_inv r (ell j), inv_ell, mul_pow]
  ring

/-- If `0 < r ≤ ℓ_k`, then `r (2 · 2^{-1/8})^k = r ℓ_k^{1/8}/ℓ_k ≤ r^{1/8}`. -/
theorem Tight.mul_two_mul_pow_le {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : r ≤ ell k) :
    r * (2 * (2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ k ≤ r ^ (1 / 8 : ℝ) := by
  have hℓ : 0 < ell k := ell_pos k
  rw [← Tight.ell_rpow_one_eighth_mul_div, mul_div_assoc', div_le_iff₀ hℓ]
  -- `ℓ^{1/8} r ≤ r^{1/8} ℓ`, from `r^{7/8} ≤ ℓ^{7/8}`
  have h78 : r ^ (7 / 8 : ℝ) ≤ ell k ^ (7 / 8 : ℝ) := Real.rpow_le_rpow hr.le hk (by norm_num)
  have er : r = r ^ (1 / 8 : ℝ) * r ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hr]
    norm_num
  have eℓ : ell k = ell k ^ (1 / 8 : ℝ) * ell k ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hℓ]
    norm_num
  calc ell k ^ (1 / 8 : ℝ) * r = ell k ^ (1 / 8 : ℝ) * (r ^ (1 / 8 : ℝ) * r ^ (7 / 8 : ℝ)) := by
        rw [← er]
    _ ≤ ell k ^ (1 / 8 : ℝ) * (r ^ (1 / 8 : ℝ) * ell k ^ (7 / 8 : ℝ)) := by gcongr
    _ = r ^ (1 / 8 : ℝ) * (ell k ^ (1 / 8 : ℝ) * ell k ^ (7 / 8 : ℝ)) := by ring
    _ = r ^ (1 / 8 : ℝ) * ell k := by rw [← eℓ]

/-- **Lemma `lem:dyadic-sum`** (source (6.6), `β = 1/8`): for `0 ≤ r ≤ 1`,
`∑_{j ≤ J} ℓ_j^{1/8} min{1, r/ℓ_j} ≤ 15 r^{1/8}` (the constant is `C_{1/8} ≈ 14.25`). -/
theorem sum_ell_rpow_min_le (J : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ j ∈ Finset.range (J + 1), ell j ^ (1/8 : ℝ) * min 1 (r / ell j) ≤ 15 * r ^ (1/8 : ℝ) := by
  rcases hr0.eq_or_lt with hr | hr
  · -- `r = 0`: every term vanishes
    subst hr
    have : ∀ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ) * min 1 (0 / ell j) = 0 := by
      intro j _
      rw [zero_div, min_eq_right zero_le_one, mul_zero]
    rw [Finset.sum_eq_zero this]
    positivity
  set p : ℝ := (2 : ℝ) ^ (-(1 / 8 : ℝ)) with hp
  obtain ⟨hp1, hp2⟩ := Tight.two_rpow_neg_one_eighth_bounds
  rw [← hp] at hp1 hp2
  have hp0 : 0 ≤ p := by positivity
  have hplt : p < 1 := by linarith
  set f : ℕ → ℝ := fun j => ell j ^ (1 / 8 : ℝ) * min 1 (r / ell j) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf]
    exact mul_nonneg (Real.rpow_nonneg (ell_pos j).le _)
      (le_min zero_le_one (div_nonneg hr.le (ell_pos j).le))
  -- the first level with `ℓ_j < r`
  have hex : ∃ j, ell j < r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rwa [ell, ← inv_pow, ← one_div]
  classical
  set j₀ := Nat.find hex with hj₀
  have hj₀lt : ell j₀ < r := Nat.find_spec hex
  have hj₀min : ∀ j < j₀, r ≤ ell j := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · exfalso
      rw [h, ell_zero] at hj₀lt
      linarith
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, j₀ = k + 1 := ⟨j₀ - 1, by omega⟩
  have hkℓ : r ≤ ell k := hj₀min k (by omega)
  -- extend the sum and split at `j₀`
  set N := max (J + 1) j₀ with hN
  have hext : ∑ j ∈ Finset.range (J + 1), f j ≤ ∑ j ∈ Finset.range N, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _))
      fun j _ _ => hf0 j
  rw [← Finset.sum_range_add_sum_Ico f (le_max_right (J + 1) j₀)] at hext
  -- the low levels: a geometric sum dominated by its last term
  have hlow : ∑ j ∈ Finset.range j₀, f j ≤ 20 / 9 * r ^ (1 / 8 : ℝ) := by
    have hq1 : 1 < 2 * p := by linarith
    have hterm : ∀ j ∈ Finset.range j₀, f j = r * (2 * p) ^ j := by
      intro j hj
      have hjr : r / ell j ≤ 1 := (div_le_one (ell_pos j)).2 (hj₀min j (Finset.mem_range.1 hj))
      simp only [hf]
      rw [min_eq_right hjr, Tight.ell_rpow_one_eighth_mul_div]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, geom_sum_eq hq1.ne']
    have hk' := Tight.mul_two_mul_pow_le hr hkℓ
    rw [← hp] at hk'
    have hq0 : 0 < 2 * p - 1 := by linarith
    rw [mul_div_assoc', div_le_iff₀ hq0, hk, pow_succ]
    -- `r ((2p)^k (2p) − 1) ≤ (20/9) r^{1/8} (2p − 1)`
    have hr18 : 0 ≤ r ^ (1 / 8 : ℝ) := by positivity
    have h1 : r * ((2 * p) ^ k * (2 * p) - 1) ≤ r * (2 * p) ^ k * (2 * p) := by
      nlinarith [hr]
    have h2 : r * (2 * p) ^ k * (2 * p) ≤ r ^ (1 / 8 : ℝ) * (2 * p) :=
      mul_le_mul_of_nonneg_right hk' (by linarith)
    have h3 : r ^ (1 / 8 : ℝ) * (2 * p) ≤ 20 / 9 * r ^ (1 / 8 : ℝ) * (2 * p - 1) := by
      have : 2 * p ≤ 20 / 9 * (2 * p - 1) := by linarith
      calc r ^ (1 / 8 : ℝ) * (2 * p) ≤ r ^ (1 / 8 : ℝ) * (20 / 9 * (2 * p - 1)) :=
            mul_le_mul_of_nonneg_left this hr18
        _ = 20 / 9 * r ^ (1 / 8 : ℝ) * (2 * p - 1) := by ring
    linarith
  -- the high levels: at most `ℓ_j^{1/8}` each
  have hhigh : ∑ j ∈ Finset.Ico j₀ N, f j ≤ 400 / 33 * r ^ (1 / 8 : ℝ) := by
    have hterm : ∀ j ∈ Finset.Ico j₀ N, f j ≤ p ^ j := by
      intro j _
      simp only [hf]
      rw [hp, ← ell_rpow_one_eighth]
      calc ell j ^ (1 / 8 : ℝ) * min 1 (r / ell j) ≤ ell j ^ (1 / 8 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (ell_pos j).le _)
        _ = ell j ^ (1 / 8 : ℝ) := mul_one _
    refine (Finset.sum_le_sum hterm).trans ((geom_sum_Ico_le_of_lt_one hp0 hplt).trans ?_)
    have hj₀r : p ^ j₀ ≤ r ^ (1 / 8 : ℝ) := by
      rw [hp, ← ell_rpow_one_eighth]
      exact Real.rpow_le_rpow (ell_pos _).le hj₀lt.le (by norm_num)
    have h1p : 0 < 1 - p := by linarith
    rw [div_le_iff₀ h1p]
    have : 1 ≤ 400 / 33 * (1 - p) := by linarith
    have hr18 : 0 ≤ r ^ (1 / 8 : ℝ) := by positivity
    nlinarith
  calc ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ) * min 1 (r / ell j)
      = ∑ j ∈ Finset.range (J + 1), f j := rfl
    _ ≤ ∑ j ∈ Finset.range j₀, f j + ∑ j ∈ Finset.Ico j₀ N, f j := hext
    _ ≤ 20 / 9 * r ^ (1 / 8 : ℝ) + 400 / 33 * r ^ (1 / 8 : ℝ) := add_le_add hlow hhigh
    _ ≤ 15 * r ^ (1 / 8 : ℝ) := by
        have hr18 : 0 ≤ r ^ (1 / 8 : ℝ) := by positivity
        nlinarith

/-! ## Lemma `lem:lowpass-holder` -/

/-- `S_J(0) = 0`: every `sin(kπ·)` vanishes at `0`. -/
theorem Tight.lowPass_zero (y : ℝ → ℝ) (J : ℕ) : lowPass y J 0 = 0 := by
  unfold lowPass
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_zero, Real.sin_zero, mul_zero]

/-- **Lemma `lem:lowpass-holder`** (source (6.5)–(6.7); ruling G13: no Bernstein inequality). There is
`C_S ≥ 0` (`C_S = 1050π`) such that for every `y` continuous on `[0,1]`, `J ∈ ℕ` and `b ≥ 0`: if
`|B_{j,a}(y)| ≤ b ℓ_j^{1/8}` for all `j ≤ J` and `a ∈ 𝒜_j`, then `S_J(y)(0) = 0` and
`|S_J(y)(s) − S_J(y)(t)| ≤ C_S b |s − t|^{1/8}` on `[0,1]`.

Proof: the grid lemma gives `sup_ℝ |B_j| ≤ 2b ℓ_j^{1/8}`, the band increment bound (`band_holder`) gives
`|B_j(s) − B_j(t)| ≤ 70π b ℓ_j^{1/8} min{1, |s − t|/ℓ_j}`, and `S_J = ∑_{j ≤ J} B_j` with
`∑_{j ≤ J} ℓ_j^{1/8} min{1, r/ℓ_j} ≤ 15 r^{1/8}` (`sum_ell_rpow_min_le`). -/
theorem lowPass_holder : ∃ C, 0 ≤ C ∧ ∀ (y : ℝ → ℝ), ContinuousOn y (Icc 0 1) → ∀ (J : ℕ) (b : ℝ), 0 ≤ b →
    (∀ j ≤ J, ∀ a ∈ probeGrid j, |band y j a| ≤ b * ell j ^ (1/8 : ℝ)) →
    lowPass y J 0 = 0 ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      |lowPass y J s - lowPass y J t| ≤ C * b * |s - t| ^ (1/8 : ℝ) := by
  refine ⟨1050 * Real.pi, by positivity, fun y hy J b hb hband => ⟨Tight.lowPass_zero y J, ?_⟩⟩
  intro s hs t ht
  -- the sup bound of every band on `ℝ`
  have hsup : ∀ j ≤ J, ∀ a, |band y j a| ≤ 2 * b * ell j ^ (1 / 8 : ℝ) := by
    intro j hj a
    obtain ⟨a', ha', hle⟩ := (probeGrid_spec j).2.2 y hy a
    calc |band y j a| ≤ 2 * |band y j a'| := hle
      _ ≤ 2 * (b * ell j ^ (1 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hband j hj a' ha') (by norm_num)
      _ = 2 * b * ell j ^ (1 / 8 : ℝ) := by ring
  have hr0 : 0 ≤ |s - t| := abs_nonneg _
  have hr1 : |s - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  rw [← sum_band_eq_lowPass, ← sum_band_eq_lowPass, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range (J + 1), (band y j s - band y j t)|
      ≤ ∑ j ∈ Finset.range (J + 1), |band y j s - band y j t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          35 * Real.pi * (2 * b * ell j ^ (1 / 8 : ℝ)) * min 1 (|s - t| / ell j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact band_holder y j (hsup j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) s t
    _ = 70 * Real.pi * b *
          ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ) * min 1 (|s - t| / ell j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 70 * Real.pi * b * (15 * |s - t| ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_ell_rpow_min_le J hr0 hr1) (by positivity)
    _ = 1050 * Real.pi * b * |s - t| ^ (1 / 8 : ℝ) := by ring

/-! ## Lemma `lem:rescaled-modulus` -/

/-- `‖X(u) − X(v)‖ = ‖(η u − u) − (η v − v)‖ / s` for the rescaled path `X = (η − id)/s`, `s > 0`. -/
theorem Tight.norm_rescaledPath_sub {s : ℝ} (hs : 0 < s) (η : C(unitInterval, ℂ)) (u v : unitInterval) :
    ‖rescaledPath s η u - rescaledPath s η v‖ =
      ‖(η u - ((u : ℝ) : ℂ)) - (η v - ((v : ℝ) : ℂ))‖ / s := by
  have e : rescaledPath s η u - rescaledPath s η v =
      ((η u - ((u : ℝ) : ℂ)) - (η v - ((v : ℝ) : ℂ))) / (s : ℂ) := by
    show (η u - ((u : ℝ) : ℂ)) / (s : ℂ) - (η v - ((v : ℝ) : ℂ)) / (s : ℂ) = _
    ring
  rw [e, Complex.norm_div, Complex.norm_of_nonneg hs.le]

/-- The small-scale case of `lem:rescaled-modulus`: if `‖η u − η v‖ ≤ (2r)^{4/5}` with `r = |u − v| ≤ γ² ≤ 1`,
then `‖(η u − u) − (η v − v)‖ ≤ 3 r^{7/15} γ^{2/3}`. -/
theorem Tight.norm_sub_le_of_small {γ r : ℝ} (hγ : 0 < γ) (hr0 : 0 ≤ r) (hr : r ≤ γ ^ 2) (hr1 : r ≤ 1)
    {z w : ℂ} (hzw : ‖z - w‖ ≤ (2 * r) ^ (4 / 5 : ℝ)) {u v : ℝ} (huv : |u - v| = r) :
    ‖(z - (u : ℂ)) - (w - (v : ℂ))‖ ≤ 3 * r ^ (7 / 15 : ℝ) * γ ^ (2 / 3 : ℝ) := by
  have h1 : ‖(z - (u : ℂ)) - (w - (v : ℂ))‖ ≤ ‖z - w‖ + r := by
    have e : (z - (u : ℂ)) - (w - (v : ℂ)) = (z - w) - ((u - v : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, huv]
  have h2 : (2 * r) ^ (4 / 5 : ℝ) ≤ 2 * r ^ (4 / 5 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hr0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr0 _)
    calc (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : r ≤ r ^ (4 / 5 : ℝ) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ (4 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 (by norm_num) (by norm_num)
  have h4 : r ^ (4 / 5 : ℝ) = r ^ (7 / 15 : ℝ) * r ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add' hr0 (by norm_num)]
    norm_num
  have h5 : r ^ (1 / 3 : ℝ) ≤ γ ^ (2 / 3 : ℝ) := by
    calc r ^ (1 / 3 : ℝ) ≤ (γ ^ 2) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hr0 hr (by norm_num)
      _ = γ ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hγ.le]
          norm_num
  have h715 : 0 ≤ r ^ (7 / 15 : ℝ) := Real.rpow_nonneg hr0 _
  calc ‖(z - (u : ℂ)) - (w - (v : ℂ))‖ ≤ ‖z - w‖ + r := h1
    _ ≤ 2 * r ^ (4 / 5 : ℝ) + r ^ (4 / 5 : ℝ) := by linarith
    _ = 3 * (r ^ (7 / 15 : ℝ) * r ^ (1 / 3 : ℝ)) := by rw [← h4]; ring
    _ ≤ 3 * (r ^ (7 / 15 : ℝ) * γ ^ (2 / 3 : ℝ)) := by gcongr
    _ = 3 * r ^ (7 / 15 : ℝ) * γ ^ (2 / 3 : ℝ) := by ring

/-- **Lemma `lem:rescaled-modulus`** (BP2 D13; ruling G12). There are `C₁, C₂ ≥ 0` (`C₁ = C_S c_β`,
`C₂ = 6 + 26 C₄`) such that, with `ω_K(r) = C₁ K r^{1/8} + C₂ r^{1/200} + 3 r^{7/15}`: for `0 < ξ ≤ γ ≤ 1`,
`K ≥ 1`, `γ² < τ_n = (2^{-n})^{5/4}/2`, a `Δ`-Euclidean geodesic `η` for `d` with `Δ ≤ ξ^{99/100}`, the
small-scale lower bound `d(z,w) ≥ |z − w|^{5/4}` on `B̄₂` for `0 < |z − w| ≤ 2^{-n}`, and the band bounds
`|B_{j,a}(y_η)| ≤ c_β K ξ^{2/3} ℓ_j^{1/8}` (`j ≤ J(ξ)`, `a ∈ 𝒜_j`), the rescaled path `X^{γ^{2/3}}(η)` lies in
`modulusSet ω_K`.

Proof. `X(0) = 0`. Let `r = |s − t|`. If `r ≤ γ²` (in particular `r < τ_n`), Corollary 6.0′ gives
`|η(s) − η(t)| ≤ (2r)^{4/5}`, and `γ^{2/3} ≥ r^{1/3}` gives `|X(s) − X(t)| ≤ 3 r^{7/15}`. If `r > γ²`, then
`ξ ≤ γ < r^{1/2}`; split `η = x + iy` with `y = S_J + R_J`, `J = J(ξ)`: `|x(u) − u| ≤ 3Δ`, the Hölder bound of
`S_J` at `b = c_β K ξ^{2/3}` and `|R_J| ≤ 13 C₄ ξ^{19/1200} ξ^{2/3}` give
`|X(s) − X(t)| ≤ C₁ K r^{1/8} + C₂ ξ^{19/1200} ≤ C₁ K r^{1/8} + C₂ r^{1/200}`, using
`ξ^{99/100 − 2/3} = ξ^{97/300} ≤ ξ^{19/1200} ≤ ξ^{1/100} ≤ r^{1/200}`. The hypothesis `ξ^{99/100} ≤ 1/100` is
part of the planned statement (it is the regime of the good event) but is not needed by this argument:
`ApproxGeod` already contains `Δ ≤ 1/100`. -/
theorem rescaled_mem_modulusSet : ∃ C₁ C₂, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (γ ξ K Δ : ℝ) (n : ℕ) (d : ℂ × ℂ → ℝ)
    (η : C(unitInterval, ℂ)),
    0 < ξ → ξ ≤ γ → γ ≤ 1 → ξ ^ (99/100 : ℝ) ≤ 1/100 → 1 ≤ K → γ ^ 2 < ((2:ℝ)⁻¹ ^ n) ^ (5/4 : ℝ) / 2 →
    ApproxGeod d η Δ → Δ ≤ ξ ^ (99/100 : ℝ) →
    (∀ z ∈ Metric.closedBall (0:ℂ) 2, ∀ w ∈ Metric.closedBall (0:ℂ) 2, 0 < ‖z - w‖ → ‖z - w‖ ≤ (2:ℝ)⁻¹ ^ n →
      ‖z - w‖ ^ (5/4 : ℝ) ≤ d (z, w)) →
    (∀ j ≤ Jxi ξ, ∀ a ∈ probeGrid j, |band (yPath η) j a| ≤ cBeta * K * ξ ^ (2/3 : ℝ) * ell j ^ (1/8 : ℝ)) →
    rescaledPath (γ ^ (2/3 : ℝ)) η ∈
      modulusSet (fun r => C₁ * K * r ^ (1/8 : ℝ) + C₂ * r ^ (1/200 : ℝ) + 3 * r ^ (7/15 : ℝ)) := by
  obtain ⟨CS, hCS, hhold⟩ := lowPass_holder
  obtain ⟨C₄, hC₄, hrem⟩ := lowPass_remainder_le_of_approx
  refine ⟨CS * cBeta, 6 + 26 * C₄, mul_nonneg hCS cBeta_pos.le, by positivity, ?_⟩
  intro γ ξ K Δ n d η hξ hξγ hγ1 _hξa hK hγn h hΔ hsmall hband
  have hγ : 0 < γ := hξ.trans_le hξγ
  have hξ1 : ξ ≤ 1 := hξγ.trans hγ1
  set s : ℝ := γ ^ (2 / 3 : ℝ) with hs_def
  have hs : 0 < s := Real.rpow_pos_of_pos hγ _
  have hsξ : ξ ^ (2 / 3 : ℝ) ≤ s := Real.rpow_le_rpow hξ.le hξγ (by norm_num)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨?_, fun u v => ?_⟩
  · -- `X(0) = 0`
    show (η 0 - (((0 : unitInterval) : ℝ) : ℂ)) / (s : ℂ) = 0
    rw [h.zero, Set.Icc.coe_zero, Complex.ofReal_zero, sub_zero, zero_div]
  set r : ℝ := |(u : ℝ) - v| with hr_def
  have hr0 : 0 ≤ r := abs_nonneg _
  have hr1 : r ≤ 1 := by
    rw [hr_def, abs_le]
    constructor <;> linarith [u.2.1, u.2.2, v.2.1, v.2.2]
  have hw0 : 0 ≤ CS * cBeta * K * r ^ (1 / 8 : ℝ) := by
    have := mul_nonneg hCS cBeta_pos.le
    positivity
  have hw1 : 0 ≤ (6 + 26 * C₄) * r ^ (1 / 200 : ℝ) := by positivity
  have hw2 : 0 ≤ 3 * r ^ (7 / 15 : ℝ) := by positivity
  show ‖rescaledPath s η u - rescaledPath s η v‖ ≤
    CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ) + 3 * r ^ (7 / 15 : ℝ)
  rw [Tight.norm_rescaledPath_sub hs, div_le_iff₀ hs]
  rcases le_or_gt r (γ ^ 2) with hrγ | hrγ
  · -- small scales: Corollary 6.0′
    have hτ : |(u : ℝ) - v| < ((2 : ℝ)⁻¹ ^ n) ^ (5 / 4 : ℝ) / 2 := hrγ.trans_lt hγn
    have hd01 : d (0, 1) ≤ 2 := by linarith [h.d01_le, h.le]
    have hball : ∀ t, η t ∈ Metric.closedBall (0 : ℂ) 2 := fun t =>
      mem_closedBall_zero_iff.2 (h.norm_lt_two t).le
    have hmod := path_modulus_of_smallScale d η n h.zero h.one h.geod hd01 hball hsmall u v hτ
    have hb := Tight.norm_sub_le_of_small hγ hr0 hrγ hr1 hmod hr_def.symm
    calc ‖(η u - ((u : ℝ) : ℂ)) - (η v - ((v : ℝ) : ℂ))‖ ≤ 3 * r ^ (7 / 15 : ℝ) * s := hb
      _ ≤ (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ) +
            3 * r ^ (7 / 15 : ℝ)) * s := by
          refine mul_le_mul_of_nonneg_right ?_ hs.le
          linarith
  · -- large scales: low frequencies, high frequencies and the horizontal component
    set y := yPath η with hy_def
    set S := lowPass y (Jxi ξ) with hS_def
    have hyc : ContinuousOn y (Icc 0 1) := (continuous_yPath η).continuousOn
    set b : ℝ := cBeta * K * ξ ^ (2 / 3 : ℝ) with hb_def
    have hb0 : 0 ≤ b := by
      have := cBeta_pos
      positivity
    have hband' : ∀ j ≤ Jxi ξ, ∀ a ∈ probeGrid j, |band y j a| ≤ b * ell j ^ (1 / 8 : ℝ) := hband
    have hS := (hhold y hyc (Jxi ξ) b hb0 hband').2 u u.2 v v.2
    have hRu := hrem h hξ hξ1 hΔ u u.2
    have hRv := hrem h hξ hξ1 hΔ v v.2
    have hxu := h.abs_re_sub_le u
    have hxv := h.abs_re_sub_le v
    set z : ℂ := (η u - ((u : ℝ) : ℂ)) - (η v - ((v : ℝ) : ℂ)) with hz_def
    have hzre : z.re = ((η u).re - u) - ((η v).re - v) := by
      simp only [hz_def, Complex.sub_re, Complex.ofReal_re]
    have hzim : z.im = y u - y v := by
      simp only [hz_def, Complex.sub_im, Complex.ofReal_im, sub_zero, hy_def, yPath_coe]
    have hre : |z.re| ≤ 6 * Δ := by
      rw [hzre]
      calc |((η u).re - u) - ((η v).re - v)| ≤ |(η u).re - u| + |(η v).re - v| := abs_sub _ _
        _ ≤ 3 * Δ + 3 * Δ := add_le_add hxu hxv
        _ = 6 * Δ := by ring
    set e : ℝ := ξ ^ (19 / 1200 : ℝ) with he_def
    set A : ℝ := ξ ^ (2 / 3 : ℝ) with hA_def
    have hA0 : 0 < A := Real.rpow_pos_of_pos hξ _
    have he0 : 0 ≤ e := Real.rpow_nonneg hξ.le _
    have him : |z.im| ≤ CS * b * r ^ (1 / 8 : ℝ) + 26 * C₄ * e * A := by
      rw [hzim]
      calc |y u - y v| = |(S u - S v) + (y u - S u) - (y v - S v)| := by ring_nf
        _ ≤ |(S u - S v) + (y u - S u)| + |y v - S v| := abs_sub _ _
        _ ≤ |S u - S v| + |y u - S u| + |y v - S v| := by
            gcongr
            exact abs_add_le _ _
        _ ≤ CS * b * r ^ (1 / 8 : ℝ) + 13 * C₄ * e * A + 13 * C₄ * e * A := by
            gcongr
        _ = CS * b * r ^ (1 / 8 : ℝ) + 26 * C₄ * e * A := by ring
    -- `Δ ≤ ξ^{19/1200} ξ^{2/3}`
    have hΔe : Δ ≤ e * A := (Tight.sqrt_ell_Jxi_mul_le_and_le hξ hξ1 h.nonneg hΔ).2
    -- `ξ^{19/1200} ≤ r^{1/200}`
    have hξr : ξ ^ 2 < r := by
      have : ξ ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hξ.le hξγ 2
      linarith
    have her : e ≤ r ^ (1 / 200 : ℝ) := by
      calc e ≤ ξ ^ (1 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (by norm_num)
        _ = (ξ ^ 2) ^ (1 / 200 : ℝ) := by
            rw [← Real.rpow_two, ← Real.rpow_mul hξ.le]
            norm_num
        _ ≤ r ^ (1 / 200 : ℝ) := Real.rpow_le_rpow (by positivity) hξr.le (by norm_num)
    have hr18 : 0 ≤ r ^ (1 / 8 : ℝ) := Real.rpow_nonneg hr0 _
    have hz : ‖z‖ ≤ A * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e) := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 6 * Δ + (CS * b * r ^ (1 / 8 : ℝ) + 26 * C₄ * e * A) := add_le_add hre him
        _ ≤ 6 * (e * A) + (CS * b * r ^ (1 / 8 : ℝ) + 26 * C₄ * e * A) := by linarith
        _ = A * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e) := by
            rw [hb_def]
            ring
    calc ‖z‖ ≤ A * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e) := hz
      _ ≤ s * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ)) := by
          have h6 : 0 ≤ 6 + 26 * C₄ := by positivity
          have hin : CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e ≤
              CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ) := by
            have := mul_le_mul_of_nonneg_left her h6
            linarith
          have hin0 : 0 ≤ CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e := by
            have := mul_nonneg h6 he0
            linarith
          calc A * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e)
              ≤ s * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * e) :=
                mul_le_mul_of_nonneg_right hsξ hin0
            _ ≤ s * (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ)) :=
                mul_le_mul_of_nonneg_left hin hs.le
      _ ≤ (CS * cBeta * K * r ^ (1 / 8 : ℝ) + (6 + 26 * C₄) * r ^ (1 / 200 : ℝ) +
            3 * r ^ (7 / 15 : ℝ)) * s := by
          rw [mul_comm s]
          exact mul_le_mul_of_nonneg_right (by linarith) hs.le

end SmallGammaGeodesics
