import HigherDimLQGContinuity.Unif4.SelfDiam
import HigherDimLQGMetric.DGZ.SuperExpAround

/-!
# Uniform around half of DGZ Lemma 4.9, certificate form (packet U1)

Blueprint Part D, `d:lem-u49` (NA3 §2.3–2.4, S1; [8]-bp `r2:def:cert`, `r2:lem:49`). Ports of
`HigherDimLQGMetric.DGZ.prob_not_aroundCertAt_le`, `DGZ.aroundGood_of_aroundCertAt` and `DGZ.superExpAround_tail`
(`DGZ/SuperExpAround.lean`, MA7 D-4.9). The certificate `DGZ.aroundCertAt ξ Q δ r₁ r₂ n ψ g` (a coarse field `ψ`, a fine
field `g`), its locality and measurability (`DGZ.aroundCert_congr`, `DGZ.measurableSet_aroundCertAt`,
`DGZ.measurableSet_aroundCert_comap`) are reused verbatim at `(ξ, Q(ξ))`: multiplying the field condition through by
`ξ > 0` gives an equivalent event, and only the probability bound is uniformized.

* `aroundGood_of_aroundCertAt_unif` (`d:lem-u49`(ii)): the deterministic consequence with a threshold `n₀ = n₀(d, δ,
  r₁, r₂)` that does not depend on `(ξ, Q)` (the proof of `DGZ.aroundGood_of_aroundCertAt` never uses them);
* `prob_not_aroundCertAt_le_unif` (`d:lem-u49`(iii)): `P[¬ cert] ≤ C e^{-n log n}` with `C = C(d, κ, b, μ, δ, r₁, r₂)`
  for every `ξ` with `UHyp d κ b μ ξ`. Changes: the field condition `|ψ| ≤ δ n log 2/(3ξ)` on the closed shell
  contains `{sup |ψ| ≤ δ n log 2/(3b)}` (`DGZ.exists_field_superExp'` at the level `δ log 2/(3b)`); the closed-site
  probability uses the uniform Prop 4.7 (`selfDiamShape_unif` at `δ/3`); `ξQ(ξ) ≥ μ > 0` (`UHyp.mu_le_phi`);
* `superExpAround_unif`: the uniform form of `DGZ.SuperExpAroundShape` (the event `E` with `AroundGood` on `E` for every
  admissible cube and `P[Eᶜ] ≤ C e^{-n log n}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-- **The certificate gives the around-good property, uniformly** (`d:lem-u49`(ii); port of
`DGZ.aroundGood_of_aroundCertAt` with the threshold `n₀` chosen before `(ξ, Q)`): there is `n₀ = n₀(d, δ, r₁, r₂)` such
that for all `ξ > 0`, all `Q`, `n ≥ n₀`, continuous `ψ, g` with `aroundCertAt ξ Q δ r₁ r₂ n ψ g`, and every cube
`B = obox (latPt 1 c) ρ` (`c ∈ ℤ^d`, `ρ ∈ ℕ`, `ρ ≥ r₁`, `0 ∈ B`):
`AroundGood ξ (ψ + g) 0 r₁ r₂ B 2^{-(1-ξQ-δ)n}`. -/
theorem aroundGood_of_aroundCertAt_unif (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) {r₁ r₂ : ℝ}
    (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ n₀ : ℕ, ∀ ξ Q : ℝ, 0 < ξ → ∀ n : ℕ, n₀ ≤ n → ∀ ψ g : Rd d → ℝ, Continuous ψ →
      Continuous g → aroundCertAt ξ Q δ r₁ r₂ n ψ g → ∀ (c : Zd d) (ρ : ℕ), r₁ ≤ ρ →
        (0 : Rd d) ∈ obox (latPt 1 c) ρ →
          AroundGood ξ (fun z => ψ z + g z) 0 r₁ r₂ (obox (latPt 1 c) ρ)
            ((2 : ℝ) ^ (-(1 - ξ * Q - δ) * n)) := by
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  obtain ⟨hϱ0, hϱ₂, hϱ₁⟩ := aroundRho_spec hr₂ hr
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((eventually_ge_atTop 1).and
    (eventually_le_two_pow_superScale (8 / (min r₂ (r₁ - r₂) / 16)))).and
    (eventually_mul_poly_le_exp 2 (8 * r₁) 3 d (b := δ * Real.log 2 / 3) (by norm_num)
      (by linarith) (by norm_num) (by positivity)))
  refine ⟨n₀, fun ξ Q hξ n hn ψ g hψ hg hcert c ρ hρ h0 => ?_⟩
  obtain ⟨⟨hn1, hs8⟩, hpath⟩ := hn₀ n hn
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hs8
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hsϱ : 8 * s ≤ min r₂ (r₁ - r₂) / 16 := by
    rw [div_le_iff₀ hϱ0] at hs8
    nlinarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3) = T := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [← hTdef]; exact Real.rpow_nonneg (by norm_num) _
  unfold aroundCertAt at hcert
  rw [hmdef, hsdef, hTdef] at hcert
  have hcert' := aroundGood_of_aroundCert hd hξ.le hψ hg hs0 hsϱ hϱ₂ hϱ₁ hT0 hcert
    (c := fun i => 2 ^ m * c i) (N := 2 ^ m * ρ) (withinInf_fine_of_mem h0)
    (by rw [← hsdef]; exact side_fine hρ)
  rw [← hsdef, obox_fine_eq, hsdef] at hcert'
  refine hcert'.mono ?_
  -- the threshold: `2 (2K+1)^d 2^{δn/3} T ≤ 2^{-(1-ξQ-δ)n}`
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, ⌈r₁ / s⌉₊ = K := ⟨_, rfl⟩
  rw [hKdef]
  have hK' : ((2 * K + 1 : ℕ) : ℝ) ≤ 8 * r₁ * (n : ℝ) ^ 2 + 3 := by
    have h4 := two_pow_superScale_le_real (n := n) (by omega)
    rw [hmdef] at h4
    have h1 : (K : ℝ) < r₁ / s + 1 := by
      rw [← hKdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    push_cast
    nlinarith
  have hpow : (((2 * K + 1) ^ d : ℕ) : ℝ) ≤ (8 * r₁ * (n : ℝ) ^ 2 + 3) ^ d := by
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK') d
  have hT2 : Real.exp (ξ * (δ * Real.log 2 / (3 * ξ) * n)) * T =
      (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) / Real.exp (δ * Real.log 2 / 3 * n) := by
    rw [← hTdef, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos,
      eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hT2, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
  have h2 : 0 ≤ (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) := Real.rpow_nonneg (by norm_num) _
  have h3 : 2 * (((2 * K + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (δ * Real.log 2 / 3 * n) :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hpath
  nlinarith

/-- **Uniform DGZ Lemma 4.9(iii), around half, certificate form** (`d:lem-u49`(iii); port of
`DGZ.prob_not_aroundCertAt_le`): for `d ≥ 2`, `κ` admissible, `b, μ, δ > 0` and `0 < r₂ < r₁` there is `C > 0`
(depending only on `d, κ, b, μ, δ, r₁, r₂`) such that for every `ξ` with `UHyp d κ b μ ξ`, every white noise, every `n`,
every version `ψ` of `H_{2^{-m(n)}, 1}` and every version `g` of `H_{2^{-n}, 2^{-m(n)}}` over it,
`P[¬ aroundCertAt ξ Q(ξ) δ r₁ r₂ n ψ g] ≤ C e^{-n log n}`. -/
theorem prob_not_aroundCertAt_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) {r₁ r₂ : ℝ} (hr₂ : 0 < r₂)
    (hr : r₂ < r₁) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (ψ g : Rd d → Ω → ℝ), IsWhiteNoise P W → ∀ n : ℕ,
          IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ superScale n) 1 ψ →
          IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ superScale n) g →
            P {ω | ¬ aroundCertAt ξ (distExp d ξ) δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)} ≤
              ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  obtain ⟨hϱ0, -, -⟩ := aroundRho_spec hr₂ hr
  obtain ⟨Csd, hCsd, hsd⟩ := selfDiamShape_unif hd hκ hb hμ (δ := δ / 3) (by positivity)
  -- the Peierls parameters (locality radius `1`)
  obtain ⟨ρk, -, hρk⟩ := hκ.exists_radius
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, ⌈2 * (1 + ρk)⌉₊ = r := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  have hθtop : ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCsd
    (θ := (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal)
    (ENNReal.toReal_pos hθ0.ne' hθtop)
  -- the coarse field: the uniform level `δ log 2/(3b)`
  obtain ⟨n₁, hn₁⟩ := exists_field_superExp' hκ (R := r₁) (by linarith)
    (c := δ * Real.log 2 / (3 * b)) (by positivity)
  -- the threshold `n₀`
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((((eventually_ge_atTop (max 1 (max n₁ (2 * k₀)))).and
    (eventually_superScale_le_mul (c := 1 / 2) (by norm_num))).and
    (eventually_peierls_superExp d (a := r₁) (b := min r₂ (r₁ - r₂) / 16) (by linarith)
      hϱ0)))
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const n₀
  obtain ⟨C, hC2, hCC₀⟩ : ∃ C : ℝ, 2 ≤ C ∧ C₀ ≤ C := ⟨max 2 C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun ξ hξh Ω _ P W ψ g hW n hψ hg => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hξb : ξ ≤ b := hξh.le_b
  have hξQ : 0 ≤ ξ * distExp d ξ := hμ.le.trans hξh.mu_le_phi
  set Q : ℝ := distExp d ξ with hQ
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le))
  obtain ⟨⟨hnbig, hm2⟩, hpei⟩ := hn₀ n hn
  have hnn₁ : n₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hnbig
  have hnk : 2 * k₀ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hnbig
  have hfield := hn₁ hW n hnn₁ hψ
  -- the scale `m = m(n)`, the mesh `s = 2^{-m}` and a reference dyadic realization
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hm2 hpei hg
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact_mod_cast this
  have hnm : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  have hk : k₀ ≤ n - m := by
    have h1 : (2 * k₀ : ℝ) ≤ n := by exact_mod_cast hnk
    have : (k₀ : ℝ) ≤ ((n - m : ℕ) : ℝ) := by rw [hnm]; linarith
    exact_mod_cast this
  obtain ⟨H, hH⟩ := exists_isDyadicRealization hκ hW
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3) = T := ⟨_, rfl⟩
  set closed : Zd d → Set Ω := fun x => {ω |
    ((∃ i, r₂ + min r₂ (r₁ - r₂) / 16 / 2 ≤ s * |(x i : ℝ)|) ∧
      ∀ i, s * |(x i : ℝ)| ≤ r₁ - min r₂ (r₁ - r₂) / 16 / 2) ∧
      T < selfDiam ξ (fun z => g z ω) (latPt s x) s} with hclosed
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, ⌈r₁ / s⌉₊ = K := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, ⌊min r₂ (r₁ - r₂) / 16 / s⌋₊ = D := ⟨_, rfl⟩
  have hreg : ∀ x : Zd d, (∀ i, s * |(x i : ℝ)| ≤ r₁ - min r₂ (r₁ - r₂) / 16 / 2) →
      WithinInf (K : ℤ) x 0 := by
    intro x hx i
    have h2 : |(x i : ℝ)| ≤ r₁ / s := by
      rw [le_div_iff₀ hs0]
      linarith [hx i]
    have h3 : |(x i : ℝ)| ≤ K := h2.trans (by rw [← hKdef]; exact Nat.le_ceil _)
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast h3
  -- the closed sites: probability, product bound, Peierls
  have hcl : ∀ x, P (closed x) ≤ ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) := by
    intro x
    have h1 := measure_selfDiamBand_gt_le hκ hξQ hδ (hsd ξ hξh) hH hmn hg (latPt s x)
    rw [hsdef, hTdef] at h1
    refine (measure_mono fun ω hω => hω.2).trans (h1.trans ?_)
    rw [← ENNReal.ofReal_toReal hθtop]
    exact ENNReal.ofReal_le_ofReal (hk₀ _ hk)
  have hPB : ProductBound P closed (r : ℤ) := by
    have := productBound_of_local hκ hW hρk (by positivity) hg hs0 hsdef.le (R := 1) closed
      fun x => measurableSet_selfDiamClosed_comap hg.continuous hs0 ξ _ T x
    rwa [hrdef] at this
  have hpeierls := measure_not_smallClusters_le P closed r _ _ hcl hPB
    (HigherDimLFPP.L33.theta_le_one d) le_rfl (HigherDimLFPP.L33.three_pow_mul_theta_le d) K D
    (fun x ω hω => hreg x hω.1.2)
  have hKb : (K : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1 := by
    have h1 : (K : ℝ) < r₁ / s + 1 := by
      rw [← hKdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    linarith
  have hDb : min r₂ (r₁ - r₂) / 16 * (2 : ℝ) ^ m ≤ D + 1 := by
    have h1 : min r₂ (r₁ - r₂) / 16 / s < D + 1 := by
      rw [← hDdef]; exact Nat.lt_floor_add_one _
    have h2 : min r₂ (r₁ - r₂) / 16 / s = min r₂ (r₁ - r₂) / 16 * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination min r₂ (r₁ - r₂) / 16 * hs2m.symm
    linarith
  have hPei := hpeierls.trans (hpei K D hKb hDb)
  -- the field level: `δ n log 2/(3b) ≤ δ n log 2/(3ξ)` (`ξ ≤ b`)
  have hlev : δ * Real.log 2 / (3 * b) * n ≤ δ * Real.log 2 / (3 * ξ) * n := by
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  -- the inclusion `{¬ cert} ⊆ 𝒢₁ᶜ ∪ 𝒢₂ᶜ`
  have hsub : {ω | ¬ aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) r₁, δ * Real.log 2 / (3 * b) * n < |ψ z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
    obtain ⟨hF, hsmall⟩ := hno
    apply hω
    unfold aroundCertAt
    rw [hmdef, hsdef, hTdef]
    refine ⟨fun z hz => (hF z hz.1).trans hlev, ?_⟩
    rw [hDdef]
    exact hsmall
  calc P {ω | ¬ aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)}
      ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) r₁, δ * Real.log 2 / (3 * b) * n < |ψ z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) :=
        (measure_union_le _ _).trans (add_le_add hfield hPei)
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * Real.log n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

/-- **Uniform DGZ Lemma 4.9, around half** (port of `DGZ.superExpAround_tail` / `DGZ.SuperExpAroundShape`): for
`d ≥ 2`, `κ` admissible, `b, μ, δ > 0` and `0 < r₂ < r₁` there is `C > 0` (depending only on
`d, κ, b, μ, δ, r₁, r₂`) such that for every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization, every cube
`B = obox (latPt 1 c) ρ` (`c ∈ ℤ^d`, `ρ ∈ ℕ`, `ρ ≥ r₁`, `0 ∈ B`) and every `n` there is a measurable event `E` with
`AroundGood(h_n, 0, r₁, r₂, B, 2^{-(1-ξQ(ξ)-δ)n})` on `E` and `P[Eᶜ] ≤ C e^{-n log n}`. -/
theorem superExpAround_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ (c : Zd d) (ρ : ℕ), r₁ ≤ ρ →
          (0 : Rd d) ∈ obox (latPt 1 c) ρ → ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧
            (∀ ω ∈ E, AroundGood ξ (fun z => H n z ω) 0 r₁ r₂ (obox (latPt 1 c) ρ)
              ((2 : ℝ) ^ (-(1 - ξ * distExp d ξ - δ) * n))) ∧
            P Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  obtain ⟨C₁, hC₁, hprob⟩ := prob_not_aroundCertAt_le_unif hd hκ hb hμ hδ hr₂ hr
  obtain ⟨n₀, hdet⟩ := aroundGood_of_aroundCertAt_unif hd hδ hr₂ hr
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (eventually_superScale_le_mul (c := 1) one_pos)
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const (max n₀ n₂)
  obtain ⟨C, hC1, hC0⟩ : ∃ C : ℝ, C₁ ≤ C ∧ C₀ ≤ C := ⟨max C₁ C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun ξ hξh Ω _ P W H hH c ρ hρ h0 n => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n (max n₀ n₂) with hn | hn
  · -- small `n`: `E = ∅`
    refine ⟨∅, MeasurableSet.empty, fun ω hω => absurd hω (Set.notMem_empty ω), ?_⟩
    calc P ∅ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hC0 (Real.exp_pos _).le))
  have hmn : superScale n ≤ n := by
    have := hn₂ n ((le_max_right _ _).trans hn)
    rw [one_mul] at this
    exact_mod_cast this
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  refine ⟨{ω | aroundCertAt ξ (distExp d ξ) δ r₁ r₂ n (fun z => H (superScale n) z ω)
      (fun z => H n z ω - H (superScale n) z ω)}, ?_, fun ω hω => ?_, ?_⟩
  · exact measurableSet_aroundCertAt (hH.band _).continuous (hH.band _).measurable
      hG.continuous hG.measurable ξ _ δ r₁ r₂ n
  · have hgood := hdet ξ (distExp d ξ) hξ n ((le_max_left _ _).trans hn) _ _
      ((hH.band _).continuous ω) (hG.continuous ω) hω c ρ hρ h0
    have e : (fun z => H (superScale n) z ω + (H n z ω - H (superScale n) z ω)) =
        fun z => H n z ω := funext fun z => by ring
    rwa [e] at hgood
  · rw [compl_ofPred]
    exact (hprob ξ hξh Ω P W _ _ hW n (hH.band _) hG).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le))

end HigherDimLQGContinuity
