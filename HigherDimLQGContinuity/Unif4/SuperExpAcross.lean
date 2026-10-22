import HigherDimLQGContinuity.Unif4.AcrossLower
import HigherDimLQGMetric.DGZ.SuperExpAcross

/-!
# Uniform across half of DGZ Lemma 4.10 (packet U1)

Blueprint Part D, `d:lem-u410` (NA3 §2.4, §2.15 row 8; [8]-bp `r2:lem:410`). Port of
`HigherDimLQGMetric.DGZ.superExpAcross_tail` / `DGZ.SuperExpAcrossShape` (`DGZ/SuperExpAcross.lean`, MA7 D-4.10).

**Statement** (`superExpAcross_unif`). Let `d ≥ 2`, `κ` admissible, `b, μ, δ > 0` and `0 < r₂ < r₁`. There is
`C = C(d, κ, b, μ, δ, r₁, r₂) > 0` such that for every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization and every
`n`, `P*[D_n(across B_{r₁}(0) \ B_{r₂}(0)) ≤ 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n log n}`.

**Proof** (the proof of `DGZ.superExpAcross_tail` with the two changes of `d:lem-u410`):
* (a) the coarse field event is `{sup_{B̄_{r₁+1}} |h_m| ≤ δ n log 2/(3b)}` (`DGZ.exists_field_superExp` at the level
  `δ log 2/(3b)`): on it `ξ sup |h_m| ≤ δ n log 2/3` because `ξ ≤ b` (the threshold `δ n log 2/(3ξ)` of [1]
  multiplied through by `ξ`);
* (b) the scale condition `ξ Q m ≤ δ n/12` holds for `m(n) ≤ δ n/(12 (1 + √(2d) b))` because
  `ξ Q(ξ) ≤ 1 + √(2d) b` (`u1_phi_bounds`);
* the per-site bound uses the uniform Prop 4.8 (`acrossLower_unif` at `δ/4`); the deterministic crossing lemma
  `DGZ.le_acrossDist_of_smallDiam`, the product bound and the Peierls estimate do not involve `ξ`.
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

/-- **Uniform DGZ Lemma 4.10, across half** (`d:lem-u410`; port of `DGZ.superExpAcross_tail`): for `d ≥ 2`, `κ`
admissible, `b, μ, δ > 0` and `0 < r₂ < r₁` there is `C > 0` (depending only on `d, κ, b, μ, δ, r₁, r₂`) such that for
every `ξ` with `UHyp d κ b μ ξ`, every dyadic realization and every `n`,
`P*[D_n(across B_{r₁}(0) \ B_{r₂}(0)) ≤ 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n log n}`. -/
theorem superExpAcross_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤
            (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + δ) * n)} ≤
              ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  -- the uniform bound `ξ Q(ξ) ≤ Φ = 1 + √(2d) b`
  obtain ⟨Φ, hΦ0, hΦdef⟩ : ∃ Φ : ℝ, 0 < Φ ∧ 1 + √(2 * d) * b = Φ :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨Cal, hCal, hal⟩ := acrossLower_unif hd hκ hb hμ (δ := δ / 4) (by positivity)
  -- the Peierls parameters
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, ⌈2 * (2 + ρ)⌉₊ = r := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  have hθtop : ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCal
    (θ := (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal)
    (ENNReal.toReal_pos hθ0.ne' hθtop)
  -- the field at the coarse scale: the uniform level `c₀ = δ log 2/(3b)`
  obtain ⟨n₁, hn₁⟩ := exists_field_superExp hκ (R := r₁ + 1) (by linarith)
    (c := δ * Real.log 2 / (3 * b)) (by positivity)
  -- the threshold `n₀`
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((((eventually_ge_atTop (max 1 (max n₁ (2 * k₀)))).and
    (eventually_superScale_le_mul (c := 1 / 2) (by norm_num))).and
    (eventually_superScale_le_mul (c := δ / (12 * Φ)) (by positivity))).and
    (eventually_le_two_pow_superScale (max 2 (32 / (3 * (r₁ - r₂)))))).and
    (eventually_peierls_superExp d (a := r₁) (b := (r₁ - r₂) / 4) (by linarith) (by linarith)))
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const n₀
  obtain ⟨C, hC2, hCC₀⟩ : ∃ C : ℝ, 2 ≤ C ∧ C₀ ≤ C := ⟨max 2 C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun ξ hξh Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hξb : ξ ≤ b := hξh.le_b
  set Q : ℝ := distExp d ξ with hQ
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le))
  obtain ⟨⟨⟨⟨hnbig, hm2⟩, hmQ⟩, hs2⟩, hpei⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnbig
  have hnn₁ : n₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hnbig
  have hnk : 2 * k₀ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hnbig
  -- the scale `m = m(n)` and the mesh `s = 2^{-m}`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hm2 hmQ hs2 hpei
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
  -- (b): `ξ Q m ≤ δ n/12`
  have hmQ' : ξ * Q * m ≤ δ * n / 12 := by
    have hphi : ξ * Q ≤ Φ := hΦdef ▸ (u1_phi_bounds hd hξ hξb).2
    have h1 : ξ * Q * m ≤ Φ * m := mul_le_mul_of_nonneg_right hphi (Nat.cast_nonneg m)
    have h2 : Φ * m ≤ Φ * (δ / (12 * Φ) * n) := mul_le_mul_of_nonneg_left hmQ hΦ0.le
    have e : Φ * (δ / (12 * Φ) * n) = δ * n / 12 := by field_simp
    linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hshalf : s ≤ 1 / 2 := by
    have h2 : 2 ≤ (2 : ℝ) ^ m := (le_max_left _ _).trans hs2
    rw [le_div_iff₀ two_pos]
    nlinarith
  have hs8 : 8 * s ≤ 3 * (r₁ - r₂) / 4 := by
    have h2 : 32 / (3 * (r₁ - r₂)) ≤ (2 : ℝ) ^ m := (le_max_right _ _).trans hs2
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  -- the closed sites
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n - δ * n / 3) = T' := ⟨_, rfl⟩
  set closed : Zd d → Set Ω := fun x => {ω | (∀ i, s * |(x i : ℝ)| ≤ r₁) ∧
    acrossDist ξ (fun z => H n z ω - H m z ω) (latPt s x) (2 * s) s < T'} with hclosed
  have hcl : ∀ x, P (closed x) ≤ ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) := by
    intro x
    have h1 := measure_acrossBand_lt_le hκ (hal ξ hξh) hδ hH hmn hmQ' (latPt s x)
    rw [hsdef, hT'def] at h1
    refine (measure_mono fun ω hω => hω.2).trans (h1.trans ?_)
    rw [← ENNReal.ofReal_toReal hθtop]
    exact ENNReal.ofReal_le_ofReal (hk₀ _ hk)
  have hPB : ProductBound P closed (r : ℤ) := by
    have := productBound_of_local hκ hW hρ (by positivity) hG hs0 hsdef.le (R := 2) closed
      fun x => measurableSet_acrossClosed_comap hG.continuous hs0 ξ _ T' x
    rwa [hrdef] at this
  -- the Peierls event
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, ⌈r₁ / s⌉₊ = N := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, ⌊(r₁ - r₂) / (4 * s)⌋₊ = D := ⟨_, rfl⟩
  have hN : ∀ x ω, ω ∈ closed x → WithinInf (N : ℤ) x 0 := by
    intro x ω hω i
    have h1 := hω.1 i
    have h2 : |(x i : ℝ)| ≤ r₁ / s := by
      rw [le_div_iff₀ hs0]
      linarith
    have h3 : |(x i : ℝ)| ≤ N := h2.trans (by rw [← hNdef]; exact Nat.le_ceil _)
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast h3
  have hpeierls := measure_not_smallClusters_le P closed r _ _ hcl hPB
    (HigherDimLFPP.L33.theta_le_one d) le_rfl (HigherDimLFPP.L33.three_pow_mul_theta_le d) N D hN
  have hNb : (N : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1 := by
    have h1 : (N : ℝ) < r₁ / s + 1 := by
      rw [← hNdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    linarith
  have hDb : (r₁ - r₂) / 4 * (2 : ℝ) ^ m ≤ D + 1 := by
    have h1 : (r₁ - r₂) / (4 * s) < D + 1 := by rw [← hDdef]; exact Nat.lt_floor_add_one _
    have h2 : (r₁ - r₂) / (4 * s) = (r₁ - r₂) / 4 * (2 : ℝ) ^ m := by
      rw [div_eq_iff (by positivity)]
      linear_combination (r₁ - r₂) * hs2m.symm
    linarith
  have hPei := hpeierls.trans (hpei N D hNb hDb)
  -- the field event (a)
  have hfield := hn₁ hH n hnn₁
  rw [hmdef] at hfield
  -- the inclusion
  have hsub : {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), δ * Real.log 2 / (3 * b) * n < |H m z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
    obtain ⟨hF, hsmall⟩ := hno
    have hφ := (hH.band n).continuous ω
    have hψ := hG.continuous ω
    -- every open site of the region has a large across distance
    have hopen : ∀ x ∈ {x | ω ∉ closed x}, (∀ i, s * |(x i : ℝ)| ≤ r₁) →
        T' / Real.exp (δ * Real.log 2 * n / 3) ≤
          acrossDist ξ (fun z => H n z ω) (latPt s x) (2 * s) s := by
      intro x hx hreg
      have hT : T' ≤ acrossDist ξ (fun z => H n z ω - H m z ω) (latPt s x) (2 * s) s := by
        by_contra hlt
        exact hx ⟨hreg, not_le.1 hlt⟩
      have hcmp := acrossDist_le_mul_of_exp_le hψ hφ (by linarith : s < 2 * s)
        (C := Real.exp (δ * Real.log 2 * n / 3)) (c := latPt s x) (ξ := ξ)
        (Real.exp_pos _).le (by
          intro z hz
          have hz1 : z ∈ cbox (0 : Rd d) (r₁ + 1) := by
            intro i
            have h1 := hz.1 i
            have h2 := hreg i
            simp only [PiLp.zero_apply, sub_zero]
            rw [latPt_apply] at h1
            have h3 := abs_sub_abs_le_abs_sub (z i) (s * (x i : ℝ))
            rw [abs_mul, abs_of_pos hs0] at h3
            linarith
          have h1 := hF z hz1
          have h2 := neg_abs_le (H m z ω)
          rw [← Real.exp_add, Real.exp_le_exp]
          -- `-ξ h_m(z) ≤ ξ c₀ n ≤ b c₀ n = δ n log 2/3`
          have hc0n : 0 ≤ δ * Real.log 2 / (3 * b) * n := by positivity
          have h3 : -H m z ω ≤ δ * Real.log 2 / (3 * b) * n := by linarith
          have h4 : ξ * -H m z ω ≤ ξ * (δ * Real.log 2 / (3 * b) * n) :=
            mul_le_mul_of_nonneg_left h3 hξ.le
          have h5 : ξ * (δ * Real.log 2 / (3 * b) * n) ≤ b * (δ * Real.log 2 / (3 * b) * n) :=
            mul_le_mul_of_nonneg_right hξb hc0n
          have e : b * (δ * Real.log 2 / (3 * b) * n) = δ * Real.log 2 * n / 3 := by
            field_simp
          have e2 : ξ * (H n z ω - H m z ω) = ξ * H n z ω + ξ * -H m z ω := by ring
          rw [e2]
          linarith)
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hlow := le_acrossDist_of_smallDiam hd1 hφ hs0 hr₂.le
      (fun C hC => (hsmall C hC).2) (by
        have h1 : (D : ℝ) ≤ (r₁ - r₂) / (4 * s) := by
          rw [← hDdef]; exact Nat.floor_le (by positivity)
        rw [le_div_iff₀ (by positivity)] at h1
        linarith) hopen
    have hlt : (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) <
        T' / Real.exp (δ * Real.log 2 * n / 3) := by
      rw [lt_div_iff₀ (Real.exp_pos _), ← hT'def, Real.rpow_def_of_pos two_pos,
        Real.rpow_def_of_pos two_pos, ← Real.exp_add, Real.exp_lt_exp]
      have h1 : (0 : ℝ) < δ * Real.log 2 * n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        positivity
      have e : Real.log 2 * (-(1 - ξ * Q) * n - δ * n / 3) -
          (Real.log 2 * (-(1 - ξ * Q + δ) * n) + δ * Real.log 2 * n / 3) =
            δ * Real.log 2 * n / 3 := by ring
      linarith
    have hω' : acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) := hω
    linarith
  calc P {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)}
      ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), δ * Real.log 2 / (3 * b) * n < |H m z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) :=
        (measure_union_le _ _).trans (add_le_add hfield hPei)
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * Real.log n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

end HigherDimLQGContinuity
