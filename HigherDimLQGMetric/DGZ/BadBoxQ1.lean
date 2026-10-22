import HigherDimLQGMetric.DGZ.BadBoxOsc

/-!
# DGZ Lemma 5.5: bad `a₁`-boxes are unlikely for large `L` (packet L4a2)

Source: [2] Lemma 5.5 (TeX l. 2158–2178, p. 42); planning audit MA7 D-5.5–5.9 (Lemma 5.5:
"(1′) by D-OSC; (3) by D-4.8 rescaled … uniformly in `k ≥ 1`"); blueprint Lemma `r2:lem:55`.

An `a₁`-box `B_{s₁}(s₁ u)` is bad iff (1′) or (3) fails (`NiceBox p H 1 u`).

* (1′): `prob_not_niceOscOne_le` (L4a2, `BadBoxOsc`).
* (3): by scaling (`BadBox.measure_acrossDist_band_le_eq`) every one of the at most `(2·2^{a₁})^d`
  points `y = s₀ v` has `P[D_{n,n+k}(across B_{2s₀}(y) \ B_{s₀}(y)) ≤ L⁻¹ 2^{-n-(1-ξQ+ε)k}] =
  P[D_k(across B₂(0) \ B₁(0)) ≤ L⁻¹ 2^{-(1-ξQ+ε)k}]` (`prob_not_niceAcrossOne_le`).
* `acrossTail_uniform`: the last probability is `≤ η` for all `k ≥ 1` once `L ≥ L₀(η)`, uniformly in
  the realization: for `k ≥ k₁` by L3c3's `acrossLower_tail` (D-4.8, `δ = ε`, since `L > 1`); for
  `1 ≤ k < k₁` because `D_k(across) ≥ e^{-ξ sup_{B̄₂} |h_k|}` (`exp_mul_le_acrossDist`) and L3b2's
  Gaussian supremum tail `exists_sup_cbox_gaussian_tail` (MA7 states only the large-`k` argument
  "uniformly in `k ≥ 1`"; the finitely many small `k` need this second bound). For `k = 0` the field
  `h_{n,n} = 0` and (3) holds deterministically once `L > 1`.
* `q1_le` (uniform form): for every `A` and `η > 0` there is `L₀` such that `q₁ ≤ η` whenever
  `a₀ = 0`, `a₁ ≤ A`, `L ≥ L₀`, for all `n, k`, boxes and dyadic realizations; `q1_tendsto`
  (**target**, DGZ's form): `lim_{L→∞} sup_{n,k,u} q₁ = 0` for DGZ's parameters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The across distances of condition (3) -/

/-- **Condition (3) by scaling**: for a dyadic realization and `a₀ = 0`, the `a₁`-box
`B_{s₁}(s₁ u)` fails (3) with probability at most `(2·2^{a₁})^d` times
`P[D_k(across B₂(0) \ B₁(0)) ≤ L⁻¹ 2^{-(1-ξQ+ε)k}]`. -/
theorem prob_not_niceAcrossOne_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (p : NiceParams) (ha0 : p.a 0 = 0) (u : Zd d) :
    P {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} ≤
      ENNReal.ofReal (((2 : ℝ) * 2 ^ p.a 1) ^ d) *
        P {ω | acrossDist p.ξ (fun z => H p.k z ω) 0 2 1 ≤
          p.L⁻¹ * (2 : ℝ) ^ (-(1 - p.ξ * p.Q + p.ε) * p.k)} := by
  have hs0 : p.s 0 = (2 : ℝ)⁻¹ ^ p.n := by simp only [NiceParams.s, ha0, Nat.sub_zero]
  set N : ℕ := 2 ^ ((p.n - p.a 0) - (p.n - p.a 1)) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hsN : p.s 1 = (N : ℝ) * p.s 0 :=
    BadBox.s_eq_pow_mul p (Nat.sub_le_sub_left (by rw [ha0]; exact Nat.zero_le _) _)
  have hG := isBandVersion_sub_of_realization hκ hH (Nat.le_add_right p.n p.k)
  have hset : {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} =
      {ω | ∃ v : Zd d, latPt (p.s 0) v ∈ obox (latPt (p.s 1) u) (p.s 1) ∧
        acrossDist p.ξ (fun z => H (p.n + p.k) z ω - H p.n z ω) (latPt (p.s 0) v)
          (2 * p.s 0) (p.s 0) ≤ p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k)} := by
    ext ω
    simp only [mem_ofPred_eq, NiceAcrossOne, not_forall, not_lt, exists_prop]
  rw [hset]
  refine (BadBox.measure_exists_le_card_mul P (BadBox.cube ((N : ℤ) • u) (N - 1)) _ _
    (b := P {ω | acrossDist p.ξ (fun z => H p.k z ω) 0 2 1 ≤
      p.L⁻¹ * (2 : ℝ) ^ (-(1 - p.ξ * p.Q + p.ε) * p.k)})
    (fun v hv => ?_) (fun v _ => le_of_eq ?_)).trans ?_
  · rw [hsN] at hv
    exact (BadBox.latPt_mem_obox_iff_mem_cube (p.s_pos 0) N hN1 u v).1 hv
  · -- the scaled law
    have h := BadBox.measure_acrossDist_band_le_eq hκ hH (Nat.le_add_right p.n p.k) hG p.ξ
      (latPt (p.s 0) v) 2 1 (p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k))
    rw [one_mul, ← hs0, Nat.add_sub_cancel_left] at h
    have ht : p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k) / p.s 0 =
        p.L⁻¹ * (2 : ℝ) ^ (-(1 - p.ξ * p.Q + p.ε) * p.k) := by
      rw [hs0, mul_div_assoc, two_rpow_div_inv_two_pow]
      congr 2
      ring
    rw [h, ht]
  · gcongr
    rw [BadBox.card_cube]
    have hNle : N ≤ 2 ^ p.a 1 := Nat.pow_le_pow_right two_pos (by omega)
    have h1 : 2 * (N - 1) + 1 ≤ 2 * 2 ^ p.a 1 := by omega
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (((2 * (N - 1) + 1) ^ d : ℕ) : ℝ) ≤ (((2 * 2 ^ p.a 1) ^ d : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_left h1 d
      _ = ((2 : ℝ) * 2 ^ p.a 1) ^ d := by push_cast; ring

/-- For `k = 0` condition (3) holds deterministically once `L > 1` (`h_{n,n} = 0`, so the across
distance is at least `s₀`). -/
theorem niceAcrossOne_of_k_eq_zero (hd : 0 < d) (p : NiceParams) (ha0 : p.a 0 = 0) (hk : p.k = 0)
    (hL : 1 < p.L) (H : ℕ → Rd d → ℝ) (hc : ∀ q, Continuous (H q)) (u : Zd d) :
    NiceAcrossOne p H u := by
  intro v _
  have hs0 := p.s_pos 0
  have hfield : Continuous fun z => H (p.n + p.k) z - H p.n z := (hc _).sub (hc _)
  have hlow := exp_mul_le_acrossDist (ξ := p.ξ) (c := latPt (p.s 0) v) hd hfield hs0.le
    (by linarith : p.s 0 < 2 * p.s 0) (m := 0) (fun z _ => by rw [hk, Nat.add_zero, sub_self,
      mul_zero])
  rw [Real.exp_zero, one_mul, show 2 * p.s 0 - p.s 0 = p.s 0 by ring] at hlow
  refine lt_of_lt_of_le ?_ hlow
  have e : (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k) = p.s 0 := by
    rw [hk, Nat.cast_zero, mul_zero, sub_zero]
    simp only [NiceParams.s, ha0, Nat.sub_zero]
    exact (inv_two_pow_eq_rpow p.n).symm
  rw [e]
  have hL0 : 0 < p.L := by linarith
  calc p.L⁻¹ * p.s 0 < 1 * p.s 0 := by
        refine mul_lt_mul_of_pos_right ?_ hs0
        exact inv_lt_one_of_one_lt₀ hL
    _ = p.s 0 := one_mul _

/-! ## The uniform lower tail of `D_k(across B₂(0) \ B₁(0))` -/

/-- **Uniform lower tail** (MA7 D-5.5, blueprint `r2:lem:55`): for `ε > 0` and `η > 0` there is
`L₀ > 1` such that `P[D_k(across B₂(0) \ B₁(0)) ≤ L⁻¹ 2^{-(1-ξQ+ε)k}] ≤ η` for every dyadic
realization, every `L ≥ L₀` and every `k ≥ 1`. -/
theorem acrossTail_uniform {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 < L₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ L : ℝ, L₀ ≤ L → ∀ k : ℕ, 1 ≤ k →
        P {ω | acrossDist ξ (fun z => H k z ω) 0 2 1 ≤ L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k)} ≤
          ENNReal.ofReal η := by
  have hd : 0 < d := by have := h.dim; omega
  have hκ := h.kernel
  have hξ := h.xi_pos
  obtain ⟨hL2, -⟩ := log_two_pos_lt_one
  -- large `k`: Prop 4.8 (lower half) with `δ = ε`
  obtain ⟨C₁, hC₁, hlow⟩ := acrossLower_tail h hε
  obtain ⟨k₁, hk₁⟩ := exists_mul_exp_neg_div_le hC₁ hη
  -- small `k`: the supremum of `|h_k|` on `B̄₂(0)`
  obtain ⟨C₂, hC₂, hsup⟩ := exists_sup_cbox_gaussian_tail.{0} hκ (R := 2) (by norm_num)
  set V : ℝ := k₁ * Real.log 2 with hV
  have hV0 : 0 ≤ V := by positivity
  set u : ℝ := √(2 * V * |Real.log (2 / η)|) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  set M : ℝ := √(2 * d) * V + C₂ * √V + C₂ + u with hM
  set c : ℝ := 1 - ξ * Q + ε with hc
  refine ⟨max 2 (Real.exp (ξ * M) * (2 : ℝ) ^ (|c| * k₁) + 1), lt_of_lt_of_le one_lt_two
    (le_max_left _ _), fun Ω _ P W H hH L hL k hk => ?_⟩
  have hL1 : 1 < L := lt_of_lt_of_le one_lt_two ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := by linarith
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases le_or_gt k₁ k with hkk | hkk
  · -- `k ≥ k₁`: the event is contained in `{D_k < 2^{-(1-ξQ+ε)k}}`
    refine (measure_mono fun ω hω => ?_).trans ((hlow Ω P W H hH k).trans
      (ENNReal.ofReal_le_ofReal (hk₁ k hkk)))
    simp only [mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt hω ?_
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) := Real.rpow_pos_of_pos two_pos _
    calc L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) < 1 * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) :=
          mul_lt_mul_of_pos_right (inv_lt_one_of_one_lt₀ hL1) hpos
      _ = (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) := one_mul _
      _ = (2 : ℝ) ^ (-(1 - ξ * Q + ε) * (k : ℝ)) := rfl
  · -- `1 ≤ k < k₁`: the field bound
    have hX := hH.band k
    have hlogk := log_one_div_inv_two_pow k
    set v : ℝ := Real.log (1 / (2 : ℝ)⁻¹ ^ k) with hv
    have hv0 : 0 < v := by
      rw [hlogk]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    have hvV : v ≤ V := by
      rw [hlogk, hV]
      have : (k : ℝ) ≤ k₁ := by exact_mod_cast hkk.le
      exact mul_le_mul_of_nonneg_right this hL2.le
    have hb := hsup hW (a := (2 : ℝ)⁻¹ ^ k) (b := 1) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) hX 0 hu0
    rw [mul_one, ← hv] at hb
    -- the threshold of the field event is at most `M`
    have hMk : √(2 * d) * v + C₂ * √v + C₂ + u ≤ M := by
      have h1 : √v ≤ √V := Real.sqrt_le_sqrt hvV
      have h2 : √(2 * d) * v ≤ √(2 * d) * V := mul_le_mul_of_nonneg_left hvV (Real.sqrt_nonneg _)
      have h3 : C₂ * √v ≤ C₂ * √V := mul_le_mul_of_nonneg_left h1 hC₂
      linarith
    refine (measure_mono fun ω hω => ?_).trans (hb.trans (ENNReal.ofReal_le_ofReal ?_))
    · -- if `|h_k| ≤ M_k` on `B̄₂(0)` the across distance exceeds the threshold
      simp only [mem_ofPred_eq] at hω ⊢
      by_contra hcon
      push Not at hcon
      have hlow' := exp_mul_le_acrossDist (ξ := ξ) (c := (0 : Rd d)) hd ((hX.continuous ω))
        (zero_le_one) (one_lt_two) (m := -(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u)))
        (fun z hz => by
          have h0 := hcon z hz.1
          have h1 := neg_abs_le (H k z ω)
          have h2 := mul_le_mul_of_nonneg_left h0 hξ.le
          have h3 := mul_le_mul_of_nonneg_left h1 hξ.le
          linarith)
      have hexpM : Real.exp (-(ξ * M)) ≤
          Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hMk hξ.le
      have hthr : L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) < Real.exp (-(ξ * M)) := by
        have hck : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) ≤ (2 : ℝ) ^ (|c| * k₁) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
          have h1 : -(1 - ξ * Q + ε) ≤ |c| := by rw [hc]; exact neg_le_abs _
          have h2 : (k : ℝ) ≤ k₁ := by exact_mod_cast hkk.le
          have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          calc -(1 - ξ * Q + ε) * k ≤ |c| * k := mul_le_mul_of_nonneg_right h1 h3
            _ ≤ |c| * k₁ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        have hLM : Real.exp (ξ * M) * (2 : ℝ) ^ (|c| * k₁) < L :=
          lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hL)
        rw [inv_mul_lt_iff₀ hL0, Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos _)]
        calc (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * Real.exp (ξ * M)
            ≤ (2 : ℝ) ^ (|c| * k₁) * Real.exp (ξ * M) :=
              mul_le_mul_of_nonneg_right hck (Real.exp_pos _).le
          _ < L := by rw [mul_comm]; exact hLM
      have : Real.exp (-(ξ * M)) ≤ acrossDist ξ (fun z => H k z ω) 0 2 1 := by
        calc Real.exp (-(ξ * M)) ≤ Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) := hexpM
          _ = Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) * (2 - 1) := by ring
          _ ≤ _ := hlow'
      linarith
    · -- the Gaussian tail is at most `η`
      have hlog : Real.log (2 / η) ≤ u ^ 2 / (2 * v) := by
        rw [le_div_iff₀ (by positivity), hu, Real.sq_sqrt (by positivity)]
        have h1 := le_abs_self (Real.log (2 / η))
        have h2 : 0 ≤ |Real.log (2 / η)| := abs_nonneg _
        nlinarith
      calc 2 * Real.exp (-u ^ 2 / (2 * v)) ≤ 2 * Real.exp (-Real.log (2 / η)) := by
            gcongr
            rw [neg_div]
            linarith
        _ = η := by
            rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
            field_simp

/-! ## Lemma 5.5 -/

/-- **DGZ Lemma 5.5, uniform form** (MA7 D-5.5; blueprint `r2:lem:55`): for every `A : ℕ` and
`η > 0` there is `L₀` such that for every dyadic realization and all parameters with `p.ξ = ξ`,
`p.Q = Q`, `p.ε = ε`, `a₀ = 0`, `a₁ ≤ A` and `L ≥ L₀`, every `a₁`-box is bad with probability at
most `η` (all `n`, `k`, all boxes). -/
theorem q1_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ε : ℝ} (hε : 0 < ε) (A : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.ε = ε → p.a 0 = 0 → p.a 1 ≤ A → L₀ ≤ p.L →
          ∀ u : Zd d, P {ω | ¬ NiceBox p (fun q z => H q z ω) 1 u} ≤ ENNReal.ofReal η := by
  have hd : 0 < d := by have := h.dim; omega
  have hκ := h.kernel
  set B : ℝ := ((2 : ℝ) * 2 ^ A) ^ d with hB
  have hB0 : 0 < B := by positivity
  -- (1′)
  obtain ⟨C₀, hC₀, hone⟩ := prob_not_niceOscOne_le (d := d) hκ
  obtain ⟨x₀, hx₀⟩ := BadBox.exists_mul_two_exp_neg_sq_le hC₀ hB0.le (half_pos hη)
  -- (3)
  obtain ⟨L₁, hL₁, hacr⟩ := acrossTail_uniform h hε (η := η / 2 / B) (by positivity)
  refine ⟨max (max L₁ (3 * x₀)) (3 * C₀),
    fun Ω _ P W H hH p hpξ hpQ hpε ha0 ha1 hL u => ?_⟩
  have hL₁' : L₁ ≤ p.L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hx₀' : x₀ ≤ p.L / 3 := by
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    linarith
  have hC₀' : C₀ ≤ p.L / 3 := by
    have := (le_max_right _ _).trans hL
    linarith
  have hL1 : 1 < p.L := lt_of_lt_of_le hL₁ hL₁'
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  have hsplit : {ω | ¬ NiceBox p (fun q z => H q z ω) 1 u} ⊆
      {ω | ¬ NiceOscOne p (fun q z => H q z ω) u} ∪
        {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} := by
    intro ω hω
    simp only [mem_ofPred_eq, niceBox_one_iff, not_and_or] at hω
    exact hω
  refine (measure_mono hsplit).trans ((measure_union_le _ _).trans ?_)
  have hB1 : ((2 : ℝ) * 2 ^ p.a 1) ^ d ≤ B := by
    rw [hB]
    gcongr
    · exact one_le_two
  -- (1′)
  have h1 : P {ω | ¬ NiceOscOne p (fun q z => H q z ω) u} ≤ ENNReal.ofReal (η / 2) := by
    refine (hone Ω P W H hH p ha0 hC₀' u).trans (ENNReal.ofReal_le_ofReal ?_)
    calc ((2 : ℝ) * 2 ^ p.a 1) ^ d * (2 * Real.exp (-(p.L / 3 - C₀) ^ 2 / C₀))
        ≤ B * (2 * Real.exp (-(p.L / 3 - C₀) ^ 2 / C₀)) := by gcongr
      _ ≤ η / 2 := hx₀ _ hx₀'
  -- (3)
  have h3 : P {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} ≤ ENNReal.ofReal (η / 2) := by
    rcases Nat.eq_zero_or_pos p.k with hk | hk
    · have hempty : {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
        exact niceAcrossOne_of_k_eq_zero hd p ha0 hk hL1 _ (fun q => hc q ω) u
      rw [hempty, measure_empty]
      exact zero_le
    · refine (prob_not_niceAcrossOne_le hκ hH p ha0 u).trans ?_
      have ht := hacr Ω P W H hH p.L hL₁' p.k hk
      rw [hpξ, hpQ, hpε]
      calc ENNReal.ofReal (((2 : ℝ) * 2 ^ p.a 1) ^ d) *
            P {ω | acrossDist ξ (fun z => H p.k z ω) 0 2 1 ≤
              p.L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * p.k)}
          ≤ ENNReal.ofReal B * ENNReal.ofReal (η / 2 / B) := by
            gcongr
        _ = ENNReal.ofReal (η / 2) := by
            rw [← ENNReal.ofReal_mul hB0.le]
            congr 1
            field_simp
  calc _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add h1 h3
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **DGZ Lemma 5.5** (target `q1_tendsto`; MA7 D-5.5; blueprint `r2:lem:55`): for DGZ's parameters
with a fixed `K` (any `θ`, `R`), `lim_{L→∞} sup_{n,k,u} q₁ = 0`, where
`q₁ = P[B_{s₁}(s₁ u) is bad]`. -/
theorem q1_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (K R : ℕ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) :
    Tendsto (fun L : ℝ => ⨆ (n : ℕ) (k : ℕ) (u : Zd d),
      P {ω | ¬ NiceBox (dgzParams d ξ Q θ ε L K R n k) (fun q z => H q z ω) 1 u}) atTop
      (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact Eventually.of_forall fun _ => le_top
  · have hη' : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
    obtain ⟨L₀, hL₀⟩ := q1_le h hε (K ^ 4) hη'
    filter_upwards [eventually_ge_atTop L₀] with L hL
    refine iSup_le fun n => iSup_le fun k => iSup_le fun u => ?_
    refine (hL₀ Ω P W H hH _ rfl rfl rfl rfl le_rfl hL u).trans ?_
    rw [ENNReal.ofReal_toReal hηtop]

end DGZ

end HigherDimLQGMetric
