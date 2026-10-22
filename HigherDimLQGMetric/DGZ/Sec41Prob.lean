import HigherDimLQGMetric.DGZ.Sec41Config
import HigherDimLQGMetric.DGZ.Sec41Nice
import HigherDimLQGMetric.DGZ.FieldTailsOsc
import HigherDimLFPP.Exist.GoodEvent

/-!
# DGZ Lemma 4.2(1), completed (packet L3c1; MA7 D-4.2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.2(1) (TeX l. 1383–1460, pp. 27–29);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.2 (repairs of G2 at
l. 1444 and of G25), §5 row L3c1.

For an admissible kernel `κ`, `ξ > 0` and `η < ξ (Q - √(2d))` (DGZ (4.3); `Q` need not be the
exponent for these bounds):

* `prob_G_compl_le`: `P[𝒢_nᶜ] ≤ C e^{-n/C}` (from L3b2's `prob_sharpSup_compl_le`);
* `prob_E_compl_le`: there is `c₄ < 1` and `C` (independent of `q`, as in DGZ) with
  `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `q ∈ (c₄, 1)`, all dyadic realizations and all `m < n`;
* `prob_F_compl_le` (`d ≥ 2`): the same for `ℱ_{m,n}` (free-site form), `1 ≤ m < n`;
* `lemma42_1`: the three bounds with one `c₄` and one `C` (DGZ Lemma 4.2(1)).

Proof (MA7 D-4.2).
* `ℰ_{m,n}`: on the white noise of the realization take a version `G` of
  `h_{m,n} = H_{2^{-n}, 2^{-m}}`; `h_m + G` is a version of `h_n`, so `h_n = h_m + G` everywhere
  almost surely (`exists_band_decomp`). The `m`-bad sites of `G` (level `a^{(q)}_{n-m}`) have
  probability `≤ 2d(1 - q)` (HigherDimLFPP `measure_closedSite_le_lowerQuantile_of_band`, with
  `h_{n-m}` as the version of `H_{2^{-n}/2^{-m}, 1}`) and satisfy the product bound with range
  `r = ⌈2(2 + ρ)⌉` (`productBound_closedSite`). For `q > c₄` the Peierls hypotheses hold with
  `θ = (2·3^d)^{-1}` (`exists_c4`), so `Perc.diameterBound` bounds the probability that some bad
  cluster (all lie in `𝓛_m ⊆ B̄_{2^{m+1}}(0)`) has diameter `> m² - 101²` by
  `(2·2^{m+1} + 1)^d 2^{-⌊(m² - 101²)/2⌋} ≤ e^{-m}` for `m ≥ M₀` (`exists_peierls_tail`). Off this
  event, on `𝒢_m` and where `h_n = h_m + G`, `ℰ_{m,n}` holds (`smallClusters_mOpen_of_mGood`).
  For `m < M₀` the probability is at most `1 ≤ C e^{-m/C}`.
* `ℱ_{m,n}`: versions `G₁` of `h_{m-1,n}` and `G₂` of `h_{m,n}`; rough sites have probability
  `≤ (1 + 3^d) 2d (1 - q)` and satisfy the product bound (`Sec41Nice`); `diameterBound` with
  `N = 2^m`, `D' = ⌊(m² - 3)/2⌋` (so `2D' + 3 ≤ m²`) bounds the probability that a rough cluster
  has diameter `> D'` by `e^{-m}` for large `m`. Off this event and on
  `ℰ_{m,n} ∩ ℰ_{m-1,n} ∩ 𝒢_m ∩ 𝒢_{m-1}` (where the band decompositions hold), `ℱ_{m,n}` holds
  (`exists_free_of_smallClusters_mNice`). Sum the bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox SiteClosed closedSite)

variable {d : ℕ}

/-! ### Numerics -/

/-- **The level `c₄`**: for `0 < t ≤ 1` and `K ∈ ℕ` there is `c₄ < 1` with `K (1 - q) ≤ t` for all
`q > c₄`. -/
lemma exists_c4 {t : ℝ≥0∞} (ht0 : 0 < t) (ht1 : t ≤ 1) (K : ℕ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ q : ℝ≥0∞, c₄ < q → (K : ℝ≥0∞) * (1 - q) ≤ t := by
  set u : ℝ≥0∞ := t / ((K : ℝ≥0∞) + 1) with hu
  have hKt : (K : ℝ≥0∞) + 1 ≠ ⊤ := by simp
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (ENNReal.div_pos_iff.2 ⟨ht0.ne', hKt⟩).ne'
  have hut : u ≤ t := by
    rw [hu]
    refine ENNReal.div_le_of_le_mul ?_
    calc t = 1 * t := (one_mul t).symm
      _ ≤ ((K : ℝ≥0∞) + 1) * t := by gcongr; exact le_add_self
      _ = t * ((K : ℝ≥0∞) + 1) := mul_comm _ _
  have hu1 : u ≤ 1 := hut.trans ht1
  refine ⟨1 - u, ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hu0, fun q hq => ?_⟩
  have h1 : 1 - q ≤ u := by
    calc 1 - q ≤ 1 - (1 - u) := tsub_le_tsub_left hq.le 1
      _ = u := ENNReal.sub_sub_cancel ENNReal.one_ne_top hu1
  calc (K : ℝ≥0∞) * (1 - q) ≤ (K : ℝ≥0∞) * u := by gcongr
    _ ≤ t := by
      rw [hu, ← mul_div_assoc]
      refine ENNReal.div_le_of_le_mul ?_
      calc (K : ℝ≥0∞) * t ≤ ((K : ℝ≥0∞) + 1) * t := by gcongr; exact le_self_add
        _ = t * ((K : ℝ≥0∞) + 1) := mul_comm _ _

/-- **The Peierls tail** (DGZ (4.13), (4.15)): `(2·2^{m+k} + 1)^d 2^{-j} ≤ e^{-m}` when
`m² ≤ 4j + c` and `m ≥ M₀(d, k, c)`. -/
lemma exists_peierls_tail (d k c : ℕ) : ∃ M₀ : ℕ, ∀ m j : ℕ, M₀ ≤ m → m ^ 2 ≤ 4 * j + c →
    (2 * ((2 ^ (m + k) : ℕ) : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ j ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  refine ⟨4 * (d + 2) + 4 * (k + 2) * d + c + 1, fun m j hm hj => ?_⟩
  set E : ℕ := (m + k + 2) * d with hE
  have hEj : E + 2 * m ≤ j := by
    have h1 : (4 * (d + 2) + 4 * (k + 2) * d + c + 1) * m ≤ m * m := Nat.mul_le_mul_right m hm
    have h2 : 4 * (k + 2) * d + c + 1 ≤ (4 * (k + 2) * d + c + 1) * m :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h3 : (4 * (d + 2) + 4 * (k + 2) * d + c + 1) * m =
        4 * (d + 2) * m + (4 * (k + 2) * d + c + 1) * m := by ring
    have h4 : m ^ 2 = m * m := sq m
    have h5 : E = d * m + 2 * m + (k + 2) * d - 2 * m := by rw [hE]; ring_nf; omega
    nlinarith
  rw [HigherDimLFPP.L33.box_mul_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN : 2 * ((2 ^ (m + k) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (m + k + 2) := by
    have : (1 : ℝ) ≤ 2 ^ (m + k) := one_le_pow₀ (by norm_num)
    push_cast
    have e : (2 : ℝ) ^ (m + k + 2) = 4 * 2 ^ (m + k) := by ring
    linarith
  have h1 : (2 * ((2 ^ (m + k) : ℕ) : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ E := by
    rw [hE, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hN d
  have hsplit : j = (j - E) + E := by omega
  have h2 : (2 : ℝ) ^ E * (2⁻¹ : ℝ) ^ j = (2⁻¹ : ℝ) ^ (j - E) := by
    conv_lhs => rw [hsplit, pow_add]
    rw [mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
  have h3 : (2⁻¹ : ℝ) ^ (j - E) ≤ (2⁻¹ : ℝ) ^ (2 * m) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h4 : (2⁻¹ : ℝ) ^ (2 * m) ≤ Real.exp (-(m : ℝ)) := by
    rw [pow_mul, show -(m : ℝ) = m * (-1) by ring, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by norm_num) ?_ m
    rw [Real.exp_neg]
    have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
    rw [show ((2 : ℝ)⁻¹) ^ 2 = (4 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (Real.exp_pos 1) he
  calc (2 * ((2 ^ (m + k) : ℕ) : ℝ) + 1) ^ d * (2⁻¹ : ℝ) ^ j
      ≤ (2 : ℝ) ^ E * (2⁻¹ : ℝ) ^ j := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2⁻¹ : ℝ) ^ (j - E) := h2
    _ ≤ (2⁻¹ : ℝ) ^ (2 * m) := h3
    _ ≤ Real.exp (-(m : ℝ)) := h4

/-- `A e^{-x/B} ≤ A' e^{-x/B'}` for `0 ≤ A ≤ A'`, `0 < B ≤ B'`, `x ≥ 0`. -/
lemma mul_exp_neg_div_le_of_le {A A' B B' x : ℝ} (hA : 0 ≤ A) (hAA' : A ≤ A') (hB : 0 < B)
    (hBB' : B ≤ B') (hx : 0 ≤ x) : A * Real.exp (-x / B) ≤ A' * Real.exp (-x / B') := by
  have h : Real.exp (-x / B) ≤ Real.exp (-x / B') := by
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hx hB hBB'
  calc A * Real.exp (-x / B) ≤ A * Real.exp (-x / B') := mul_le_mul_of_nonneg_left h hA
    _ ≤ A' * Real.exp (-x / B') := mul_le_mul_of_nonneg_right hAA' (Real.exp_pos _).le

/-- `e^{-(m-1)/B} = e^{1/B} e^{-m/B}` for `m ≥ 1`. -/
lemma exp_neg_pred_div {B : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-((m - 1 : ℕ) : ℝ) / B) = Real.exp (1 / B) * Real.exp (-(m : ℝ) / B) := by
  rw [← Real.exp_add, Nat.cast_sub hm]
  congr 1
  push_cast
  ring

/-! ### Band decompositions -/

/-- Two adjacent bands: the sum of versions of `H_{b,c}` and `H_{a,b}` is a version of `H_{a,c}`
(`0 < a ≤ b ≤ c`). -/
theorem isBandVersion_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) {H₀ H₁ : Rd d → Ω → ℝ} (h₀ : IsBandVersion P W κ b c H₀)
    (h₁ : IsBandVersion P W κ a b H₁) :
    IsBandVersion P W κ a c (fun z ω => H₀ z ω + H₁ z ω) where
  continuous ω := (h₀.continuous ω).add (h₁.continuous ω)
  measurable z := (h₀.measurable z).add (h₁.measurable z)
  ae_eq z := by
    filter_upwards [h₀.ae_eq z, h₁.ae_eq z, hW.bandVec_add_ae hκ ha hab hbc z] with ω e0 e1 e2
    show H₀ z ω + H₁ z ω = _
    rw [e0, e1, e2]
    ring

/-- **Band decomposition of a dyadic realization**: for `m ≤ n` there is a version `G` of
`h_{m,n} = H_{2^{-n}, 2^{-m}}` (same white noise) with `h_n = h_m + G` everywhere, almost surely. -/
theorem exists_band_decomp {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n) :
    ∃ G : Rd d → Ω → ℝ, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G ∧
      ∀ᵐ ω ∂P, ∀ z, H n z ω = H m z ω + G z ω := by
  have hW := hH.whiteNoise
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  obtain ⟨G, hG⟩ := exists_isBandVersion hκ hW ha ((2 : ℝ)⁻¹ ^ m)
  have hab : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hbc : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsum := isBandVersion_add hκ hW ha hab hbc (hH.band m) hG
  exact ⟨G, hG, (hH.band n).ae_eq_forall hsum⟩

/-- `2^{-n} / 2^{-m} = 2^{-(n-m)}` for `m ≤ n`. -/
lemma inv_two_pow_div_inv_two_pow {m n : ℕ} (hmn : m ≤ n) :
    (2 : ℝ)⁻¹ ^ n / (2 : ℝ)⁻¹ ^ m = (2 : ℝ)⁻¹ ^ (n - m) :=
  (pow_sub₀ _ (by norm_num) hmn).symm

/-- The `m`-bad sites of a version `G` of `h_{m,n}` (level `a^{(q)}_{n-m}`) have probability at
most `2d(1 - q)`. -/
lemma measure_closedSite_le_of_realization {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n) {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G) (ξ : ℝ) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) (y : Zd d) :
    P (closedSite ξ G ((2 : ℝ)⁻¹ ^ m) (aQ P H ξ (n - m) q) (2 - (2 : ℝ)⁻¹ ^ m) y) ≤
      2 * d * (1 - q) := by
  have hH' : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / (2 : ℝ)⁻¹ ^ m) 1 (H (n - m)) :=
    (hH.band (n - m)).congr_band (inv_two_pow_div_inv_two_pow hmn).symm rfl
  exact HigherDimLFPP.DGZ.measure_closedSite_le_lowerQuantile_of_band hκ hH.whiteNoise
    hH.whiteNoise (by positivity) (by positivity) hG hH' ξ hq0 hq1 _ y

/-! ### `𝒢_n` -/

/-- **DGZ Lemma 4.2(1), first bound** (MA7 D-4.2): `P[𝒢_nᶜ] ≤ C e^{-n/C}` for every dyadic
realization and every `n`. -/
theorem prob_G_compl_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ} (hξ : 0 < ξ)
    (hη : η < ξ * (Q - √(2 * d))) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
      {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ n : ℕ,
        P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨C, hC, h⟩ := prob_sharpSup_compl_le hκ hξ hη
  refine ⟨C, hC, fun {Ω} _ {P} {W} {H} hH n => ?_⟩
  have e : (eventG ξ Q η H n)ᶜ =
      {ω | ∃ z ∈ cbox (0 : Rd d) 3, (n : ℝ) * (Q - η / ξ) * Real.log 2 < H n z ω} := by
    ext ω
    simp only [eventG, mem_compl_iff, mem_ofPred_eq, not_forall, not_le, exists_prop]
  rw [e]
  exact h hH.whiteNoise n (hH.band n)

/-! ### `ℰ_{m,n}` -/

/-- The Peierls parameter `θ = (2·3^d)^{-1}` of HigherDimLFPP: `0 < θ^{(r+1)^d} ≤ 1`. -/
lemma theta_pow_pos_le_one (d r : ℕ) :
    0 < ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ∧
      ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ≤ 1 :=
  ⟨ENNReal.pow_pos (ENNReal.ofReal_pos.2 (by positivity)) _,
    pow_le_one₀ zero_le (HigherDimLFPP.L33.theta_le_one d)⟩

/-- **DGZ Lemma 4.2(1), second bound** (MA7 D-4.2): there are `c₄ < 1` and `C > 0` such that for
every `q ∈ (c₄, 1)`, every dyadic realization and all `m < n`, `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}`. -/
theorem prob_E_compl_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ} (hξ : 0 < ξ)
    (hη : η < ξ * (Q - √(2 * d))) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∃ C > 0, ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, m < n →
          P (eventE P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le hκ hξ hη
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  set r : ℕ := ⌈2 * (2 + ρ)⌉₊ with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ with hθ
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  obtain ⟨c₄, hc₄1, hc₄⟩ := exists_c4 hθ0 hθ1 (2 * d)
  obtain ⟨M₀, hM₀⟩ := exists_peierls_tail d 1 (2 * 101 ^ 2 + 2)
  set C : ℝ := max (CG + 1) ((M₀ : ℝ) + 1) with hC
  have hCG1 : CG + 1 ≤ C := le_max_left _ _
  have hCM : (M₀ : ℝ) + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨c₄, hc₄1, C, hC0, fun q hq₁ hq₂ Ω _ P W H hH m n hmn => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hq₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hm : m < M₀
  · calc P (eventE P H ξ Q η q m n)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
          refine ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg_div hm0 ?_)
          have : (m : ℝ) + 1 ≤ M₀ := by exact_mod_cast hm
          linarith
  push Not at hm
  -- the band decomposition `h_n = h_m + h_{m,n}` and the bad sites of `h_{m,n}`
  obtain ⟨G, hG', hsum⟩ := exists_band_decomp hκ hH hmn.le
  set s : ℝ := (2 : ℝ)⁻¹ ^ m with hs
  set a : ℝ := aQ P H ξ (n - m) q with ha
  set closed : Zd d → Set Ω := closedSite ξ G s a (2 - s) with hclosed
  have hcl : ∀ y, P (closed y) ≤ 2 * d * (1 - q) := fun y =>
    measure_closedSite_le_of_realization hκ hH hmn.le hG' ξ hq0 hq₂ y
  have hPB : ProductBound P closed (r : ℤ) :=
    HigherDimLFPP.DGZ.productBound_closedSite hκ hW hρ (by positivity) hG' (by positivity) le_rfl
      ξ a (2 - s)
  have hεθ : 2 * (d : ℝ≥0∞) * (1 - q) ≤ θ ^ ((r + 1) ^ d) := by
    have := hc₄ q hq₁
    push_cast at this
    exact this
  -- the Peierls event: a bad cluster of diameter `> m² - 101²`
  set B : Set Ω := {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧
    (∃ z ∈ C, WithinInf ((2 ^ (m + 1) : ℕ) : ℤ) z 0) ∧
      ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf ((m ^ 2 - 101 ^ 2 : ℕ) : ℤ) y y'} with hB
  have hPB' : P B ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
    (Perc.diameterBound d P closed r _ θ hcl hPB (HigherDimLFPP.L33.theta_le_one d) hεθ
      (HigherDimLFPP.L33.three_pow_mul_theta_le d) 0 (2 ^ (m + 1)) (m ^ 2 - 101 ^ 2)).trans
      (hM₀ m _ hm (by omega))
  -- the exceptional set of the decomposition
  set N0 : Set Ω := {ω | ¬ ∀ z, H n z ω = H m z ω + G z ω} with hN0
  have hPN0 : P N0 = 0 := ae_iff.1 hsum
  -- the inclusion (4.11)
  have hsub : (eventE P H ξ Q η q m n)ᶜ ⊆ (eventG ξ Q η H m)ᶜ ∪ N0 ∪ B := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hGω, hsumω⟩, hBω⟩ := hcon
    apply hω
    have hGω' : ω ∈ eventG ξ Q η H m := not_not.1 hGω
    have hsumω' : ∀ z, H n z ω = H m z ω + G z ω := not_not.1 hsumω
    refine smallClusters_mOpen_of_mGood hξ ((hH.band n).continuous ω) (hG'.continuous ω)
      hsumω' hGω' ?_
    intro C hC
    refine ⟨⟨2 ^ (m + 1), fun y hy => withinInf_of_not_mem_mGood (hC.2.1 hy)⟩, ?_⟩
    by_contra hD
    push Not at hD
    obtain ⟨y, hy, y', hy', hyy'⟩ := hD
    obtain ⟨c, hc⟩ := hC.1
    refine hBω ⟨C, hC, ⟨c, hc, ?_⟩, y, hy, y', hy', hyy'⟩
    have := withinInf_of_not_mem_mGood (hC.2.1 hc)
    exact_mod_cast this
  calc P (eventE P H ξ Q η q m n)ᶜ ≤ P ((eventG ξ Q η H m)ᶜ ∪ N0 ∪ B) := measure_mono hsub
    _ ≤ P (eventG ξ Q η H m)ᶜ + P N0 + P B :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (CG * Real.exp (-(m : ℝ) / CG)) + 0 +
          ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
        gcongr
        · exact hG hH m
        · exact hPN0.le
    _ = ENNReal.ofReal (CG * Real.exp (-(m : ℝ) / CG) + Real.exp (-(m : ℝ))) := by
        rw [add_zero, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : CG * Real.exp (-(m : ℝ) / CG) ≤ CG * Real.exp (-(m : ℝ) / C) :=
          mul_exp_neg_div_le_of_le hCG.le le_rfl hCG (by linarith) hm0
        have h2 : 1 * Real.exp (-(m : ℝ) / 1) ≤ 1 * Real.exp (-(m : ℝ) / C) :=
          mul_exp_neg_div_le_of_le zero_le_one le_rfl one_pos (by linarith) hm0
        rw [one_mul, one_mul, div_one] at h2
        have h3 := Real.exp_pos (-(m : ℝ) / C)
        nlinarith

/-! ### `ℱ_{m,n}` -/

/-- **DGZ Lemma 4.2(1), third bound** (MA7 D-4.2, free-site form of `ℱ_{m,n}`; `d ≥ 2`): there
are `c₄ < 1` and `C > 0` such that for every `q ∈ (c₄, 1)`, every dyadic realization and all
`1 ≤ m < n`, `P[ℱ_{m,n}ᶜ] ≤ C e^{-m/C}`. -/
theorem prob_F_compl_le (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ}
    (hξ : 0 < ξ) (hη : η < ξ * (Q - √(2 * d))) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∃ C > 0, ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, 1 ≤ m → m < n →
          P (eventF P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨cE, hcE1, CE, hCE, hE⟩ := prob_E_compl_le hκ hξ hη
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le hκ hξ hη
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  set r : ℕ := ⌈2 * (2 + ρ)⌉₊ with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ with hθ
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  obtain ⟨cN, hcN1, hcN⟩ := exists_c4 hθ0 hθ1 ((1 + 3 ^ d) * (2 * d))
  obtain ⟨M₀, hM₀⟩ := exists_peierls_tail d 0 6
  set M₁ : ℕ := max M₀ 2 with hM₁
  set A : ℝ := CE + CE * Real.exp (1 / CE) + CG + CG * Real.exp (1 / CG) + 1 with hA
  set C : ℝ := max A ((M₁ : ℝ) + 1) with hC
  have hAC : A ≤ C := le_max_left _ _
  have hMC : (M₁ : ℝ) + 1 ≤ C := le_max_right _ _
  have hE1 : 0 ≤ CE * Real.exp (1 / CE) := by positivity
  have hG1 : 0 ≤ CG * Real.exp (1 / CG) := by positivity
  have hCEC : CE ≤ C := by linarith
  have hCGC : CG ≤ C := by linarith
  have h1C : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨max cE cN, max_lt hcE1 hcN1, C, hC0, fun q hq₁ hq₂ Ω _ P W H hH m n hm1 hmn => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hqE : cE < q := lt_of_le_of_lt (le_max_left _ _) hq₁
  have hqN : cN < q := lt_of_le_of_lt (le_max_right _ _) hq₁
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hq₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hm : m < M₁
  · calc P (eventF P H ξ Q η q m n)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
          refine ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg_div hm0 ?_)
          have : (m : ℝ) + 1 ≤ M₁ := by exact_mod_cast hm
          linarith
  push Not at hm
  have hM₀m : M₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  -- the band decompositions `h_n = h_{m-1} + h_{m-1,n} = h_m + h_{m,n}`
  obtain ⟨G₂, hG₂, hsum₂⟩ := exists_band_decomp hκ hH hmn.le
  obtain ⟨G₁, hG₁, hsum₁⟩ := exists_band_decomp hκ hH (show m - 1 ≤ n by omega)
  set a₁ : ℝ := aQ P H ξ (n - (m - 1)) q with ha₁
  set a₂ : ℝ := aQ P H ξ (n - m) q with ha₂
  have hcl₁ : ∀ y, P (closedSite ξ G₁ ((2 : ℝ)⁻¹ ^ (m - 1)) a₁ (2 - (2 : ℝ)⁻¹ ^ (m - 1)) y) ≤
      2 * d * (1 - q) :=
    fun y => measure_closedSite_le_of_realization hκ hH (by omega) hG₁ ξ hq0 hq₂ y
  have hcl₂ : ∀ z, P (closedSite ξ G₂ ((2 : ℝ)⁻¹ ^ m) a₂ (2 - (2 : ℝ)⁻¹ ^ m) z) ≤
      2 * d * (1 - q) :=
    fun z => measure_closedSite_le_of_realization hκ hH hmn.le hG₂ ξ hq0 hq₂ z
  -- the rough sites: probability, product bound, Peierls event
  set rough : Zd d → Set Ω := roughSite ξ G₁ G₂ m a₁ a₂ with hrough
  have hrl : ∀ y, P (rough y) ≤ (1 + 3 ^ d) * (2 * d * (1 - q)) :=
    measure_roughSite_le hcl₁ hcl₂
  have hPB : ProductBound P rough (r : ℤ) :=
    productBound_roughSite hκ hW hρ (by positivity) hm1 hG₁ hG₂ ξ a₁ a₂
  have hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤ θ ^ ((r + 1) ^ d) := by
    have := hcN q hqN
    push_cast at this
    rw [← mul_assoc]
    exact this
  set D' : ℕ := (m ^ 2 - 3) / 2 with hD'
  set B : Set Ω := {ω | ∃ C, IsClosedCluster {y | ω ∉ rough y} C ∧
    (∃ z ∈ C, WithinInf ((2 ^ m : ℕ) : ℤ) z 0) ∧
      ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf (D' : ℤ) y y'} with hB
  have hPB' : P B ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
    (Perc.diameterBound d P rough r _ θ hrl hPB (HigherDimLFPP.L33.theta_le_one d) hεθ
      (HigherDimLFPP.L33.three_pow_mul_theta_le d) 0 (2 ^ m) D').trans
      (hM₀ m (D' / 2) hM₀m (by omega))
  -- the exceptional sets of the decompositions
  set N₁ : Set Ω := {ω | ¬ ∀ z, H n z ω = H (m - 1) z ω + G₁ z ω} with hN₁
  set N₂ : Set Ω := {ω | ¬ ∀ z, H n z ω = H m z ω + G₂ z ω} with hN₂
  have hPN₁ : P N₁ = 0 := ae_iff.1 hsum₁
  have hPN₂ : P N₂ = 0 := ae_iff.1 hsum₂
  -- the inclusion (4.14), free-site form
  have hsub : (eventF P H ξ Q η q m n)ᶜ ⊆ (eventE P H ξ Q η q m n)ᶜ ∪
      (eventE P H ξ Q η q (m - 1) n)ᶜ ∪ (eventG ξ Q η H m)ᶜ ∪ (eventG ξ Q η H (m - 1))ᶜ ∪
        (N₁ ∪ N₂) ∪ B := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨⟨hEm, hEm1⟩, hGm⟩, hGm1⟩, hN₁ω, hN₂ω⟩, hBω⟩ := hcon
    apply hω
    refine ⟨⟨not_not.1 hEm, not_not.1 hEm1⟩, fun x _ => ?_⟩
    have hN : SmallClusters (mNice ξ (fun z => G₁ z ω) (fun z => G₂ z ω) m a₁ a₂) D' := by
      rw [← setOf_not_mem_roughSite]
      intro C hC
      have hCreg : ∀ y ∈ C, WithinInf (2 ^ m) y 0 := by
        intro y hy i
        have hyr : ω ∈ rough y := not_not.1 (hC.2.1 hy)
        have := (mem_latRegion_pred_iff hm1).1 hyr.1 i
        rw [Pi.zero_apply, sub_zero]
        exact this.le
      refine ⟨⟨2 ^ m, hCreg⟩, ?_⟩
      by_contra hD
      push Not at hD
      obtain ⟨y, hy, y', hy', hyy'⟩ := hD
      obtain ⟨c, hc⟩ := hC.1
      refine hBω ⟨C, hC, ⟨c, hc, ?_⟩, y, hy, y', hy', hyy'⟩
      have := hCreg c hc
      exact_mod_cast this
    exact exists_free_of_smallClusters_mNice hd hξ hm1 ((hH.band n).continuous ω)
      (hG₁.continuous ω) (hG₂.continuous ω) (not_not.1 hN₁ω) (not_not.1 hN₂ω)
      (not_not.1 hGm1) (not_not.1 hGm) hN (by omega) x
  -- the probability bound
  have hPE := hE q hqE hq₂ hH m n hmn
  have hPE1 := hE q hqE hq₂ hH (m - 1) n (by omega)
  have hPG := hG hH m
  have hPG1 := hG hH (m - 1)
  have hPN : P (N₁ ∪ N₂) = 0 := measure_union_null hPN₁ hPN₂
  calc P (eventF P H ξ Q η q m n)ᶜ
      ≤ P ((eventE P H ξ Q η q m n)ᶜ ∪ (eventE P H ξ Q η q (m - 1) n)ᶜ ∪
          (eventG ξ Q η H m)ᶜ ∪ (eventG ξ Q η H (m - 1))ᶜ ∪ (N₁ ∪ N₂) ∪ B) := measure_mono hsub
    _ ≤ P (eventE P H ξ Q η q m n)ᶜ + P (eventE P H ξ Q η q (m - 1) n)ᶜ +
          P (eventG ξ Q η H m)ᶜ + P (eventG ξ Q η H (m - 1))ᶜ + P (N₁ ∪ N₂) + P B := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (CE * Real.exp (-(m : ℝ) / CE)) +
          ENNReal.ofReal (CE * Real.exp (-((m - 1 : ℕ) : ℝ) / CE)) +
          ENNReal.ofReal (CG * Real.exp (-(m : ℝ) / CG)) +
          ENNReal.ofReal (CG * Real.exp (-((m - 1 : ℕ) : ℝ) / CG)) + 0 +
          ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
        rw [hPN]
        exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hPE hPE1) hPG) hPG1)
          le_rfl) hPB'
    _ = ENNReal.ofReal (CE * Real.exp (-(m : ℝ) / CE) +
          CE * Real.exp (-((m - 1 : ℕ) : ℝ) / CE) + CG * Real.exp (-(m : ℝ) / CG) +
          CG * Real.exp (-((m - 1 : ℕ) : ℝ) / CG) + Real.exp (-(m : ℝ))) := by
        rw [add_zero, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have t1 : CE * Real.exp (-(m : ℝ) / CE) ≤ CE * Real.exp (-(m : ℝ) / C) :=
          mul_exp_neg_div_le_of_le hCE.le le_rfl hCE hCEC hm0
        have t2 : CE * Real.exp (-((m - 1 : ℕ) : ℝ) / CE) ≤
            CE * Real.exp (1 / CE) * Real.exp (-(m : ℝ) / C) := by
          rw [exp_neg_pred_div hm1, ← mul_assoc]
          exact mul_exp_neg_div_le_of_le hE1 le_rfl hCE hCEC hm0
        have t3 : CG * Real.exp (-(m : ℝ) / CG) ≤ CG * Real.exp (-(m : ℝ) / C) :=
          mul_exp_neg_div_le_of_le hCG.le le_rfl hCG hCGC hm0
        have t4 : CG * Real.exp (-((m - 1 : ℕ) : ℝ) / CG) ≤
            CG * Real.exp (1 / CG) * Real.exp (-(m : ℝ) / C) := by
          rw [exp_neg_pred_div hm1, ← mul_assoc]
          exact mul_exp_neg_div_le_of_le hG1 le_rfl hCG hCGC hm0
        have t5 : 1 * Real.exp (-(m : ℝ) / 1) ≤ 1 * Real.exp (-(m : ℝ) / C) :=
          mul_exp_neg_div_le_of_le zero_le_one le_rfl one_pos h1C hm0
        rw [one_mul, one_mul, div_one] at t5
        have t6 : A * Real.exp (-(m : ℝ) / C) ≤ C * Real.exp (-(m : ℝ) / C) :=
          mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
        have e : A * Real.exp (-(m : ℝ) / C) = CE * Real.exp (-(m : ℝ) / C) +
            CE * Real.exp (1 / CE) * Real.exp (-(m : ℝ) / C) + CG * Real.exp (-(m : ℝ) / C) +
            CG * Real.exp (1 / CG) * Real.exp (-(m : ℝ) / C) + Real.exp (-(m : ℝ) / C) := by
          rw [hA]; ring
        linarith

/-- **DGZ Lemma 4.2(1)** (MA7 D-4.2; `d ≥ 2`, `ξ > 0`, `η < ξ (Q - √(2d))`): there are `c₄ < 1`
and `C > 0` such that for all `q ∈ (c₄, 1)` and every dyadic realization,
`P[𝒢_nᶜ] ≤ C e^{-n/C}` for all `n`, `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `m < n`, and
`P[ℱ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `1 ≤ m < n`. -/
theorem lemma42_1 (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ} (hξ : 0 < ξ)
    (hη : η < ξ * (Q - √(2 * d))) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∃ C > 0, ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H →
          (∀ n : ℕ, P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C))) ∧
          (∀ m n : ℕ, m < n →
            P (eventE P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C))) ∧
          (∀ m n : ℕ, 1 ≤ m → m < n →
            P (eventF P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C))) := by
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le hκ hξ hη
  obtain ⟨cE, hcE1, CE, hCE, hE⟩ := prob_E_compl_le hκ hξ hη
  obtain ⟨cF, hcF1, CF, hCF, hF⟩ := prob_F_compl_le hd hκ hξ hη
  set C : ℝ := max (max CG CE) CF with hC
  have hCG' : CG ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCE' : CE ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCF' : CF ≤ C := le_max_right _ _
  refine ⟨max cE cF, max_lt hcE1 hcF1, C, lt_of_lt_of_le hCG hCG',
    fun q hq₁ hq₂ Ω _ P W H hH => ⟨fun n => ?_, fun m n hmn => ?_, fun m n hm hmn => ?_⟩⟩
  · exact (hG hH n).trans (ENNReal.ofReal_le_ofReal
      (mul_exp_neg_div_le_of_le hCG.le hCG' hCG hCG' (Nat.cast_nonneg n)))
  · exact (hE q (lt_of_le_of_lt (le_max_left _ _) hq₁) hq₂ hH m n hmn).trans
      (ENNReal.ofReal_le_ofReal (mul_exp_neg_div_le_of_le hCE.le hCE' hCE hCE' (Nat.cast_nonneg m)))
  · exact (hF q (lt_of_le_of_lt (le_max_right _ _) hq₁) hq₂ hH m n hm hmn).trans
      (ENNReal.ofReal_le_ofReal (mul_exp_neg_div_le_of_le hCF.le hCF' hCF hCF' (Nat.cast_nonneg m)))

end DGZ

end HigherDimLQGMetric
