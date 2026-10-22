import HigherDimLQGContinuity.UnifBase.Consts
import HigherDimLQGMetric.DGZ.SelfDiam

/-!
# Uniform DGZ Lemma 4.2(1) and the event `𝒜_{r,n}` (packet U1)

Blueprint Part D, `d:lem-u42` (uniform [1, Lemma 4.2(1)] via the slope `Q₀(η) = √(2d) + (μ - η)/b`; NA3 §2.4,
§2.15 rows 3–4; rulings N3, N8). Ports of `HigherDimLQGMetric.DGZ.prob_G_compl_le`, `prob_E_compl_le`,
`prob_F_compl_le`, `lemma42_1` (`DGZ/Sec41Prob.lean`) and `prob_eventA_compl_le` (`DGZ/SelfDiam.lean`).

The events `𝒢_n`, `ℰ_{m,n}`, `ℱ_{m,n}`, `𝒜_{r,n}` (`DGZ.eventG`, `eventE`, `eventF`, `eventA`) are reused verbatim
at `(ξ, Q, η)`. The fixed-`ξ` bounds return constants after `(ξ, Q, η)`; here they come before the parameter. The
parameters are those of `S(b, μ)` with an arbitrary `Q` (the bounds never use that `Q` is the exponent):
`0 < ξ ≤ b` and `μ ≤ ξ (Q - √(2d))`. For `UHyp d κ b μ ξ` take `Q = distExp d ξ` and the fields `h.base.xi_pos`,
`h.le_b`, `h.gap`.

* `u1_slope_le`, `eventG_supset`: `Q - η/ξ ≥ Q₀(η)` for `η < μ`, hence
  `𝒢_n ⊇ {h_n ≤ n Q₀(η) log 2 on B̄₃(0)}`; at `η = uEta μ = μ/2` the slope is U0's `uQ0 d b μ`
  (`eventG_supset_uQ0`);
* `prob_G_compl_le_unif`: `P[𝒢_nᶜ] ≤ C e^{-n/C}` with `C = C(d, κ, (μ - η)/b)` (the sharp supremum tail
  `DGZ.exists_sup_cbox_tail` at the slope `Q₀(η) > √(2d)`);
* `prob_E_compl_le_unif`, `prob_F_compl_le_unif`, `lemma42_1_unif`: one `c₄ = c₄(d, κ) < 1` (chosen before
  `b, μ, η`) and `C = C(d, κ, b, μ, η)`; the proofs of `DGZ.prob_E_compl_le`, `DGZ.prob_F_compl_le` are repeated with
  the constant of the `𝒢`-bound made explicit (`u1_prob_E_compl_le_of_G`, `u1_prob_F_compl_le_of_G`): the bad and
  rough site probabilities and the Peierls thresholds do not involve `ξ`;
* `prob_eventA_compl_le_unif`: `P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C}` for `1 ≤ r < n` (union bound, as `DGZ.prob_eventA_compl_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox SiteClosed closedSite)

variable {d : ℕ}

/-! ### The slope of `𝒢_n` -/

/-- **The uniform slope** (`d:lem-u42`; NA3 R3): for `0 < ξ ≤ b` and `η < μ ≤ ξ (Q - √(2d))`,
`√(2d) + (μ - η)/b ≤ Q - η/ξ`. -/
theorem u1_slope_le {b μ η ξ Q : ℝ} (hξ : 0 < ξ) (hξb : ξ ≤ b) (hημ : η < μ)
    (hgap : μ ≤ ξ * (Q - √(2 * d))) : √(2 * d) + (μ - η) / b ≤ Q - η / ξ := by
  have h1 : (μ - η) / b ≤ (μ - η) / ξ := div_le_div_of_nonneg_left (by linarith) hξ hξb
  have h2 : (μ - η) / ξ ≤ Q - √(2 * d) - η / ξ := by
    have e : Q - √(2 * d) - η / ξ = (ξ * (Q - √(2 * d)) - η) / ξ := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hξ.le
  linarith

/-- **`𝒢_n` contains the uniform slope event** (`d:lem-u42`, `eventG_supset`): for `0 < ξ ≤ b` and
`η < μ ≤ ξ (Q - √(2d))`, `{h_n ≤ n Q₀(η) log 2 on B̄₃(0)} ⊆ 𝒢_n(ξ, Q, η)` with `Q₀(η) = √(2d) + (μ - η)/b`. -/
theorem eventG_supset {b μ η ξ Q : ℝ} (hξ : 0 < ξ) (hξb : ξ ≤ b) (hημ : η < μ)
    (hgap : μ ≤ ξ * (Q - √(2 * d))) {Ω : Type*} (H : ℕ → Rd d → Ω → ℝ) (n : ℕ) :
    {ω | ∀ z ∈ cbox (0 : Rd d) 3, H n z ω ≤ n * (√(2 * d) + (μ - η) / b) * Real.log 2} ⊆
      eventG ξ Q η H n := by
  intro ω hω z hz
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2 : (n : ℝ) * (√(2 * d) + (μ - η) / b) * Real.log 2 ≤ n * (Q - η / ξ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (u1_slope_le hξ hξb hημ hgap)
      (Nat.cast_nonneg n)) hl.le
  exact (hω z hz).trans h2

/-- **The slope at the standard margin** (`d:lem-u42`, last sentence; U0's constant package): at `η = uEta μ = μ/2`
the slope `Q₀(η)` is `uQ0 d b μ = √(2d) + μ/(2b)` (`d:lem-consts`), so
`{h_n ≤ n Q₀ log 2 on B̄₃(0)} ⊆ 𝒢_n(ξ, Q, μ/2)` for `0 < ξ ≤ b` and `0 < μ ≤ ξ (Q - √(2d))`. -/
theorem eventG_supset_uQ0 {b μ ξ Q : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hξb : ξ ≤ b)
    (hgap : μ ≤ ξ * (Q - √(2 * d))) {Ω : Type*} (H : ℕ → Rd d → Ω → ℝ) (n : ℕ) :
    {ω | ∀ z ∈ cbox (0 : Rd d) 3, H n z ω ≤ n * uQ0 d b μ * Real.log 2} ⊆
      eventG ξ Q (uEta μ) H n := by
  have e : uQ0 d b μ = √(2 * d) + (μ - uEta μ) / b := by
    unfold uQ0 uEta
    congr 1
    ring
  rw [e]
  exact eventG_supset hξ hξb (uEta_lt hμ) hgap H n

/-! ### `𝒢_n` -/

/-- **Uniform DGZ Lemma 4.2(1), first bound** (`d:lem-u42`; port of `DGZ.prob_G_compl_le`): for `η < μ` there is
`C = C(d, κ, (μ - η)/b) > 0` such that for all `0 < ξ ≤ b` and `Q` with `μ ≤ ξ (Q - √(2d))`, every dyadic
realization and every `n`, `P[𝒢_nᶜ] ≤ C e^{-n/C}`. -/
theorem prob_G_compl_le_unif {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ η : ℝ} (hημ : η < μ) :
    ∃ C > 0, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b → μ ≤ ξ * (Q - √(2 * d)) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ n : ℕ,
          P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  rcases le_or_gt b 0 with hb | hb
  · exact ⟨1, one_pos, fun ξ Q hξ hξb _ => absurd (hξ.trans_le hξb) (not_lt.2 hb)⟩
  have hA : √(2 * d) < √(2 * d) + (μ - η) / b :=
    lt_add_of_pos_right _ (div_pos (sub_pos.2 hημ) hb)
  obtain ⟨C, hC0, htail⟩ := exists_sup_cbox_tail (d := d) hκ hA (R := 3) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C / Real.log 2, by positivity, fun ξ Q hξ hξb hgap Ω _ P W H hH n => ?_⟩
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := htail hH.whiteNoise ha hab (hH.band n) 0
  rw [log_one_div_inv_two_pow, mul_one] at h
  refine (measure_mono fun ω hω => ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · have hω' : ω ∉ {ω | ∀ z ∈ cbox (0 : Rd d) 3,
        H n z ω ≤ n * (√(2 * d) + (μ - η) / b) * Real.log 2} :=
      fun h' => hω (eventG_supset hξ hξb hημ hgap H n h')
    simp only [mem_ofPred_eq, not_forall, not_le, exists_prop] at hω'
    obtain ⟨z, hz, hlt⟩ := hω'
    refine ⟨z, hz, ?_⟩
    have e : (√(2 * d) + (μ - η) / b) * ((n : ℝ) * Real.log 2) =
        n * (√(2 * d) + (μ - η) / b) * Real.log 2 := by ring
    rw [e]
    exact hlt.trans_le (le_abs_self _)
  · have e : -((n : ℝ) * Real.log 2) / C = -(n : ℝ) / (C / Real.log 2) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [le_div_iff₀ hlog2]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith

/-! ### `ℰ_{m,n}` -/

/-- **The `ℰ`-bound with the `𝒢`-constant made explicit** (the proof of `DGZ.prob_E_compl_le`): there is
`c₄ = c₄(d, κ) < 1`, and for every `CG > 0` there is `C = C(d, κ, CG) > 0`, such that at every `(ξ, Q, η)` with
`ξ > 0` whose `𝒢`-bound holds with the constant `CG`, `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `q ∈ (c₄, 1)`, every dyadic
realization and all `m < n`. -/
theorem u1_prob_E_compl_le_of_G {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ CG : ℝ, 0 < CG → ∃ C > 0, ∀ ξ Q η : ℝ, 0 < ξ →
      (∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ n : ℕ,
          P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (CG * Real.exp (-(n : ℝ) / CG))) →
      ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, m < n →
          P (eventE P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  set r : ℕ := ⌈2 * (2 + ρ)⌉₊ with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ with hθ
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  obtain ⟨c₄, hc₄1, hc₄⟩ := exists_c4 hθ0 hθ1 (2 * d)
  refine ⟨c₄, hc₄1, fun CG hCG => ?_⟩
  obtain ⟨M₀, hM₀⟩ := exists_peierls_tail d 1 (2 * 101 ^ 2 + 2)
  set C : ℝ := max (CG + 1) ((M₀ : ℝ) + 1) with hC
  have hCG1 : CG + 1 ≤ C := le_max_left _ _
  have hCM : (M₀ : ℝ) + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun ξ Q η hξ hG q hq₁ hq₂ Ω _ P W H hH m n hmn => ?_⟩
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
  set B : Set Ω := {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧
    (∃ z ∈ C, WithinInf ((2 ^ (m + 1) : ℕ) : ℤ) z 0) ∧
      ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf ((m ^ 2 - 101 ^ 2 : ℕ) : ℤ) y y'} with hB
  have hPB' : P B ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
    (Perc.diameterBound d P closed r _ θ hcl hPB (HigherDimLFPP.L33.theta_le_one d) hεθ
      (HigherDimLFPP.L33.three_pow_mul_theta_le d) 0 (2 ^ (m + 1)) (m ^ 2 - 101 ^ 2)).trans
      (hM₀ m _ hm (by omega))
  set N0 : Set Ω := {ω | ¬ ∀ z, H n z ω = H m z ω + G z ω} with hN0
  have hPN0 : P N0 = 0 := ae_iff.1 hsum
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

/-- **Uniform DGZ Lemma 4.2(1), second bound** (`d:lem-u42`; port of `DGZ.prob_E_compl_le`): there is
`c₄ = c₄(d, κ) < 1`, and for all `b, μ, η` with `η < μ` there is `C > 0`, such that for all `0 < ξ ≤ b` and `Q` with
`μ ≤ ξ (Q - √(2d))`, all `q ∈ (c₄, 1)`, every dyadic realization and all `m < n`, `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}`. -/
theorem prob_E_compl_le_unif {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ b μ η : ℝ, η < μ → ∃ C > 0, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b →
      μ ≤ ξ * (Q - √(2 * d)) → ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, m < n →
          P (eventE P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨c₄, hc₄, hE⟩ := u1_prob_E_compl_le_of_G hκ
  refine ⟨c₄, hc₄, fun b μ η hημ => ?_⟩
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le_unif (d := d) hκ (b := b) hημ
  obtain ⟨C, hC, h⟩ := hE CG hCG
  exact ⟨C, hC, fun ξ Q hξ hξb hgap => h ξ Q η hξ fun hH n => hG ξ Q hξ hξb hgap hH n⟩

/-! ### `ℱ_{m,n}` -/

/-- **The `ℱ`-bound with the `𝒢`-constant made explicit** (the proof of `DGZ.prob_F_compl_le`; `d ≥ 2`): there is
`c₄ = c₄(d, κ) < 1`, and for every `CG > 0` there is `C = C(d, κ, CG) > 0`, such that at every `(ξ, Q, η)` with
`ξ > 0` whose `𝒢`-bound holds with the constant `CG`, `P[ℱ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `q ∈ (c₄, 1)`, every dyadic
realization and all `1 ≤ m < n`. -/
theorem u1_prob_F_compl_le_of_G (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ CG : ℝ, 0 < CG → ∃ C > 0, ∀ ξ Q η : ℝ, 0 < ξ →
      (∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ n : ℕ,
          P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (CG * Real.exp (-(n : ℝ) / CG))) →
      ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, 1 ≤ m → m < n →
          P (eventF P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨cE, hcE1, hEof⟩ := u1_prob_E_compl_le_of_G hκ
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  set r : ℕ := ⌈2 * (2 + ρ)⌉₊ with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ with hθ
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  obtain ⟨cN, hcN1, hcN⟩ := exists_c4 hθ0 hθ1 ((1 + 3 ^ d) * (2 * d))
  refine ⟨max cE cN, max_lt hcE1 hcN1, fun CG hCG => ?_⟩
  obtain ⟨CE, hCE, hE⟩ := hEof CG hCG
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
  refine ⟨C, hC0, fun ξ Q η hξ hG q hq₁ hq₂ Ω _ P W H hH m n hm1 hmn => ?_⟩
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
  set N₁ : Set Ω := {ω | ¬ ∀ z, H n z ω = H (m - 1) z ω + G₁ z ω} with hN₁
  set N₂ : Set Ω := {ω | ¬ ∀ z, H n z ω = H m z ω + G₂ z ω} with hN₂
  have hPN₁ : P N₁ = 0 := ae_iff.1 hsum₁
  have hPN₂ : P N₂ = 0 := ae_iff.1 hsum₂
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
  have hPE := hE ξ Q η hξ hG q hqE hq₂ hH m n hmn
  have hPE1 := hE ξ Q η hξ hG q hqE hq₂ hH (m - 1) n (by omega)
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

/-- **Uniform DGZ Lemma 4.2(1), third bound** (`d:lem-u42`; port of `DGZ.prob_F_compl_le`, free-site form of
`ℱ_{m,n}`; `d ≥ 2`): there is `c₄ = c₄(d, κ) < 1`, and for all `b, μ, η` with `η < μ` there is `C > 0`, such that for
all `0 < ξ ≤ b` and `Q` with `μ ≤ ξ (Q - √(2d))`, all `q ∈ (c₄, 1)`, every dyadic realization and all `1 ≤ m < n`,
`P[ℱ_{m,n}ᶜ] ≤ C e^{-m/C}`. -/
theorem prob_F_compl_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ b μ η : ℝ, η < μ → ∃ C > 0, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b →
      μ ≤ ξ * (Q - √(2 * d)) → ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ m n : ℕ, 1 ≤ m → m < n →
          P (eventF P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C)) := by
  obtain ⟨c₄, hc₄, hF⟩ := u1_prob_F_compl_le_of_G hd hκ
  refine ⟨c₄, hc₄, fun b μ η hημ => ?_⟩
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le_unif (d := d) hκ (b := b) hημ
  obtain ⟨C, hC, h⟩ := hF CG hCG
  exact ⟨C, hC, fun ξ Q hξ hξb hgap => h ξ Q η hξ fun hH n => hG ξ Q hξ hξb hgap hH n⟩

/-- **Uniform DGZ Lemma 4.2(1)** (`d:lem-u42`; port of `DGZ.lemma42_1`; `d ≥ 2`): there is `c₄ = c₄(d, κ) < 1`, and
for all `b, μ, η` with `η < μ` there is `C > 0`, such that for all `0 < ξ ≤ b` and `Q` with `μ ≤ ξ (Q - √(2d))`,
all `q ∈ (c₄, 1)` and every dyadic realization: `P[𝒢_nᶜ] ≤ C e^{-n/C}` for all `n`, `P[ℰ_{m,n}ᶜ] ≤ C e^{-m/C}` for
all `m < n`, and `P[ℱ_{m,n}ᶜ] ≤ C e^{-m/C}` for all `1 ≤ m < n`. -/
theorem lemma42_1_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ b μ η : ℝ, η < μ → ∃ C > 0, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b →
      μ ≤ ξ * (Q - √(2 * d)) → ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H →
          (∀ n : ℕ, P (eventG ξ Q η H n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C))) ∧
          (∀ m n : ℕ, m < n →
            P (eventE P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C))) ∧
          (∀ m n : ℕ, 1 ≤ m → m < n →
            P (eventF P H ξ Q η q m n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(m : ℝ) / C))) := by
  obtain ⟨cE, hcE1, hE⟩ := prob_E_compl_le_unif (d := d) hκ
  obtain ⟨cF, hcF1, hF⟩ := prob_F_compl_le_unif hd hκ
  refine ⟨max cE cF, max_lt hcE1 hcF1, fun b μ η hημ => ?_⟩
  obtain ⟨CG, hCG, hG⟩ := prob_G_compl_le_unif (d := d) hκ (b := b) hημ
  obtain ⟨CE, hCE, hE'⟩ := hE b μ η hημ
  obtain ⟨CF, hCF, hF'⟩ := hF b μ η hημ
  set C : ℝ := max (max CG CE) CF with hC
  have hCG' : CG ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCE' : CE ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCF' : CF ≤ C := le_max_right _ _
  refine ⟨C, lt_of_lt_of_le hCG hCG', fun ξ Q hξ hξb hgap q hq₁ hq₂ Ω _ P W H hH =>
    ⟨fun n => ?_, fun m n hmn => ?_, fun m n hm hmn => ?_⟩⟩
  · exact (hG ξ Q hξ hξb hgap hH n).trans (ENNReal.ofReal_le_ofReal
      (mul_exp_neg_div_le_of_le hCG.le hCG' hCG hCG' (Nat.cast_nonneg n)))
  · exact (hE' ξ Q hξ hξb hgap q (lt_of_le_of_lt (le_max_left _ _) hq₁) hq₂ hH m n hmn).trans
      (ENNReal.ofReal_le_ofReal (mul_exp_neg_div_le_of_le hCE.le hCE' hCE hCE' (Nat.cast_nonneg m)))
  · exact (hF' ξ Q hξ hξb hgap q (lt_of_le_of_lt (le_max_right _ _) hq₁) hq₂ hH m n hm hmn).trans
      (ENNReal.ofReal_le_ofReal (mul_exp_neg_div_le_of_le hCF.le hCF' hCF hCF' (Nat.cast_nonneg m)))

/-! ### `𝒜_{r,n}` -/

/-- **Uniform `P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C}`** (port of `DGZ.prob_eventA_compl_le`; Lemma 4.2(1) and a union bound over
`r ≤ k < n`; `d ≥ 2`): there is `c₄ = c₄(d, κ) < 1`, and for all `b, μ, η` with `η < μ` there is `C > 0`, such that
for all `0 < ξ ≤ b` and `Q` with `μ ≤ ξ (Q - √(2d))`, all `q ∈ (c₄, 1)`, every dyadic realization and all
`1 ≤ r < n`, `P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C}`. -/
theorem prob_eventA_compl_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ c₄ : ℝ≥0∞, c₄ < 1 ∧ ∀ b μ η : ℝ, η < μ → ∃ C > 0, ∀ ξ Q : ℝ, 0 < ξ → ξ ≤ b →
      μ ≤ ξ * (Q - √(2 * d)) → ∀ q : ℝ≥0∞, c₄ < q → q < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ r n : ℕ, 1 ≤ r → r < n →
          P (eventA P H ξ Q η q r n)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(r : ℝ) / C)) := by
  obtain ⟨c₄, hc₄, h42⟩ := lemma42_1_unif hd hκ
  refine ⟨c₄, hc₄, fun b μ η hημ => ?_⟩
  obtain ⟨C₁, hC₁, hb⟩ := h42 b μ η hημ
  set x : ℝ := Real.exp (-1 / C₁) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.2 (by rw [neg_div]; linarith [one_div_pos.2 hC₁])
  set C : ℝ := C₁ * (1 + 1 / (1 - x)) with hC
  have h1x : 0 < 1 - x := by linarith
  have hCC₁ : C₁ ≤ C := by
    rw [hC]
    have : 0 ≤ 1 / (1 - x) := by positivity
    nlinarith
  refine ⟨C, by positivity, fun ξ Q hξ hξb hgap q hq hq1 Ω _ P W H hH r n hr hrn => ?_⟩
  obtain ⟨hG, -, hF⟩ := hb ξ Q hξ hξb hgap q hq hq1 hH
  have hsub : (eventA P H ξ Q η q r n)ᶜ ⊆
      (eventG ξ Q η H n)ᶜ ∪ ⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ := by
    intro ω hω
    rw [mem_compl_iff, mem_eventA_iff] at hω
    by_cases hg : ω ∈ eventG ξ Q η H n
    · right
      have : ¬ ∀ k, r ≤ k → k < n → ω ∈ eventF P H ξ Q η q k n := fun h' => hω ⟨hg, h'⟩
      push Not at this
      obtain ⟨k, hk1, hk2, hk3⟩ := this
      exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨hk1, hk2⟩)) hk3
    · left
      exact hg
  have hexp_k : ∀ k : ℕ, Real.exp (-(k : ℝ) / C₁) = x ^ k := by
    intro k
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    ring
  have hreal : C₁ * x ^ n + ∑ k ∈ Finset.Ico r n, C₁ * x ^ k ≤ C * Real.exp (-(r : ℝ) / C) := by
    have h1 : x ^ n ≤ x ^ r := pow_le_pow_of_le_one hx0.le hx1.le hrn.le
    have h2 := geom_sum_Ico_le_of_lt_one (m := r) (n := n) hx0.le hx1
    have h3 : x ^ r ≤ Real.exp (-(r : ℝ) / C) := by
      rw [← hexp_k]
      refine Real.exp_le_exp.2 ?_
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      rw [div_le_div_iff₀ hC₁ (by positivity)]
      nlinarith
    rw [← Finset.mul_sum]
    calc C₁ * x ^ n + C₁ * ∑ k ∈ Finset.Ico r n, x ^ k
        ≤ C₁ * x ^ r + C₁ * (x ^ r / (1 - x)) := by gcongr
      _ = C * x ^ r := by rw [hC]; field_simp
      _ ≤ C * Real.exp (-(r : ℝ) / C) := by gcongr
  calc P (eventA P H ξ Q η q r n)ᶜ
      ≤ P ((eventG ξ Q η H n)ᶜ ∪ ⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ) :=
        measure_mono hsub
    _ ≤ P (eventG ξ Q η H n)ᶜ + P (⋃ k ∈ Finset.Ico r n, (eventF P H ξ Q η q k n)ᶜ) :=
        measure_union_le _ _
    _ ≤ P (eventG ξ Q η H n)ᶜ + ∑ k ∈ Finset.Ico r n, P (eventF P H ξ Q η q k n)ᶜ :=
        add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(n : ℝ) / C₁)) +
          ∑ k ∈ Finset.Ico r n, ENNReal.ofReal (C₁ * Real.exp (-(k : ℝ) / C₁)) := by
        refine add_le_add (hG n) (Finset.sum_le_sum fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        exact hF k n (by omega) hk.2
    _ = ENNReal.ofReal (C₁ * x ^ n + ∑ k ∈ Finset.Ico r n, C₁ * x ^ k) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun k _ => by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), hexp_k]
        simp only [hexp_k]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(r : ℝ) / C)) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
