import HigherDimLQGContinuity.Unif4.Sec42
import HigherDimLQGContinuity.Unif4.Lemma36
import HigherDimLQGMetric.DGZ.CompareShell

/-!
# Uniform DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)` (packet U3)

Blueprint Part D, `d:lem-u514` (NA3 R5, §2.15 row 16; [8]-bp `r2:lem:514`). Port of
`HigherDimLQGMetric.DGZ.prob_not_lemma514Good_le` and `DGZ.lemma514` (`DGZ/CompareShell.lean`, MA7 D-5.14).

**The form used** (`DGZ.Lemma514Good`, reused verbatim). Fix `λ' ∈ (0, 1)`, put `σ_n = 2^{-⌊λ'n⌋}` and
`τ_n = 2^{-(1-ϕ(ξ)+u)n}`, `ϕ(ξ) = ξQ(ξ)`. The good event: (i) `D_n(0, a; B₂(0)) ≤ τ_n` for `a ∈ B̄_{σ_n}(0)` and
`D_n(b, e₁; B₂(0)) ≤ τ_n` for `b ∈ B̄_{σ_n}(e₁)`; (ii) `6τ_n ≤ D_n(0, e₁; B₂(0))`.

* `prob_not_lemma514Good_le_unif`: there are `u = u(μ, λ') > 0` and `C = C(d, κ, b, μ, λ') > 0` such that for every
  `ξ ∈ S(b, μ)`, every dyadic realization and every `n`, the good event fails with probability `≤ C e^{-n/C}`.
* `lemma514_unif` (**target**, the set-distance form of [1]): for `0 < σ ≤ σ_n`, `σ ≤ 1/2`,
  `P[D_n(0, e₁; B₂(0)) > 3 D_n(B̄_σ(0), B̄_σ(e₁); B₂(0))] ≤ C e^{-n/C}`, uniformly in `ξ ∈ S(b, μ)`.

**Proof** (the sealed proof, with the changes of NA3 R5):
* the margin of `𝒜_{r,n}` is `η = uEta μ = μ/2` (instead of `ξ(Q - √(2d))/2`); it satisfies `η < μ ≤ ξ(Q(ξ) - √(2d))`
  on `S(b, μ)`, and U1's `prob_eventA_compl_le_unif` bounds `P[𝒜_{r,n}ᶜ] ≤ C₁ e^{-r/C₁}` with `C₁` before `ξ`;
* `ε' = ηλ'/8`, `u = ηλ'/4`; the quantile bound `a^{(q)}_N ≤ A 2^{-(1-ϕ-ε')N}` (all `N`) is U1's
  `exists_aQ_le_unif` (from U-EXP);
* the numerics of the chaining sum do not involve `ϕ` (both sides carry the factor `2^{ϕ n}`), so their threshold `n₀`
  is taken at `ϕ = 0` and transferred (`u3_chain_le_of_zero`);
* (ii) uses U1's `lemma36_lower_unif` with `δ = u/2` (as the sealed proof uses the fixed-ξ Lemma 3.6; this replaces
  the blueprint's separating-shell argument of step (ii), which needs the field decomposition `h_n = h_l + h_{l,n}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The numerics of D-5.14 (i), uniformly in `ϕ` -/

/-- The chaining numerics do not depend on `ϕ = ξQ`: both sides of
`K n^{2d} y^r 2^{-(1-ϕ-ε')n} ≤ 2^{-(1-ϕ+u)n}` carry the factor `2^{ϕn}`. -/
theorem u3_chain_le_of_zero {K y ε' u : ℝ} {n r : ℕ}
    (h : K * (n : ℝ) ^ (2 * d) * y ^ r * (2 : ℝ) ^ (-(1 - 0 * 0 - ε') * n) ≤
      (2 : ℝ) ^ (-(1 - 0 * 0 + u) * n)) (φ : ℝ) :
    K * (n : ℝ) ^ (2 * d) * y ^ r * (2 : ℝ) ^ (-(1 - φ - ε') * n) ≤
      (2 : ℝ) ^ (-(1 - φ + u) * n) := by
  have e1 : (2 : ℝ) ^ (-(1 - φ - ε') * n) =
      (2 : ℝ) ^ (φ * n) * (2 : ℝ) ^ (-(1 - 0 * 0 - ε') * n) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  have e2 : (2 : ℝ) ^ (-(1 - φ + u) * n) =
      (2 : ℝ) ^ (φ * n) * (2 : ℝ) ^ (-(1 - 0 * 0 + u) * n) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  have hpos : 0 ≤ (2 : ℝ) ^ (φ * n) := (Real.rpow_pos_of_pos two_pos _).le
  rw [e1, e2]
  calc K * (n : ℝ) ^ (2 * d) * y ^ r * ((2 : ℝ) ^ (φ * n) * (2 : ℝ) ^ (-(1 - 0 * 0 - ε') * n))
      = (2 : ℝ) ^ (φ * n) * (K * (n : ℝ) ^ (2 * d) * y ^ r *
          (2 : ℝ) ^ (-(1 - 0 * 0 - ε') * n)) := by ring
    _ ≤ (2 : ℝ) ^ (φ * n) * (2 : ℝ) ^ (-(1 - 0 * 0 + u) * n) :=
        mul_le_mul_of_nonneg_left h hpos

/-! ## The good event of Lemma 5.14, uniformly -/

/-- **Uniform DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)`, form used** (port of
`DGZ.prob_not_lemma514Good_le`; `d:lem-u514`, NA3 R5): for `d ≥ 2`, `κ` admissible, `b, μ > 0` and `λ' ∈ (0, 1)`
there are `u > 0` and `C > 0` (depending only on `d, κ, b, μ, λ'`) such that for every `ξ ∈ S(b, μ)`, every dyadic
realization and every `n`, the good event `Lemma514Good ξ Q(ξ) u λ' h_n n` fails with probability `≤ C e^{-n/C}`. -/
theorem prob_not_lemma514Good_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {lam' : ℝ} (hlam' : 0 < lam') (hlam1 : lam' < 1) :
    ∃ u > 0, ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | ¬ Lemma514Good ξ (distExp d ξ) u lam' (fun z => H n z ω) n} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  set η : ℝ := uEta μ with hηdef
  have hη : 0 < η := uEta_pos hμ
  have hημ : η < μ := uEta_lt hμ
  obtain ⟨c₄, hc₄, hA42⟩ := prob_eventA_compl_le_unif hd hκ
  obtain ⟨C₁, hC₁, hAc⟩ := hA42 b μ η hημ
  obtain ⟨q, hc₄q, hq1⟩ := exists_between hc₄
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hc₄q
  set ε' : ℝ := η * lam' / 8 with hε'def
  set u : ℝ := η * lam' / 4 with hudef
  have hε' : 0 < ε' := by positivity
  have hu : 0 < u := by positivity
  obtain ⟨A, hA0, haQ⟩ := exists_aQ_le_unif.{0} hd hκ hb hq0 hq1 hε'
  obtain ⟨C₀, hC₀, hdiam⟩ := cmp_diam_le hd
  obtain ⟨C₂, hC₂, h36⟩ := lemma36_lower_unif.{0} hd hκ hb (δ := u / 2) (by positivity)
  have hηε : 0 < η + ε' := by positivity
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-(η + ε')) := by
    have : (2 : ℝ) ^ (-(η + ε')) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  set K : ℝ := C₀ * ((A + 1) / (1 - (2 : ℝ) ^ (-(η + ε')))) with hKdef
  have hK : 0 ≤ K := mul_nonneg hC₀.le (div_nonneg (by linarith) hgeo.le)
  -- the numerics, eventually in `n`, at `ϕ = 0` (uniform in `ξ` by `u3_chain_le_of_zero`)
  have hmargin : u + ε' + η * lam' / 2 ≤ (η + ε') * lam' := by
    have : 0 ≤ ε' * lam' := mul_nonneg hε'.le hlam'.le
    nlinarith
  have hev1 := cmp_eventually_chain_le 0 0 hK hηε (by positivity : 0 < η * lam' / 2) hmargin d
  have hev2 : ∀ᶠ n : ℕ in atTop, 110 ≤ ⌊lam' * n⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      hlam')).eventually_ge_atTop 110
  have hev3 : ∀ᶠ n : ℕ in atTop, (6 : ℝ) / u ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hev1.and (hev2.and (hev3.and hev4)))
  -- the constants
  set C₃ : ℝ := max (C₁ * Real.exp (1 / C₁)) (C₁ / lam') with hC₃def
  have hC₃ : 0 < C₃ := lt_of_lt_of_le (mul_pos hC₁ (Real.exp_pos _)) (le_max_left _ _)
  obtain ⟨C, hC, hsmall, hbig⟩ := cmp_exists_exp_const (add_pos hC₃ hC₂) n₀
  refine ⟨u, hu, C, hC, fun ξ hU Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hU.base.xi_pos
  have hξb : ξ ≤ b := hU.le_b
  set Q : ℝ := distExp d ξ with hQdef
  have hPprob := hH.whiteNoise.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (hsmall n hn))
  obtain ⟨hnum0, hr110, hn6, hn1⟩ := hn₀ n hn
  have hnum := u3_chain_le_of_zero hnum0 (ξ * Q)
  set r : ℕ := ⌊lam' * n⌋₊ with hrdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrn : r < n := by
    have h1 : (r : ℝ) ≤ lam' * n := Nat.floor_le (by positivity)
    have h2 : lam' * (n : ℝ) < n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    exact_mod_cast h1.trans_lt h2
  set τ : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) with hτdef
  -- the chain bound gives (i) on `𝒜_{r,n}`
  have hchain : C₀ * chainSum P H ξ Q η q r n ≤ τ := by
    have h1 := chainSum_le_tail (P := P) (H := H) (ξ := ξ) (Q := Q) (η := η) (ε := ε') hηε
      (q := q) hA0.le (haQ ξ hξ hξb Ω P W H hH) (j := r) (n := n) hrn.le
    calc C₀ * chainSum P H ξ Q η q r n ≤ C₀ * ((A + 1) / (1 - (2 : ℝ) ^ (-(η + ε'))) *
          (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ r * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n)) :=
          mul_le_mul_of_nonneg_left h1 hC₀.le
      _ = K * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ r *
          (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n) := by
          rw [hKdef]
          ring
      _ ≤ τ := hnum
  -- `6 τ ≤ 2^{-(1-ξQ+u/2)n}`
  have h6 : 6 * τ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n) := by
    have e : (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n) = (2 : ℝ) ^ (u / 2 * n) * τ := by
      rw [hτdef, ← Real.rpow_add two_pos]
      ring_nf
    have h8 : (6 : ℝ) ≤ (2 : ℝ) ^ (u / 2 * n) := by
      have h3 : (3 : ℝ) ≤ u / 2 * n := by
        rw [div_le_iff₀ hu] at hn6
        nlinarith
      calc (6 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (u / 2 * n) := Real.rpow_le_rpow_of_exponent_le one_le_two h3
    rw [e]
    exact mul_le_mul_of_nonneg_right h8 (Real.rpow_pos_of_pos two_pos _).le
  -- the bad event is covered by `𝒜ᶜ` and the lower tail of `D_n(0, e₁; B₃(0))`
  have hsub : {ω | ¬ Lemma514Good ξ Q u lam' (fun z => H n z ω) n} ⊆
      (eventA P H ξ Q η q r n)ᶜ ∪ {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3) 0
        (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_lt] at hcon
    obtain ⟨hAω, hDω⟩ := hcon
    apply hω
    have hc := (hH.band n).continuous ω
    obtain ⟨hd0, hde⟩ := hdiam P H ξ Q η q r n ω hξ hr110 hrn hc hAω
    refine ⟨fun a ha => (hd0 a ha).trans hchain, fun b hb => (hde b hb).trans hchain, ?_⟩
    have hmono : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3) 0 (e₁ d) ≤
        lfppDistance d ξ (fun z => H n z ω) := by
      rw [cmp_lfppDistance_eq_obox]
      exact lfppDistOn_mono (fun z hz i => (hz i).trans (by norm_num))
        (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2) cmp_zero_mem_obox_two
          cmp_e₁_mem_obox_two)
    linarith
  have h0mem : (0 : Rd d) ∈ cbox (0 : Rd d) 2 := fun i => by
    show |(0 : Rd d).ofLp i - (0 : Rd d).ofLp i| ≤ 2
    rw [sub_self, abs_zero]
    norm_num
  have he₁mem : e₁ d ∈ cbox (0 : Rd d) 2 := fun i => by
    show |(e₁ d).ofLp i - (0 : Rd d).ofLp i| ≤ 2
    rw [PiLp.zero_apply, sub_zero, e₁_ofLp]
    split_ifs <;> norm_num
  have hfar : ∃ i, (1 : ℝ) / 2 ≤ |(0 : Rd d).ofLp i - (e₁ d).ofLp i| := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [PiLp.zero_apply, e₁_ofLp]
    norm_num
  -- the first term: `C₁ e^{-r/C₁} ≤ C₃ e^{-n/C₃}`
  have hterm1 : C₁ * Real.exp (-(r : ℝ) / C₁) ≤ C₃ * Real.exp (-(n : ℝ) / C₃) := by
    have hr' : lam' * n - 1 ≤ r := by
      have := Nat.lt_floor_add_one (lam' * n)
      linarith
    have e1 : C₁ * Real.exp (-(r : ℝ) / C₁) ≤
        C₁ * Real.exp (1 / C₁) * Real.exp (-(n : ℝ) / (C₁ / lam')) := by
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      have key : -(r : ℝ) / C₁ ≤ (1 - lam' * n) / C₁ :=
        div_le_div_of_nonneg_right (by linarith) hC₁.le
      have e : 1 / C₁ + -(n : ℝ) / (C₁ / lam') = (1 - lam' * n) / C₁ := by
        field_simp
        ring
      rw [e]
      exact key
    refine e1.trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le hC₃.le)
    exact cmp_exp_neg_div_mono (div_pos hC₁ hlam') (le_max_right _ _) n
  calc P {ω | ¬ Lemma514Good ξ Q u lam' (fun z => H n z ω) n}
      ≤ P ((eventA P H ξ Q η q r n)ᶜ ∪ {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3)
          0 (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)}) := measure_mono hsub
    _ ≤ P (eventA P H ξ Q η q r n)ᶜ + P {ω | lfppDistOn ξ (fun z => H n z ω)
          (obox (0 : Rd d) 3) 0 (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(r : ℝ) / C₁)) +
          ENNReal.ofReal (C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        add_le_add (hAc ξ Q hξ hξb hU.gap q hc₄q hq1 hH r n (by omega) hrn)
          (h36 ξ hξ hξb Ω P W H hH 0 (e₁ d) h0mem he₁mem hfar n)
    _ ≤ ENNReal.ofReal (C₃ * Real.exp (-(n : ℝ) / C₃)) +
          ENNReal.ofReal (C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hterm1) le_rfl
    _ = ENNReal.ofReal (C₃ * Real.exp (-(n : ℝ) / C₃) + C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) :=
        ENNReal.ofReal_le_ofReal ((cmp_add_exp_le hC₃ hC₂ n).trans (hbig n))

/-- **Uniform DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)`**, the set-distance form of [1] (port of
`DGZ.lemma514`; `d:lem-u514`): for `d ≥ 2`, `κ` admissible, `b, μ > 0` and `λ' ∈ (0, 1)` there is `C > 0` (depending
only on `d, κ, b, μ, λ'`) such that for every `ξ ∈ S(b, μ)`, every dyadic realization, every `n` and every
`0 < σ ≤ min(1/2, 2^{-⌊λ'n⌋})`: `P[D_n(0, e₁; B₂(0)) > 3 D_n(B̄_σ(0), B̄_σ(e₁); B₂(0))] ≤ C e^{-n/C}`. -/
theorem lemma514_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {lam' : ℝ} (hlam' : 0 < lam') (hlam1 : lam' < 1) :
    ∃ C > 0, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ (n : ℕ) (σ : ℝ), 0 < σ →
          σ ≤ 1 / 2 → σ ≤ (2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊ →
          P {ω | 3 * lfppSetDist ξ (fun z => H n z ω) (obox (0 : Rd d) 2) (cbox 0 σ)
            (cbox (e₁ d) σ) < lfppDistance d ξ (fun z => H n z ω)} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨u, hu, C, hC, hP⟩ := prob_not_lemma514Good_le_unif hd hκ hb hμ hlam' hlam1
  refine ⟨C, hC, fun ξ hU Ω _ P W H hH n σ hσ hσ2 hσn =>
    le_trans (measure_mono ?_) (hP ξ hU Ω P W H hH n)⟩
  intro ω hω hG
  simp only [mem_ofPred_eq] at hω
  obtain ⟨hd0, hd1, h6⟩ := hG
  have hφ := (hH.band n).continuous ω
  have hσ12 : σ < 2 := by linarith
  have hτ : 0 < (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + u) * n) := Real.rpow_pos_of_pos two_pos _
  have hA : ∀ a ∈ cbox (0 : Rd d) σ, a ∈ obox (0 : Rd d) 2 := fun a ha i =>
    lt_of_le_of_lt (ha i) hσ12
  have hB : ∀ b ∈ cbox (e₁ d) σ, b ∈ obox (0 : Rd d) 2 := fun b hb i => by
    have h1 := hb i
    show |b.ofLp i - (0 : Rd d).ofLp i| < 2
    rw [PiLp.zero_apply, sub_zero]
    have h3 : |(e₁ d).ofLp i| ≤ 1 := by
      rw [e₁_ofLp]
      split_ifs <;> norm_num
    calc |b.ofLp i| = |(b.ofLp i - (e₁ d).ofLp i) + (e₁ d).ofLp i| := by ring_nf
      _ ≤ |b.ofLp i - (e₁ d).ofLp i| + |(e₁ d).ofLp i| := abs_add_le _ _
      _ < 2 := by
        have : |b.ofLp i - (e₁ d).ofLp i| ≤ σ := h1
        linarith
  have hsub0 : cbox (0 : Rd d) σ ⊆ cbox (0 : Rd d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊) :=
    fun a ha i => (ha i).trans hσn
  have hsub1 : cbox (e₁ d) σ ⊆ cbox (e₁ d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊) :=
    fun a ha i => (ha i).trans hσn
  have hne0 : (cbox (0 : Rd d) σ).Nonempty := ⟨0, fun i => by
    show |(0 : Rd d).ofLp i - (0 : Rd d).ofLp i| ≤ σ
    rw [sub_self, abs_zero]
    exact hσ.le⟩
  have hne1 : (cbox (e₁ d) σ).Nonempty := ⟨e₁ d, fun i => by
    show |(e₁ d).ofLp i - (e₁ d).ofLp i| ≤ σ
    rw [sub_self, abs_zero]
    exact hσ.le⟩
  have key : 2 / 3 * lfppDistance d ξ (fun z => H n z ω) ≤
      lfppSetDist ξ (fun z => H n z ω) (obox (0 : Rd d) 2) (cbox 0 σ) (cbox (e₁ d) σ) := by
    refine le_lfppSetDist hne0 hne1 fun a ha b hb => ?_
    have htri := cmp_lfppDistance_le_add_three (ξ := ξ) hφ (hA a ha) (hB b hb)
    have := hd0 a (hsub0 ha)
    have := hd1 b (hsub1 hb)
    linarith
  linarith

end HigherDimLQGContinuity
