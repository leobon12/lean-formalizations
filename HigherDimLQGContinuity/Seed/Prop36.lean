import HigherDimLQGContinuity.Seed.Ceiling

/-!
# Proposition 3.6: a seed at fixed confidence (packet P8b)

Blueprint Part A, Proposition `a:prop36` ([C] Prop. 3.6, p. 9–10, l. 454–483; NA1 item 28, R11; NA0 §2.3; erratum
EA `a:err-36`).

**Statement** (`prop36`). Let `d ≥ 2`, assume Lemma 2.1 (`UniformEstimates d ξ̄ s`, interface I1) for all pins
`s ∈ [1, 10]` and Proposition 3.5 (`Prop35Shape d ξ̄`, interface I15). There is `R_s ≥ 1` such that for every
`p_s > 0` there are `B, C₆ > 0` with: for all `a ∈ (0, ξ̄]`, `ξ, η ∈ [a, ξ̄]`, `D, E` strong and `u ∈ (0, 1)`,
`|ξ − η| ≤ exp(-C₆ a^{-B} u^{-B})` implies `𝐏₁₀{g : supd_{R_s}(ρ^D_g, ρ^E_g) > u} ≤ p_s`.

**Proof** (blueprint, NA1 R11). Fixed data: `C_b` of Lemma 3.2 (`4 < C_b`); `(C₃₂, c₃₂)` of Lemma 3.2 at pin `10`;
`p₀` of Proposition 3.3; references `𝓡` at pin `10` with failure `p₀/2`; `(M₃, C₃, c₃)` of Proposition 3.3 for
`C_b`, `𝓡`, `s₁ = s₂ = 10`; Proposition 3.5 with `C_b` and `p_t = p₀/2`: `R_s, q₀, 𝒫, v₀`. Given `p_s`:
`q₀' = min(q₀, p_s/8, 1/16)`; `M_s` (the diameter quantile, failure `p_s/4`); the ceiling `B, C₆` (`p8b_ceiling`).
Given `a, ξ, η, u`: `v = min(v₀/2, u/(160 M_s))`, `(g, ε∗, t∗)` from Proposition 3.5, `ε' = min(ε∗, u/16)`, depths
`n₀ = p8bN0`, `n_g = p8bNg`. Start: Lemma 3.2. Step (`c ∈ [1 + 20v, C_b]`): Proposition 3.5 (premise with the larger
error `ε∗`, by monotonicity) gives `𝐏₁₀(H↑(D, E; c − g)) ≤ p₀/2`; with the references the local bad event has
probability `≤ p₀`; Proposition 3.3 with `b = c − g`, slack `g/2`, error `ε'`, radius `R_s`, depth `n_g` gives the
comparison at `c − g/2` with failure `≤ q₀'`. Iteration (`p8b_iterate`): each step is an implication between two
probability bounds, no exceptional events are intersected across steps; the coefficient reaches `1 + 20v`. The same
for `(E, D)`. On the two final comparison events and the two diameter events (failure `≤ 2q₀' + p_s/2 ≤ p_s`):
`|ρ^E − ρ^D| ≤ 20 v M_s + ε' ≤ 3u/16 < u` on `B̄_{R_s}²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The iteration -/

/-- **The downward iteration of Proposition 3.6** (blueprint `a:prop36`, "Iteration"; NA1 R11), at the level of
probability bounds: if the bad events `P c` shrink as `c` grows, `μ(P C_b) ≤ q`, and each step from a coefficient
`c ∈ [lo, C_b]` with `μ(P c) ≤ q` gives `μ(P (c − g)) ≤ q`, then `μ(P lo) ≤ q`. -/
theorem p8b_iterate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : ℝ → Set Ω} {gs lo Cb : ℝ}
    {q : ℝ≥0∞} (hgs : 0 < gs) (hlo : lo ≤ Cb) (hmono : ∀ c c' : ℝ, c ≤ c' → P c' ⊆ P c)
    (hstart : μ (P Cb) ≤ q) (hstep : ∀ c : ℝ, lo ≤ c → c ≤ Cb → μ (P c) ≤ q → μ (P (c - gs)) ≤ q) :
    μ (P lo) ≤ q := by
  have key : ∀ k : ℕ, μ (P (max (Cb - k * gs) lo)) ≤ q := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, sub_zero, max_eq_left hlo]
      exact hstart
    | succ k ih =>
      rcases le_or_gt lo (Cb - k * gs) with h | h
      · rw [max_eq_left h] at ih
        have hk : 0 ≤ (k : ℝ) * gs := by positivity
        have h1 := hstep (Cb - k * gs) h (by linarith) ih
        refine le_trans (measure_mono (hmono _ _ ?_)) h1
        push_cast
        exact le_max_of_le_left (by linarith)
      · rw [max_eq_right h.le] at ih
        have h2 : max (Cb - ((k + 1 : ℕ) : ℝ) * gs) lo = lo := by
          apply max_eq_right
          push_cast
          nlinarith
        rw [h2]
        exact ih
  obtain ⟨k, hk⟩ := exists_nat_ge ((Cb - lo) / gs)
  have hk' : Cb - k * gs ≤ lo := by
    rw [div_le_iff₀ hgs] at hk
    linarith
  have := key k
  rwa [max_eq_right hk'] at this

/-- **One orientation of Proposition 3.6** (blueprint `a:prop36`, "Start", "Step", "Iteration"): from the start at
`C_b`, the implication of Proposition 3.5 (premise at the error `ε∗ ≥ ε'`), the references and Proposition 3.3 at slack
`g/2` (already specialized to the depth `n_g`), the comparison holds at the coefficient `1 + 20v` with failure `≤ q`. -/
theorem p8b_prop36_side {D E : DistRd d → ContMetric d} {H₀ σ₀ β₀ m M Cb v gn εs ε' q₀ q p₀ Rs : ℝ}
    (hgn : 0 < gn) (hgnv : gn ≤ v) (hε' : ε' ≤ εs) (hq : q ≤ q₀) (hlo : 1 + 20 * v ≤ Cb) (hp₀ : 0 < p₀)
    (hstart : pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) Cb ε' Rs} ≤ ENNReal.ofReal q)
    (h35 : ∀ c : ℝ, 1 + 20 * v ≤ c → c ≤ Cb →
      pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) c εs Rs} ≤ ENNReal.ofReal q₀ →
      pinLaw d 10 (Hup D E (c - gn)) ≤ ENNReal.ofReal (p₀ / 2))
    (hrefs : pinLaw d 10 (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ≤ ENNReal.ofReal (p₀ / 2))
    (h33 : ∀ b : ℝ, 0 < b → b ≤ Cb →
      pinLaw d 10 (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ) ≤ ENNReal.ofReal p₀ →
      pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) (b + gn / 2) ε' Rs} ≤ ENNReal.ofReal q) :
    pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) (1 + 20 * v) ε' Rs} ≤ ENNReal.ofReal q := by
  refine p8b_iterate (μ := pinLaw d 10) (P := fun c => {g | ¬ CompOn (rho E g) (rho D g) c ε' Rs})
    (gs := gn / 2) (by positivity) hlo (fun c c' hcc' => p8b_notCompOn_anti hcc') hstart ?_
  intro c hc hcC hPc
  have hPc' : pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) c εs Rs} ≤ ENNReal.ofReal q₀ :=
    (measure_mono (p8b_notCompOn_anti_err hε')).trans (hPc.trans (ENNReal.ofReal_le_ofReal hq))
  have hH := h35 c hc hcC hPc'
  have hloc : pinLaw d 10 (Hup D E (c - gn) ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ) ≤ ENNReal.ofReal p₀ := by
    calc pinLaw d 10 (Hup D E (c - gn) ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)
        ≤ pinLaw d 10 (Hup D E (c - gn)) + pinLaw d 10 (PairRefs D E H₀ σ₀ β₀ m M)ᶜ :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (p₀ / 2) + ENNReal.ofReal (p₀ / 2) := add_le_add hH hrefs
      _ = ENNReal.ofReal p₀ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hv : 0 < v := lt_of_lt_of_le hgn hgnv
  have hb0 : 0 < c - gn := by linarith
  have hbC : c - gn ≤ Cb := by linarith
  have h1 := h33 (c - gn) hb0 hbC hloc
  rw [show c - gn + gn / 2 = c - gn / 2 by ring] at h1
  exact h1

/-! ## The final step -/

/-- **The final union bound of Proposition 3.6**: the two final comparisons at coefficient `1 + w` and error `e`, and
the diameter bound `M` for both metrics, give `supd_{R}(ρ^D, ρ^E) ≤ w M + e`; so the bad event is contained in the
union of the four failure events. -/
theorem p8b_prop36_subset (D E : DistRd d → ContMetric d) {w e M R u : ℝ} (hw : 0 ≤ w)
    (hwu : w * M + e < u) :
    {g | ENNReal.ofReal u < supDistLU d R (rho D g).1 (rho E g).1} ⊆
      {g | ¬ CompOn (rho E g) (rho D g) (1 + w) e R} ∪ {g | ¬ CompOn (rho D g) (rho E g) (1 + w) e R} ∪
        {g | ¬ ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, (rho D g).1 (x, y) ≤ M} ∪
        {g | ¬ ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, (rho E g).1 (x, y) ≤ M} := by
  intro g hg
  by_contra hcon
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
  obtain ⟨⟨⟨h₁, h₂⟩, hD⟩, hE⟩ := hcon
  have h := p8b_supDistLU_le_of_compOn hw h₁ h₂ hD hE
  exact absurd (lt_of_lt_of_le hg h) (not_lt.2 (ENNReal.ofReal_le_ofReal hwu.le))

/-! ## Proposition 3.6 -/

/-- **Proposition 3.6** (a seed at fixed confidence; blueprint `a:prop36`; [C] Prop. 3.6; NA1 item 28, R11). -/
theorem prop36 (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s)
    (h35 : Prop35Shape d ξbar) :
    ∃ Rs : ℝ, 1 ≤ Rs ∧ ∀ ps : ℝ, 0 < ps → ∃ B C₆ : ℝ, 0 < B ∧ 0 < C₆ ∧
      ∀ a ∈ Ioc (0 : ℝ) ξbar, ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ u : ℝ, 0 < u → u < 1 →
          |ξ - η| ≤ Real.exp (-(C₆ * a ^ (-B) * u ^ (-B))) →
          pinLaw d 10 {g | ENNReal.ofReal u < supDistLU d Rs (rho D g).1 (rho E g).1} ≤
            ENNReal.ofReal ps := by
  -- the fixed data
  obtain ⟨Cb, hCb, hl32⟩ := lemma32 hd hU
  obtain ⟨C₃₂, c₃₂, hC₃₂, hc₃₂, hstart⟩ := hl32 10 (by norm_num) le_rfl
  obtain ⟨p₀, hp₀, h33⟩ := prop33 hd hU
  have hU10 := hU 10 ⟨by norm_num, le_rfl⟩
  obtain ⟨H₀, σ₀, β₀, m, M, -, -, -, hm, hmM, -, hrefs⟩ :=
    refs_prob hd (by norm_num : (0 : ℝ) < 10) hU10 (p := p₀ / 2) (by positivity)
  obtain ⟨M₃, C₃, c₃, hM₃, hC₃, hc₃, hamp⟩ :=
    h33 Cb H₀ σ₀ β₀ m M (by linarith) hm hmM.le 10 10 (by norm_num) le_rfl (by norm_num) le_rfl
  obtain ⟨Rs, q₀, Ap, kp, v₀, hRs, hq₀, hv₀, hv₀', h35'⟩ := h35 Cb (p₀ / 2) (by linarith) (by positivity)
  refine ⟨Rs, hRs, fun ps hps => ?_⟩
  set q : ℝ := min (min q₀ (ps / 8)) (1 / 16) with hqdef
  have hq0 : 0 < q := lt_min (lt_min hq₀ (by positivity)) (by norm_num)
  have hqq₀ : q ≤ q₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hqps : q ≤ ps / 8 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hq16 : q ≤ 1 / 16 := min_le_right _ _
  obtain ⟨Ms, hMs, hdiam⟩ := p8b_diam_quantile hd (by norm_num : (0 : ℝ) < 10) hU10 (R := Rs)
    (by linarith) (p := ps / 4) (by positivity)
  obtain ⟨B, C₆, hB, hC₆, hceil⟩ := p8b_ceiling (ξbar := ξbar) (Ap := Ap) (kp := kp) hRs hq0
    (by linarith) hC₃₂ hc₃₂ hC₃ hc₃ hM₃ hv₀ hv₀' hMs
  refine ⟨B, C₆, hB, hC₆, ?_⟩
  intro a ha ξ hξ η hη D E hD hE u hu hu1 hτ
  have hξ' : ξ ∈ Ioc (0 : ℝ) ξbar := ⟨lt_of_lt_of_le ha.1 hξ.1, hξ.2⟩
  have hη' : η ∈ Ioc (0 : ℝ) ξbar := ⟨lt_of_lt_of_le ha.1 hη.1, hη.2⟩
  -- Proposition 3.5 at `(a, v)`
  set v : ℝ := min (v₀ / 2) (u / (160 * Ms)) with hvdef
  have hv0 : 0 < v := lt_min (by positivity) (by positivity)
  have hvv₀ : v < v₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvu : v ≤ u / (160 * Ms) := min_le_right _ _
  have hv160 : v < 1 / 160 := by
    refine lt_of_le_of_lt hvu ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨gn, εs, ts, hgnlo, hgnv, hεs, -, hlogε, htslo, hcmp⟩ := h35' a ha v ⟨hv0, hvv₀⟩
  obtain ⟨hτts, hτn₀, hτng⟩ := hceil a u gn εs ts ha.1 ha.2 hu hu1 hgnlo hgnv hεs hlogε htslo
  have hgn0 : 0 < gn := lt_of_lt_of_le (Real.exp_pos _) hgnlo
  -- the per-parameter quantities
  set ε' : ℝ := min εs (u / 16) with hε'def
  have hε'0 : 0 < ε' := lt_min hεs (by positivity)
  have hε'u : ε' ≤ u / 16 := min_le_right _ _
  have hε'8 : ε' < 1 / 8 := by linarith
  have hε'εs : ε' ≤ εs := min_le_left _ _
  have hδg : gn / 2 < 1 / 8 := by linarith
  have hδg0 : 0 < gn / 2 := by positivity
  have hlo : 1 + 20 * v ≤ Cb := by linarith
  -- the drift
  have hτts' : |η - ξ| ≤ ts := by rw [abs_sub_comm]; exact hτ.trans hτts
  have hτts'' : |ξ - η| ≤ ts := hτ.trans hτts
  -- the start (Lemma 3.2)
  have hn₀ : 0 ≤ p8bN0 C₃₂ Rs ε' q := by
    rw [p8bN0]
    have h1 : 0 ≤ Real.log (1 + Rs) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log ε'⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε'0, by linarith⟩)
    have h3 : 0 ≤ Real.log q⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hq0, by linarith⟩)
    positivity
  have hdr₀ : |η - ξ| * p8bN0 C₃₂ Rs ε' q ≤ c₃₂ := by
    rw [abs_sub_comm]
    exact (mul_le_mul_of_nonneg_right hτ hn₀).trans hτn₀
  have hst := hstart ξ hξ' η hη' D E hD hE Rs ε' q (p8bN0 C₃₂ Rs ε' q) hRs hε'0 hε'8 hq0
    (by linarith) le_rfl hdr₀
  have hst₁ : pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) Cb ε' Rs} ≤ ENNReal.ofReal q :=
    (measure_mono (show {g | ¬ CompOn (rho E g) (rho D g) Cb ε' Rs} ⊆
      {g | ¬ (CompOn (rho E g) (rho D g) Cb ε' Rs ∧ CompOn (rho D g) (rho E g) Cb ε' Rs)} from
        fun _ hg hc => hg hc.1)).trans hst
  have hst₂ : pinLaw d 10 {g | ¬ CompOn (rho D g) (rho E g) Cb ε' Rs} ≤ ENNReal.ofReal q :=
    (measure_mono (show {g | ¬ CompOn (rho D g) (rho E g) Cb ε' Rs} ⊆
      {g | ¬ (CompOn (rho E g) (rho D g) Cb ε' Rs ∧ CompOn (rho D g) (rho E g) Cb ε' Rs)} from
        fun _ hg hc => hg hc.2)).trans hst
  -- the step depth (Proposition 3.3 at slack `g/2`)
  obtain ⟨hdepth, hfail⟩ := p8b_ng_spec (ε := ε') (q := q) (δg := gn / 2) hC₃ hc₃ hM₃ hRs hε'0
    (by linarith) hq0 (by linarith) hδg0 (by linarith)
  have hng : 0 ≤ p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2) := by
    refine le_trans ?_ hdepth
    have h1 : 0 ≤ Real.log (1 + Rs) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log ε'⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε'0, by linarith⟩)
    have h3 : 0 ≤ Real.log (gn / 2)⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hδg0, by linarith⟩)
    have := Real.rpow_pos_of_pos hδg0 (-M₃)
    positivity
  have hdrg : |η - ξ| * p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2) ≤ c₃ * (gn / 2) := by
    rw [abs_sub_comm]
    exact (mul_le_mul_of_nonneg_right hτ hng).trans hτng
  have hdrg' : |ξ - η| * p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2) ≤ c₃ * (gn / 2) :=
    (mul_le_mul_of_nonneg_right hτ hng).trans hτng
  have hfail' : ENNReal.ofReal (C₃ * Rs ^ M₃ * (gn / 2) ^ (-M₃) *
      Real.exp (-c₃ * (gn / 2) ^ M₃ * p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2))) ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hfail
  -- the two orientations
  have hside₁ : pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) (1 + 20 * v) ε' Rs} ≤ ENNReal.ofReal q :=
    p8b_prop36_side hgn0 hgnv hε'εs hqq₀ hlo hp₀ hst₁
      (fun c hc hcC hP => hcmp ξ hξ η hη hτts' D E hD hE c hc hcC hP) (hrefs ξ hξ' η hη' D E hD hE)
      (fun b hb hbC hloc => (hamp ξ hξ' η hη' D E hD hE b hb hbC hloc Rs (gn / 2) ε'
        (p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2)) hRs hδg0 hδg hε'0 hε'8 hdepth hdrg).trans hfail')
  have hside₂ : pinLaw d 10 {g | ¬ CompOn (rho D g) (rho E g) (1 + 20 * v) ε' Rs} ≤ ENNReal.ofReal q :=
    p8b_prop36_side hgn0 hgnv hε'εs hqq₀ hlo hp₀ hst₂
      (fun c hc hcC hP => hcmp η hη ξ hξ hτts'' E D hE hD c hc hcC hP) (hrefs η hη' ξ hξ' E D hE hD)
      (fun b hb hbC hloc => (hamp η hη' ξ hξ' E D hE hD b hb hbC hloc Rs (gn / 2) ε'
        (p8bNg C₃ c₃ M₃ Rs ε' q (gn / 2)) hRs hδg0 hδg hε'0 hε'8 hdepth hdrg').trans hfail')
  -- the final union bound
  have hwu : 20 * v * Ms + ε' < u := by
    have h1 : 20 * v * Ms ≤ u / 8 := by
      have h2 : v * (160 * Ms) ≤ u := by
        have := mul_le_mul_of_nonneg_right hvu (by positivity : (0 : ℝ) ≤ 160 * Ms)
        rwa [div_mul_cancel₀ _ (by positivity)] at this
      nlinarith
    linarith
  have hsub := p8b_prop36_subset D E (R := Rs) (by positivity : (0 : ℝ) ≤ 20 * v) hwu
  calc pinLaw d 10 {g | ENNReal.ofReal u < supDistLU d Rs (rho D g).1 (rho E g).1}
      ≤ pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) (1 + 20 * v) ε' Rs} +
          pinLaw d 10 {g | ¬ CompOn (rho D g) (rho E g) (1 + 20 * v) ε' Rs} +
          pinLaw d 10 {g | ¬ ∀ x ∈ closedBall (0 : Rd d) Rs, ∀ y ∈ closedBall (0 : Rd d) Rs,
            (rho D g).1 (x, y) ≤ Ms} +
          pinLaw d 10 {g | ¬ ∀ x ∈ closedBall (0 : Rd d) Rs, ∀ y ∈ closedBall (0 : Rd d) Rs,
            (rho E g).1 (x, y) ≤ Ms} := by
        refine (measure_mono hsub).trans ?_
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal (ps / 4) + ENNReal.ofReal (ps / 4) :=
        add_le_add (add_le_add (add_le_add hside₁ hside₂) (hdiam ξ hξ' D hD)) (hdiam η hη' E hE)
    _ ≤ ENNReal.ofReal ps := by
        rw [← ENNReal.ofReal_add hq0.le hq0.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

end HigherDimLQGContinuity
