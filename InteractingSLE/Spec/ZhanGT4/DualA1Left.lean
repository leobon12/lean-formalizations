/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD10Frozen

/-!
# (D9) for a protected rectangle, the other orientation (frozen curve on the left)

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L341, R38). The
two-coordinate argument of §A.1 freezes each curve in turn: with sources `x₁ < x₂`, curve `1` grows with curve `2`
frozen on its right (PROVE-ZHAN-GT4-A9's `exists_twoCurveD9`, `0 < q < W₂(0)`), and curve `2` grows with curve `1`
frozen on its **left**. This file proves the latter orientation, `W₂(0) < q < 0`, by the same argument with the tip
separation of `exists_le_neg_re_fwdMap_tip_left` (the image of the frozen tip lies `γ` to the left of the image
driver) and the transposed own-derivative bound through `exists_le_re_fwdMap_tip_right`:

* `exists_exp_le_norm_deriv_refl_own_left` (mirror of `exists_exp_le_norm_deriv_refl_own`);
* **`exists_twoCurveD9_left`** (mirror of `exists_twoCurveD9`): every frozen-left configuration satisfies
  `TwoCurveD9` (the (D9) constants, aliveness and distinctness of the marks, the bound of the image driver);
* **`exists_frzD10Hyp_left`**: the hypotheses `FrzD10Hyp` of the frozen-curve martingale, Girsanov step and (D10)
  (`FrzD10Hyp.martingale_d10`, `FrzD10Hyp.martingale_d10_imgDrift`) for this orientation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull)

/-- **(D9), the own derivative factor from below, frozen curve on the left** (mirror of
`exists_exp_le_norm_deriv_refl_own`): the same bound `e^{−2t₂/γ²} ≤ |G'(W₁(s))|` when `W₂ 0 < q < W₁ 0`. -/
theorem exists_exp_le_norm_deriv_refl_own_left {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    {δ : ℝ} (hδ : 0 < δ) (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (s t₂ : ℝ) (a₂ W₂' : ℝ → ℝ),
      ImgData W₂ (fwdHull W₁ s) (fun z => fwdMap W₁ s z + W₁ s) t₂ a₂ W₂' →
      Continuous W₁ → 0 ≤ s → ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
      q < W₁ 0 → W₂ 0 < q → fwdHull W₁ s ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      ∀ (R G : ℂ → ℂ) (ε : ℝ), IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) R → 0 < ε →
        DifferentiableOn ℂ G (ball (W₁ s : ℂ) ε) → EqOn G R (ball (W₁ s : ℂ) ε ∩ H) →
        Real.exp (-(2 / γ ^ 2 * t₂)) ≤ ‖deriv G (W₁ s)‖ := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hsepδ z hz a ha
  have hsep : Disjoint (closure H₁) (closure H₂) := disjoint_closure_of_le_norm_sub hδ hsepδ
  have hqH' : Disjoint (ball (q : ℂ) (2 * d)) (H₂ ∪ H₁) := by rwa [union_comm]
  obtain ⟨γ, hγ, hleft⟩ := exists_le_re_fwdMap_tip_right hH₂ hH₁ hsep.symm hd hqH'
  obtain ⟨r₁, hr₁, hcl₁⟩ := exists_le_norm_fwdMap_uniform hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hcl₂⟩ := exists_le_norm_fwdMap_uniform hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  refine ⟨γ, hγ, ?_⟩
  intro W₁ W₂ s t₂ a₂ W₂' h hW₁ hs hW₁H hW₂H hx₁q hqx₂ hK₁ hK₂ R G ε hR hε hGd hGR
  have hW₂ := h.cont
  have ht₂ := h.pos
  have hsmem : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂.le, le_rfl⟩
  -- clearances
  have hc₁ : ∀ z ∈ fwdHull W₂ t₂, r₁ ≤ ‖fwdMap W₁ s z‖ := fun z hz =>
    hcl₁ W₁ hW₁ hW₁H s hK₁ s hsmem z (hK₂ hz)
  have hclr : ∀ v ∈ Icc (0 : ℝ) t₂, Disjoint (ball (W₂ v : ℂ) r₂)
      ((fun z => fwdMap W₂ v z + W₂ v) '' fwdHull W₁ s) := fun v hv =>
    OwnData.disjoint_ball_of_le_norm fun z hz => hcl₂ W₂ hW₂ hW₂H t₂ hK₂ v hv z (hK₁ hz)
  -- the separation of the tips, in the transposed configuration
  have hgap : ∀ v ∈ Icc (0 : ℝ) t₂, γ ≤ ‖fwdMap W₂' (a₂ v) (W₁ s)‖ := fun v hv =>
    (hleft W₂ W₁ s t₂ a₂ W₂' r₁ h hW₁ hs hW₁H hqx₂ hx₁q hK₂ hK₁ hr₁ hc₁ v hv).trans (Complex.re_le_norm _)
  -- the tip `W₁(s)` is alive for the image chain of curve `2`
  obtain ⟨u0, hu0, hW₂'0⟩ := h.exists_start_alive hW₁ hs (by linarith)
  have hu0pos := QuantumZipper.re_neg_isForwardSol_real hW₁ hs hu0 (by linarith) s hsmem
  obtain ⟨vζ, hvζ⟩ := h.exists_tip_alive hr₁ hc₁ (by rw [hW₂'0]; intro h'; linarith) ht₂mem
  have hode := h.exp_neg_le_norm_deriv_fwdMap_image hr₂ hclr hvζ hγ hgap ht₂mem
  -- identification of the derivative
  set τ := a₂ t₂ with hτdef
  have hτ0 : 0 ≤ τ := (h.mapsTo_clock_Icc ht₂mem).1
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ0, le_rfl⟩
  have hgt : IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) (fun w => fwdMap W₂' τ w + W₂' τ) := by
    rw [← h.img t₂ ht₂mem]; exact isMapOut_fwdMap_gen h.contW' hτ0
  have hEhull : IsHPHull ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) := by
    rw [← h.img t₂ ht₂mem]; exact isHPHull_fwdHull h.contW' hτ0
  have hReq := IsMapOut.eqOn hEhull hR hgt
  obtain ⟨δζ, hδζ, hlowζ, hζdisc⟩ := exists_aliveDisc_self hvζ hτ0
  have hfd : DifferentiableAt ℂ (fwdMap W₂' τ) (W₁ s) :=
    (hasDerivAt_fwdMap_aliveDisc h.contW' hvζ hδζ hlowζ hζdisc hτmem).differentiableAt
  have hxB : ((W₁ s : ℝ) : ℂ) ∈ ball ((W₁ s : ℝ) : ℂ) ε := mem_ball_self hε
  have hGx : DifferentiableAt ℂ G (W₁ s) := hGd.differentiableAt (isOpen_ball.mem_nhds hxB)
  set ε' := min ε r₁ with hε'def
  have hε' : 0 < ε' := lt_min hε hr₁
  have hupper : ∀ e ∈ Ioo (0 : ℝ) ε', G ((W₁ s : ℂ) + (e : ℂ) * I) =
      fwdMap W₂' τ ((W₁ s : ℂ) + (e : ℂ) * I) + W₂' τ := by
    intro e he
    have hnorm : ‖((W₁ s : ℂ) + (e : ℂ) * I) - (W₁ s : ℂ)‖ = e := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos he.1]
    have hzH : (W₁ s : ℂ) + (e : ℂ) * I ∈ H := by
      show 0 < ((W₁ s : ℂ) + (e : ℂ) * I).im
      simp [he.1]
    have hzB : (W₁ s : ℂ) + (e : ℂ) * I ∈ ball ((W₁ s : ℝ) : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, hnorm]; exact he.2.trans_le (min_le_left _ _)
    have hzE : (W₁ s : ℂ) + (e : ℂ) * I ∉ (fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂ := by
      rintro ⟨k, hk, hkz⟩
      have h1 := hc₁ k hk
      have h2 : ‖fwdMap W₁ s k‖ = e := by
        rw [← hnorm, ← hkz]; congr 1; push_cast; ring
      have h3 : e < r₁ := he.2.trans_le (min_le_right _ _)
      linarith
    rw [hGR ⟨hzB, hzH⟩, hReq ⟨hzH, hzE⟩]
  have hGval : G (W₁ s) = fwdMap W₂' τ (W₁ s) + W₂' τ := by
    have hGc : Tendsto G (𝓝[H] ((W₁ s : ℝ) : ℂ)) (𝓝 (G (W₁ s))) :=
      hGx.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hgc : Tendsto (fun w => fwdMap W₂' τ w + W₂' τ) (𝓝[H] ((W₁ s : ℝ) : ℂ))
        (𝓝 (fwdMap W₂' τ (W₁ s) + W₂' τ)) :=
      ((hfd.add_const ((W₂' τ : ℝ) : ℂ)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ w in 𝓝[H] ((W₁ s : ℝ) : ℂ), G w = fwdMap W₂' τ w + W₂' τ := by
      have hball : ball ((W₁ s : ℝ) : ℂ) ε' ∈ 𝓝 ((W₁ s : ℝ) : ℂ) := ball_mem_nhds _ hε'
      filter_upwards [inter_mem_nhdsWithin H hball] with w hw
      have hwH : w ∈ H := hw.1
      have hwB : w ∈ ball ((W₁ s : ℝ) : ℂ) ε := ball_subset_ball (min_le_left _ _) hw.2
      have hwE : w ∉ (fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂ := by
        rintro ⟨k, hk, hkz⟩
        have h1 := hc₁ k hk
        have hw1 := hw.2
        rw [mem_ball, dist_eq_norm, ← hkz] at hw1
        have e2 : fwdMap W₁ s k + ((W₁ s : ℝ) : ℂ) - ((W₁ s : ℝ) : ℂ) = fwdMap W₁ s k := by ring
        rw [e2] at hw1
        linarith [hw1.trans_le (min_le_right ε r₁)]
      rw [hGR ⟨hwB, hwH⟩, hReq ⟨hwH, hwE⟩]
    have hne : (𝓝[H] ((W₁ s : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    exact tendsto_nhds_unique (hGc.congr' hev) hgc
  have hderiv := deriv_eq_of_eq_upper hε' hGx (hfd.add_const ((W₂' τ : ℝ) : ℂ)) hGval hupper
  rw [hderiv, deriv_add_const]
  exact hode.1

/-- **(D9) for a protected rectangle, frozen curve on the left** (mirror of `exists_twoCurveD9`): for separated
enclosures, a protected point `q < 0` and protected marks, uniform constants such that every configuration with curve
`2` frozen at `0 < t₂ ≤ Tm` in `H₂` and starting left of `q` satisfies `TwoCurveD9`. -/
theorem exists_twoCurveD9_left {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {n : ℕ} {p : Fin n → ℝ}
    (hpH : ∀ m, Disjoint (ball (p m : ℂ) (2 * d)) (H₁ ∪ H₂)) (hpinj : Function.Injective p) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam : ℝ, 0 < r ∧ 0 < a₀ ∧ 0 < γ ∧
      ∀ (W W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ) (κ : ℝ) (rr : Fin n → ℝ),
      OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' → Continuous W₂ →
      ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
      fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      TwoCurveD9 (⟨W, W', a, fun z => fwdMap W₂ t₂ z + W₂ t₂, κ, rr, W₂ t₂,
        fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂⟩ : FrzData n) (fwdHull W₂ t₂) T r a₀ γ Γ lam := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hsepδ z hz a ha
  have hsep : Disjoint (closure H₁) (closure H₂) := disjoint_closure_of_le_norm_sub hδ hsepδ
  have h2d : (0 : ℝ) < 2 * d := by linarith
  obtain ⟨r₁, hr₁, hcl₁⟩ := exists_le_norm_fwdMap_uniform hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hcl₂⟩ := exists_le_norm_fwdMap_uniform hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  obtain ⟨γt, hγt, htip⟩ := exists_le_neg_re_fwdMap_tip_left hH₁ hH₂ hsep hd hqH
  choose γp hγp hprot using fun m => exists_le_norm_fwdMap_protected hH₁ hH₂ hsep hd (hpH m)
  obtain ⟨γo, hγo, hown⟩ := exists_exp_le_norm_deriv_refl_own_left hH₁ hH₂ hδ hsepδ hd hqH
  have hpH₂ : ∀ m, Disjoint (ball (p m : ℂ) (2 * d)) H₂ := fun m => (hpH m).mono_right subset_union_right
  choose μ hμ hderiv using fun m => exists_deriv_fwdMap_real_bounds hH₂ h2d (hpH₂ m)
  obtain ⟨C₀, hC₀⟩ := (hH₁.2.1.union hH₂.2.1).exists_norm_le
  set R₀ := max C₀ 1 with hR₀def
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : closure (H₁ ∪ H₂) ⊆ closedBall ((0 : ℝ) : ℂ) R₀ :=
    isClosed_closedBall.closure_subset_iff.2 fun z hz => by
      rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right]; exact (hC₀ z hz).trans (le_max_left _ _)
  -- the gap constant of the image chain
  obtain ⟨γm, hγm, hγmle⟩ := exists_pos_le_of_fintype γp hγp
  set γ₀ := min γt γm with hγ₀def
  have hγ₀ : 0 < γ₀ := lt_min hγt hγm
  -- the gap constant of the frozen chain at the marks
  obtain ⟨β, hβ, hβle⟩ := exists_pos_le_of_fintype (fun m => 2 * d / 96 * μ m) fun m => by
    have := hμ m; positivity
  -- the mutual distances of the marks
  obtain ⟨ν, hν, hνle⟩ := exists_pos_le_of_fintype
    (fun mk : Fin n × Fin n => if mk.1 = mk.2 then 1 else |p mk.1 - p mk.2|) fun mk => by
      by_cases h : mk.1 = mk.2
      · simp [h]
      · simp only [h, ↓reduceIte]; exact abs_pos.2 (sub_ne_zero.2 fun h' => h (hpinj h'))
  set cζ := min β (ν * Real.exp (-(2 / β ^ 2 * Tm))) with hcζdef
  have hcζ : 0 < cζ := lt_min hβ (by positivity)
  set Z := ∑ m, |p m| + 7 * R₀ with hZdef
  have hZ0 : 0 ≤ ∑ m, |p m| := Finset.sum_nonneg fun m _ => abs_nonneg _
  refine ⟨r₁, Real.exp (-(2 / γo ^ 2 * Tm)), min γ₀ (cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm))),
    max (Z + 72 * R₀) (2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm)), 2 / γ₀ ^ 2 * Tm, hr₁, Real.exp_pos _,
    lt_min hγ₀ (by positivity), ?_⟩
  intro W W₂ t₂ T a W' κ rr h hW₂ hW₂H hqW ht₂ ht₂m hTm hK₁ hK₂
  have hW := h.cont
  have hW0 := h.zero
  have hT := h.pos
  have hI := h.toImgData
  have hW'c := h.contW'
  have ht₂0 := ht₂.le
  have hW0H : ((W 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hK₁ (start_mem_closure_fwdHull hW hT)
  have hWq : q < W 0 := by rw [hW0]; exact hq
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  -- clearances
  have hclr : ∀ t ∈ Icc (0 : ℝ) T,
      Disjoint (ball (W t : ℂ) r₁) ((fun z => fwdMap W t z + W t) '' fwdHull W₂ t₂) := fun t ht =>
    OwnData.disjoint_ball_of_le_norm fun z hz => hcl₁ W hW hW0H T hK₁ t ht z (hK₂ hz)
  have hcl₂' : ∀ z ∈ fwdHull W T, r₂ ≤ ‖fwdMap W₂ t₂ z‖ := fun z hz =>
    hcl₂ W₂ hW₂ hW₂H t₂ hK₂ t₂ ⟨ht₂0, le_rfl⟩ z (hK₁ hz)
  -- the start of curve 1 in the frozen chart
  obtain ⟨u0, hu0, hW'0⟩ := hI.exists_start_alive hW₂ ht₂0 (by linarith : W 0 ≠ W₂ 0)
  have hu0neg := QuantumZipper.re_pos_isForwardSol_real hW₂ ht₂0 hu0 (by linarith) t₂ ⟨ht₂0, le_rfl⟩
  have hne0 : W₂ t₂ ≠ W' 0 := by rw [hW'0]; linarith
  have halive₀ : ∀ s ∈ Icc (0 : ℝ) T, ∃ v, IsForwardSol W' ((W₂ t₂ : ℝ) : ℂ) (a s) v := fun s hs =>
    hI.exists_tip_alive hr₂ hcl₂' hne0 hs
  have htipγ := htip W W₂ t₂ T a W' r₂ hI hW₂ ht₂0 hW₂H hqW hWq hK₁ hK₂ hr₂ hcl₂'
  have hprot' := fun m => hprot m W W₂ t₂ T a W' hI hW₂ ht₂0 hW₂H hK₁ hK₂
  -- the gaps of the image chain
  have hgap₀ : ∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ((W₂ t₂ : ℝ) : ℂ)‖ := fun s hs =>
    (min_le_left _ _).trans ((htipγ s hs).trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)))
  have hgapm : ∀ m, ∀ s ∈ Icc (0 : ℝ) T,
      γ₀ ≤ ‖fwdMap W' (a s) (((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ)‖ := fun m s hs =>
    (min_le_right _ _).trans ((hγmle m).trans (hprot' m s hs).2)
  obtain ⟨v₀, hv₀⟩ := halive₀ T hTmem
  choose vm hvm using fun m => (hprot' m T hTmem).1
  -- the discs containing the hulls
  have hA2 : fwdHull W₂ t₂ ⊆ closedBall ((0 : ℝ) : ℂ) R₀ := fun z hz =>
    hball (subset_closure (Or.inr (hK₂ hz)))
  have hW₂0 : |W₂ 0 - 0| ≤ R₀ := by
    have h1 := hball (closure_mono subset_union_right hW₂H)
    rwa [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  have hφ₂ := isMapOut_fwdMap_gen hW₂ ht₂0
  have hhull₂ := isHPHull_fwdHull hW₂ ht₂0
  have himg : ∀ s ∈ Icc (0 : ℝ) T, fwdHull W' (a s) ⊆ closedBall ((0 : ℝ) : ℂ) (6 * R₀) := by
    intro s hs z hz
    rw [h.img s hs] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwH1 : w ∈ H₁ := hK₁ ((QuantumZipper.fwdHull_mono).1 hs.2 hw)
    have hwA : w ∉ fwdHull W₂ t₂ := fun hwA => Set.disjoint_left.1 (hI.disjoint_A_K hs) hwA hw
    have hb := hφ₂.norm_sub_center_le hhull₂ hR₀ hA2 ⟨hH₁.1 hwH1, hwA⟩
    have hw0 : ‖w - ((0 : ℝ) : ℂ)‖ ≤ R₀ := by
      have := hball (subset_closure (Or.inl hwH1)); rwa [mem_closedBall, dist_eq_norm] at this
    rw [mem_closedBall, dist_eq_norm]; linarith
  have hW'0b : |W' 0 - 0| ≤ 6 * R₀ := by
    have hb := norm_sol_add_sub_le hW₂ ht₂0 hR₀ hA2 hu0
    have e : W' 0 - 0 = (u0 t₂ + ((W₂ t₂ : ℝ) : ℂ) - ((0 : ℝ) : ℂ)).re := by rw [hW'0]; simp
    rw [e]
    refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
    rw [hW0, sub_self, norm_zero]; linarith
  have hupper : ∀ (ζ : ℝ) (v : ℝ → ℂ), IsForwardSol W' (ζ : ℂ) (a T) v → ∀ s ∈ Icc (0 : ℝ) T,
      ‖fwdMap W' (a s) ζ‖ ≤ |ζ| + 72 * R₀ := by
    intro ζ v hv s hs
    have has := hI.mapsTo_clock_Icc hs
    have hvs := QuantumZipper.isForwardSol_restrict hv has.1 has.2
    rw [fwdMap_eq_of_isForwardSol hW'c hv has]
    have := norm_sol_le hW'c has.1 (by positivity : (0 : ℝ) < 6 * R₀) (himg s hs) hW'0b hvs
    rw [sub_zero] at this; linarith
  have hclock : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s ∧ a s ≤ Tm := fun s hs =>
    ⟨(hI.mapsTo_clock_Icc hs).1, (hI.clock_le hr₁ hclr hs).trans (hs.2.trans hTm)⟩
  -- the frozen chain at the marks
  have hW₂notin : ∀ m, ∀ y : ℝ, (y : ℂ) ∈ ball (p m : ℂ) (2 * d / 2) → y ≠ W₂ 0 := by
    intro m y hy hyW
    have hn := notMem_ball_of_mem_closure (hpH₂ m) hW₂H
    rw [hyW] at hy; exact hn (ball_subset_ball (by linarith) hy)
  have hgap₂ : ∀ m, ∀ s ∈ Icc (0 : ℝ) t₂, β ≤ ‖fwdMap W₂ s (p m)‖ := by
    intro m s hs
    have hKs : fwdHull W₂ s ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 hs.2).trans hK₂
    have hk := le_norm_fwdMap_real hW₂ hs.1 h2d ((hpH₂ m).mono_right hKs) (hW₂notin m)
    obtain ⟨-, hμle, -⟩ := hderiv m W₂ hW₂ s hs.1 hKs (hW₂notin m)
    have h1 : 2 * d / 96 * μ m ≤ 2 * d / 96 * ‖deriv (fwdMap W₂ s) (p m)‖ :=
      mul_le_mul_of_nonneg_left (hμle.trans (Complex.re_le_norm _)) (by positivity)
    exact (hβle m).trans (h1.trans hk)
  have hpalive : ∀ m, ∃ w, IsForwardSol W₂ (p m : ℂ) t₂ w := fun m =>
    exists_isForwardSol_of_disjoint_ball_gen hW₂ (hW₂notin m (p m) (mem_ball_self (by linarith))) ht₂0 h2d
      ((hpH₂ m).mono_right hK₂)
  choose wm hwm using hpalive
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂0, le_rfl⟩
  have hpsum : ∀ m, |p m| ≤ ∑ k, |p k| := fun m =>
    Finset.single_le_sum (f := fun k => |p k|) (fun k _ => abs_nonneg _) (Finset.mem_univ m)
  have hζ₀Z : |W₂ t₂| ≤ Z := by
    have := abs_driver_sub_le hW₂ ht₂0 hR₀ hA2 hW₂0 ht₂mem
    rw [sub_zero] at this; linarith
  have hζmZ : ∀ m, |(fwdMap W₂ t₂ (p m)).re + W₂ t₂| ≤ Z := by
    intro m
    have hb := norm_sol_add_sub_le hW₂ ht₂0 hR₀ hA2 (hwm m)
    rw [← fwdMap_eq_of_isForwardSol hW₂ (hwm m) ht₂mem] at hb
    have e : (fwdMap W₂ t₂ (p m)).re + W₂ t₂ =
        (fwdMap W₂ t₂ (p m) + ((W₂ t₂ : ℝ) : ℂ) - ((0 : ℝ) : ℂ)).re := by simp
    rw [e]
    refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_zero]
    linarith [hpsum m]
  have hζ0m : ∀ m, β ≤ ‖((W₂ t₂ : ℝ) : ℂ) - (((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ)‖ ∧
      ‖((W₂ t₂ : ℝ) : ℂ) - (((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ)‖ ≤ 2 * Z := by
    intro m
    have him := fwdMap_real_im hW₂ (hwm m) ht₂mem
    have e : ‖((W₂ t₂ : ℝ) : ℂ) - (((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ)‖ = ‖fwdMap W₂ t₂ (p m)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show W₂ t₂ - ((fwdMap W₂ t₂ (p m)).re + W₂ t₂) = -(fwdMap W₂ t₂ (p m)).re by ring, abs_neg,
        abs_re_eq_norm.2 him]
    refine ⟨e ▸ hgap₂ m t₂ ht₂mem, ?_⟩
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc |W₂ t₂ - ((fwdMap W₂ t₂ (p m)).re + W₂ t₂)| ≤ |W₂ t₂| + |(fwdMap W₂ t₂ (p m)).re + W₂ t₂| :=
          abs_sub _ _
      _ ≤ 2 * Z := by linarith [hζmZ m]
  have hζmk : ∀ m k, m ≠ k → cζ ≤ ‖(((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ) -
      (((fwdMap W₂ t₂ (p k)).re + W₂ t₂ : ℝ) : ℂ)‖ := by
    intro m k hmk
    have hg : ∀ j, ∀ s ∈ Icc (0 : ℝ) t₂, β ≤ ‖wm j s‖ := fun j s hs => by
      rw [← fwdMap_eq_of_isForwardSol hW₂ (hwm j) hs]; exact hgap₂ j s hs
    have hb := (norm_sol_sub_bounds (hwm k) (hwm m) hβ (hg k) (hg m) ht₂mem).1
    have h1 := fwdMap_real_im hW₂ (hwm m) ht₂mem
    have h2 := fwdMap_real_im hW₂ (hwm k) ht₂mem
    rw [fwdMap_eq_of_isForwardSol hW₂ (hwm m) ht₂mem] at h1
    rw [fwdMap_eq_of_isForwardSol hW₂ (hwm k) ht₂mem] at h2
    have e : ‖(((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) : ℂ) - (((fwdMap W₂ t₂ (p k)).re + W₂ t₂ : ℝ) : ℂ)‖ =
        ‖wm m t₂ - wm k t₂‖ := by
      rw [fwdMap_eq_of_isForwardSol hW₂ (hwm m) ht₂mem, fwdMap_eq_of_isForwardSol hW₂ (hwm k) ht₂mem,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show (wm m t₂).re + W₂ t₂ - ((wm k t₂).re + W₂ t₂) = (wm m t₂ - wm k t₂).re by simp,
        abs_re_eq_norm.2 (by simp [h1, h2])]
    rw [e]
    have hν' : ν ≤ |p m - p k| := by have := hνle (m, k); simpa [hmk] using this
    have hpmk : ‖(p m : ℂ) - p k‖ = |p m - p k| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hpmk] at hb
    calc cζ ≤ ν * Real.exp (-(2 / β ^ 2 * Tm)) := min_le_right _ _
      _ ≤ |p m - p k| * Real.exp (-(2 / β ^ 2 * t₂)) :=
          mul_le_mul hν' (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ht₂m (by positivity))))
            (Real.exp_pos _).le (abs_nonneg _)
      _ ≤ _ := hb
  -- the constants
  have hΓ1 : Z + 72 * R₀ ≤ max (Z + 72 * R₀) (2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm)) := le_max_left _ _
  have hΓ2 : 2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm) ≤ max (Z + 72 * R₀) (2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm)) :=
    le_max_right _ _
  have hγD : min γ₀ (cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm))) ≤ γ₀ := min_le_left _ _
  have hγD' : min γ₀ (cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm))) ≤ cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm)) :=
    min_le_right _ _
  have hZ : 0 ≤ Z := by positivity
  -- the mutual bounds through the image chain
  have hpair : ∀ (ζ₁ ζ₂ : ℝ) (v₁ v₂ : ℝ → ℂ), IsForwardSol W' (ζ₁ : ℂ) (a T) v₁ → IsForwardSol W' (ζ₂ : ℂ) (a T) v₂ →
      (∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ζ₁‖) → (∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ζ₂‖) →
      cζ ≤ ‖(ζ₂ : ℂ) - ζ₁‖ → ‖(ζ₂ : ℂ) - ζ₁‖ ≤ 2 * Z → ∀ t ∈ Icc (0 : ℝ) T,
      min γ₀ (cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm))) ≤ |frzImg W' a ζ₂ t - frzImg W' a ζ₁ t| ∧
        |frzImg W' a ζ₂ t - frzImg W' a ζ₁ t| ≤ max (Z + 72 * R₀) (2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm)) := by
    intro ζ₁ ζ₂ v₁ v₂ hv₁ hv₂ hg₁ hg₂ hlo hhi t ht
    have has := hI.mapsTo_clock_Icc ht
    have him₁ := fwdMap_real_im hW'c hv₁ has
    have him₂ := fwdMap_real_im hW'c hv₂ has
    have e : frzImg W' a ζ₂ t - frzImg W' a ζ₁ t = (fwdMap W' (a t) ζ₂ - fwdMap W' (a t) ζ₁).re := by
      unfold frzImg; simp
    rw [e, abs_re_eq_norm.2 (by simp [him₁, him₂])]
    obtain ⟨hb1, hb2⟩ := hI.norm_fwdMap_sub_bounds hv₁ hv₂ hγ₀ hg₁ hg₂ ht
    obtain ⟨ha0, haT⟩ := hclock t ht
    constructor
    · refine hγD'.trans (le_trans ?_ hb1)
      exact mul_le_mul hlo (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left haT (by positivity))))
        (Real.exp_pos _).le (norm_nonneg _)
    · refine hb2.trans (le_trans ?_ hΓ2)
      exact mul_le_mul hhi (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left haT (by positivity)))
        (Real.exp_pos _).le (by positivity)
  have hscale : ∀ (ζ : ℝ) (v : ℝ → ℂ), IsForwardSol W' (ζ : ℂ) (a T) v →
      (∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ζ‖) → ∀ t ∈ Icc (0 : ℝ) T,
      InScale (2 / γ₀ ^ 2 * Tm) (frzImgD W' a ζ t) := by
    intro ζ v hv hg t ht
    have has := hI.mapsTo_clock_Icc ht
    obtain ⟨him, -⟩ := deriv_fwdMap_real hW'c hv has
    obtain ⟨hlo, hhi⟩ := hI.exp_neg_le_norm_deriv_fwdMap_image hr₁ hclr hv hγ₀ hg ht
    have htT : t ≤ Tm := ht.2.trans hTm
    unfold InScale frzImgD
    rw [abs_re_eq_norm.2 him]
    exact ⟨(Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left htT (by positivity)))).trans hlo,
      hhi.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT (by positivity)))⟩
  refine ⟨⟨hr₁, Real.exp_pos _, lt_min hγ₀ (by positivity), fun t ht => hclr t ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨v₀, hv₀⟩, fun m => ⟨vm m, hvm m⟩, ?_, ?_, fun t ht => ?_⟩
  · -- `A_{j,1} ≥ a₀`
    intro t ht
    show Real.exp (-(2 / γo ^ 2 * Tm)) ≤ frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 1 t
    have hd' : Disjoint (closure (fwdHull W t)) (closure (fwdHull W₂ t₂)) :=
      h.disj.symm.mono_left (closure_mono ((QuantumZipper.fwdHull_mono).1 ht.2))
    obtain ⟨a₂, W₂', hI2⟩ :=
      exists_imgData hW₂ ht₂ (isHPHull_fwdHull hW ht.1) (isMapOut_fwdMap_gen hW ht.1) hd'
    obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
    obtain ⟨hGd, -, -, -, -, hGR⟩ := h.ownExt_props ht (hclr t ht)
    have hKt : fwdHull W t ⊆ H₁ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK₁
    have hb := hown W W₂ t t₂ a₂ W₂' hI2 hW ht.1 hW0H hW₂H hWq hqW hKt hK₂ R _ (r₁ / 2) hR (by positivity)
      hGd (hGR R hR)
    obtain ⟨him, hre, -⟩ := h.deriv_ownExt_driver ht hr₁ (hclr t ht)
    rw [← abs_re_eq_norm.2 him, abs_of_pos hre] at hb
    unfold frzA
    simp only [Function.iterate_one]
    exact le_trans (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ht₂m (by positivity)))) hb
  · -- `E`
    intro t ht
    show _ ≤ |frzImg W' a (W₂ t₂) t - frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ∧
      |frzImg W' a (W₂ t₂) t - frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ≤ _
    rw [h.frzA_zero ht]
    unfold frzImg
    rw [add_sub_cancel_right]
    have hpos := htipγ t ht
    have hneg : (fwdMap W' (a t) ((W₂ t₂ : ℝ) : ℂ)).re < 0 := by linarith [hγt.trans_le hpos]
    rw [abs_of_neg hneg]
    refine ⟨hγD.trans ((min_le_left _ _).trans hpos), ?_⟩
    exact (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hupper _ v₀ hv₀ t ht)).trans (by linarith)
  · -- `E_{j,m}`
    intro t ht m
    show _ ≤ |frzImg W' a ((fwdMap W₂ t₂ (p m)).re + W₂ t₂) t -
        frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ∧
      |frzImg W' a ((fwdMap W₂ t₂ (p m)).re + W₂ t₂) t - frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ≤ _
    rw [h.frzA_zero ht]
    unfold frzImg
    rw [add_sub_cancel_right]
    have has := hI.mapsTo_clock_Icc ht
    rw [abs_re_eq_norm.2 (fwdMap_real_im hW'c (hvm m) has)]
    exact ⟨hγD.trans (hgapm m t ht), (hupper _ (vm m) (hvm m) t ht).trans (by linarith [hζmZ m])⟩
  · -- `E_{k,m}`
    intro t ht m
    exact hpair _ _ (vm m) v₀ (hvm m) hv₀ (hgapm m) hgap₀ ((hζ0m m).1.trans' (min_le_left _ _)) (hζ0m m).2 t ht
  · -- `C_{mk}`
    intro t ht m k hmk
    refine hpair _ _ (vm k) (vm m) (hvm k) (hvm m) (hgapm k) (hgapm m) (hζmk m k hmk) ?_ t ht
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hζmZ m, hζmZ k])
  · -- `A_{k,1}`
    exact hscale _ v₀ hv₀ hgap₀
  · -- `B_{m,1}`
    intro t ht m
    exact hscale _ (vm m) (hvm m) (hgapm m) t ht
  · -- the marks avoid the other source
    intro m heq
    have h1 := (hζ0m m).1
    have heq' : ((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) = W₂ t₂ := heq
    rw [heq', sub_self, norm_zero] at h1
    linarith
  · -- the marks are distinct
    intro m k heq
    by_contra hmk
    have h1 := hζmk m k hmk
    have heq' : ((fwdMap W₂ t₂ (p m)).re + W₂ t₂ : ℝ) = (fwdMap W₂ t₂ (p k)).re + W₂ t₂ := heq
    rw [heq', sub_self, norm_zero] at h1
    linarith
  · -- the image driver
    have has := hI.mapsTo_clock_Icc ht
    have h := abs_driver_sub_le hW'c has.1 (by positivity : (0 : ℝ) < 6 * R₀) (himg t ht) hW'0b ⟨has.1, le_rfl⟩
    rw [sub_zero] at h
    show |W' (a t)| ≤ _
    exact h.trans (by linarith)

section Hyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open QuantumZipper (drive)

/-- **The hypotheses of (D10) from the enclosure data, frozen curve on the left** (`exists_frzD10Hyp` with
`exists_twoCurveD9_left`). -/
theorem exists_frzD10Hyp_left {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {n : ℕ} {p : Fin n → ℝ}
    (hpH : ∀ m, Disjoint (ball (p m : ℂ) (2 * d)) (H₁ ∪ H₂)) (hpinj : Function.Injective p) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam L : ℝ, ∀ [Nonempty Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (rr : Fin n → ℝ)
      (W₂ : ℝ → ℝ) (t₂ : ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ),
      (∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω)) →
      (∀ ω, (S ω : ℝ) ≤ T ω) → (∀ ω, T ω ≤ Tm) → (∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁) →
      Continuous W₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → 0 < t₂ → t₂ ≤ Tm → fwdHull W₂ t₂ ⊆ H₂ →
      FrzD10Hyp κ B W' a (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) rr (W₂ t₂)
        (fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂) S T r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, hmain⟩ := exists_twoCurveD9_left hH₁ hH₂ hδ hsepδ hd hq hqH hpH hpinj Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀ hγ Γ lam Tm
  refine ⟨r, a₀, γ, Γ, lam, L, fun κ B W' a rr W₂ t₂ S T hown hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ => ?_⟩
  have hD := fun ω => hmain (drive κ B ω) W₂ t₂ (T ω) (a ω) (W' ω) κ rr (hown ω) hW₂ hW₂H hqW ht₂ ht₂m (hTm ω)
    (hK₁ ω) hK₂
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  exact ⟨⟨hown, hST, hTm, fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₀).ne, (hD ω₀).inj,
    fun ω => (hD ω).d9, hL⟩, fun ω t ht => (hD ω).drv t ht⟩

end Hyp

end InteractingSLE.ZhanGT4
