/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Upper
import InteractingSLE.Spec.ZhanGT4.MTildeBoundField

/-!
# (D9): the constants of a protected rectangle, assembled

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, Part A.1.3 (`ig1_followup_proofs.txt` L300–L340, ruling
R38): "There are deterministic constants `0 < c < C < ∞`, depending on the enclosures and original marked configuration,
such that `c ≤ M(s, t) ≤ C`" and "In a Lean implementation it is convenient to package the paragraph as a deterministic
compactness lemma for two separated hull enclosures."

The configuration: curve `1` (driver `W`, `W 0 = 0`) grows on `[0, T]` inside an enclosure `H₁`; curve `2` (driver
`W₂`) is frozen at time `t₂ > 0` with hull `A = K₂(t₂)` inside `H₂`; the enclosures are `2δ`-separated; the real point
`q > 0` and the marks `p_m` are protected (`B(·, 2d)` misses `H₁ ∪ H₂`); curve 2 starts to the right of `q`. The image
chain `(a, W')` of curve 1 in the chart `φ = g^{(2)}_{t₂}` (`OwnData`) carries the other source `ζ₀ = W₂(t₂)` and the
marks `ζ_m = φ(p_m)`.

* `exists_twoCurveD9`: there are constants `r, a₀, γ, Γ, λ`, depending only on `H₁, H₂, δ, q, d, p` and a time bound
  `Tm`, such that for every such configuration with `t₂, T ≤ Tm` all (D9) bounds hold on `[0, T]`
  (`FrzData.D9Const`), the marks are alive for the image chain up to `a(T)`, distinct and different from `ζ₀`
  (`TwoCurveD9`): PROVE-ZHAN-GT4-A6's lower bounds and this packet's upper bounds (`D9Upper`).
* `exists_scaleOK`: every such family of constants admits a scale `L` (`ScaleOK`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull)

/-- A finite family of positive reals has a positive lower bound (`1/(1 + Σ 1/f_i)`). -/
theorem exists_pos_le_of_fintype {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c > 0, ∀ i, c ≤ f i := by
  set S := ∑ i, 1 / f i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hf i)).le
  refine ⟨1 / (1 + S), by positivity, fun i => ?_⟩
  have hi : 1 / f i ≤ S :=
    Finset.single_le_sum (f := fun i => 1 / f i) (fun j _ => (one_div_pos.2 (hf j)).le) (Finset.mem_univ i)
  rw [div_le_iff₀ (by positivity)]
  have h0 := hf i
  have h1 : f i * (1 / f i) = 1 := by field_simp
  nlinarith

/-- A point of the closure of `S` is not in an open ball missing `S`. -/
theorem notMem_ball_of_mem_closure {S : Set ℂ} {c : ℂ} {ρ : ℝ} (hd : Disjoint (ball c ρ) S) {x : ℂ}
    (hx : x ∈ closure S) : x ∉ ball c ρ := fun hxb => Set.disjoint_left.1 (hd.closure_right isOpen_ball) hxb hx

/-- **The deterministic facts of a frozen-curve configuration** used by the stopped martingale of `M̃`
(`FrzMartHyp`): the (D9) constants on `[0, T]`, the other source and the marks alive for the image chain up to
`a(T)`, the marks distinct and different from the other source. -/
structure TwoCurveD9 {n : ℕ} (d : FrzData n) (A : Set ℂ) (T r a₀ γ Γ lam : ℝ) : Prop where
  d9 : d.D9Const A T r a₀ γ Γ lam
  alive₀ : ∃ v, IsForwardSol d.W' d.ζ₀ (d.a T) v
  alive : ∀ m, ∃ v, IsForwardSol d.W' (d.ζ m) (d.a T) v
  ne : ∀ m, d.ζ m ≠ d.ζ₀
  inj : Function.Injective d.ζ
  /-- The image driver `A_{j,0} = W'(a(t))` is bounded by `Γ`. -/
  drv : ∀ t ∈ Icc (0 : ℝ) T, |d.W' (d.a t)| ≤ Γ

/-- **(D9) for a protected rectangle, assembled** (§A.1.3). For separated enclosures `H₁, H₂`, a protected point
`q > 0` and protected injective marks `p_m`, and a time bound `Tm`, there are constants `r, a₀, γ, Γ, λ` such that for
every driver `W` of curve 1 (`W 0 = 0`, hull in `H₁` up to `T ≤ Tm`) and every frozen curve 2 (start in `closure H₂`
to the right of `q`, hull in `H₂` at the time `0 < t₂ ≤ Tm`), the frozen data with the other source `ζ₀ = W₂(t₂)` and
the marks `ζ_m = g^{(2)}_{t₂}(p_m)` satisfy `TwoCurveD9`. -/
theorem exists_twoCurveD9 {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {n : ℕ} {p : Fin n → ℝ}
    (hpH : ∀ m, Disjoint (ball (p m : ℂ) (2 * d)) (H₁ ∪ H₂)) (hpinj : Function.Injective p) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam : ℝ, 0 < r ∧ 0 < a₀ ∧ 0 < γ ∧
      ∀ (W W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ) (κ : ℝ) (rr : Fin n → ℝ),
      OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' → Continuous W₂ →
      ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → q < W₂ 0 → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
      fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      TwoCurveD9 (⟨W, W', a, fun z => fwdMap W₂ t₂ z + W₂ t₂, κ, rr, W₂ t₂,
        fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂⟩ : FrzData n) (fwdHull W₂ t₂) T r a₀ γ Γ lam := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hsepδ z hz a ha
  have hsep : Disjoint (closure H₁) (closure H₂) := disjoint_closure_of_le_norm_sub hδ hsepδ
  have h2d : (0 : ℝ) < 2 * d := by linarith
  obtain ⟨r₁, hr₁, hcl₁⟩ := exists_le_norm_fwdMap_uniform hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hcl₂⟩ := exists_le_norm_fwdMap_uniform hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  obtain ⟨γt, hγt, htip⟩ := exists_le_re_fwdMap_tip_right hH₁ hH₂ hsep hd hqH
  choose γp hγp hprot using fun m => exists_le_norm_fwdMap_protected hH₁ hH₂ hsep hd (hpH m)
  obtain ⟨γo, hγo, hown⟩ := exists_exp_le_norm_deriv_refl_own hH₁ hH₂ hδ hsepδ hd hqH
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
  have hWq : W 0 < q := by rw [hW0]; exact hq
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  -- clearances
  have hclr : ∀ t ∈ Icc (0 : ℝ) T,
      Disjoint (ball (W t : ℂ) r₁) ((fun z => fwdMap W t z + W t) '' fwdHull W₂ t₂) := fun t ht =>
    OwnData.disjoint_ball_of_le_norm fun z hz => hcl₁ W hW hW0H T hK₁ t ht z (hK₂ hz)
  have hcl₂' : ∀ z ∈ fwdHull W T, r₂ ≤ ‖fwdMap W₂ t₂ z‖ := fun z hz =>
    hcl₂ W₂ hW₂ hW₂H t₂ hK₂ t₂ ⟨ht₂0, le_rfl⟩ z (hK₁ hz)
  -- the start of curve 1 in the frozen chart
  obtain ⟨u0, hu0, hW'0⟩ := hI.exists_start_alive hW₂ ht₂0 (by linarith : W 0 ≠ W₂ 0)
  have hu0neg := QuantumZipper.re_neg_isForwardSol_real hW₂ ht₂0 hu0 (by linarith) t₂ ⟨ht₂0, le_rfl⟩
  have hne0 : W₂ t₂ ≠ W' 0 := by rw [hW'0]; linarith
  have halive₀ : ∀ s ∈ Icc (0 : ℝ) T, ∃ v, IsForwardSol W' ((W₂ t₂ : ℝ) : ℂ) (a s) v := fun s hs =>
    hI.exists_tip_alive hr₂ hcl₂' hne0 hs
  have htipγ := htip W W₂ t₂ T a W' r₂ hI hW₂ ht₂0 hW₂H hWq hqW hK₁ hK₂ hr₂ hcl₂'
  have hprot' := fun m => hprot m W W₂ t₂ T a W' hI hW₂ ht₂0 hW₂H hK₁ hK₂
  -- the gaps of the image chain
  have hgap₀ : ∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ((W₂ t₂ : ℝ) : ℂ)‖ := fun s hs =>
    (min_le_left _ _).trans ((htipγ s hs).trans (Complex.re_le_norm _))
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
    rw [abs_of_pos (hγt.trans_le hpos)]
    refine ⟨hγD.trans ((min_le_left _ _).trans hpos), ?_⟩
    exact ((Complex.re_le_norm _).trans (hupper _ v₀ hv₀ t ht)).trans (by linarith)
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

/-- **A scale for given (D9) constants.** For `r, a₀, γ > 0` and any `Γ, λ, T` there is `L` with `ScaleOK`
(`L = max λ 0 + M`, `M` the sum of the finitely many numerical thresholds; `e^L ≥ 1 + L`). -/
theorem exists_scaleOK {r a₀ γ : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hγ : 0 < γ) (Γ lam T : ℝ) :
    ∃ L, ScaleOK r a₀ γ Γ lam T L := by
  have hc := clrRad_pos hr ha₀
  have hrb : 0 ≤ rateBound r a₀ := by unfold rateBound; positivity
  have t1 : 0 ≤ 2 / a₀ := by positivity
  have t2 : 0 ≤ 2 / γ := by positivity
  have t3 : 0 ≤ 384 / r := by positivity
  have t4 : 0 ≤ 3072 / r ^ 2 := by positivity
  have t5 : 0 ≤ 49152 / r ^ 3 := by positivity
  have t6 : 0 ≤ |Γ| + γ / 2 := by positivity
  have t7 : 0 ≤ 24 * 96 ^ 2 / (clrRad r a₀ * a₀) := by positivity
  have t8 : 0 ≤ 96 * 96 ^ 2 / (clrRad r a₀ ^ 2 * a₀) := by positivity
  have t9 : 0 ≤ 2 / γ ^ 2 := by positivity
  have t10 : 0 ≤ |T| * rateBound r a₀ := by positivity
  set M := 2 / a₀ + 2 / γ + 96 + 384 / r + 3072 / r ^ 2 + 49152 / r ^ 3 + (|Γ| + γ / 2) +
    24 * 96 ^ 2 / (clrRad r a₀ * a₀) + 96 * 96 ^ 2 / (clrRad r a₀ ^ 2 * a₀) + 2 / γ ^ 2 + rateBound r a₀ +
    |T| * rateBound r a₀ with hM
  have hM0 : 0 ≤ M := by positivity
  set L := max lam 0 + M with hL
  have hl0 : 0 ≤ max lam 0 := le_max_right _ _
  have hexp : 1 + M ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hle : ∀ K, K ≤ M → K ≤ Real.exp L := fun K hK => by linarith
  have hneg : ∀ c, 0 < c → 2 / c ≤ M → Real.exp (-L) ≤ c / 2 := by
    intro c hc0 hcM
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact hle _ hcM
  refine ⟨L, by positivity, by linarith [le_max_left lam 0], hneg a₀ ha₀ (by linarith),
    hneg γ hγ (by linarith), hle _ (by linarith), hle _ (by linarith), hle _ (by linarith),
    hle _ (by linarith), hle _ (by linarith [le_abs_self Γ]), hle _ (by linarith), hle _ (by linarith),
    hle _ (by linarith), ?_, hle _ (by linarith),
    hle _ (by linarith [mul_le_mul_of_nonneg_right (le_abs_self T) hrb])⟩
  have h1 : Real.exp lam ≤ Real.exp (max lam 0) := Real.exp_le_exp.2 (le_max_left _ _)
  have h2 : 2 / γ ^ 2 ≤ 1 + M := by linarith
  have h3 : 1 + M ≤ Real.exp M := by have := Real.add_one_le_exp M; linarith
  rw [hL, Real.exp_add]
  calc 2 * Real.exp lam / γ ^ 2 = Real.exp lam * (2 / γ ^ 2) := by ring
    _ ≤ Real.exp (max lam 0) * Real.exp M :=
        mul_le_mul h1 (h2.trans h3) (by positivity) (Real.exp_pos _).le

end InteractingSLE.ZhanGT4
