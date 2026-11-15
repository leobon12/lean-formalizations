/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA1Left
import InteractingSLE.Spec.Zhan.ConstDriftAlive

/-!
# Zhan's A.1 (R80): the (D9) constants of the large-curve direction with the small curve's accesses as marks

Packet PROVE-A1-LARGEDENS. Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L300–L341, R38):
"There are deterministic constants `0 < c < C < ∞`, depending on the enclosures and original marked configuration, such
that `c ≤ M(s, t) ≤ C`"; follow-up 4 §2.5 item 1 (R71): "a deterministic `m > 0` and `C < ∞` with `m ≤ h'_j ≤ C` …
throughout a real neighborhood containing the own driver and all own seed coordinates".

In the large-curve direction the growing curve is the large curve and the frozen curve is the small curve stopped at a
positive time; the frozen-chart marks are the small curve's **boundary accesses** (the images `x±`/`y±` of its
seeds, the image of an ordinary mark) and its tip. The landed (D9) assembly with the frozen curve on the left
(`exists_twoCurveD9_left`, `exists_frzD10Hyp_left`) takes the marks to be frozen images `g_{t₂}(p_m)` of protected
real points; seed accesses are not of that form (a seed sits at the source of the frozen curve, inside its enclosure).
Here the marks are arbitrary real points of the frozen chart **to the left of the image of the protected point `q`**,
with a given mutual separation `ν` and bound `M`:

* **`exists_le_neg_re_fwdMap_of_lt_left`**: such a point is alive for the image chain and its image stays at least `γ`
  to the left of the image driver (order of the real flow below the protected point's image, whose gap is
  `exists_le_norm_fwdMap_protected`; the tip case is `exists_le_neg_re_fwdMap_tip_left`);
* **`exists_twoCurveD9_left_marks`**: uniform (D9) constants (`TwoCurveD9`) for every such configuration;
* **`exists_frzD10Hyp_left_marks`**: the frozen-curve hypotheses `FrzD10Hyp` of the (D10) line, hence (through
  `A1LargeDens.isSeedSampleLaw_of_frzD10Hyp`) the large-curve direction's one-sample law.

The proof of `exists_twoCurveD9_left_marks` is the landed proof of `exists_twoCurveD9_left` with its protected-mark part
(frozen-chain gaps of `p_m`, the contraction of their mutual distances) replaced by the given separation and bound.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1LargeDens

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull)
open InteractingSLE.Zhan.LowerGap (exists_isForwardSol_of_gt_of_continuousOn)

/-- **(D9), separation of an image mark left of the protected point, frozen curve on the left.** If
`W₂ 0 < q < W₁ 0` and `ζ` lies left of the frozen image `g^{(2)}_{t₂}(q)` of the protected point, then `ζ` is alive for
the image chain and its image lies at least `γ` to the left of the image driver: `γ ≤ −f̃_{a(s)}(ζ)`. -/
theorem exists_le_neg_re_fwdMap_of_lt_left {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    (hsep : Disjoint (closure H₁) (closure H₂)) {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ γ > 0, ∀ (W₁ W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ),
      ImgData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
      Continuous W₂ → 0 ≤ t₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → q < W₁ 0 →
      fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ → ∀ ζ : ℝ, ζ < (fwdMap W₂ t₂ q).re + W₂ t₂ →
      ∀ s ∈ Icc (0 : ℝ) T, (∃ v, IsForwardSol W' (ζ : ℂ) (a s) v) ∧ γ ≤ -(fwdMap W' (a s) ζ).re := by
  obtain ⟨γ, hγ, hcore⟩ := exists_le_norm_fwdMap_protected hH₁ hH₂ hsep hd hqH
  refine ⟨γ, hγ, ?_⟩
  intro W₁ W₂ t₂ T a W' h hW₂ ht₂ hW₂H hW₂q hqx₁ hK₁ hK₂ ζ hζ s hs
  obtain ⟨⟨vp, hvp⟩, hle⟩ := hcore W₁ W₂ t₂ T a W' h hW₂ ht₂ hW₂H hK₁ hK₂ s hs
  obtain ⟨u0, hu0, hW'0⟩ := h.exists_start_alive hW₂ ht₂ (by linarith)
  have h2d : 0 < 2 * d := by linarith
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₂ (show q ≠ W₂ 0 by linarith) ht₂ h2d
    (hqH.mono_right (hK₂.trans subset_union_right))
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hord₂ := QuantumZipper.F1.isForwardSol_lt_of_lt ht₂ hqx₁ huq hu0 t₂ ht₂mem
  rw [fwdMap_eq_of_isForwardSol hW₂ huq ht₂mem] at hvp hle hζ
  set p : ℝ := (uq t₂).re + W₂ t₂ with hpdef
  have hp0p : p < W' 0 := by rw [hW'0, hpdef]; linarith
  have hτ0 : 0 ≤ a s := (h.mapsTo_clock_Icc hs).1
  have hτmem : a s ∈ Icc (0 : ℝ) (a s) := ⟨hτ0, le_rfl⟩
  have hvpim : (vp (a s)).im = 0 := im_eq_zero_of_isForwardSol_real h.contW' hvp hτmem
  have hvpneg : (vp (a s)).re < 0 :=
    QuantumZipper.re_neg_isForwardSol_real h.contW' hτ0 hvp hp0p (a s) hτmem
  obtain ⟨vζ, hvζ⟩ := exists_isForwardSol_of_gt_of_continuousOn hτ0 h.contW'.continuousOn hp0p hζ hvp
  refine ⟨⟨vζ, hvζ⟩, ?_⟩
  have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hτ0 hζ hvζ hvp (a s) hτmem
  rw [fwdMap_eq_of_isForwardSol h.contW' hvp hτmem] at hle
  rw [fwdMap_eq_of_isForwardSol h.contW' hvζ hτmem]
  have hnorm : ‖vp (a s)‖ = -(vp (a s)).re := by
    have : vp (a s) = (((vp (a s)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hvpim])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by simpa using hvpneg)]
    simp
  rw [hnorm] at hle
  linarith

/-- **(D9) for a protected rectangle, frozen curve on the left, marks left of the protected point** (variant of
`exists_twoCurveD9_left`): for separated enclosures, a protected point `q < 0`, a separation `ν > 0`, a bound `M` and a
time bound `Tm`, uniform constants such that every configuration with curve `2` frozen at `0 < t₂ ≤ Tm` in `H₂` and
starting left of `q`, and every family of frozen-chart marks `ζ_m` left of `g^{(2)}_{t₂}(q)`, bounded by `M`,
`ν`-separated from the frozen tip and from each other, satisfies `TwoCurveD9`. -/
theorem exists_twoCurveD9_left_marks {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ}
    (hδ : 0 < δ) (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {ν M : ℝ} (hν : 0 < ν) (n : ℕ) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam : ℝ, 0 < r ∧ 0 < a₀ ∧ 0 < γ ∧
      ∀ (W W₂ : ℝ → ℝ) (t₂ T : ℝ) (a W' : ℝ → ℝ) (κ : ℝ) (rr : Fin n → ℝ) (ζ : Fin n → ℝ),
      OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' → Continuous W₂ →
      ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
      fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
      (∀ m, ζ m < (fwdMap W₂ t₂ q).re + W₂ t₂) → (∀ m, |ζ m| ≤ M) → (∀ m, ν ≤ |ζ m - W₂ t₂|) →
      (∀ m k, m ≠ k → ν ≤ |ζ m - ζ k|) →
      TwoCurveD9 (⟨W, W', a, fun z => fwdMap W₂ t₂ z + W₂ t₂, κ, rr, W₂ t₂, ζ⟩ : FrzData n) (fwdHull W₂ t₂) T
        r a₀ γ Γ lam := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hsepδ z hz a ha
  have hsep : Disjoint (closure H₁) (closure H₂) := disjoint_closure_of_le_norm_sub hδ hsepδ
  have h2d : (0 : ℝ) < 2 * d := by linarith
  obtain ⟨r₁, hr₁, hcl₁⟩ := exists_le_norm_fwdMap_uniform hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hcl₂⟩ := exists_le_norm_fwdMap_uniform hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  obtain ⟨γt, hγt, htip⟩ := exists_le_neg_re_fwdMap_tip_left hH₁ hH₂ hsep hd hqH
  obtain ⟨γm, hγm, hleft⟩ := exists_le_neg_re_fwdMap_of_lt_left hH₁ hH₂ hsep hd hqH
  obtain ⟨γo, hγo, hown⟩ := exists_exp_le_norm_deriv_refl_own_left hH₁ hH₂ hδ hsepδ hd hqH
  obtain ⟨C₀, hC₀⟩ := (hH₁.2.1.union hH₂.2.1).exists_norm_le
  set R₀ := max C₀ 1 with hR₀def
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : closure (H₁ ∪ H₂) ⊆ closedBall ((0 : ℝ) : ℂ) R₀ :=
    isClosed_closedBall.closure_subset_iff.2 fun z hz => by
      rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right]; exact (hC₀ z hz).trans (le_max_left _ _)
  -- the gap constant of the image chain
  set γ₀ := min γt γm with hγ₀def
  have hγ₀ : 0 < γ₀ := lt_min hγt hγm
  set cζ := ν with hcζdef
  have hcζ : 0 < cζ := hν
  set Z := |M| + 7 * R₀ with hZdef
  have hZ0 : 0 ≤ |M| := abs_nonneg M
  refine ⟨r₁, Real.exp (-(2 / γo ^ 2 * Tm)), min γ₀ (cζ * Real.exp (-(2 / γ₀ ^ 2 * Tm))),
    max (Z + 72 * R₀) (2 * Z * Real.exp (2 / γ₀ ^ 2 * Tm)), 2 / γ₀ ^ 2 * Tm, hr₁, Real.exp_pos _,
    lt_min hγ₀ (by positivity), ?_⟩
  intro W W₂ t₂ T a W' κ rr ζ h hW₂ hW₂H hqW ht₂ ht₂m hTm hK₁ hK₂ hζq hζM hζν hζνmk
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
  have hleft' := fun m => hleft W W₂ t₂ T a W' hI hW₂ ht₂0 hW₂H hqW hWq hK₁ hK₂ (ζ m) (hζq m)
  -- the gaps of the image chain
  have hgap₀ : ∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ((W₂ t₂ : ℝ) : ℂ)‖ := fun s hs =>
    (min_le_left _ _).trans ((htipγ s hs).trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)))
  have hgapm : ∀ m, ∀ s ∈ Icc (0 : ℝ) T, γ₀ ≤ ‖fwdMap W' (a s) ((ζ m : ℝ) : ℂ)‖ := fun m s hs =>
    (min_le_right _ _).trans (((hleft' m s hs).2).trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)))
  obtain ⟨v₀, hv₀⟩ := halive₀ T hTmem
  choose vm hvm using fun m => (hleft' m T hTmem).1
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
  have ht₂mem : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂0, le_rfl⟩
  have hζ₀Z : |W₂ t₂| ≤ Z := by
    have := abs_driver_sub_le hW₂ ht₂0 hR₀ hA2 hW₂0 ht₂mem
    rw [sub_zero] at this; linarith
  have hζmZ : ∀ m, |ζ m| ≤ Z := fun m => by linarith [hζM m, le_abs_self M]
  have hζ0m : ∀ m, cζ ≤ ‖((W₂ t₂ : ℝ) : ℂ) - ((ζ m : ℝ) : ℂ)‖ ∧
      ‖((W₂ t₂ : ℝ) : ℂ) - ((ζ m : ℝ) : ℂ)‖ ≤ 2 * Z := by
    intro m
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    refine ⟨hζν m, ?_⟩
    calc |ζ m - W₂ t₂| ≤ |ζ m| + |W₂ t₂| := abs_sub _ _
      _ ≤ 2 * Z := by linarith [hζmZ m]
  have hζmk : ∀ m k, m ≠ k → cζ ≤ ‖((ζ m : ℝ) : ℂ) - ((ζ k : ℝ) : ℂ)‖ := by
    intro m k hmk
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hζνmk m k hmk
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
    show _ ≤ |frzImg W' a (ζ m) t -
        frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ∧
      |frzImg W' a (ζ m) t - frzA W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) 0 t| ≤ _
    rw [h.frzA_zero ht]
    unfold frzImg
    rw [add_sub_cancel_right]
    have has := hI.mapsTo_clock_Icc ht
    rw [abs_re_eq_norm.2 (fwdMap_real_im hW'c (hvm m) has)]
    exact ⟨hγD.trans (hgapm m t ht), (hupper _ (vm m) (hvm m) t ht).trans (by linarith [hζmZ m])⟩
  · -- `E_{k,m}`
    intro t ht m
    exact hpair _ _ (vm m) v₀ (hvm m) hv₀ (hgapm m) hgap₀ (hζ0m m).1 (hζ0m m).2 t ht
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
    have heq' : (ζ m : ℝ) = W₂ t₂ := heq
    rw [heq', sub_self, norm_zero] at h1
    linarith
  · -- the marks are distinct
    intro m k heq
    by_contra hmk
    have h1 := hζmk m k hmk
    have heq' : (ζ m : ℝ) = ζ k := heq
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

/-- **The hypotheses of (D10) from the enclosure data, frozen curve on the left, marks left of the protected point**
(`exists_frzD10Hyp_left` with `exists_twoCurveD9_left_marks`). -/
theorem exists_frzD10Hyp_left_marks {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {ν M : ℝ} (hν : 0 < ν) (n : ℕ) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam L : ℝ, ∀ [Nonempty Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (rr : Fin n → ℝ)
      (ζ : Fin n → ℝ) (W₂ : ℝ → ℝ) (t₂ : ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ),
      (∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω)) →
      (∀ ω, (S ω : ℝ) ≤ T ω) → (∀ ω, T ω ≤ Tm) → (∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁) →
      Continuous W₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₂ 0 < q → 0 < t₂ → t₂ ≤ Tm → fwdHull W₂ t₂ ⊆ H₂ →
      (∀ m, ζ m < (fwdMap W₂ t₂ q).re + W₂ t₂) → (∀ m, |ζ m| ≤ M) → (∀ m, ν ≤ |ζ m - W₂ t₂|) →
      (∀ m k, m ≠ k → ν ≤ |ζ m - ζ k|) →
      FrzD10Hyp κ B W' a (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) rr (W₂ t₂) ζ S T r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, hmain⟩ :=
    exists_twoCurveD9_left_marks hH₁ hH₂ hδ hsepδ hd hq hqH (M := M) hν n Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀ hγ Γ lam Tm
  refine ⟨r, a₀, γ, Γ, lam, L, fun κ B W' a rr ζ W₂ t₂ S T hown hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ hζq hζM hζν
    hζνmk => ?_⟩
  have hD := fun ω => hmain (drive κ B ω) W₂ t₂ (T ω) (a ω) (W' ω) κ rr ζ (hown ω) hW₂ hW₂H hqW ht₂ ht₂m (hTm ω)
    (hK₁ ω) hK₂ hζq hζM hζν hζνmk
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  exact ⟨⟨hown, hST, hTm, fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₀).ne, (hD ω₀).inj,
    fun ω => (hD ω).d9, hL⟩, fun ω t ht => (hD ω).drv t ht⟩

end Hyp

end InteractingSLE.ZhanGT4.A1LargeDens
