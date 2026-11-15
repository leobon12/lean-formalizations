/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSConfig

/-!
# Aux. 61, the two new sides: the seed and the transport along the real line

Packet PROVE-AUX61-TWOSIDES, item (D1), continued. In the configuration `IsTwoSideConfig`:

* `exists_isPosReflect_seed`, `seed_sign`, **`tendsto_log_im_collar`** : the restart chart `Ψ` reflects across the
  collar `(−δ, δ)` with `Ψ(0) = 0`, preserves the sign of real points, and its seed-normalized logarithm has
  imaginary part tending to `0` at every real point of the collar (constant lattice phase, R16/GLUECOND pattern);
* **`seed_limits`** : at a real point `p` whose boundary image `F̄_σ(p) = ξ` is a nonzero real point of the collar,
  `Ξ(y)` tends to a real `x₀` of the sign of `ξ`, and `Im xiLog → 0` (Aux. 57 at the untouched points of both
  charts, plus the collar normalization);
* `xi_ne_zero` : at a good point the reflected value of `Ξ` is not `0` (`0` is the chart tip, the image of `β′(τ)`);
* `exists_left_base`, `exists_right_base`, `isGoodPt_of_left_slit`, `isGoodPt_of_right_slit` : the real points
  between a base point of the collar and a slit point are good;
* **`tendsto_im_xiLog_of_interval`**, **`pos_of_interval`**, **`neg_of_interval`** : along an interval of good
  points, the vanishing of `Im xiLog` and the sign of the reflected value of `Ξ` are transported.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61TwoS

open WangWu (IsProperArc chartAL chartAR)

theorem ofReal_mem_ball_zero_iff {ξ δ : ℝ} : (ξ : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ ↔ |ξ| < δ := by
  rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_zero]

theorem ofReal_re_eq {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz])

/-- The image of a real point untouched by a hull under the forward Loewner map tends to a real point. -/
theorem exists_tendsto_fwdMap_of_disjoint {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {x ρ : ℝ} (hρ : 0 < ρ) (hd : Disjoint (ball (x : ℂ) ρ) (fwdHull w t)) :
    ∃ x₀ : ℝ, Tendsto (fwdMap w t) (𝓝[H] (x : ℂ)) (𝓝 (x₀ : ℂ)) := by
  obtain ⟨G, hG⟩ := Sec7.exists_isBdryReflection (isHPHull_fwdHull hw ht) (isMapOut_fwdMap hw hw0 ht) hρ hd
  have hxB : (x : ℂ) ∈ ball (x : ℂ) (ρ / 2) := mem_ball_self (half_pos hρ)
  have hGc : ContinuousAt G x := (hG.diff.differentiableAt (isOpen_ball.mem_nhds hxB)).continuousAt
  refine ⟨(G x).re - w t, ?_⟩
  have e : (((G x).re - w t : ℝ) : ℂ) = G x - w t := by
    rw [ofReal_sub, ofReal_re_eq hG.im_center]
  rw [e]
  refine ((hGc.tendsto.sub_const _).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with z hz
  rw [hG.eqOn ⟨hz.2, hz.1⟩]
  ring

namespace IsTwoSideConfig

variable {W : ℝ → ℝ} {β β' : ℝ → ℂ} {σ τ : ℝ} {Ω : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {δ : ℝ} {w : ℝ → ℝ}
  {γ : ℝ → ℂ} {t : ℝ}

variable (hc : IsTwoSideConfig W β β' σ τ Ω Ψ Ψi LΨ δ w γ t)
include hc

/-! ### The seed -/

/-- **The seed reflection** of the restart chart across the collar, with `Ψ(0) = 0`. -/
theorem exists_isPosReflect_seed : ∃ GΨ, IsPosReflect Ψ GΨ 0 δ ∧ GΨ 0 = 0 := by
  have hcol : H ∩ ball ((0 : ℝ) : ℂ) δ ⊆ Ω := by rw [ofReal_zero]; exact hc.collar
  obtain ⟨G, hG⟩ := exists_isPosReflect (Ξ := Ψ) (v := 0) hc.δpos (hc.diff.mono hcol)
    (hc.mapsTo.mono_left hcol) (hc.injOn.mono hcol) fun x hx => hc.tendsto_im x (ofReal_mem_ball_zero_iff.1 hx)
  refine ⟨G, hG, ?_⟩
  have h1 := hG.tendsto (y := 0) (mem_ball_self hc.δpos)
  have hNB := GlueImg.nhdsWithin_H_neBot 0
  rw [ofReal_zero] at h1 hNB
  exact tendsto_nhds_unique h1 hc.tendsto_zero

/-- **The seed preserves the sign of the collar's real points.** -/
theorem seed_sign {GΨ : ℂ → ℂ} (hG : IsPosReflect Ψ GΨ 0 δ) (h0 : GΨ 0 = 0) {ξ : ℝ} (hξ : |ξ| < δ) :
    (GΨ ξ).im = 0 ∧ (ξ < 0 → (GΨ ξ).re < 0) ∧ (0 < ξ → 0 < (GΨ ξ).re) := by
  set g : ℝ → ℝ := fun s => (GΨ s).re with hgdef
  have hD : ∀ s ∈ Ioo (-δ) δ, (s : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ := fun s hs =>
    ofReal_mem_ball_zero_iff.2 (abs_lt.2 hs)
  have hder : ∀ s ∈ Ioo (-δ) δ, HasDerivAt g (deriv GΨ s).re s := fun s hs =>
    ((hG.diff.differentiableAt (isOpen_ball.mem_nhds (hD s hs))).hasDerivAt).real_of_complex
  have hmono : StrictMonoOn g (Ioo (-δ) δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
      fun s hs => ?_
    rw [interior_Ioo] at hs
    rw [(hder s hs).deriv]
    exact (hG.deriv_pos (hD s hs)).2
  have hξI : ξ ∈ Ioo (-δ) δ := abs_lt.1 hξ
  have h0I : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith [hc.δpos], hc.δpos⟩
  have hg0 : g 0 = 0 := by simp [hgdef, h0]
  refine ⟨hG.im_eq_zero (hD ξ hξI), fun hneg => ?_, fun hpos => ?_⟩
  · have := hmono hξI h0I hneg; rwa [hg0] at this
  · have := hmono h0I hξI hpos; rwa [hg0] at this

/-- **The collar normalization**: the seed-normalized logarithm of `Ψ′` has imaginary part tending to `0` at every
real point of the collar (its integer is constant along the collar and `0` at the seed). -/
theorem tendsto_log_im_collar {ξ : ℝ} (hξ : |ξ| < δ) :
    Tendsto (fun z => (LΨ z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨GΨ, hG, -⟩ := hc.exists_isPosReflect_seed
  have hcol : H ∩ ball ((0 : ℝ) : ℂ) δ ⊆ Ω := by rw [ofReal_zero]; exact hc.collar
  refine GlueImg.tendsto_zero_of_forall_tendsto_two_pi_int (I := Ioo (-δ) δ) isPreconnected_Ioo (fun x hx => ?_)
    (x₀ := 0) ⟨by linarith [hc.δpos], hc.δpos⟩ (by rw [ofReal_zero]; exact hc.log_seed) (abs_lt.1 hξ)
  obtain ⟨r', hr', hsub⟩ := exists_ball_subset_ball (ofReal_mem_ball_zero_iff.2 (abs_lt.2 hx))
  have hG' := hG.of_subset hr' hsub
  have hsub' : H ∩ ball (x : ℂ) r' ⊆ Ω := fun z hz => hcol ⟨hz.1, hsub hz.2⟩
  exact hG'.exists_int_tendsto_im (hc.log.1.continuousOn.mono hsub') fun z hz => hc.log.2 z (hsub' hz)

/-! ### The real points of the time-`σ` flow chart -/

/-- A real point whose boundary image is in `ℍ` is sent onto the flow hull. -/
theorem extendFrom_mem_hull_of_mem_H {x : ℝ} (hx : extendFrom H (fwdMapInv W σ) x ∈ H) :
    extendFrom H (fwdMapInv W σ) x ∈ fwdHull W σ := by
  by_contra hn
  have hNB := GlueImg.nhdsWithin_H_neBot x
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hfc : ContinuousAt (fwdMap W σ) (extendFrom H (fwdMapInv W σ) x) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hc.hW hc.σ_nonneg).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc.hW hc.σ_nonneg).mem_nhds ⟨hx, hn⟩)).continuousAt
  have h1 := hfc.tendsto.comp (hB.tendsto hxH)
  have h2 : Tendsto (fun y => fwdMap W σ (fwdMapInv W σ y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg hy).symm
  have h3 := tendsto_nhds_unique h1 h2
  have h4 : (0 : ℝ) < (fwdMap W σ (extendFrom H (fwdMapInv W σ) x)).im :=
    QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hW hc.σ_nonneg ⟨hx, hn⟩
  rw [h3] at h4
  simp at h4

/-- A real point strictly between the left base point and `0` is good (a non-tip slit point). -/
theorem isGoodPt_of_slit {x : ℝ} (hL : chartAL W σ < x) (hR : x < chartAR W σ) (hx0 : x ≠ 0) :
    IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := by
  have hH := GlueImg.extendFrom_mem_H_of_chartAL_lt hc.trace hc.arc hc.hW hc.hW0 hc.σpos hL hR
  have hK := hc.extendFrom_mem_hull_of_mem_H hH
  rw [hc.hullσ_eq] at hK
  obtain ⟨u, hu, hue⟩ := hK
  refine Or.inr ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 fun huσ => hx0 ?_⟩, hue.symm⟩
  rw [huσ] at hue
  exact WangWu.eq_zero_of_extendFrom_eq_tip hc.trace hc.arc hc.hW hc.hW0 hc.σpos hue.symm

/-- **The left base**: a real point `v₁` left of the left base point whose boundary image is a negative real point of
the collar, all points of `[v₁, chartAL]` being good. -/
theorem exists_left_base : ∃ v₁ : ℝ, v₁ < chartAL W σ ∧
    (∀ x ∈ Icc v₁ (chartAL W σ), IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x)) ∧
    ∃ ξ : ℝ, extendFrom H (fwdMapInv W σ) v₁ = ξ ∧ ξ < 0 ∧ |ξ| < δ := by
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  set a := chartAL W σ with hadef
  have ha0 := GlueImg.extendFrom_chartAL_eq_zero hc.trace hc.arc hc.hW hc.hW0 hc.σpos
  obtain ⟨η, hη, hηsub⟩ := Metric.continuousWithinAt_iff.1
    (hB.continuousOn (a : ℂ) (mem_Hbar_of_im_eq_zero (by simp))) δ hc.δpos
  have hsmall : ∀ x : ℝ, |x - a| < η → ‖extendFrom H (fwdMapInv W σ) x‖ < δ := fun x hx => by
    have := @hηsub (x : ℂ) (mem_Hbar_of_im_eq_zero (by simp)) (by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx)
    rwa [ha0, dist_zero_right] at this
  have hgood : ∀ x ∈ Icc (a - η / 2) a, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := by
    intro x hx
    have hxs : |x - a| < η := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    rcases hx.2.lt_or_eq with hlt | heq
    · obtain ⟨him, -⟩ := GlueImg.re_extendFrom_neg_of_lt_chartAL hc.trace hc.arc hc.hW hc.hW0 hc.σpos hlt
      refine Or.inl ⟨him, (abs_re_le_norm _).trans_lt (hsmall x hxs)⟩
    · rw [heq, ha0]
      exact Or.inl ⟨Complex.zero_im, by rw [Complex.zero_re, abs_zero]; exact hc.δpos⟩
  refine ⟨a - η / 2, by linarith, hgood, ?_⟩
  obtain ⟨him, hre⟩ := GlueImg.re_extendFrom_neg_of_lt_chartAL hc.trace hc.arc hc.hW hc.hW0 hc.σpos
    (show a - η / 2 < chartAL W σ by linarith)
  refine ⟨(extendFrom H (fwdMapInv W σ) (a - η / 2 : ℝ)).re, (ofReal_re_eq him).symm, hre,
    (abs_re_le_norm _).trans_lt (hsmall _ ?_)⟩
  rw [abs_lt]; constructor <;> linarith

/-- **The right base** (mirror of `exists_left_base`). -/
theorem exists_right_base : ∃ v₁ : ℝ, chartAR W σ < v₁ ∧
    (∀ x ∈ Icc (chartAR W σ) v₁, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x)) ∧
    ∃ ξ : ℝ, extendFrom H (fwdMapInv W σ) v₁ = ξ ∧ 0 < ξ ∧ |ξ| < δ := by
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  set a := chartAR W σ with hadef
  have ha0 := GlueImg.extendFrom_chartAR_eq_zero hc.trace hc.arc hc.hW hc.hW0 hc.σpos
  obtain ⟨η, hη, hηsub⟩ := Metric.continuousWithinAt_iff.1
    (hB.continuousOn (a : ℂ) (mem_Hbar_of_im_eq_zero (by simp))) δ hc.δpos
  have hsmall : ∀ x : ℝ, |x - a| < η → ‖extendFrom H (fwdMapInv W σ) x‖ < δ := fun x hx => by
    have := @hηsub (x : ℂ) (mem_Hbar_of_im_eq_zero (by simp)) (by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx)
    rwa [ha0, dist_zero_right] at this
  have hgood : ∀ x ∈ Icc a (a + η / 2), IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := by
    intro x hx
    have hxs : |x - a| < η := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    rcases hx.1.lt_or_eq with hlt | heq
    · obtain ⟨him, -⟩ := GlueImg.re_extendFrom_pos_of_chartAR_lt hc.trace hc.arc hc.hW hc.hW0 hc.σpos hlt
      refine Or.inl ⟨him, (abs_re_le_norm _).trans_lt (hsmall x hxs)⟩
    · rw [← heq, ha0]
      exact Or.inl ⟨Complex.zero_im, by rw [Complex.zero_re, abs_zero]; exact hc.δpos⟩
  refine ⟨a + η / 2, by linarith, hgood, ?_⟩
  obtain ⟨him, hre⟩ := GlueImg.re_extendFrom_pos_of_chartAR_lt hc.trace hc.arc hc.hW hc.hW0 hc.σpos
    (show chartAR W σ < a + η / 2 by linarith)
  refine ⟨(extendFrom H (fwdMapInv W σ) (a + η / 2 : ℝ)).re, (ofReal_re_eq him).symm, hre,
    (abs_re_le_norm _).trans_lt (hsmall _ ?_)⟩
  rw [abs_lt]; constructor <;> linarith

/-! ### Values of `Ξ` at good points -/

/-- **The reflected value of `Ξ` at a good point is not `0`**: `0` is the chart tip, whose preimage is `β′(τ)`. -/
theorem xi_ne_zero {p ε : ℝ} {G : ℂ → ℂ} (hp : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p))
    (hreg : ∀ y ∈ H ∩ ball (p : ℂ) ε, fwdMapInv W σ y ∈ Ω ∧ Ψ (fwdMapInv W σ y) ∉ fwdHull w t)
    (hG : IsPosReflect (xiMap w t Ψ W σ) G p ε) : G p ≠ 0 := by
  intro h0
  have hpB : (p : ℂ) ∈ ball (p : ℂ) ε := mem_ball_self hG.pos
  have hNB := GlueImg.nhdsWithin_H_neBot p
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  have hpH : (p : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hev : ∀ᶠ y in 𝓝[H] (p : ℂ), y ∈ H ∩ ball (p : ℂ) ε :=
    inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hpB)
  -- `Ψ ∘ F_σ → γ(t) = Ψ(β′ τ)`
  have h1 : Tendsto (fun y => fwdMapInv w t (xiMap w t Ψ W σ y)) (𝓝[H] (p : ℂ)) (𝓝 (γ t)) := by
    have := hG.tendsto_nhdsWithin hpB
    rw [h0] at this
    exact (hc.ctrace.tendsto_fwdMapInv_tip hc.hw hc.hw0 hc.t_nonneg).comp this
  have h2 : Tendsto (fun y => Ψ (fwdMapInv W σ y)) (𝓝[H] (p : ℂ)) (𝓝 (Ψ (β' τ))) := by
    rw [← hc.tip]
    refine h1.congr' ?_
    filter_upwards [hev] with y hy
    exact QuantumZipper.RS.fwdMapInv_fwdMap hc.hw hc.hw0 hc.t_nonneg ⟨hc.mapsTo (hreg y hy).1, (hreg y hy).2⟩
  have hτΩ : β' τ ∈ Ω := hc.cont_mapsTo ⟨hc.σpos.trans hc.σ_lt_τ, le_rfl⟩
  have hiC : ContinuousAt Ψi (Ψ (β' τ)) := hc.inv_contOn.continuousAt
    (QuantumZipper.isOpen_H.mem_nhds (hc.mapsTo hτΩ))
  have h3 : Tendsto (fun y => fwdMapInv W σ y) (𝓝[H] (p : ℂ)) (𝓝 (β' τ)) := by
    have := hiC.tendsto.comp h2
    rw [hc.inv_apply _ hτΩ] at this
    refine this.congr' ?_
    filter_upwards [hev] with y hy
    exact hc.inv_apply _ (hreg y hy).1
  have h4 := tendsto_nhds_unique (hB.tendsto hpH) h3
  rcases hp with ⟨him, -⟩ | ⟨u, hu, hue⟩
  · have := hc.dom_subset hτΩ
    rw [← h4] at this
    exact absurd him (ne_of_gt this)
  · rw [hue, ← hc.cont_eqOn ⟨hu.1.le, hu.2.le⟩] at h4
    have := hc.cont_injOn ⟨hu.1.le, hu.2.le.trans hc.σ_lt_τ.le⟩ ⟨(hc.σpos.trans hc.σ_lt_τ).le, le_rfl⟩ h4
    linarith [hu.2, hc.σ_lt_τ]

/-- At a good point `Ξ` tends to a nonzero real number. -/
theorem exists_tendsto_xi_real {p : ℝ} (hp : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p)) :
    ∃ x₀ : ℝ, x₀ ≠ 0 ∧ Tendsto (xiMap w t Ψ W σ) (𝓝[H] (p : ℂ)) (𝓝 (x₀ : ℂ)) := by
  obtain ⟨ε, hε, hreg, G, hG⟩ := hc.exists_isPosReflect_xi hp
  have hpB : (p : ℂ) ∈ ball (p : ℂ) ε := mem_ball_self hε
  refine ⟨(G p).re, fun h => hc.xi_ne_zero hp hreg hG ?_, ?_⟩
  · rw [← ofReal_re_eq (hG.im_eq_zero hpB), h, ofReal_zero]
  · rw [ofReal_re_eq (hG.im_eq_zero hpB)]
    exact hG.tendsto hpB

/-- At a good point `Im xiLog` tends to a multiple of `2π`. -/
theorem exists_int_tendsto_xiLog {p : ℝ} (hp : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p)) :
    ∃ n : ℤ, Tendsto (fun y => (xiLog w t Ψ LΨ W σ y).im) (𝓝[H] (p : ℂ)) (𝓝 (2 * π * n)) := by
  obtain ⟨ε, hε, hreg, G, hG⟩ := hc.exists_isPosReflect_xi hp
  exact hG.exists_int_tendsto_im (hc.continuousOn_xiLog inter_subset_left hreg) fun y hy =>
    hc.exp_xiLog hy.1 (hreg y hy).1 (hreg y hy).2

/-! ### The seed limits -/

/-- **The seed limits.** At a real point `p` whose boundary image is a nonzero real point `ξ` of the collar, `Ξ`
tends to a real point of the sign of `ξ`, and `Im xiLog → 0`. -/
theorem seed_limits {p ξ : ℝ} (hq : extendFrom H (fwdMapInv W σ) p = ξ) (hξ : |ξ| < δ) (hξ0 : ξ ≠ 0) :
    ∃ x₀ : ℝ, (ξ < 0 → x₀ < 0) ∧ (0 < ξ → 0 < x₀) ∧
      Tendsto (xiMap w t Ψ W σ) (𝓝[H] (p : ℂ)) (𝓝 (x₀ : ℂ)) ∧
      Tendsto (fun y => (xiLog w t Ψ LΨ W σ y).im) (𝓝[H] (p : ℂ)) (𝓝 0) := by
  have hgood : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p) := Or.inl ⟨by rw [hq]; simp, by rw [hq]; simpa⟩
  obtain ⟨ε, hε, hreg, -, -⟩ := hc.exists_isPosReflect_xi hgood
  have hpB : (p : ℂ) ∈ ball (p : ℂ) ε := mem_ball_self hε
  have hNB := GlueImg.nhdsWithin_H_neBot p
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  have hpH : (p : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hev : ∀ᶠ y in 𝓝[H] (p : ℂ), y ∈ H ∩ ball (p : ℂ) ε :=
    inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hpB)
  -- `F_σ → ξ` within `ℍ`
  have hF : Tendsto (fwdMapInv W σ) (𝓝[H] (p : ℂ)) (𝓝[H] (ξ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by rw [← hq]; exact hB.tendsto hpH, eventually_nhdsWithin_of_forall
      fun y hy => (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg hy).1⟩
  -- the seed reflection: `Ψ ∘ F_σ → ζ = GΨ(ξ)`, real of the sign of `ξ`
  obtain ⟨GΨ, hGΨ, hGΨ0⟩ := hc.exists_isPosReflect_seed
  have hξB : (ξ : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ := ofReal_mem_ball_zero_iff.2 hξ
  obtain ⟨hζim, hζneg, hζpos⟩ := hc.seed_sign hGΨ hGΨ0 hξ
  set ζ : ℝ := (GΨ ξ).re with hζdef
  have hζe : (ζ : ℂ) = GΨ ξ := ofReal_re_eq hζim
  have hζ0 : ζ ≠ 0 := by
    rcases lt_or_gt_of_ne hξ0 with h | h
    · exact (hζneg h).ne
    · exact (hζpos h).ne'
  have hΨF : Tendsto (fun y => Ψ (fwdMapInv W σ y)) (𝓝[H] (p : ℂ)) (𝓝[H] (ζ : ℂ)) := by
    rw [hζe]
    refine tendsto_nhdsWithin_iff.2 ⟨(hGΨ.tendsto hξB).comp hF, ?_⟩
    filter_upwards [hev] with y hy
    exact hc.mapsTo (hreg y hy).1
  -- the chart is untouched at `ζ`
  obtain ⟨ρ, hρ, hd⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hc.ctrace hc.carc hc.t_nonneg hζ0
  obtain ⟨x₀, hx₀⟩ := exists_tendsto_fwdMap_of_disjoint hc.hw hc.hw0 hc.t_nonneg hρ hd
  have hΞ : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (p : ℂ)) (𝓝 (x₀ : ℂ)) := hx₀.comp hΨF
  -- `F̄_t(x₀) = ζ`
  have hBt := hc.ctrace.hasBdryLimits hc.hw hc.hw0 hc.t_nonneg
  have hx₀H : (x₀ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hΞH : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (p : ℂ)) (𝓝[H] (x₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hΞ, ?_⟩
    filter_upwards [hev] with y hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hw hc.t_nonneg ⟨hc.mapsTo (hreg y hy).1, (hreg y hy).2⟩
  have hFt : extendFrom H (fwdMapInv w t) x₀ = ζ := by
    have h1 := (hBt.tendsto hx₀H).comp hΞH
    have h2 : Tendsto (fun y => fwdMapInv w t (xiMap w t Ψ W σ y)) (𝓝[H] (p : ℂ)) (𝓝 (ζ : ℂ)) := by
      refine (hΨF.mono_right nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hev] with y hy
      exact (QuantumZipper.RS.fwdMapInv_fwdMap hc.hw hc.hw0 hc.t_nonneg
        ⟨hc.mapsTo (hreg y hy).1, (hreg y hy).2⟩).symm
    exact tendsto_nhds_unique h1 h2
  have hcases := GlueImg.extendFrom_real_cases hc.ctrace hc.carc hc.hw hc.hw0 hc.tpos
    (x := x₀) (by rw [hFt]; simp)
  rw [hFt, ofReal_re] at hcases
  refine ⟨x₀, fun hneg => ?_, fun hpos => ?_, hΞ, ?_⟩
  · rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hζ0
    · exact absurd h (not_lt.2 (hζneg hneg).le)
    · exact h.trans_le (WangWu.chartAL_nonpos hc.hw hc.t_nonneg)
  · rcases hcases with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h hζ0
    · exact (WangWu.chartAR_nonneg hc.hw hc.t_nonneg).trans_lt h
    · exact absurd h (not_lt.2 (hζpos hpos).le)
  -- the branch
  have hLt : Tendsto (fun y => (logDerivFwd w t (Ψ (fwdMapInv W σ y))).im) (𝓝[H] (p : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hc.hw hc.t_nonneg)
      (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hc.hw hc.hw0 hc.t_nonneg)
      (isMapOut_fwdMap hc.hw hc.hw0 hc.t_nonneg) hρ hd).comp hΨF
  have hLΨ : Tendsto (fun y => (LΨ (fwdMapInv W σ y)).im) (𝓝[H] (p : ℂ)) (𝓝 0) :=
    (hc.tendsto_log_im_collar hξ).comp hF
  obtain ⟨ρ', hρ', hd'⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hc.trace hc.arc hc.σ_nonneg hξ0
  have hLσ : Tendsto (fun y => (logDerivFwd W σ (fwdMapInv W σ y)).im) (𝓝[H] (p : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hc.hW hc.σ_nonneg)
      (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hc.hW hc.hW0 hc.σ_nonneg)
      (isMapOut_fwdMap hc.hW hc.hW0 hc.σ_nonneg) hρ' hd').comp hF
  have := (hLt.add hLΨ).sub hLσ
  simp only [add_zero, sub_zero] at this
  refine this.congr fun y => ?_
  simp only [xiLog, sub_im, add_im]

/-! ### Transport along an interval of good points -/

/-- **The branch is transported** along an interval of good points: `Im xiLog → 0` at one end gives it at every
point. -/
theorem tendsto_im_xiLog_of_interval {a b : ℝ}
    (hgood : ∀ x ∈ Icc a b, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (h₀ : Tendsto (fun y => (xiLog w t Ψ LΨ W σ y).im) (𝓝[H] (x₀ : ℂ)) (𝓝 0)) {x : ℝ} (hx : x ∈ Icc a b) :
    Tendsto (fun y => (xiLog w t Ψ LΨ W σ y).im) (𝓝[H] (x : ℂ)) (𝓝 0) :=
  GlueImg.tendsto_zero_of_forall_tendsto_two_pi_int isPreconnected_Icc
    (fun x hx => hc.exists_int_tendsto_xiLog (hgood x hx)) hx₀ h₀ hx

/-- **The sign is transported** along an interval of good points (positive version). -/
theorem pos_of_interval {a b : ℝ}
    (hgood : ∀ x ∈ Icc a b, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x)) {x₀ p₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (hp₀ : 0 < p₀) (h₀ : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ))) {x p : ℝ} (hx : x ∈ Icc a b)
    (h : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) : 0 < p :=
  GlueImg.pos_of_forall_tendsto_real isPreconnected_Icc
    (fun x hx => hc.exists_tendsto_xi_real (hgood x hx)) hx₀ hp₀ h₀ hx h

/-- **The sign is transported** along an interval of good points (negative version). -/
theorem neg_of_interval {a b : ℝ}
    (hgood : ∀ x ∈ Icc a b, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x)) {x₀ p₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (hp₀ : p₀ < 0) (h₀ : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ))) {x p : ℝ} (hx : x ∈ Icc a b)
    (h : Tendsto (xiMap w t Ψ W σ) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) : p < 0 :=
  GlueImg.neg_of_forall_tendsto_real isPreconnected_Icc
    (fun x hx => hc.exists_tendsto_xi_real (hgood x hx)) hx₀ hp₀ h₀ hx h

end IsTwoSideConfig

end InteractingSLE.Sec5.Aux61TwoS
