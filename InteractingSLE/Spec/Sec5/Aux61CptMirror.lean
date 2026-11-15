/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptJump
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Spec.Sec7.LocalExtAHL7

/-!
# The mirror reflection: counterflow collars from chart-side data

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). COMPARE's collar lemmas start from a counterflow collar
`(ξ₀, δ)` in the chart `Ψ = revChart w s` and reflect `c ∘ Ψ⁻¹`. The selection of the per-outcome family is made on
the restart chart's side, so here the roles are exchanged: on a chart half-disc `ℍ ∩ B(v, ε)` with

* a bound `‖Ψ(c⁻¹ y)‖ ≤ M`, and
* boundary limits `c⁻¹ y → z(t) ∈ R(K_s)` at every real `t` of the ball (physical points on the counterflow hull),

the transition `Ξ = Ψ ∘ c⁻¹` reflects (`exists_isPosReflect_mirror`, through `tendsto_im_revChart_of_bounded`), and its
reflection `G` is a local biholomorphism near `v` with `G(v) = ξ₀` real, which gives the counterflow collar about `ξ₀`
(`mirror_collar`): `Ψ⁻¹` maps `ℍ ∩ B(ξ₀, δ)` into the chart domain, `c ∘ Ψ⁻¹ → v` at `ξ₀`, and every real point of
`B(ξ₀, δ)` is nonzero, has a nonzero inverse boundary value, and its physical point `cfBdry` is one of the `z(t)`.

Deterministic; R48/R77 respected. Nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu Aux61TwoS Aux61Cmp

/-! ### Local preimages of a positive reflection -/

/-- **Local surjectivity of a positive reflection**: a ball about `G(v)` is covered by `G` from the ball about `v`,
upper points from upper points and real points from real points. -/
theorem IsPosReflect.exists_local_preimage {Ξ G : ℂ → ℂ} {v r : ℝ} (h : IsPosReflect Ξ G v r) :
    ∃ δ > 0, ∀ ζ ∈ ball (G v) δ, ∃ t ∈ ball (v : ℂ) r, G t = ζ ∧ (0 < ζ.im → 0 < t.im) ∧
      (ζ.im = 0 → t.im = 0) := by
  have hvB : ((v : ℝ) : ℂ) ∈ ball (v : ℂ) r := mem_ball_self h.pos
  have hd0 : deriv G v ≠ 0 := fun h0 => by
    have := (h.deriv_pos hvB).2; rw [h0, zero_re] at this; exact lt_irrefl _ this
  have hs' : HasStrictDerivAt G (deriv G v) v :=
    (h.diff.analyticAt (isOpen_ball.mem_nhds hvB)).hasStrictDerivAt
  set g := hs'.localInverse G (deriv G v) v hd0 with hgdef
  have hg1 : g (G v) = v := (hs'.eventually_left_inverse hd0).self_of_nhds
  have hgc : ContinuousAt g (G v) := (hs'.to_localInverse hd0).hasDerivAt.continuousAt
  have hgB : ∀ᶠ y in 𝓝 (G v), g y ∈ ball (v : ℂ) r := by
    have := hgc.tendsto
    rw [hg1] at this
    exact this (isOpen_ball.mem_nhds hvB)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (hgB.and (hs'.eventually_right_inverse hd0))
  refine ⟨δ, hδ, fun ζ hζ => ?_⟩
  obtain ⟨hB, hr⟩ := hsub hζ
  have hcB : conj (g ζ) ∈ ball (v : ℂ) r := QuantumZipper.CA.conj_mem_ball_ofReal hB
  have hconj : G (conj (g ζ)) = conj ζ := by rw [h.conj_eq _ hB, hr]
  refine ⟨g ζ, hB, hr, fun hpos => ?_, fun h0 => ?_⟩
  · by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with hlt | heq
    · have hcH : conj (g ζ) ∈ H := show (0 : ℝ) < (conj (g ζ)).im by rw [conj_im]; linarith
      have h2 : 0 < (G (conj (g ζ))).im := h.conf.2.2.2.1 ⟨hcH, hcB⟩
      rw [hconj, conj_im] at h2
      linarith
    · have h3 := h.conf.2.2.1 (g ζ) hB heq
      rw [hr] at h3
      linarith
  · rcases lt_trichotomy (g ζ).im 0 with hlt | heq | hgt
    · have hcH : conj (g ζ) ∈ H := show (0 : ℝ) < (conj (g ζ)).im by rw [conj_im]; linarith
      have h2 : 0 < (G (conj (g ζ))).im := h.conf.2.2.2.1 ⟨hcH, hcB⟩
      rw [hconj, conj_im, h0] at h2
      linarith
    · exact heq
    · have h2 : 0 < (G (g ζ)).im := h.conf.2.2.2.1 ⟨hgt, hB⟩
      rw [hr, h0] at h2
      exact absurd h2 (lt_irrefl _)

section Mirror

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s)

include hw hs in
/-- **`Im Ψ → 0` at hull points along a set with bounded chart image.** -/
theorem tendsto_im_revChart_of_bounded {ι : Type*} {l : Filter ι} {f : ι → ℂ} {z₀ : ℂ}
    (hz₀ : z₀ ∈ negInv '' fwdHull w s) (hf : Tendsto f l (𝓝 z₀))
    (hfD : ∀ᶠ i in l, f i ∈ H \ negInv '' fwdHull w s) {M : ℝ}
    (hM : ∀ᶠ i in l, ‖revChart w s (f i)‖ ≤ M) :
    Tendsto (fun i => (revChart w s (f i)).im) l (𝓝 0) := by
  obtain ⟨y₀, hy₀, rfl⟩ := hz₀
  have hy₀H : y₀ ∈ H := hy₀.1
  have hz0 : negInv y₀ ≠ 0 := negInv_ne_zero (Aux8Inf.ne_zero_of_mem_H' hy₀H)
  have hN : Tendsto (fun i => negInv (f i)) l (𝓝[H \ fwdHull w s] y₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hfD.mono fun i hi => negInv_notMem_fwdHull hi⟩
    have h := (continuousAt_negInv hz0).tendsto.comp hf
    rwa [Function.comp_def, negInv_negInv'] at h
  have hu := (LocalExt.tendsto_im_fwdMap_of_mem_fwdHull hw hs hy₀).comp hN
  have hsq : Tendsto (fun i => (fwdMap w s (negInv (f i))).im * M ^ 2) l (𝓝 0) := by
    have := hu.mul_const (M ^ 2)
    simpa only [Function.comp_apply, zero_mul] using this
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards [hfD] with i hi
    exact (revChart_mem_H hw hs hi).le
  · filter_upwards [hfD, hM] with i hi hMi
    have hwH := negInv_notMem_fwdHull hi
    set u := fwdMap w s (negInv (f i)) with hudef
    have huH : u ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hwH
    have hu0 : u ≠ 0 := Aux8Inf.ne_zero_of_mem_H' huH
    have hR : revChart w s (f i) = negInv u := rfl
    have hnorm : ‖negInv u‖ ^ 2 = (Complex.normSq u)⁻¹ := by
      rw [norm_negInv, inv_pow, ← Complex.normSq_eq_norm_sq]
    have him : (negInv u).im = u.im * ‖negInv u‖ ^ 2 := by
      rw [hnorm, negInv, neg_im, inv_im, neg_div, neg_neg, div_eq_mul_inv]
    rw [hR, him]
    have hM' : ‖negInv u‖ ^ 2 ≤ M ^ 2 := by
      rw [← hR]
      exact pow_le_pow_left₀ (norm_nonneg _) hMi 2
    exact mul_le_mul_of_nonneg_left hM' (le_of_lt huH)

include hw hw0 hs in
/-- **A chart limit away from `0` has a nonzero counterflow-chart limit**: `‖Ψ(ζ)‖ (‖ζ‖⁻¹ + C) ≥ 1`. -/
theorem ne_zero_of_tendsto_revChart {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ} {z₀ x : ℂ}
    (hz₀ : z₀ ≠ 0) (hf : Tendsto f l (𝓝 z₀)) (hfD : ∀ᶠ i in l, f i ∈ H \ negInv '' fwdHull w s)
    (hx : Tendsto (fun i => revChart w s (f i)) l (𝓝 x)) : x ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fwdMap_sub_le hw hw0 hs
  intro hx0
  rw [hx0] at hx
  have hprod : Tendsto (fun i => ‖revChart w s (f i)‖ * (‖f i‖⁻¹ + C)) l (𝓝 (0 * (‖z₀‖⁻¹ + C))) :=
    (tendsto_norm_zero.comp hx).mul ((hf.norm.inv₀ (norm_ne_zero_iff.2 hz₀)).add_const C)
  rw [zero_mul] at hprod
  have hge : ∀ᶠ i in l, 1 ≤ ‖revChart w s (f i)‖ * (‖f i‖⁻¹ + C) := by
    filter_upwards [hfD] with i hi
    have hwH := negInv_notMem_fwdHull hi
    set u := fwdMap w s (negInv (f i)) with hudef
    have huH : u ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hwH
    have hu0 : 0 < ‖u‖ := norm_pos_iff.2 (Aux8Inf.ne_zero_of_mem_H' huH)
    have hle : ‖u‖ ≤ ‖f i‖⁻¹ + C := by
      have h1 := hC _ hwH
      have h2 : ‖u‖ ≤ ‖negInv (f i)‖ + ‖u - negInv (f i)‖ := by
        have := norm_add_le (negInv (f i)) (u - negInv (f i))
        rwa [add_sub_cancel] at this
      rw [norm_negInv] at h2
      linarith
    have hR : ‖revChart w s (f i)‖ = ‖u‖⁻¹ := norm_negInv u
    rw [hR]
    calc (1 : ℝ) = ‖u‖⁻¹ * ‖u‖ := (inv_mul_cancel₀ hu0.ne').symm
      _ ≤ ‖u‖⁻¹ * (‖f i‖⁻¹ + C) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hu0.le)
  have hlim := ge_of_tendsto hprod hge
  linarith

variable {c : Chart} (hc : c.IsConformal) (hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)

include hw hw0 hs hc hsubK in
/-- **The mirror reflection**: with a bounded counterflow-chart image and hull boundary limits of `c⁻¹` on the real
points of the ball, the transition `Ψ ∘ c⁻¹` has a positive real reflection. -/
theorem exists_isPosReflect_mirror {v ε M : ℝ} (hε : 0 < ε)
    (hbd : ∀ y ∈ H ∩ ball (v : ℂ) ε, ‖revChart w s (c.2.1 y)‖ ≤ M)
    (hland : ∀ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε → ∃ z₀ ∈ negInv '' fwdHull w s,
      Tendsto c.2.1 (𝓝[H] (t : ℂ)) (𝓝 z₀)) :
    ∃ G, IsPosReflect (revChart w s ∘ c.2.1) G v ε := by
  have hmem : ∀ y ∈ H ∩ ball (v : ℂ) ε, c.2.1 y ∈ H \ negInv '' fwdHull w s :=
    fun y hy => hsubK (hc.inv_mem_dom hy.1)
  refine exists_isPosReflect hε ?_ ?_ ?_ ?_
  · intro y hy
    exact ((GlueImg.differentiableAt_revChart hw hs (hmem y hy)).comp_differentiableWithinAt y
      ((hc.1 y hy.1).mono inter_subset_left))
  · intro y hy
    exact revChart_mem_H hw hs (hmem y hy)
  · intro y hy y' hy' he
    have h1 := congrArg (revChartInv w s) he
    simp only [Function.comp_apply] at h1
    rw [revChartInv_revChart hw hw0 hs (hmem y hy), revChartInv_revChart hw hw0 hs (hmem y' hy')] at h1
    exact hc.injOn hy.1 hy'.1 h1
  · intro t ht
    obtain ⟨z₀, hz₀, hlim⟩ := hland t ht
    have hev : ∀ᶠ y in 𝓝[H] (t : ℂ), y ∈ H ∩ ball (v : ℂ) ε :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds ht)
    exact tendsto_im_revChart_of_bounded hw hs hz₀ hlim (hev.mono hmem) (hev.mono hbd)

include hw hw0 hβ hs in
/-- **Inverse boundary value from a chart limit**: if points `f i ∈ ℍ ∖ R(K_s)` tend to `z₀ ≠ 0` and their
counterflow-chart images tend to the real point `x' ≠ 0` from `ℍ`, then `F̄_s(R x') = R z₀`. -/
theorem extendFrom_eq_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ} {z₀ : ℂ} {x' : ℝ}
    (hz₀ : z₀ ≠ 0) (hx' : x' ≠ 0) (hf : Tendsto f l (𝓝 z₀))
    (hfD : ∀ᶠ i in l, f i ∈ H \ negInv '' fwdHull w s)
    (hx : Tendsto (fun i => revChart w s (f i)) l (𝓝 (x' : ℂ))) :
    extendFrom H (fwdMapInv w s) (negInv (x' : ℂ)) = negInv z₀ := by
  have hx₁' : (x' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx'
  have hN : Tendsto (fun i => negInv (revChart w s (f i))) l (𝓝[H] (negInv (x' : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_negInv hx₁').tendsto.comp hx, ?_⟩
    filter_upwards [hfD] with i hi
    exact negInv_mem_H (revChart_mem_H hw hs hi)
  have hbar : negInv (x' : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (negInv_ofReal_im x')
  have hlim1 := ((hβ.hasBdryLimits hw hw0 hs).tendsto hbar).comp hN
  have heq : ∀ᶠ i in l, (fwdMapInv w s ∘ fun i => negInv (revChart w s (f i))) i = negInv (f i) := by
    filter_upwards [hfD] with i hi
    have h := congrArg negInv (revChartInv_revChart hw hw0 hs hi)
    rw [revChartInv, negInv_negInv'] at h
    exact h
  have hlim2 : Tendsto (fun i => negInv (f i)) l (𝓝 (negInv z₀)) :=
    (continuousAt_negInv hz₀).tendsto.comp hf
  exact tendsto_nhds_unique (hlim1.congr' heq) hlim2

include hw hw0 hβ hs hc hsubK in
/-- **The counterflow collar from the mirror reflection** (at the centre `v` of the chart half-disc): `Ψ⁻¹` maps a
half-disc about `ξ₀ = G(v)` into the chart domain, `c ∘ Ψ⁻¹ → v` at `ξ₀`, the physical point of `ξ₀` is `z(v)`, and
every real point of the collar is nonzero with a nonzero inverse boundary value and the physical point of some
`z(t)`. -/
theorem mirror_collar {v ε M : ℝ} (hε : 0 < ε)
    (hbd : ∀ y ∈ H ∩ ball (v : ℂ) ε, ‖revChart w s (c.2.1 y)‖ ≤ M)
    (z : ℝ → ℂ) (hz : ∀ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε → z t ∈ negInv '' fwdHull w s ∧
      Tendsto c.2.1 (𝓝[H] (t : ℂ)) (𝓝 (z t))) :
    ∃ ξ₀ δ : ℝ, 0 < δ ∧
      MapsTo (revChartInv w s) (H ∩ ball (ξ₀ : ℂ) δ) c.dom ∧
      (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
        extendFrom H (fwdMapInv w s) (negInv (x' : ℂ)) ≠ 0 ∧
        ∃ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε ∧ cfBdry w s x' = z t) ∧
      cfBdry w s ξ₀ = z v ∧
      Tendsto (fun ζ => c.1 (revChartInv w s ζ)) (𝓝[H] (ξ₀ : ℂ)) (𝓝 (v : ℂ)) ∧
      Tendsto (fun y => revChart w s (c.2.1 y)) (𝓝[H] (v : ℂ)) (𝓝 (ξ₀ : ℂ)) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_mirror hw hw0 hs hc hsubK hε hbd fun t ht => ⟨z t, (hz t ht).1, (hz t ht).2⟩
  have hmem : ∀ y ∈ H ∩ ball (v : ℂ) ε, c.2.1 y ∈ H \ negInv '' fwdHull w s :=
    fun y hy => hsubK (hc.inv_mem_dom hy.1)
  have hvB : ((v : ℝ) : ℂ) ∈ ball (v : ℂ) ε := mem_ball_self hε
  set ξ₀ : ℝ := (G v).re with hξ₀
  have hGv : G v = (ξ₀ : ℂ) := Complex.ext (by simp [hξ₀]) (by simp [hG.im_eq_zero hvB])
  obtain ⟨δ, hδ, hpre⟩ := Aux61Cpt.IsPosReflect.exists_local_preimage hG
  rw [hGv] at hpre
  -- the physical point at a real point of the chart ball
  have hphys : ∀ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε →
      G t ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (G t)) = negInv (z t) := by
    intro t ht
    have := GlueImg.nhdsWithin_H_neBot t
    have hev : ∀ᶠ y in 𝓝[H] (t : ℂ), y ∈ H ∩ ball (v : ℂ) ε :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds ht)
    have hzt := hz t ht
    have hz0 : z t ≠ 0 := by
      obtain ⟨y₀, hy₀, hy⟩ := hzt.1
      rw [← hy]
      exact negInv_ne_zero (Aux8Inf.ne_zero_of_mem_H' hy₀.1)
    have hGt : (G t).im = 0 := hG.im_eq_zero ht
    have hGt' : G t = ((G t).re : ℂ) := Complex.ext (by simp) (by simp [hGt])
    have hlim : Tendsto (fun y => revChart w s (c.2.1 y)) (𝓝[H] (t : ℂ)) (𝓝 (((G t).re : ℝ) : ℂ)) := by
      rw [← hGt']
      exact hG.tendsto ht
    have hne := ne_zero_of_tendsto_revChart hw hw0 hs hz0 hzt.2 (hev.mono hmem) hlim
    have hre : (G t).re ≠ 0 := fun h0 => hne (by rw [h0, Complex.ofReal_zero])
    refine ⟨fun h0 => hne (by rw [← hGt', h0]), ?_⟩
    rw [hGt']
    exact extendFrom_eq_of_tendsto hw hw0 hβ hs hz0 hre hzt.2 (hev.mono hmem) hlim
  refine ⟨ξ₀, δ, hδ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    obtain ⟨t, htB, hGt, hpos, -⟩ := hpre ζ hζ.2
    have htH : t ∈ H := hpos hζ.1
    have he : revChart w s (c.2.1 t) = ζ := by
      rw [← hGt]
      exact (hG.eqOn ⟨htH, htB⟩).symm
    rw [← he, revChartInv_revChart hw hw0 hs (hmem t ⟨htH, htB⟩)]
    exact hc.inv_mem_dom htH
  · intro x' hx'
    obtain ⟨t, htB, hGt, -, hreal⟩ := hpre x' hx'
    have ht0 : t.im = 0 := hreal (by simp)
    have htr : t = ((t.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [ht0])
    rw [htr] at htB hGt
    obtain ⟨hne, hext⟩ := hphys t.re htB
    rw [hGt] at hne hext
    refine ⟨fun h0 => hne (by rw [h0, Complex.ofReal_zero]), ?_, t.re, htB, ?_⟩
    · rw [hext]
      have hz0 : z t.re ≠ 0 := by
        obtain ⟨y₀, hy₀, hy⟩ := (hz t.re htB).1
        rw [← hy]
        exact negInv_ne_zero (Aux8Inf.ne_zero_of_mem_H' hy₀.1)
      exact negInv_ne_zero hz0
    · rw [cfBdry, hext, negInv_negInv']
  · obtain ⟨-, hext⟩ := hphys v hvB
    rw [hGv] at hext
    rw [cfBdry, hext, negInv_negInv']
  · have hΘ : ∀ y ∈ H ∩ ball (v : ℂ) ε, (fun ζ => c.1 (revChartInv w s ζ)) ((revChart w s ∘ c.2.1) y) = y := by
      intro y hy
      simp only [Function.comp_apply]
      rw [revChartInv_revChart hw hw0 hs (hmem y hy)]
      exact hc.2.2 y hy.1
    have h := hG.tendsto_leftInv (Θ := fun ζ => c.1 (revChartInv w s ζ)) hΘ
    rw [hGv] at h
    exact h.mono_right nhdsWithin_le_nhds
  · have h := hG.tendsto hvB
    rw [hGv] at h
    exact h

end Mirror

end InteractingSLE.Sec5.Aux61Cpt
