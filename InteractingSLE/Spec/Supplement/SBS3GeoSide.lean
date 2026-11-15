/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3EntryPositive
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftSide
import InteractingSLE.Spec.Supplement.SB2FinConfig

/-!
# Lemma S3: the old chart preserves the side of the second path

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification p. 580, "The free left collar of S2 is also in this
*joint* unbounded component"). Deterministic.

* `projU`, `lowExt`: a map on the closed upper half-plane continued below the axis by vertical translation;
* `eq_of_g_eq_untouched`: a point of `ℍ̄` sent by a left entry chart's inverse extension to an untouched original
  real point `y < L` is the chart coordinate `e(y)`;
* **`image_leftSide_inter_H_subset`**: the inverse extension `g` of a left entry chart maps the open left side of
  S2's lift `γ` (in `ℍ`) into the open left side of the post-entrance second arc `β(t_L + ·)`. The continued map
  sends the preconnected left side of `γ` off the closed curve of `β(t_L + ·)` (injectivity above the axis; below it
  the left side lies left of `0`, and negative coordinates go to untouched reals left of `L`), and hits its
  lower-left quadrant.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3.Geo

open Supp9B (IsProperCurve leftSide rightSide closedRightSide lowerLeft)

/-- The projection of `ℂ` onto the closed upper half-plane `re w + i max(im w, 0)`. -/
def projU (w : ℂ) : ℂ := (w.re : ℂ) + ((max w.im 0 : ℝ) : ℂ) * I

theorem continuous_projU : Continuous projU := by
  unfold projU
  exact (continuous_ofReal.comp continuous_re).add
    ((continuous_ofReal.comp (continuous_im.max continuous_const)).mul continuous_const)

theorem projU_im_nonneg (w : ℂ) : 0 ≤ (projU w).im := by
  simp [projU]

theorem projU_of_pos {w : ℂ} (hw : 0 < w.im) : projU w = w :=
  Complex.ext (by simp [projU]) (by simp [projU, max_eq_left hw.le])

theorem projU_of_nonpos {w : ℂ} (hw : w.im ≤ 0) : projU w = (w.re : ℂ) :=
  Complex.ext (by simp [projU]) (by simp [projU, max_eq_right hw])

/-- A map on the closed upper half-plane continued below the real axis by vertical translation. -/
def lowExt (g : ℂ → ℂ) (w : ℂ) : ℂ := g (projU w) + ((min w.im 0 : ℝ) : ℂ) * I

theorem continuous_lowExt {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) : Continuous (lowExt g) := by
  unfold lowExt
  exact (hgc.comp_continuous continuous_projU projU_im_nonneg).add
    ((continuous_ofReal.comp (continuous_im.min continuous_const)).mul continuous_const)

theorem lowExt_of_pos {g : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im) : lowExt g w = g w := by
  simp [lowExt, projU_of_pos hw, min_eq_right hw.le]

theorem lowExt_of_nonpos {g : ℂ → ℂ} {w : ℂ} (hw : w.im ≤ 0) :
    lowExt g w = g (w.re : ℂ) + (w.im : ℂ) * I := by
  simp [lowExt, projU_of_nonpos hw, min_eq_left hw]

/-- **Preimages of an untouched original real point** under a left entry chart: a point `w` of `ℍ̄` with `g(w) = y`,
`y < L`, is the chart coordinate `e(y)`. -/
theorem eq_of_g_eq_untouched {A : Set ℂ} {L : ℝ} {c : Chart} (hD : IsDomainChart (H \ fillH A) c)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {e : ℝ → ℝ}
    (hlim : ∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) {w : ℂ} (hw : 0 ≤ w.im) {y : ℝ} (hy : y < L)
    (hgw : g w = (y : ℂ)) : w = (e y : ℂ) := by
  have hgH : ∀ u ∈ H, g u ∈ H := fun u hu => by
    rw [hgi hu]; exact (hD.inv_mem hu).1
  have hT : Tendsto g (𝓝[H] w) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall hgH⟩
    have h1 := (hgc w hw).mono (fun u (hu : u ∈ H) => (le_of_lt hu : 0 ≤ u.im))
    rw [← hgw]
    exact h1.tendsto
  have hcomp : Tendsto (fun u => c.1 (g u)) (𝓝[H] w) (𝓝 (e y : ℂ)) := (hlim y hy).comp hT
  have hid : Tendsto (fun u => c.1 (g u)) (𝓝[H] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [hgi hu]; exact (hD.fwd_inv hu).symm
  have hne : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hw
  exact tendsto_nhds_unique hid hcomp

/-- **The old chart preserves the side of the second path** (Lemma S3's free left collar, p. 580). Let `c` be a left
entry chart of `A = p([0, 1])` with inverse extension `g`, let `β` be a proper curve whose post-entrance arc
`β(t_L + ·)` from `L = min(A ∩ ℝ)` has the proper lift `γ` (`g ∘ γ = β(t_L + ·)`, `γ(0) = 0`). Then `g` maps the
open left side of `γ`, in `ℍ`, into the open left side of `β(t_L + ·)`.

Proof. Continue `g` below the axis by vertical translation (`lowExt`). On the left side `Z` of `γ` this map avoids the
closed curve of `β(t_L + ·)`: above the axis by injectivity and the lift, on and below it because `Z` lies left of
`0` there and `g` sends negative coordinates to untouched original reals left of `L`, whose only preimages are those
coordinates. The image of the preconnected `Z` contains a point of the lower-left quadrant at `L`. -/
theorem image_leftSide_inter_H_subset {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    {c : Chart} {g : ℂ → ℂ} (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {β : ℝ≥0 → ℂ} (hβ : IsProperCurve β) {tL : ℝ≥0} (htL : β tL = realMin (p '' Icc 0 1))
    {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hlift : ∀ s, g (γ s) = β (tL + s)) :
    g '' (leftSide γ ∩ H) ⊆ leftSide (postCurve β tL) := by
  set A := p '' Icc 0 1 with hAdef
  set L := realMin A with hLdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hD := hc.1
  obtain ⟨e, hlim, -, hge, hsurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  have hγ0' : (γ 0).im = 0 := by rw [hγ0]; simp
  have hβ''p : IsProperCurve (postCurve β tL) := isProperCurve_postCurve hβ
  have hβ''0 : postCurve β tL 0 = (L : ℂ) := by
    show β (tL + 0) = _
    rw [add_zero, htL]
  have hneg : ∀ x : ℝ, x < 0 → ∃ y < L, g (x : ℂ) = (y : ℂ) ∧ e y = x := fun x hx => by
    obtain ⟨y, hy, hey⟩ := hsurj x hx
    exact ⟨y, hy, by rw [← hey]; exact (hge y hy).2, hey⟩
  have hgH : ∀ u ∈ H, g u ∈ H \ fillH A := fun u hu => by
    rw [hgi hu]; exact hD.inv_mem hu
  -- `γ` meets `β(t_L + ·)`'s values in `D_A` only in `ℍ`
  have hnotrange : ∀ w ∈ leftSide γ, ∀ s : ℝ≥0, lowExt g w ≠ postCurve β tL s := by
    intro w hwZ s hws
    have hwS : w ∉ seedRayClosure γ := connectedComponentIn_subset _ _ hwZ
    rcases lt_or_ge 0 w.im with hpos | hnonpos
    · rw [lowExt_of_pos hpos] at hws
      have hgw := hgH w hpos
      have hgs : g (γ s) = g w := by rw [hlift s]; exact hws.symm
      rcases (hγ.2.2.1 s).lt_or_eq with hsH | hs0
      · have := (hgi.symm.injOn_iff.1 hD.isConformal.injOn) (show γ s ∈ H from hsH) hpos hgs
        exact hwS (Or.inl ⟨s, this⟩)
      · have hr := FinRel.g_ofReal_mem hD hgc hgi (γ s).re
        have hγs : ((γ s).re : ℂ) = γ s := Complex.ext rfl (by simp [hs0.symm])
        rw [hγs, hgs] at hr
        rcases hr with hA | hR
        · rw [hAc.isClosed.closure_eq] at hA
          exact hgw.2 ⟨hgw.1, Or.inl (subset_closure hA)⟩
        · have h1 : (0 : ℝ) < (g w).im := hgw.1
          rw [show (g w).im = 0 from hR] at h1
          exact lt_irrefl _ h1
    · have hre := re_lt_of_mem_leftSide hγ hγ0' hwZ hnonpos
      rw [hγ0, Complex.zero_re] at hre
      obtain ⟨y, hy, hgy, hey⟩ := hneg w.re hre
      rw [lowExt_of_nonpos hnonpos, hgy] at hws
      have hsim : 0 ≤ (postCurve β tL s).im := hβ''p.2.2.1 s
      have hwim : w.im = 0 := by
        refine le_antisymm hnonpos ?_
        have := congrArg Complex.im hws
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add] at this
        linarith
      have hval : g (γ s) = (y : ℂ) := by
        rw [hlift s]
        show postCurve β tL s = _
        rw [← hws, hwim]; simp
      have heq := eq_of_g_eq_untouched hD hgc hgi hlim (hγ.2.2.1 s) hy hval
      have hw : w = (w.re : ℂ) := Complex.ext rfl (by simp [hwim])
      exact hwS (Or.inl ⟨s, by rw [heq, hey, ← hw]⟩)
  have hsub : lowExt g '' leftSide γ ⊆ (seedRayClosure (postCurve β tL))ᶜ := by
    rintro _ ⟨w, hwZ, rfl⟩ (⟨s, hs⟩ | ⟨hre, him⟩)
    · exact hnotrange w hwZ s hs.symm
    · rw [hβ''0, ofReal_re] at hre
      rw [hβ''0, ofReal_im] at him
      rcases lt_or_ge 0 w.im with hpos | hnonpos
      · rw [lowExt_of_pos hpos] at him
        exact absurd (hgH w hpos).1 (not_lt.2 him)
      · have hre' := re_lt_of_mem_leftSide hγ hγ0' hwZ hnonpos
        rw [hγ0, Complex.zero_re] at hre'
        obtain ⟨y, hy, hgy, -⟩ := hneg w.re hre'
        rw [lowExt_of_nonpos hnonpos, hgy] at hre
        simp at hre
        linarith
  have href : γ 0 - 1 - I ∈ leftSide γ :=
    mem_connectedComponentIn (Supp9B.lowerLeft_subset_compl hγ.2.2.1 (Supp9B.left_ref_mem_lowerLeft hγ0'))
  have hmem : lowExt g (γ 0 - 1 - I) ∈ leftSide (postCurve β tL) := by
    have him : (γ 0 - 1 - I).im ≤ 0 := by rw [hγ0]; simp
    have hre : (γ 0 - 1 - I).re = -1 := by rw [hγ0]; simp
    obtain ⟨y, hy, hgy, -⟩ := hneg (-1) (by norm_num)
    rw [lowExt_of_nonpos him, hre, hgy]
    refine Supp9B.lowerLeft_subset_leftSide hβ''p.2.2.1 (by rw [hβ''0, ofReal_im]) ⟨?_, ?_⟩
    · rw [hβ''0, ofReal_re]; simp [hγ0]; linarith
    · simp [hγ0]
  have hpc : IsPreconnected (lowExt g '' leftSide γ) :=
    isPreconnected_connectedComponentIn.image _ (continuous_lowExt hgc).continuousOn
  have himg : lowExt g '' leftSide γ ⊆ leftSide (postCurve β tL) := by
    have h1 := hpc.subset_connectedComponentIn ⟨_, href, rfl⟩ hsub
    unfold leftSide at hmem ⊢
    rwa [← connectedComponentIn_eq hmem] at h1
  rintro _ ⟨w, ⟨hwZ, hwH⟩, rfl⟩
  rw [← lowExt_of_pos (g := g) hwH]
  exact himg ⟨w, hwZ, rfl⟩

end InteractingSLE.Theorem14.SB.S3.Geo
