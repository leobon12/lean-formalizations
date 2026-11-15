/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmRay
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Supplement.SB2NbStmt

/-!
# D34's clause: the free-ray geometry of the hull chart and the clause at one sample

Worker PROVE-SB2-F3LAW (round 2, target 3, steps (G) and (H) of handoff §R2.6). Let `A` be a hull free right of a real
point `p` (every real `x > p` has a ball missing `A`) and `g` any continuous extension to `ℍ̄` of the inverse of
`Φ = Mo.hullChart A 0`. Aux. lemma 57's Schwarz reflection (`Sec7.exists_isBdryReflection`) at each free point gives
the real boundary value `bdryVal A x` of the mapping-out function, with a positive derivative; so `bdryVal A` is
strictly increasing on `(p, ∞)`, within `M` of the identity, and `g ∘ bdryVal A = id` there. With the entry
`entry A p = inf bdryVal A ((p, ∞))`: `g (entry A p) = p`, `g` maps `(entry A p, ∞)` onto `(p, ∞)` increasingly.

With F3's mean identity and Lemma 7.8's vanishing harmonic part at untouched real points, the word keeps the original
heights on `(entry A p, ∞)` (`fn_eq_of_meanIdentity_at`, the lift tends to `0` by Aux. 57), so D34's clause
`Nb.HeightClause` reduces to the admissibility of the heights left of `entry A p`:

* `FreeRight`, `bdryVal`, `tendsto_mapOut_bdryVal`, `hasDerivAt_bdryVal`, `strictMonoOn_bdryVal`, `ext_bdryVal`;
* `entry`, **`exists_entry_of_freeRight`** (geometry), **`heightClause_of_meanIdentity`** (the clause at one sample);
* `fn_bdryVal_eq`: the original height at the boundary value of any untouched real point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Fm

open Restart Sec7

/-- Every real point right of `p` has a ball missing `A`. -/
def FreeRight (A : Set ℂ) (p : ℝ) : Prop :=
  ∀ x : ℝ, p < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) A

/-- The real boundary value of the mapping-out function at a real point (its limit along `ℍ`). -/
def bdryVal (A : Set ℂ) (x : ℝ) : ℝ :=
  (limUnder (𝓝[H] (x : ℂ)) (ConformalImage.mapOut A)).re

theorem neBot_nhdsWithin_H_real (x : ℝ) : (𝓝[H] (x : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have ht : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h0 : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) (𝓝 0) (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) *
        Complex.I)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  show (0 : ℝ) < ((x : ℂ) + (ε : ℂ) * Complex.I).im
  simpa using hε

/-- Near the centre of a boundary reflection the mapping-out function tends to the reflection's value. -/
theorem tendsto_mapOut_of_reflection {A : Set ℂ} {G : ℂ → ℂ} {x r : ℝ}
    (hG : IsBdryReflection A (ConformalImage.mapOut A) G x r) {t : ℝ} (ht : (t : ℂ) ∈ ball (x : ℂ) r) :
    Tendsto (ConformalImage.mapOut A) (𝓝[H] (t : ℂ)) (𝓝 (G t)) := by
  have hGc : ContinuousAt G t := (hG.diff.differentiableAt (isOpen_ball.mem_nhds ht)).continuousAt
  refine (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds ht)] with z hz
  exact hG.eqOn ⟨hz.2, hz.1⟩

theorem bdryVal_eq_of_reflection {A : Set ℂ} {G : ℂ → ℂ} {x r : ℝ}
    (hG : IsBdryReflection A (ConformalImage.mapOut A) G x r) {t : ℝ} (ht : (t : ℂ) ∈ ball (x : ℂ) r) :
    bdryVal A t = (G t).re := by
  have := neBot_nhdsWithin_H_real t
  unfold bdryVal
  rw [(tendsto_mapOut_of_reflection hG ht).limUnder_eq]

theorem ofReal_bdryVal_of_reflection {A : Set ℂ} {G : ℂ → ℂ} {x r : ℝ}
    (hG : IsBdryReflection A (ConformalImage.mapOut A) G x r) {t : ℝ} (ht : (t : ℂ) ∈ ball (x : ℂ) r) :
    ((bdryVal A t : ℝ) : ℂ) = G t := by
  rw [bdryVal_eq_of_reflection hG ht]
  exact Complex.ext (by simp) (by simp [hG.real_of_im _ ht (by simp)])

/-- **The mapping-out function tends to its real boundary value** at an untouched real point. -/
theorem tendsto_mapOut_bdryVal {A : Set ℂ} (hA : IsHPHull A) {x r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (x : ℂ) r) A) :
    Tendsto (ConformalImage.mapOut A) (𝓝[H] (x : ℂ)) (𝓝 ((bdryVal A x : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := exists_isBdryReflection hA (ConformalImage.isMapOut_mapOut hA) hr hd
  have hx : (x : ℂ) ∈ ball (x : ℂ) (r / 2) := mem_ball_self hG.pos
  rw [ofReal_bdryVal_of_reflection hG hx]
  exact tendsto_mapOut_of_reflection hG hx

/-- **The boundary value has a positive derivative** at an untouched real point. -/
theorem hasDerivAt_bdryVal {A : Set ℂ} (hA : IsHPHull A) {x r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (x : ℂ) r) A) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (bdryVal A) d x := by
  have hg := ConformalImage.isMapOut_mapOut hA
  obtain ⟨G, hG⟩ := exists_isBdryReflection hA hg hr hd
  have hx : (x : ℂ) ∈ ball (x : ℂ) (r / 2) := mem_ball_self hG.pos
  have hGd : HasDerivAt G (deriv G x) (x : ℂ) :=
    (hG.diff.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  refine ⟨(deriv G x).re, (hG.deriv_im_eq_zero_and_re_pos hg).2, ?_⟩
  refine hGd.real_of_complex.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ s : ℝ in 𝓝 x, (s : ℂ) ∈ ball (x : ℂ) (r / 2) :=
    (Complex.continuous_ofReal.tendsto x).eventually (isOpen_ball.mem_nhds hx)
  filter_upwards [hev] with s hs
  exact bdryVal_eq_of_reflection hG hs

theorem abs_bdryVal_sub_le {A : Set ℂ} (hA : IsHPHull A) {M : ℝ}
    (hM : ∀ z ∈ H \ A, ‖ConformalImage.mapOut A z - z‖ ≤ M) {x r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (x : ℂ) r) A) : |bdryVal A x - x| ≤ M := by
  obtain ⟨G, hG⟩ := exists_isBdryReflection hA (ConformalImage.isMapOut_mapOut hA) hr hd
  have hx : (x : ℂ) ∈ ball (x : ℂ) (r / 2) := mem_ball_self hG.pos
  have h := hG.norm_sub_le hM
  rw [bdryVal_eq_of_reflection hG hx]
  have e : (G x).re - x = (G x - x).re := by simp
  rw [e]
  exact (Complex.abs_re_le_norm _).trans h

/-- On the free ray the boundary value is strictly increasing. -/
theorem strictMonoOn_bdryVal {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) :
    StrictMonoOn (bdryVal A) (Ioi p) := by
  have hd : ∀ x ∈ Ioi p, ∃ d : ℝ, 0 < d ∧ HasDerivAt (bdryVal A) d x := fun x hx => by
    obtain ⟨r, hr, hdisj⟩ := hp x hx
    exact hasDerivAt_bdryVal hA hr hdisj
  refine strictMonoOn_of_deriv_pos (convex_Ioi p) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨d, -, hD⟩ := hd x hx
    exact hD.continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    obtain ⟨d, hd0, hD⟩ := hd x hx
    rw [hD.deriv]
    exact hd0

theorem continuousOn_bdryVal {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) :
    ContinuousOn (bdryVal A) (Ioi p) := fun x hx => by
  obtain ⟨r, hr, hdisj⟩ := hp x hx
  obtain ⟨d, -, hD⟩ := hasDerivAt_bdryVal hA hr hdisj
  exact hD.continuousAt.continuousWithinAt

/-- **A continuous extension of the chart's inverse inverts the boundary value** on the free ray. -/
theorem ext_bdryVal {A : Set ℂ} (hA : IsHPHull A) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hg : EqOn g (Mo.hullChart A 0).2.1 H) {x r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) A) :
    g ((bdryVal A x : ℝ) : ℂ) = (x : ℂ) := by
  have hc := Mo.isConformal_hullChart hA 0
  have hdom := Mo.coe_dom_hullChart hA 0
  have hNe := neBot_nhdsWithin_H_real x
  have hT := tendsto_mapOut_bdryVal hA hr hd
  have hsub : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ A := by
    have hev : H ∩ ball (x : ℂ) r ∈ 𝓝[H] (x : ℂ) :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hev] with z hz
    exact ⟨hz.1, fun hzA => Set.disjoint_left.1 hd hz.2 hzA⟩
  have hfwd : ∀ z ∈ H \ A, (Mo.hullChart A 0).1 z = ConformalImage.mapOut A z := fun z _ => by
    simp [Mo.hullChart_fwd]
  have hT' : Tendsto (ConformalImage.mapOut A) (𝓝[H] (x : ℂ))
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((bdryVal A x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hT, ?_⟩
    filter_upwards [hsub] with z hz
    have h1 := hc.fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hz)
    rw [hfwd z hz] at h1
    exact le_of_lt h1
  have hgy : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} ((bdryVal A x : ℝ) : ℂ) :=
    hgc _ (show (0 : ℝ) ≤ ((bdryVal A x : ℝ) : ℂ).im by simp)
  have h1 : Tendsto (fun z => g (ConformalImage.mapOut A z)) (𝓝[H] (x : ℂ)) (𝓝 (g ((bdryVal A x : ℝ) : ℂ))) :=
    hgy.tendsto.comp hT'
  have h2 : Tendsto (fun z => g (ConformalImage.mapOut A z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hsub] with z hz
    have hzd : z ∈ (Mo.hullChart A 0).dom := by rw [← SetLike.mem_coe, hdom]; exact hz
    have hm := hc.fwd_mem hzd
    rw [← hfwd z hz, hg hm, hc.inv_fwd hzd]
    rfl
  exact tendsto_nhds_unique h1 h2

/-- The **entry** of the free ray right of `p` in the chart: the infimum of the boundary values right of `p`. -/
def entry (A : Set ℂ) (p : ℝ) : ℝ := sInf (bdryVal A '' Ioi p)

/-- **Free-ray geometry of the hull chart.** For a hull `A` free right of `p` and a continuous extension `g` of the
inverse of `Mo.hullChart A 0` to `ℍ̄`, there is an entry `e` with `g e = p`; `g` maps `(e, ∞)` onto the free ray
through the inverse of the strictly increasing boundary value, and `Re ∘ g` is strictly increasing on `[e, ∞)`. -/
theorem exists_entry_of_freeRight {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hg : EqOn g (Mo.hullChart A 0).2.1 H) :
    g (entry A p : ℂ) = (p : ℂ) ∧ StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici (entry A p)) ∧
      ∀ y : ℝ, entry A p < y → ∃ x : ℝ, p < x ∧ g (y : ℂ) = (x : ℂ) ∧ bdryVal A x = y := by
  obtain ⟨M, hM⟩ := (ConformalImage.isMapOut_mapOut hA).exists_norm_sub_le hA
  set F := bdryVal A with hFdef
  have hmono := strictMonoOn_bdryVal hA hp
  have hcont := continuousOn_bdryVal hA hp
  have hlow : ∀ x ∈ Ioi p, x - M ≤ F x := fun x hx => by
    obtain ⟨r, hr, hdisj⟩ := hp x hx
    have := abs_bdryVal_sub_le hA hM hr hdisj
    have := neg_abs_le (F x - x)
    linarith
  have hinv : ∀ x ∈ Ioi p, g ((F x : ℝ) : ℂ) = (x : ℂ) := fun x hx => by
    obtain ⟨r, hr, hdisj⟩ := hp x hx
    exact ext_bdryVal hA hgc hg hr hdisj
  have hne : (F '' Ioi p).Nonempty := ⟨F (p + 1), p + 1, by simp, rfl⟩
  have hbdd : BddBelow (F '' Ioi p) := ⟨p - M, by
    rintro _ ⟨x, hx, rfl⟩
    have := hlow x hx
    have hx' : p < x := hx
    linarith⟩
  set e := entry A p with he
  have hle : ∀ x ∈ Ioi p, e ≤ F x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  have hlt : ∀ y, e < y → ∃ x ∈ Ioi p, F x < y := fun y hy => by
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := exists_lt_of_csInf_lt hne hy
    exact ⟨x, hx, hxy⟩
  -- the boundary value tends to `e` at `p⁺`
  have hTe : Tendsto F (𝓝[>] p) (𝓝 e) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with x hx using lt_of_lt_of_le ha (hle x hx)
    · obtain ⟨x₁, hx₁, hx₁a⟩ := hlt a ha
      have hmem : Ioo p x₁ ∈ 𝓝[>] p := Ioo_mem_nhdsGT hx₁
      filter_upwards [hmem] with x hx
      exact lt_trans (hmono hx.1 hx₁ hx.2) hx₁a
  -- the entry
  have hge : g (e : ℂ) = (p : ℂ) := by
    have hgy : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (e : ℂ) := hgc _ (show (0 : ℝ) ≤ (e : ℂ).im by simp)
    have hTe' : Tendsto (fun x => ((F x : ℝ) : ℂ)) (𝓝[>] p) (𝓝[{z : ℂ | 0 ≤ z.im}] (e : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto e).comp hTe, ?_⟩
      exact Eventually.of_forall fun x => show (0 : ℝ) ≤ ((F x : ℝ) : ℂ).im by simp
    have h1 := hgy.tendsto.comp hTe'
    have h2 : Tendsto (fun x => g ((F x : ℝ) : ℂ)) (𝓝[>] p) (𝓝 (p : ℂ)) := by
      have h0 : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] p) (𝓝 (p : ℂ)) :=
        (Complex.continuous_ofReal.tendsto p).mono_left nhdsWithin_le_nhds
      refine h0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx using (hinv x hx).symm
    exact tendsto_nhds_unique h1 h2
  -- surjectivity onto `(e, ∞)`
  have hsurj : ∀ y, e < y → ∃ x, p < x ∧ F x = y := fun y hy => by
    obtain ⟨x₁, hx₁, hx₁y⟩ := hlt y hy
    set x₂ := max x₁ (y + M + 1) with hx₂
    have hx₁₂ : x₁ ≤ x₂ := le_max_left _ _
    have hx₂p : x₂ ∈ Ioi p := lt_of_lt_of_le hx₁ hx₁₂
    have hFx₂ : y ≤ F x₂ := by
      have := hlow x₂ hx₂p
      have : y + M + 1 ≤ x₂ := le_max_right _ _
      linarith
    have hsub : Icc x₁ x₂ ⊆ Ioi p := fun t ht => lt_of_lt_of_le hx₁ ht.1
    obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hx₁₂ (hcont.mono hsub) ⟨hx₁y.le, hFx₂⟩
    exact ⟨x, hsub hx, hFx⟩
  refine ⟨hge, ?_, fun y hy => ?_⟩
  · intro y₁ hy₁ y₂ hy₂ hlt₁₂
    have hy₂e : e < y₂ := lt_of_le_of_lt hy₁ hlt₁₂
    obtain ⟨x₂, hx₂, rfl⟩ := hsurj y₂ hy₂e
    simp only
    rw [hinv x₂ hx₂, Complex.ofReal_re]
    rcases eq_or_lt_of_le (show e ≤ y₁ from hy₁) with h | h
    · rw [← h, hge, Complex.ofReal_re]
      exact hx₂
    · obtain ⟨x₁, hx₁, rfl⟩ := hsurj y₁ h
      rw [hinv x₁ hx₁, Complex.ofReal_re]
      by_contra hc
      exact absurd hlt₁₂ (not_lt.2 (hmono.le_iff_le hx₂ hx₁ |>.2 (not_lt.1 hc)))
  · obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨x, hx, hinv x hx, rfl⟩

/-- **D34's clause at one sample from the mean identity and the left heights.** For a hull `A` free right of `p`, a
sorted word `β` with F3's mean identity `w + u₀ = β.mean ∘ Φ.1 − χ · Φ.2.2` in `Φ = Mo.hullChart A 0` whose harmonic
part `w` tends to `0` at the untouched real points, and admissible heights left of the entry `entry A p`, the clause
`Nb.HeightClause` holds at `p` (part (a) with the exceptional set `β.jumps`). -/
theorem heightClause_of_meanIdentity {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {A : Set ℂ}
    (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) {β : BoundaryWord} (hβ : β.IsSorted) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {w : ℂ → ℝ}
    (hid : EqOn (fun z => w z + u₀ z)
      (fun z => β.mean ((Mo.hullChart A 0).1 z) - QuantumZipper.chiC κ * (Mo.hullChart A 0).2.2 z) (H \ A))
    (hw : ∀ x : ℝ, (∃ r > 0, Disjoint (ball (x : ℂ) r) A) → Tendsto w (𝓝[H \ A] (x : ℂ)) (𝓝 0))
    (hL : LeftAdm κ β (entry A p)) : Nb.HeightClause κ b jumps A (p : ℂ) β := by
  intro g hgc hg
  obtain ⟨hge, hmono, hray⟩ := exists_entry_of_freeRight hA hp hgc hg
  have hc := Mo.isConformal_hullChart hA 0
  have hdom := Mo.coe_dom_hullChart hA 0
  refine ⟨entry A p, hge, fun y hy => ?_, hmono, ⟨β.jumps, fun y hy hyF hxJ => ?_⟩,
    fun y hy hyJ => cumWeightLeft_gt_of_lt hκ (hL y hy hyJ)⟩
  · obtain ⟨x, -, hx, -⟩ := hray y hy
    rw [hx, Complex.ofReal_im]
  · obtain ⟨x, hpx, hx, hFx⟩ := hray y hy
    rw [hx, Complex.ofReal_re] at hxJ ⊢
    obtain ⟨r, hr, hd⟩ := hp x hpx
    have hle : 𝓝[H \ A] (x : ℂ) ≤ 𝓝[H] (x : ℂ) := nhdsWithin_mono _ sdiff_subset
    have hfwd : ∀ z, (Mo.hullChart A 0).1 z = ConformalImage.mapOut A z := fun z => by
      simp [Mo.hullChart_fwd]
    have hT : Tendsto (Mo.hullChart A 0).1 (𝓝[H \ A] (x : ℂ)) (𝓝[H] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (tendsto_mapOut_bdryVal hA hr hd).mono_left hle
        rw [hFx] at h
        refine h.congr' (Eventually.of_forall fun z => (hfwd z).symm)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact hc.fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hz)
    have hl : Tendsto (Mo.hullChart A 0).2.2 (𝓝[H \ A] (x : ℂ)) (𝓝 0) := by
      have h := (IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hA (isCanonicalDerivLog_canonDerivLog hA)
        (ConformalImage.isMapOut_mapOut hA) hr hd).mono_left hle
      exact h
    exact fn_eq_of_meanIdentity_at κ hβ hu₀ hid hxJ hr hd (hw x ⟨r, hr, hd⟩) hyF hT hl

/-- **The word's height at the boundary value of any untouched real point is the original height** (F3's mean
identity in `Mo.hullChart A 0`, harmonic part `→ 0` at `x`). -/
theorem fn_bdryVal_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {A : Set ℂ} (hA : IsHPHull A) {β : BoundaryWord}
    (hβ : β.IsSorted) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {w : ℂ → ℝ}
    (hid : EqOn (fun z => w z + u₀ z)
      (fun z => β.mean ((Mo.hullChart A 0).1 z) - QuantumZipper.chiC κ * (Mo.hullChart A 0).2.2 z) (H \ A))
    {x r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) A) (hw : Tendsto w (𝓝[H \ A] (x : ℂ)) (𝓝 0))
    (hx : x ∉ jumps) (hy : bdryVal A x ∉ β.jumps) : β.fn (bdryVal A x) = b x := by
  have hc := Mo.isConformal_hullChart hA 0
  have hdom := Mo.coe_dom_hullChart hA 0
  have hle : 𝓝[H \ A] (x : ℂ) ≤ 𝓝[H] (x : ℂ) := nhdsWithin_mono _ sdiff_subset
  have hfwd : ∀ z, (Mo.hullChart A 0).1 z = ConformalImage.mapOut A z := fun z => by
    simp [Mo.hullChart_fwd]
  have hT : Tendsto (Mo.hullChart A 0).1 (𝓝[H \ A] (x : ℂ)) (𝓝[H] ((bdryVal A x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((tendsto_mapOut_bdryVal hA hr hd).mono_left hle).congr' (Eventually.of_forall fun z => (hfwd z).symm)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hc.fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hz)
  have hl : Tendsto (Mo.hullChart A 0).2.2 (𝓝[H \ A] (x : ℂ)) (𝓝 0) :=
    (IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hA (isCanonicalDerivLog_canonDerivLog hA)
      (ConformalImage.isMapOut_mapOut hA) hr hd).mono_left hle
  exact fn_eq_of_meanIdentity_at κ hβ hu₀ hid hx hr hd hw hy hT hl

end InteractingSLE.Theorem14.SB.Fm
