/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetChartSides

/-!
# Prime-end clearance at the old common points: `RetTouchClearStatement` PROVED

Packet PROVE-T15-RET5 (Aux. lemma 83, supplement pp. 297–298: "Actual proper completion implies prime-end
clearance"). At a touching ordinary pair with W0's ordered proper completions `α̂`, `β̂`:

* **the side of the collar** (`eventually_mem_connectedComponentIn_of_path`): near a chart point `w` of the first
  prefix's right side `(M₁, R₁)`, the retained chart inverse lands in the right Jordan side of `α̂`; the chart path from
  `w + iε` along the side to an untouched real point right of the first base stays off `α̂` (its real points land on the
  prefix away from the tip, or on real points near the base, at positive distance from the closed tail `α̂([a, ∞))`, and
  uniform continuity of `ψ` keeps the path within that distance);
* **the collar in the individual chart**: a small half-disc of the first path's individual chart around the chart value
  `y > 0` of `w` is mapped by the inverse individual chart into a ball around the common point off the tail, so it lies
  in one Jordan side of `α̂`, the right one (it contains the landing points of the first step), hence off `β̂ ⊆ closed
  left side of α̂`; it avoids the retained union, so it lies in the active domain and misses the filled union;
* symmetrically on the second prefix's left side `(L₂, 0)` with the left Jordan side of `β̂`, which misses `α̂` by the
  duality `α̂ ⊆ closed right side of β̂` (`Supp9B.range_subset_closedRightSide`).

Main result: **`retTouchClearStatement : RetTouchClearStatement`**. Deterministic.
-/

set_option autoImplicit false

noncomputable section

universe u

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetChart

open Restart Supp7 Sec7 Sec7.Lemma76G Sec7.SideHeightBox RetTouch

/-! ### A chart path to a real reference point -/

theorem dist_ofReal_re (p : ℂ) : dist p (p.re : ℂ) = |p.im| := by
  rw [Complex.dist_eq]
  have e : p - (p.re : ℂ) = (p.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Points of the segment between two points of equal height `h` have height `h` and real part between theirs. -/
theorem mem_segment_horiz {z c p : ℂ} (hzc : z.im = c.im) (hp : p ∈ segment ℝ z c) :
    p.im = z.im ∧ min z.re c.re ≤ p.re ∧ p.re ≤ max z.re c.re := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  simp only [add_im, smul_im, add_re, smul_re, smul_eq_mul]
  refine ⟨by rw [← hzc]; linear_combination z.im * hab, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left z.re c.re) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right z.re c.re) hb
    have e : a * min z.re c.re + b * min z.re c.re = min z.re c.re := by rw [← add_mul, hab, one_mul]
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (le_max_left z.re c.re) ha
    have h2 := mul_le_mul_of_nonneg_left (le_max_right z.re c.re) hb
    have e : a * max z.re c.re + b * max z.re c.re = max z.re c.re := by rw [← add_mul, hab, one_mul]
    linarith

/-- Points of the vertical segment from `v + ih` down to `v` have real part `v` and height in `[0, h]`. -/
theorem mem_segment_vert {v h : ℝ} (hh : 0 ≤ h) {p : ℂ} (hp : p ∈ segment ℝ ((v : ℂ) + (h : ℂ) * I) (v : ℂ)) :
    p.re = v ∧ 0 ≤ p.im ∧ p.im ≤ h := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  simp only [add_im, smul_im, add_re, smul_re, smul_eq_mul, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
  refine ⟨by linear_combination v * hab, by nlinarith, by nlinarith⟩

/-- **A chart path to a real reference point.** Let `ψ` be continuous on `ℍ̄`, `S ⊆ ℂ`, and `T` a closed set such that
the images of `ℍ` meet `S` only in `T`. If the images of the real chart points of `[lo, hi]` avoid `T` and the image
of the chart point `v ∈ [lo, hi]` avoids `S`, then near every `u ∈ (lo, hi)` the images of points of `ℍ` lie in the
component of `ψ v` in the complement of `S`. -/
theorem eventually_mem_connectedComponentIn_of_path {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) {S T : Set ℂ}
    (hT : IsClosed T) (hST : ∀ z ∈ H, ψ z ∈ S → ψ z ∈ T) {lo hi u v : ℝ} (hu : u ∈ Ioo lo hi)
    (hv : v ∈ Icc lo hi) (hK : ∀ t ∈ Icc lo hi, ψ t ∉ T) (hvS : ψ v ∉ S) :
    ∀ᶠ z in 𝓝[H] (u : ℂ), ψ z ∈ connectedComponentIn Sᶜ (ψ v) := by
  -- the compact image of the real interval avoids `T`
  set K := (fun t : ℝ => ψ t) '' Icc lo hi with hKdef
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn
    (hψc.comp_continuous continuous_ofReal fun t => ofReal_mem_Hbar t).continuousOn
  have hKT : Disjoint K T := Set.disjoint_left.2 fun p ⟨t, ht, hp⟩ hpT => hK t ht (by rw [← hp] at hpT; exact hpT)
  obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist hKc hT hKT
  -- uniform continuity on a box
  set Q : Set ℂ := {z : ℂ | z.re ∈ Icc lo hi ∧ z.im ∈ Icc (0 : ℝ) 1} with hQdef
  have hQc : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hQH : Q ⊆ Hbar := fun z hz => show (0 : ℝ) ≤ z.im from hz.2.1
  have huc := hQc.uniformContinuousOn_of_continuous (hψc.mono hQH)
  obtain ⟨ε, hε, hεψ⟩ := Metric.uniformContinuousOn_iff.1 huc r (by exact_mod_cast hr0)
  -- the eventual set
  have hev : ∀ᶠ z in 𝓝[H] (u : ℂ), z.re ∈ Ioo lo hi ∧ z.im < min ε 1 := by
    have h1 : ∀ᶠ z in 𝓝 (u : ℂ), z.re ∈ Ioo lo hi :=
      (continuous_re.tendsto (u : ℂ)) (by simpa using Ioo_mem_nhds hu.1 hu.2)
    have h2 : ∀ᶠ z in 𝓝 (u : ℂ), z.im < min ε 1 :=
      (continuous_im.tendsto (u : ℂ)) (by simpa using Iio_mem_nhds (lt_min hε one_pos))
    exact nhdsWithin_le_nhds (h1.and h2)
  filter_upwards [hev, self_mem_nhdsWithin] with z ⟨hzre, hzim⟩ hzH
  have hzim0 : 0 < z.im := hzH
  set c : ℂ := (v : ℂ) + (z.im : ℂ) * I with hcdef
  have hcre : c.re = v := by simp [hcdef]
  have hcim : c.im = z.im := by simp [hcdef]
  set P : Set ℂ := segment ℝ z c ∪ segment ℝ c (v : ℂ) with hPdef
  have hPpc : IsPreconnected P :=
    (convex_segment z c).isPreconnected.union c (right_mem_segment ℝ z c) (left_mem_segment ℝ c _)
      (convex_segment c _).isPreconnected
  have hPQ : P ⊆ Q := by
    rintro p (hp | hp)
    · obtain ⟨h1, h2, h3⟩ := mem_segment_horiz hcim.symm hp
      rw [hcre] at h2 h3
      refine ⟨⟨?_, ?_⟩, ⟨by rw [h1]; exact hzH.le, by rw [h1]; exact (hzim.trans_le (min_le_right _ _)).le⟩⟩
      · exact (le_min hzre.1.le hv.1).trans h2
      · exact h3.trans (max_le hzre.2.le hv.2)
    · obtain ⟨h1, h2, h3⟩ := mem_segment_vert hzH.le hp
      exact ⟨h1 ▸ hv, h2, h3.trans (hzim.trans_le (min_le_right _ _)).le⟩
  have hPS : ψ '' P ⊆ Sᶜ := by
    rintro _ ⟨p, hp, rfl⟩ hpS
    have hpQ := hPQ hp
    have hpre : ((p.re : ℝ) : ℂ) ∈ Q := ⟨by simpa using hpQ.1, by simp⟩
    have hdist : dist p (p.re : ℂ) < ε := by
      rw [dist_ofReal_re, abs_of_nonneg hpQ.2.1]
      rcases hp with hp | hp
      · rw [(mem_segment_horiz hcim.symm hp).1]; exact hzim.trans_le (min_le_left _ _)
      · exact (mem_segment_vert hzH.le hp).2.2.trans_lt (hzim.trans_le (min_le_left _ _))
    have h1 : dist (ψ p) (ψ (p.re : ℂ)) < r := hεψ p hpQ (p.re : ℂ) hpre hdist
    by_cases hpH : p ∈ H
    · have hpT := hST p hpH hpS
      have h2 := hr (ψ (p.re : ℂ)) ⟨p.re, hpQ.1, rfl⟩ (ψ p) hpT
      rw [edist_dist, dist_comm] at h2
      have h3 : ENNReal.ofReal (dist (ψ p) (ψ (p.re : ℂ))) < ENNReal.ofReal (r : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr0)).2 h1
      rw [ENNReal.ofReal_coe_nnreal] at h3
      exact absurd (h2.trans h3) (lt_irrefl _)
    · have hp0 : p.im = 0 := le_antisymm (not_lt.1 hpH) hpQ.2.1
      have hpv : p = (v : ℂ) := by
        rcases hp with hp | hp
        · exact absurd ((mem_segment_horiz hcim.symm hp).1 ▸ hp0) (ne_of_gt hzim0)
        · exact Complex.ext (by simpa using (mem_segment_vert hzH.le hp).1) (by simpa using hp0)
      exact hvS (hpv ▸ hpS)
  have hvP : (v : ℂ) ∈ P := Or.inr (right_mem_segment ℝ c _)
  have hzP : z ∈ P := Or.inl (left_mem_segment ℝ z c)
  have hcomp := (hPpc.image ψ (hψc.mono (hPQ.trans hQH))).subset_connectedComponentIn ⟨_, hvP, rfl⟩ hPS
  exact hcomp ⟨z, hzP, rfl⟩

/-! ### The collar in the individual chart -/

/-- **The collar in the individual chart is cleared** (Aux. lemma 83's last step). Let `K` be closed,
`A = γ([0, c]) ⊆ K` a prefix with individual chart `(G, Φ)`, `γ'` a proper curve from a real seed completing it,
and `Csd` a component of the complement of `γ'` closed along its lower seed ray that misses `K ∖ A`. Let the joint
chart inverse `ψ` (continuous on `ℍ̄`, `ψ(ℍ) ⊆ ℍ ∖ fill(K)`) land in `Csd` near the real chart point `w`, let `G ∘ ψ`
tend to the real `y` there with `Φ(y) = ψ(w)`, and let `ψ(w)` be off the tail `γ'([c, ∞))`. Then a ball around `y`
misses `G(fill(K) ∖ fill(A))`. -/
theorem exists_ball_disjoint_of_side {K Csd : Set ℂ} {ψ G Φ : ℂ → ℂ} (hK : IsClosed K) {γ : ℝ≥0 → ℂ} {c : ℝ≥0}
    (hAK : γ '' Icc 0 c ⊆ K) (hψD : MapsTo ψ H (H \ fillH K)) (hch : IsPhysChart γ c G Φ)
    {γ' : ℝ≥0 → ℂ} (hγ' : Supp9B.IsProperCurve γ') (h0 : (γ' 0).im = 0) (hagree : ∀ t ≤ c, γ' t = γ t)
    {ref : ℂ} (hCsd : Csd = connectedComponentIn (seedRayClosure γ')ᶜ ref) (hCK : Disjoint Csd (K \ γ '' Icc 0 c))
    {w : ℝ} (hside : ∀ᶠ q in 𝓝[H] ((w : ℝ) : ℂ), ψ q ∈ Csd) {y : ℝ}
    (hy : Tendsto (fun q => G (ψ q)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ))) (hΦy : Φ y = ψ w)
    (hpT : ψ w ∉ γ' '' Ici c) :
    ∃ ρ > 0, Disjoint (ball ((y : ℝ) : ℂ) ρ) (G '' (fillH K \ fillH (γ '' Icc 0 c))) := by
  set A := γ '' Icc 0 c with hAdef
  set S := seedRayClosure γ' with hSdef
  set T := γ' '' Ici c with hTdef
  have hTc : IsClosed T := Supp9B.isClosed_image hγ' isClosed_Ici
  obtain ⟨ε₀, hε₀, hε₀T⟩ := Metric.isOpen_iff.1 hTc.isOpen_compl _ hpT
  have hyH : ((y : ℝ) : ℂ) ∈ Hbar := ofReal_mem_Hbar y
  obtain ⟨ρ, hρ, hρΦ⟩ := Metric.continuousWithinAt_iff.1 (hch.inv_cont _ hyH) ε₀ hε₀
  refine ⟨ρ, hρ, ?_⟩
  set V := Φ '' (ball ((y : ℝ) : ℂ) ρ ∩ H) with hVdef
  have hVpc : IsPreconnected V :=
    ((convex_ball _ _).inter RLC.convex_H).isPreconnected.image Φ
      (hch.inv_cont.mono (inter_subset_right.trans H_subset_Hbar))
  have hVU : V ⊆ H \ fillH A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hch.inv_mem hs.2
  have hAH : ∀ v ∈ H \ fillH A, v ∉ A := fun v hv hvA =>
    hv.2 (mem_fillH_of_mem_closure hv.1 (subset_closure hvA))
  have hVS : V ⊆ Sᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hsS
    have hU := hch.inv_mem hs.2
    rcases hsS with ⟨t, ht⟩ | ⟨-, him⟩
    · rcases le_total t c with htc | htc
      · rw [hagree t htc] at ht
        exact hAH _ hU (ht ▸ ⟨t, ⟨zero_le, htc⟩, rfl⟩)
      · have hd : dist (Φ s) (ψ w) < ε₀ := by
          rw [← hΦy]; exact hρΦ (H_subset_Hbar hs.2) (mem_ball.1 hs.1)
        exact hε₀T (mem_ball.2 hd) ⟨t, htc, ht⟩
    · have h1 : (0 : ℝ) < (Φ s).im := hU.1
      rw [h0] at him
      linarith
  -- a landing point of the collar in the side
  have hev := (hside.and (hy.eventually (ball_mem_nhds _ hρ))).and self_mem_nhdsWithin
  obtain ⟨q₀, ⟨hq₀C, hq₀b⟩, hq₀H⟩ := (neBot_nhdsWithin_H w).nonempty_of_mem hev
  have hψq₀ := hψD hq₀H
  have hψq₀A : ψ q₀ ∈ H \ fillH A := ⟨hψq₀.1, fun h => hψq₀.2 (fillH_mono hAK h)⟩
  have hq₀V : ψ q₀ ∈ V := ⟨G (ψ q₀), ⟨hq₀b, hch.maps hψq₀A⟩, hch.inv_f _ hψq₀A⟩
  have hVC : V ⊆ Csd := by
    have hcomp := hVpc.subset_connectedComponentIn hq₀V hVS
    rw [hCsd] at hq₀C ⊢
    rwa [← connectedComponentIn_eq hq₀C] at hcomp
  have hVK : V ⊆ H \ K := fun v hv => ⟨(hVU hv).1, fun hvK => by
    by_cases hvA : v ∈ A
    · exact hAH v (hVU hv) hvA
    · exact Set.disjoint_left.1 hCK (hVC hv) ⟨hvK, hvA⟩⟩
  have hVD : V ⊆ H \ fillH K := by
    intro v hv
    refine ⟨(hVK hv).1, fun hvF => ?_⟩
    have hcomp := hVpc.subset_connectedComponentIn hq₀V hVK
    have heq := connectedComponentIn_eq (hcomp hv)
    rcases hvF.2 with hcl | hbd
    · rw [hK.closure_eq] at hcl; exact (hVK hv).2 hcl
    · rw [hK.closure_eq] at hbd
      rw [← heq] at hbd
      rcases (show ψ q₀ ∉ fillH K from hψq₀.2) with h
      exact h ⟨hψq₀.1, Or.inr (by rw [hK.closure_eq]; exact hbd)⟩
  -- the transition hull misses the ball
  rw [Set.disjoint_left]
  rintro _ hs ⟨q, ⟨hqK, hqA⟩, rfl⟩
  have hqU : q ∈ H \ fillH A := ⟨hqK.1, hqA⟩
  have hqV : q ∈ V := ⟨G q, ⟨hs, hch.maps hqU⟩, hch.inv_f q hqU⟩
  exact (hVD hqV).2 hqK

/-! ### The statement -/

/-- **`RetTouchClearStatement` is proved** (Aux. lemma 83 at a touching ordinary pair; see the module docstring). -/
theorem retTouchClearStatement : RetTouchClearStatement := by
  intro α β ζ₁ ζ₂ x₁ x₂ a b φ ψ lift W₁ W₂ hp₁ hp₂ hx hp _ hC ht hg₁ hWc₁ hW0₁ hg₂ hWc₂ hW0₂
  set z := zoneDataT φ (activeDomain α a β b) ψ α a β b with hzdef
  have hz := ht.good
  have h0₁ : (α 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₁]; simp
  have h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₂]; simp
  have ha0 : 0 < a := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 : (0 : ℝ) < (α a).im := hp.2.2.1
    rw [h, h0₁] at h1
    exact lt_irrefl 0 h1
  have hb0 : 0 < b := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 : (0 : ℝ) < (β b).im := hp.2.2.2.1
    rw [h, h0₂] at h1
    exact lt_irrefl 0 h1
  have hc₁ := Sec7.IsPathGood.continuousOn_Icc hp₁ hp.1.le
  have hc₂ := Sec7.IsPathGood.continuousOn_Icc hp₂ hp.2.1.le
  have hK : IsCompact (prefixSet α a β b) :=
    (Sec7.IsPathGood.isCompact_image hp₁ hp.1.le).union (Sec7.IsPathGood.isCompact_image hp₂ hp.2.1.le)
  have hbij : BijOn ψ H (H \ fillH (prefixSet α a β b)) := by
    rw [← activeDomain_eq hK.isClosed]; exact hC.bijOn h0₂
  have hψc : ContinuousOn ψ Hbar := hC.continuousOn_inv
  have hψD : MapsTo ψ H (H \ fillH (prefixSet α a β b)) := hbij.mapsTo
  have hψU₁ : MapsTo ψ H (H \ fillH (α '' Icc 0 a)) := fun _ hw => IsSetting.fill₁_subset (hbij.mapsTo hw)
  have hψU₂ : MapsTo ψ H (H \ fillH (β '' Icc 0 b)) := fun _ hw => IsSetting.fill₂_subset (hbij.mapsTo hw)
  have hψr : Continuous fun t : ℝ => ψ t := hψc.comp_continuous continuous_ofReal fun t => ofReal_mem_Hbar t
  have hKH : ∀ q ∈ H, ψ q ∉ prefixSet α a β b := fun q hq hqK =>
    (hψD hq).2 (mem_fillH_of_mem_closure (hψD hq).1 (subset_closure hqK))
  -- W0's completions
  obtain ⟨α', β', hα', hβ', hord⟩ := hp.2.2.2.2.2.2.2.2
  have hα'c := Supp9B.isProperCurve_of_isProperCompletion hα'
  have hβ'c := Supp9B.isProperCurve_of_isProperCompletion hβ'
  have hα'0 : α' 0 = x₁ := by rw [hα'.2.2.2.2 0 zero_le, Sec7.IsPathGood.zero hp₁]
  have hβ'0 : β' 0 = x₂ := by rw [hβ'.2.2.2.2 0 zero_le, Sec7.IsPathGood.zero hp₂]
  have h0α' : (α' 0).im = 0 := by rw [hα'0]; simp
  have h0β' : (β' 0).im = 0 := by rw [hβ'0]; simp
  -- the tips have unique chart preimages
  have hne₁ : ∀ s < a, α s ≠ α a := fun s hs he =>
    (ne_of_lt hs) ((Sec7.IsPathGood.injOn_Icc hp₁ hp.1.le) ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he)
  have hne₂ : ∀ t < b, β t ≠ β b := fun t hs he =>
    (ne_of_lt hs) ((Sec7.IsPathGood.injOn_Icc hp₂ hp.2.1.le) ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he)
  obtain ⟨w₁, -, -, -, huniq₁⟩ := hC.exists_tendsto_of_regular h0₂ hp.2.2.2.2.2.2.1
    (Supp7.isChartRegularPoint_tip₁ hc₁ hc₂ h0₁ h0₂ hp.2.2.2.2.2.1 hne₁)
  obtain ⟨w₂, -, -, -, huniq₂⟩ := hC.exists_tendsto_of_regular h0₂ hp.2.2.2.2.2.2.2.1
    (Supp7.isChartRegularPoint_tip₂ hc₁ hc₂ h0₁ h0₂ hp.2.2.2.2.1 hne₂)
  have htip₁ : ∀ t : ℝ, ψ t = α a → t = z.M₁ := fun t h => by
    have e := (huniq₁ t (ofReal_mem_Hbar t) h).trans (huniq₁ z.M₁ (ofReal_mem_Hbar _) ht.tip₁).symm
    exact_mod_cast e
  have htip₂ : ∀ t : ℝ, ψ t = β b → t = 0 := fun t h => by
    have h0H : (0 : ℂ) ∈ Hbar := by simpa using ofReal_mem_Hbar 0
    have e := (huniq₂ t (ofReal_mem_Hbar t) h).trans (huniq₂ 0 h0H ht.tip₂).symm
    exact_mod_cast e
  refine ⟨fun w hM hR hβw => ?_, fun w hL hw0 hαw => ?_⟩
  · -- the first prefix's right side
    set T := α' '' Ici a with hTdef
    have hTc : IsClosed T := Supp9B.isClosed_image hα'c isClosed_Ici
    have hnT : ∀ p ∈ α '' Icc 0 a, p ≠ α a → p ∉ T := by
      rintro _ ⟨s, hs, rfl⟩ hne ⟨t, ht', he⟩
      rw [← hα'.2.2.2.2 s hs.2] at he
      have hts := hα'.2.1 he
      rw [hts] at ht'
      exact hne (by rw [le_antisymm hs.2 ht'])
    have hside₁ : ∀ t : ℝ, z.M₁ < t → t ≤ z.R₁ → ψ t ∉ T := fun t h1 h2 => by
      have hmem : ψ t ∈ α '' Icc 0 a := by
        rcases h2.lt_or_eq with h2 | rfl
        · exact ht.side₄ t h1 h2
        · exact ht.R₁_mem
      exact hnT _ hmem fun h => (ne_of_gt h1) (htip₁ t h)
    obtain ⟨r₀, hr₀, hr₀T⟩ := Metric.isOpen_iff.1 hTc.isOpen_compl _ (hside₁ z.R₁ (hM.trans hR) le_rfl)
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuous_iff.1 hψr z.R₁ r₀ hr₀
    set lo := (z.M₁ + w) / 2 with hlo
    set hi := z.R₁ + δ / 2 with hhi
    have hlow : lo < w := by rw [hlo]; linarith
    have hMlo : z.M₁ < lo := by rw [hlo]; linarith
    have hwhi : w < hi := by rw [hhi]; linarith
    have hKt : ∀ t ∈ Icc lo hi, ψ t ∉ T := by
      intro t htI
      by_cases h : t ≤ z.R₁
      · exact hside₁ t (hMlo.trans_le htI.1) h
      · refine fun hT => hr₀T (mem_ball.2 (hδψ t ?_)) hT
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [htI.2]
    obtain ⟨hvim, hvre, -⟩ := ht.zone₂ hi (by rw [hhi]; linarith)
    have hve : ψ hi = (((ψ hi).re : ℝ) : ℂ) := (Restart.ofReal_re_eq hvim).symm
    have hb₁ : x₁ ≤ z.b₁ := seed_le_baseR hp₁ hp.1.le
    have hvT : ψ hi ∉ T := hKt hi ⟨(hlow.trans hwhi).le, le_rfl⟩
    have hvα : ψ hi ∉ range α' := by
      rintro ⟨t, htv⟩
      rcases le_total t a with hta | hta
      · rw [hα'.2.2.2.2 t hta] at htv
        refine ht.notMem_zone (ψ hi).re (Or.inr hvre) (Or.inl ?_)
        rw [← hve, ← htv]; exact ⟨t, ⟨zero_le, hta⟩, rfl⟩
      · exact hvT ⟨t, hta, htv⟩
    have hvS : ψ hi ∉ seedRayClosure α' := by
      rintro (hS | ⟨hre, -⟩)
      · exact hvα hS
      · rw [hα'0] at hre; simp only [ofReal_re] at hre; linarith
    have hST : ∀ q ∈ H, ψ q ∈ seedRayClosure α' → ψ q ∈ T := by
      intro q hq hqS
      rcases hqS with ⟨t, htq⟩ | ⟨-, him⟩
      · rcases le_total t a with hta | hta
        · exfalso
          rw [hα'.2.2.2.2 t hta] at htq
          exact hKH q hq (Or.inl ⟨t, ⟨zero_le, hta⟩, htq⟩)
        · exact ⟨t, hta, htq⟩
      · have : (0 : ℝ) < (ψ q).im := (hψD hq).1
        rw [h0α'] at him; linarith
    have hside := eventually_mem_connectedComponentIn_of_path hψc hTc hST ⟨hlow, hwhi⟩
      ⟨(hlow.trans hwhi).le, le_rfl⟩ hKt hvS
    have hvR : ψ hi ∈ Supp9B.rightSide α' := by
      rw [hve]
      refine ofReal_mem_rightSide_of_notMem hα'c h0α' ?_ (hve ▸ hvα)
      rw [hα'0]; simp only [ofReal_re]; linarith
    rw [← connectedComponentIn_eq hvR] at hside
    have hCK : Disjoint (Supp9B.rightSide α') (prefixSet α a β b \ α '' Icc 0 a) := by
      rw [Set.disjoint_left]
      rintro p hpR ⟨hpK | hpK, hpA⟩
      · exact hpA hpK
      · obtain ⟨t, htb, rfl⟩ := hpK
        rcases hord ⟨t, hβ'.2.2.2.2 t htb.2⟩ with hL | hS
        · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hα'c h0α') hL hpR
        · exact connectedComponentIn_subset _ _ hpR hS
    have hch : IsPhysChart α a (physF W₁ a x₁)
        (fun w => extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W₁ r.toNNReal) a) w + x₁) :=
      isPhysChart hg₁ hWc₁ hW0₁ hp₁.1 hp.1 ha0
    obtain ⟨C, hCd⟩ := physF_disp hp₁ hg₁ hWc₁ hW0₁ hp.1 ha0
    obtain ⟨M, hMd⟩ := comp_disp_of_retChart hC hψU₁ hCd
    obtain ⟨y, hΦy, hy⟩ := exists_real_tendsto_comp hch hψc hψU₁ hMd (notMem_U₁ ht (ht.R₂_lt_M₁.trans hM))
    rw [bdryVal_eq hy]
    have hwT : ψ w ∉ T := hside₁ w hM hR.le
    exact exists_ball_disjoint_of_side hK.isClosed subset_union_left hψD hch hα'c h0α'
      (fun t htc => hα'.2.2.2.2 t htc) rfl hCK hside hy hΦy hwT
  · -- the second prefix's left side
    set T := β' '' Ici b with hTdef
    have hTc : IsClosed T := Supp9B.isClosed_image hβ'c isClosed_Ici
    have hnT : ∀ p ∈ β '' Icc 0 b, p ≠ β b → p ∉ T := by
      rintro _ ⟨s, hs, rfl⟩ hne ⟨t, ht', he⟩
      rw [← hβ'.2.2.2.2 s hs.2] at he
      have hts := hβ'.2.1 he
      rw [hts] at ht'
      exact hne (by rw [le_antisymm hs.2 ht'])
    have hw0R : w < z.R₂ := hw0.trans ht.zero_lt_R₂
    have hside₂ : ∀ t : ℝ, z.L₂ ≤ t → t < 0 → ψ t ∉ T := fun t h1 h2 => by
      have hmem : ψ t ∈ β '' Icc 0 b := by
        rcases h1.lt_or_eq with h1 | rfl
        · exact ht.side₂ t h1 (h2.trans ht.zero_lt_R₂)
        · exact ht.L₂_mem
      exact hnT _ hmem fun h => (ne_of_lt h2) (htip₂ t h)
    obtain ⟨r₀, hr₀, hr₀T⟩ := Metric.isOpen_iff.1 hTc.isOpen_compl _ (hside₂ z.L₂ le_rfl (hL.trans hw0))
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuous_iff.1 hψr z.L₂ r₀ hr₀
    set lo := z.L₂ - δ / 2 with hlo
    set hi := w / 2 with hhi
    have hlow : lo < w := by rw [hlo]; linarith
    have hwhi : w < hi := by rw [hhi]; linarith
    have hhi0 : hi < 0 := by rw [hhi]; linarith
    have hKt : ∀ t ∈ Icc lo hi, ψ t ∉ T := by
      intro t htI
      by_cases h : z.L₂ ≤ t
      · exact hside₂ t h (htI.2.trans_lt hhi0)
      · refine fun hT => hr₀T (mem_ball.2 (hδψ t ?_)) hT
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [htI.1]
    obtain ⟨hvim, hvre, -⟩ := ht.zone₀ lo (by rw [hlo]; linarith)
    have hve : ψ lo = (((ψ lo).re : ℝ) : ℂ) := (Restart.ofReal_re_eq hvim).symm
    have ha₂ : z.a₂ ≤ x₂ := baseL_le_seed hp₂ hp.2.1.le
    have hvT : ψ lo ∉ T := hKt lo ⟨le_rfl, (hlow.trans hwhi).le⟩
    have hvβ : ψ lo ∉ range β' := by
      rintro ⟨t, htv⟩
      rcases le_total t b with htb | htb
      · rw [hβ'.2.2.2.2 t htb] at htv
        refine ht.notMem_zone (ψ lo).re (Or.inl hvre) (Or.inr ?_)
        rw [← hve, ← htv]; exact ⟨t, ⟨zero_le, htb⟩, rfl⟩
      · exact hvT ⟨t, htb, htv⟩
    have hvS : ψ lo ∉ seedRayClosure β' := by
      rintro (hS | ⟨hre, -⟩)
      · exact hvβ hS
      · rw [hβ'0] at hre; simp only [ofReal_re] at hre; linarith
    have hST : ∀ q ∈ H, ψ q ∈ seedRayClosure β' → ψ q ∈ T := by
      intro q hq hqS
      rcases hqS with ⟨t, htq⟩ | ⟨-, him⟩
      · rcases le_total t b with htb | htb
        · exfalso
          rw [hβ'.2.2.2.2 t htb] at htq
          exact hKH q hq (Or.inr ⟨t, ⟨zero_le, htb⟩, htq⟩)
        · exact ⟨t, htb, htq⟩
      · have : (0 : ℝ) < (ψ q).im := (hψD hq).1
        rw [h0β'] at him; linarith
    have hside := eventually_mem_connectedComponentIn_of_path hψc hTc hST ⟨hlow, hwhi⟩
      ⟨le_rfl, (hlow.trans hwhi).le⟩ hKt hvS
    have hvL : ψ lo ∈ Supp9B.leftSide β' := by
      rw [hve]
      refine Supp9B.ofReal_mem_leftSide hβ'c.2.2.1 h0β' ?_ (hve ▸ hvS)
      rw [hβ'0]; simp only [ofReal_re]; linarith
    rw [← connectedComponentIn_eq hvL] at hside
    have hαR : range α' ⊆ Supp9B.closedRightSide β' :=
      Supp9B.range_subset_closedRightSide hα'c hβ'c h0α' h0β' (by rw [hα'0, hβ'0]; simpa using hx) hord
    have hCK : Disjoint (Supp9B.leftSide β') (prefixSet α a β b \ β '' Icc 0 b) := by
      rw [Set.disjoint_left]
      rintro p hpL ⟨hpK | hpK, hpB⟩
      · obtain ⟨t, hta, rfl⟩ := hpK
        rcases hαR ⟨t, hα'.2.2.2.2 t hta.2⟩ with hR | hS
        · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hβ'c h0β') hpL hR
        · exact connectedComponentIn_subset _ _ hpL hS
      · exact hpB hpK
    have hch : IsPhysChart β b (physF W₂ b x₂)
        (fun w => extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W₂ r.toNNReal) b) w + x₂) :=
      isPhysChart hg₂ hWc₂ hW0₂ hp₂.1 hp.2.1 hb0
    obtain ⟨C, hCd⟩ := physF_disp hp₂ hg₂ hWc₂ hW0₂ hp.2.1 hb0
    obtain ⟨M, hMd⟩ := comp_disp_of_retChart hC hψU₂ hCd
    obtain ⟨y, hΦy, hy⟩ := exists_real_tendsto_comp hch hψc hψU₂ hMd (notMem_U₂ ht hw0R)
    rw [bdryVal_eq hy]
    have hwT : ψ w ∉ T := hside₂ w hL.le hw0
    exact exists_ball_disjoint_of_side hK.isClosed subset_union_right hψD hch hβ'c h0β'
      (fun t htc => hβ'.2.2.2.2 t htc) rfl hCK hside hy hΦy hwT

end RetChart

/-! ### The leaf from the two remaining inputs -/

/-- **The touching-pair chart boundary values from Lemma 7.5, Aux. lemma 85 (zones) and Aux. lemma 82 (mean
comparison)**: `retTouchChartBoundaryStatement_of_parts` with the side functions and the clearance proved here. -/
theorem retTouchChartBoundaryStatement_of_zones_collar (hL75 : Theorem15.Lemma75Statement.{u})
    (hZ : RetTouchZonesStatement) (hM : RetCollarMeanStatement.{u}) : RetTouchChartBoundaryStatement.{u} :=
  retTouchChartBoundaryStatement_of_parts hL75 hZ RetChart.retTouchSidesStatement RetChart.retTouchClearStatement hM

/-- **Theorem 1.5's leaf `RetTouchMeanWordStatement` from Lemma 7.5, Aux. lemma 85 and Aux. lemma 82.** -/
theorem retTouchMeanWordStatement_of_zones_collar (hL75 : Theorem15.Lemma75Statement.{u})
    (hZ : RetTouchZonesStatement) (hM : RetCollarMeanStatement.{u}) : RetTouchMeanWordStatement.{u} :=
  retTouchMeanWordStatement_of_chartBoundary hL75 (retTouchChartBoundaryStatement_of_zones_collar hL75 hZ hM)

end RLC

end InteractingSLE
