/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoChart
import InteractingSLE.Spec.Supplement.SBS3AssemblyUpper
import InteractingSLE.Spec.Supplement.SBS3EntryGap
import InteractingSLE.Spec.Supplement.SBS3CanonComp
import InteractingSLE.Spec.Supplement.SBS3PrimeDomains

/-!
# Lemma S3: the protected comparison at one sample (upper orientation)

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). Deterministic. The per-sample core of the
source assembly of `RationalProtectedWordStatement`: from the geometry on S2's lift
(`Geo.exists_s3_geometry_of_chart`), the old and second mean formulas with canonical logarithms, the schedule labels,
the exposed second value, the actual explored sets' protected marked union means (`ae_markedUnionMeans_stages`'
per-sample form), and the old phase gap (`exists_ball_disjoint_joint_transition_of_lift`), build the whole
`ProtectedWordComparison` with its label:

* `MarkedUnionMeans.restrict_hulls`: restrict the actual comparison to the filled hulls on a smaller open set;
* `isHPHull_fillH_image`: the fill of a curve image through a real point is a hull;
* **`exists_protectedWordComparison_upper`**: the cut time is chosen in the open common interval off the finitely many
  marks of both words (the old coordinate and the second limit are injective in the time); both readouts, both phase
  gaps (through the canonical map-outs `ConformalImage.mapOut`, equal to the hull models off the hulls), and the
  marked means restricted to `freeNear ∩ freeNear ∩ (ℍ ∖ fill(A ∪ η[0, q₂]))`.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open InteractingSLE.Restart
open Geo Canon
open Supp9B (IsProperCurve leftSide rightSide closedRightSide)

/-- **Protected comparisons restrict to larger obstacles.** Marked union means of two sets restrict to any larger
pair of sets on any smaller open domain avoiding them (the same representatives, the same distributional means). -/
theorem MarkedUnionMeans.restrict_hulls {A B A₁ A₂ O O' : Set ℂ} {p : ℂ} {v₁ v₂ : ℂ → ℝ}
    (h : MarkedUnionMeans A B O p v₁ v₂) (hA : A ⊆ A₁) (hB : B ⊆ A₂) (hO' : IsOpen O') (hO'O : O' ⊆ O)
    (hO'1 : O' ⊆ H \ A₁) (hO'2 : O' ⊆ H \ A₂) : MarkedUnionMeans A₁ A₂ O' p v₁ v₂ := by
  have hHA : H \ A₁ ⊆ H \ A := fun z hz => ⟨hz.1, fun h' => hz.2 (hA h')⟩
  have hHB : H \ A₂ ⊆ H \ B := fun z hz => ⟨hz.1, fun h' => hz.2 (hB h')⟩
  obtain ⟨G, G₁, G₂, ua, ub, hv₁, hr₁, hv₂, hr₂, hua, hra, hub, hrb, ha, hb⟩ := h.representatives
  exact ⟨hO', hO'1, hO'2, G, G₁, G₂, ua, ub, fun x hx => hv₁ x (hHA hx),
    fun φ hφ => hr₁ φ (hφ.trans hHA), fun x hx => hv₂ x (hHB hx), fun φ hφ => hr₂ φ (hφ.trans hHB),
    fun x hx => hua x (hO'O hx), fun φ hφ => hra φ (hφ.trans hO'O), fun x hx => hub x (hO'O hx),
    fun φ hφ => hrb φ (hφ.trans hO'O), ha.mono_left (nhdsWithin_mono _ hO'O),
    hb.mono_left (nhdsWithin_mono _ hO'O)⟩

/-- The fill of a bounded set through a real point (with the lower half-plane preconnected) is a hull. -/
theorem isHPHull_fillH_image {γ : ℝ≥0 → ℂ} {q : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 q)) (hγ0 : (γ 0).im = 0) :
    IsHPHull (fillH (γ '' Icc 0 q)) := by
  refine isHPHull_fillH_of_isPreconnected (isCompact_Icc.image_of_continuousOn hγ).isBounded ?_
  exact (isPreconnected_Icc.image _ hγ).union (γ 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
    (show (γ 0).im ≤ 0 by rw [hγ0]) isPreconnected_lowerHalf

/-- **Lemma S3's protected comparison at one sample (upper orientation).** Deterministic assembly. Data: the old path
image `A` on the closed right of the proper witness `β'`, a left entry chart `c` of `A` with finite-fibre boundary map
`g` (linear growth), its hull model `c + e₁` and the old mean formula with the canonical logarithm of `fill A` (word
`word`, schedule labels at interior landings); a core chart `(f, Φ)` of the witness prefix up to `q₂` with hull model
`f + e₂`, the second mean formula (word `word₂`) and the exposed left value (off a finite set `Jx`); the actual
explored sets `A' ⊆ fill A`, `B' ⊆ fill η[0, q₂]` containing the arcs in `ℍ`, with the protected marked union means of
the same representatives at every point and radii; the visit `t₀ ≤ q₁` of `L`. If `η([q₁, q₂]) ⊆ A ∩ ℍ`, the
comparison data exist, with the schedule label. -/
theorem exists_protectedWordComparison_upper {κ ϑ : ℝ} {l : List (ℝ × ℝ≥0)}
    {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    {c : Chart} {g : ℂ → ℂ} (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite)
    (hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    {e₁ : ℝ} (hmo₁ : IsMapOut (fillH (p '' Icc 0 1)) (fun z => c.1 z + (e₁ : ℂ)))
    {word : BoundaryWord} (hws : word.IsSorted) {v₁ u₀ : ℂ → ℝ}
    (hmean₁ : EqOn (fun z => v₁ z + u₀ z + chiC κ * (canonDerivLog (fillH (p '' Icc 0 1)) z).im)
      (fun z => word.mean (c.1 z)) (H \ fillH (p '' Icc 0 1)))
    (hlabel : ∀ y : ℝ, y ∉ word.jumps → g y ∈ H → Lh.SideH κ l (word.fn y))
    {η : ℝ≥0 → ℂ} {q₁ q₂ : ℝ≥0} (hag : ∀ s ≤ q₂, β' s = η s)
    {f Φ : ℂ → ℂ} (hch : IsChartCore β' q₂ f Φ) (hfd : DifferentiableOn ℂ f (H \ fillH (β' '' Icc 0 q₂)))
    (hfin : ∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) (hDo : IsOpen (H \ fillH (β' '' Icc 0 q₂)))
    {e₂ : ℝ} (hmo₂ : IsMapOut (fillH (η '' Icc 0 q₂)) (fun z => f z + (e₂ : ℂ)))
    {word₂ : BoundaryWord} (hws₂ : word₂.IsSorted) {v₂ : ℂ → ℝ}
    (hmean₂ : EqOn (fun z => v₂ z + u₀ z + chiC κ * (canonDerivLog (fillH (η '' Icc 0 q₂)) z).im)
      (fun z => word₂.mean (f z)) (H \ fillH (η '' Icc 0 q₂)))
    {Jx : Finset ℝ}
    (hexp : ∀ y : ℝ, y < 0 → y ∉ word₂.jumps → y ∉ Jx → Φ y ∈ H → word₂.fn y = -sleLambda κ - ϑ * chiC κ)
    {A' B' : Set ℂ} (hA'o : IsOpen (H \ A')) (hB'o : IsOpen (H \ B'))
    (hA'f : A' ⊆ fillH (p '' Icc 0 1)) (hB'f : B' ⊆ fillH (η '' Icc 0 q₂))
    (hA'a : p '' Icc 0 1 ∩ H ⊆ A') (hB'a : η '' Icc 0 q₂ ∩ H ⊆ B')
    (hunion : ∀ x₀ : ℂ, x₀ ∈ A' ∪ {z : ℂ | z.im = 0} → x₀ ∈ B' ∪ {z : ℂ | z.im = 0} → ∀ rA > 0, ∀ rB > 0,
      MarkedUnionMeans A' B' (FinRel.freeNear B' A' x₀ rA ∩ FinRel.freeNear A' B' x₀ rB) x₀ v₁ v₂)
    {t₀ : ℝ≥0} (ht₀ : β' t₀ = realMin (p '' Icc 0 1)) (ht₀q : t₀ ≤ q₁) (hq : q₁ < q₂)
    (harc : η '' Icc q₁ q₂ ⊆ p '' Icc 0 1 ∩ H) :
    ∃ d : ProtectedWordComparison κ (-sleLambda κ - ϑ * chiC κ) (p '' Icc 0 1) η q₁ q₂,
      Lh.SideH κ l (d.word.fn d.coordinate) := by
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have himg : β' '' Icc 0 q₂ = η '' Icc 0 q₂ := image_congr fun s hs => hag s hs.2
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hD := hc.1
  -- the geometry on S2's lift
  obtain ⟨tL, γ, htL, hγp, hγ0, hlift, hall⟩ := exists_s3_geometry_of_chart hp hp0 hpH hβ' hβ'0 hA hc hgc hgi hgf
  have htLt₀ : tL = t₀ := hβ'.2.1 (htL.trans ht₀.symm)
  have htLq : tL ≤ q₁ := htLt₀ ▸ ht₀q
  set a : ℝ≥0 := q₁ - tL with ha
  set b : ℝ≥0 := q₂ - tL with hb
  have hta : tL + a = q₁ := add_tsub_cancel_of_le htLq
  have htb : tL + b = q₂ := add_tsub_cancel_of_le (htLq.trans hq.le)
  have hab : a < b := by
    have : tL + a < tL + b := by rw [hta, htb]; exact hq
    exact lt_of_add_lt_add_left this
  have harc' : β' '' Icc (tL + a) (tL + b) ⊆ A := by
    rw [hta, htb]
    rintro _ ⟨s, hs, rfl⟩
    rw [hag s hs.2]
    exact (harc ⟨s, hs, rfl⟩).1
  have hqH : β' (tL + b) ∈ H := by
    rw [htb, hag q₂ le_rfl]; exact (harc ⟨q₂, ⟨hq.le, le_rfl⟩, rfl⟩).2
  have hmemI : ∀ t ∈ Ioo a b, tL + t ∈ Icc q₁ q₂ := fun t ht =>
    ⟨hta ▸ (add_le_add le_rfl ht.1.le), htb ▸ (add_le_add le_rfl ht.2.le)⟩
  have hmemO : ∀ t ∈ Ioo a b, tL + t ∈ Ioo q₁ q₂ := fun t ht =>
    ⟨hta ▸ (add_lt_add_of_le_of_lt le_rfl ht.1), htb ▸ (add_lt_add_of_le_of_lt le_rfl ht.2)⟩
  have hch' : IsChartCore β' (tL + b) f Φ := by rw [htb]; exact hch
  have hfd' : DifferentiableOn ℂ f (H \ fillH (β' '' Icc 0 (tL + b))) := by rw [htb]; exact hfd
  have hDo' : IsOpen (H \ fillH (β' '' Icc 0 (tL + b))) := by rw [htb]; exact hDo
  -- realness of the lifted arc
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := fun s hs =>
    im_eq_zero_of_landing_mem hD hgi (hγp.2.2.1 s)
      (by rw [hlift s]; exact harc' ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩)
  -- the second limits, chosen for every time
  have hY : ∀ t ∈ Ioo a b, ∃ y : ℝ, y < 0 ∧ Φ y = β' (tL + t) ∧
      Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) ∧
      ∃ r > 0, Disjoint (ball (y : ℂ) r)
        (f '' (fillH (A ∪ β' '' Icc 0 (tL + b)) \ fillH (β' '' Icc 0 (tL + b)))) := fun t ht =>
    (hall a b t ht harc' hqH).2.2.2.2.2 hch' hfd' hfin hDo'
  choose! Y hY using hY
  -- an unmarked time
  have hinjY : InjOn Y (Ioo a b) := fun t ht t' ht' he => by
    have h1 : β' (tL + t) = β' (tL + t') := by rw [← (hY t ht).2.1, ← (hY t' ht').2.1, he]
    exact add_left_cancel (hβ'.2.1 h1)
  have hinjX : InjOn (fun t => (γ t).re) (Ioo a b) := fun t ht t' ht' he => by
    apply hγp.2.1
    exact Complex.ext he ((hreal t ⟨ht.1.le, ht.2.le⟩).trans (hreal t' ⟨ht'.1.le, ht'.2.le⟩).symm)
  have hbad₁ : (Ioo a b ∩ (fun t => (γ t).re) ⁻¹' (word.jumps : Set ℝ)).Finite :=
    Set.Finite.of_finite_image (word.jumps.finite_toSet.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2))
      (hinjX.mono inter_subset_left)
  have hbad₂ : (Ioo a b ∩ Y ⁻¹' ((word₂.jumps ∪ Jx : Finset ℝ) : Set ℝ)).Finite :=
    Set.Finite.of_finite_image ((word₂.jumps ∪ Jx).finite_toSet.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2))
      (hinjY.mono inter_subset_left)
  obtain ⟨t, htI, htn⟩ := ((Set.Ioo_infinite hab).sdiff (hbad₁.union hbad₂)).nonempty
  have ht : t ∈ Ioo a b := htI
  have hx : (γ t).re ∉ word.jumps := fun h => htn (Or.inl ⟨ht, h⟩)
  have hy : Y t ∉ word₂.jumps := fun h => htn (Or.inr ⟨ht, by simp [h]⟩)
  have hyx : Y t ∉ Jx := fun h => htn (Or.inr ⟨ht, by simp [h]⟩)
  obtain ⟨-, hne, hFL, hFJ, hacc, -⟩ := hall a b t ht harc' hqH
  obtain ⟨hy0, hΦy, hfy, r₂, hr₂, hgap₂⟩ := hY t ht
  set F := Filter.map g (𝓝[H] (γ t)) with hFdef
  set x : ℝ := (γ t).re with hxdef
  set y : ℝ := Y t with hydef
  set pt : ℂ := β' (tL + t) with hptdef
  have hptη : pt = η (tL + t) := hag _ (hmemI t ht).2
  have hptA : pt ∈ A ∩ H := by rw [hptη]; exact harc ⟨tL + t, hmemI t ht, rfl⟩
  have hγt : γ t = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [hreal t ⟨ht.1.le, ht.2.le⟩])
  have hFne : F.NeBot := hne.map g
  -- sets
  set B₀ : Set ℂ := η '' Icc 0 q₂ with hB₀
  have hjoint : fillH (A ∪ β' '' Icc 0 (tL + b)) = fillH (A ∪ B₀) := by rw [htb, himg]
  have hsec : fillH (β' '' Icc 0 (tL + b)) = fillH B₀ := by rw [htb, himg]
  have hFD : F ≤ 𝓟 (H \ fillH (A ∪ B₀)) := by
    rw [← hjoint]; exact hFL.trans (principal_mono.2 inter_subset_right)
  have hFJ' : F ≤ 𝓝[H \ fillH (A ∪ B₀)] pt := by rw [← hjoint]; exact hFJ
  have hDA : H \ fillH (A ∪ B₀) ⊆ H \ fillH A := fun z hz => ⟨hz.1, fun h => hz.2 (fillH_mono subset_union_left h)⟩
  have hDB : H \ fillH (A ∪ B₀) ⊆ H \ fillH B₀ := fun z hz => ⟨hz.1, fun h => hz.2 (fillH_mono subset_union_right h)⟩
  -- hulls
  have hβc : ContinuousOn β' (Icc 0 q₂) := hβ'.1.continuousOn
  have hKA : IsHPHull (fillH A) := by
    refine isHPHull_fillH_of_isPreconnected hAc.isBounded ?_
    refine (isPreconnected_Icc.image _ hp).union (p 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      (show (p 0).im ≤ 0 by rw [hp0, Complex.zero_im]) isPreconnected_lowerHalf
  have hKB : IsHPHull (fillH B₀) := by
    rw [← himg]; exact isHPHull_fillH_image hβc (by rw [hβ'0, Complex.zero_im])
  have hKJ : IsHPHull (fillH (A ∪ B₀)) := by
    rw [← himg]
    have hBc : IsCompact (β' '' Icc 0 q₂) := isCompact_Icc.image_of_continuousOn hβc
    refine isHPHull_fillH_of_isPreconnected (hAc.union hBc).isBounded ?_
    have h1 : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) :=
      (isPreconnected_Icc.image _ hp).union (p 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
        (show (p 0).im ≤ 0 by rw [hp0, Complex.zero_im]) isPreconnected_lowerHalf
    have h2 : IsPreconnected (β' '' Icc 0 q₂ ∪ {z : ℂ | z.im ≤ 0}) :=
      (isPreconnected_Icc.image _ hβc).union (β' 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        (show (β' 0).im ≤ 0 by rw [hβ'0, Complex.zero_im]) isPreconnected_lowerHalf
    have h3 := h1.union (0 : ℂ) (Or.inr (show (0 : ℂ).im ≤ 0 by simp))
      (Or.inr (show (0 : ℂ).im ≤ 0 by simp)) h2
    have he : A ∪ β' '' Icc 0 q₂ ∪ {z : ℂ | z.im ≤ 0} =
        (A ∪ {z : ℂ | z.im ≤ 0}) ∪ (β' '' Icc 0 q₂ ∪ {z : ℂ | z.im ≤ 0}) := by
      ext z; simp only [mem_union]; tauto
    rw [he]; exact h3
  -- the old chart along the approach
  have hc1 : Tendsto c.1 F (𝓝[H] (x : ℂ)) := by
    rw [hFdef, tendsto_map'_iff, ← hγt]
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
    · refine (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (γ t))).mono_left le_rfl |>.congr' ?_
      · filter_upwards [self_mem_nhdsWithin] with w hw
        show w = c.1 (g w)
        rw [hgi hw, hD.fwd_inv hw]
    · show c.1 (g w) ∈ H
      rw [hgi hw, hD.fwd_inv hw]; exact hw
  -- readouts
  have hold : IsChartWordMean κ word x F v₁ u₀ (canonDerivLog (fillH A)) := by
    refine ⟨hws, hx, c.1, hc1, ?_⟩
    filter_upwards [hFD (mem_principal_self _)] with z hz
    exact hmean₁ (hDA hz)
  have hsec_read : IsChartWordMean κ word₂ y F v₂ u₀ (canonDerivLog (fillH B₀)) := by
    refine ⟨hws₂, hy, f, hfy, ?_⟩
    filter_upwards [hFD (mem_principal_self _)] with z hz
    exact hmean₂ (hDB hz)
  have hΦH : Φ y ∈ H := by rw [hΦy]; exact hptA.2
  have hval : word₂.fn y = -sleLambda κ - ϑ * chiC κ := hexp y hy0 hy hyx hΦH
  have hlab : Lh.SideH κ l (word.fn x) := by
    refine hlabel x hx ?_
    rw [← hγt, hlift t]; exact hptA.2
  -- the old phase gap
  obtain ⟨C₁, C₂, hC₁, hgb'⟩ := hgb
  have hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂ := fun w hw => by
    rw [← hgi hw]; exact hgb' w (le_of_lt (show (0 : ℝ) < w.im from hw))
  obtain ⟨-, tL', htL', -, hpre, -, -⟩ := s2HullStatement p β' hp hp0 hpH hβ' hβ'0 hA
  have htLL : tL' = tL := hβ'.2.1 (htL'.trans htL.symm)
  rw [htLL] at hpre
  obtain ⟨ρ, hρ, hgap₁⟩ := exists_ball_disjoint_joint_transition_of_lift hD hgc hgi hC₁ hgrow hAc.isClosed
    hβ'.1 hγp hpre hlift ht.1 ht.2.le hreal
  rw [hjoint] at hgap₁ hgap₂
  rw [hsec] at hgap₂
  -- the canonical map-outs
  have hm₁ := ConformalImage.isMapOut_mapOut hKA
  have hm₂ := ConformalImage.isMapOut_mapOut hKB
  have hmJ := ConformalImage.isMapOut_mapOut hKJ
  have he₁ : EqOn (ConformalImage.mapOut (fillH A)) (fun z => c.1 z + (e₁ : ℂ)) (H \ fillH A) :=
    hm₁.eqOn hKA hmo₁
  have he₂ : EqOn (ConformalImage.mapOut (fillH B₀)) (fun z => f z + (e₂ : ℂ)) (H \ fillH B₀) :=
    hm₂.eqOn hKB hmo₂
  have hBA : fillH (A ∪ B₀) \ fillH A ⊆ H \ fillH A := fun z hz => ⟨fillH_subset_H _ hz.1, hz.2⟩
  have hBB : fillH (A ∪ B₀) \ fillH B₀ ⊆ H \ fillH B₀ := fun z hz => ⟨fillH_subset_H _ hz.1, hz.2⟩
  have hgap₁' : Disjoint (ball (((x + e₁ : ℝ)) : ℂ) ρ)
      (ConformalImage.mapOut (fillH A) '' (fillH (A ∪ B₀) \ fillH A)) := by
    rw [Set.disjoint_left]
    rintro _ hu ⟨z, hz, rfl⟩
    refine Set.disjoint_left.1 hgap₁ ?_ ⟨z, hz, rfl⟩
    rw [he₁ (hBA hz), mem_ball, Complex.dist_eq] at hu
    rw [mem_ball, Complex.dist_eq, hγt]
    have h1 : c.1 z + (e₁ : ℂ) - ((x + e₁ : ℝ) : ℂ) = c.1 z - (x : ℂ) := by push_cast; ring
    rwa [h1] at hu
  have hgap₂' : Disjoint (ball (((y + e₂ : ℝ)) : ℂ) r₂)
      (ConformalImage.mapOut (fillH B₀) '' (fillH (A ∪ B₀) \ fillH B₀)) := by
    rw [Set.disjoint_left]
    rintro _ hu ⟨z, hz, rfl⟩
    refine Set.disjoint_left.1 hgap₂ ?_ ⟨z, hz, rfl⟩
    rw [he₂ (hBB hz), mem_ball, Complex.dist_eq] at hu
    rw [mem_ball, Complex.dist_eq]
    have h1 : f z + (e₂ : ℂ) - ((y + e₂ : ℝ) : ℂ) = f z - (y : ℂ) := by push_cast; ring
    rwa [h1] at hu
  have hev₁ : ∀ᶠ z in F, ConformalImage.mapOut (fillH A) z = c.1 z + (e₁ : ℂ) := by
    filter_upwards [hFD (mem_principal_self _)] with z hz using he₁ (hDA hz)
  have hev₂ : ∀ᶠ z in F, ConformalImage.mapOut (fillH B₀) z = f z + (e₂ : ℂ) := by
    filter_upwards [hFD (mem_principal_self _)] with z hz using he₂ (hDB hz)
  have hlim₁ : Tendsto (ConformalImage.mapOut (fillH A)) F (𝓝[H] (((x + e₁ : ℝ)) : ℂ)) :=
    ((translate_second (y := x) (X := ∅) (r := 1) e₁ hc1 (by simp)).1).congr' (hev₁.mono fun z hz => hz.symm)
  have hlim₂ : Tendsto (ConformalImage.mapOut (fillH B₀)) F (𝓝[H] (((y + e₂ : ℝ)) : ℂ)) :=
    ((translate_second (y := y) (X := ∅) (r := 1) e₂ hfy (by simp)).1).congr' (hev₂.mono fun z hz => hz.symm)
  have hphases : JointPhaseGaps (fillH A) (fillH B₀) (fillH (A ∪ B₀)) F (canonDerivLog (fillH A))
      (canonDerivLog (fillH B₀)) :=
    ⟨hKA, hKB, hKJ, fillH_mono subset_union_left, fillH_mono subset_union_right, hFD,
      ConformalImage.mapOut (fillH A), ConformalImage.mapOut (fillH B₀), ConformalImage.mapOut (fillH (A ∪ B₀)),
      canonDerivLog (fillH (A ∪ B₀)), x + e₁, y + e₂, ρ, r₂, hm₁, hm₂, hmJ,
      isCanonicalDerivLog_canonDerivLog hKA, isCanonicalDerivLog_canonDerivLog hKB,
      isCanonicalDerivLog_canonDerivLog hKJ, hρ, hr₂, hgap₁', hgap₂', hlim₁, hlim₂⟩
  -- the protected marked means
  have hA'J : A' ⊆ fillH (A ∪ β' '' Icc 0 (tL + b)) := by
    rw [hjoint]; exact hA'f.trans (fillH_mono subset_union_left)
  have hB'J : B' ⊆ fillH (A ∪ β' '' Icc 0 (tL + b)) := by
    rw [hjoint]; exact hB'f.trans (fillH_mono subset_union_right)
  have harcA' : β' '' Icc (tL + a) (tL + b) ⊆ A' := fun z hz => by
    obtain ⟨s, hs, rfl⟩ := hz
    refine hA'a ⟨harc' ⟨s, hs, rfl⟩, ?_⟩
    rw [htb] at hs
    rw [hag s hs.2]
    have : tL + a ≤ s := hs.1
    rw [hta] at this
    exact (harc ⟨s, ⟨this, hs.2⟩, rfl⟩).2
  have harcB' : β' '' Icc (tL + a) (tL + b) ⊆ B' := fun z hz => by
    obtain ⟨s, hs, rfl⟩ := hz
    have hs' : s ∈ Icc q₁ q₂ := by rw [← hta, ← htb]; exact hs
    refine hB'a ⟨⟨s, ⟨zero_le, hs'.2⟩, (hag s hs'.2).symm⟩, ?_⟩
    rw [hag s hs'.2]; exact (harc ⟨s, hs', rfl⟩).2
  obtain ⟨rA, hrA, hFA⟩ := hacc A' B' harcA' hA'J hB'J
  obtain ⟨rB, hrB, hFB⟩ := hacc B' A' harcB' hB'J hA'J
  have hptA' : pt ∈ A' := hA'a hptA
  have hptB' : pt ∈ B' := hB'a ⟨⟨tL + t, ⟨zero_le, (hmemI t ht).2⟩, hptη.symm⟩, hptA.2⟩
  have hU := hunion pt (Or.inl hptA') (Or.inl hptB') rA hrA rB hrB
  set O : Set ℂ := FinRel.freeNear B' A' pt rA ∩ FinRel.freeNear A' B' pt rB with hOdef
  have hOo : IsOpen (O ∩ (H \ fillH (A ∪ B₀))) :=
    ((isOpen_freeNear hA'o pt rA).inter (isOpen_freeNear hB'o pt rB)).inter hKJ.2.2.1
  have hmeans := MarkedUnionMeans.restrict_hulls hU hA'f hB'f hOo inter_subset_left
    (fun z hz => hDA hz.2) (fun z hz => hDB hz.2)
  have happ : F ≤ 𝓝[O ∩ (H \ fillH (A ∪ B₀))] pt := by
    rw [hOdef, nhdsWithin_inter, nhdsWithin_inter]
    exact le_inf (le_inf hFA hFB) hFJ'
  refine ⟨⟨pt, F, ⟨tL + t, hmemO t ht, hptη.symm⟩, hFne, hFJ', word, x,
    v₁, v₂, u₀, canonDerivLog (fillH A), canonDerivLog (fillH B₀), O ∩ (H \ fillH (A ∪ B₀)), happ,
    hmeans, hphases, hold, ⟨word₂, y, hsec_read, hval⟩⟩, hlab⟩

end InteractingSLE.Theorem14.SB.S3.Asm
