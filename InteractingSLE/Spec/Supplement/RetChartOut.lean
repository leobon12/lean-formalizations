/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetChartWord

/-!
# The touching-pair boundary values at the old common points from prime-end clearance

Packet PROVE-T15-RET5 (Aux. lemmas 82–83 and 86, supplement pp. 296–301). PROVE-T15-RET4's pathwise assembly
`RetTouch.exists_finite_tendsto_touchWord` takes the limits at the **old common points on the two outer sides** as
hypotheses (`hout₁`, `hout₂`). This file derives them from the two ingredients of Aux. lemmas 82–83, read in the
individual chart of the incident prefix:

* **clearance** (Aux. lemma 83, (OM2)): at such a point, the individual chart value `y` (positive on the first
  prefix's right side, negative on the second prefix's left side) has a ball missing the individual chart image of the
  transition hull `fill(K) ∖ fill(prefix)`;
* **mean comparison** (Aux. lemma 82): along every approach within the active domain on which the individual chart
  tends to such a cleared real point, the union mean minus the individual range mean tends to `0`.

The lift is handled by the canonical-logarithm comparison under the same clearance (`tendsto_lift_sub_of_clear`, the
argument of `Lemma76G`'s `RetData.IsMeasGood.tendsto_lift_sub` with the clearance given instead of derived from
ball-locality). Main results: `tendsto_side_of_clear` and **`exists_finite_tendsto_touchWord_of_clear`** (the touching
assembly with `hout₁`, `hout₂` replaced by clearance and mean comparison).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetChart

open Restart Supp7 Sec7 Sec7.Lemma76G Sec7.Lemma76G.ZW RetTouch

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **The retained lift minus the single-path lift under prime-end clearance** (Aux. lemma 57 in the individual chart,
with the clearance of Aux. lemma 83): along an approach `F` within the active domain on which the single-path chart
tends to a real `y` whose ball misses the chart image of the transition hull `fill(K) ∖ fill(γ[0, q])`, the retained
lift minus the single-path lift tends to `0`. -/
theorem tendsto_lift_sub_of_clear (hd : d.IsMeasGood) (ω : Ω) {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ}
    {q : ℝ≥0} (hg : IsGeneratingTrace W ζ (fun t => γ t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ})
    (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ) (hsub : γ '' Icc 0 q ⊆ d.K ω) {y ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : Disjoint (ball (y : ℂ) ρ) (physF W q x '' (fillH (d.K ω) \ fillH (γ '' Icc 0 q))))
    {F : Filter ℂ} (hF : F ≤ 𝓟 (d.D ω)) (hfy : Tendsto (physF W q x) F (𝓝 (y : ℂ))) :
    Tendsto (fun z => d.lift ω z - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) F
      (𝓝 0) := by
  have hB := hd.isHPHull ω
  obtain ⟨κ, hK, hgm, hL⟩ := ReverseArc.exists_physChart hg hWc hW0 hq
  have hdisj' : Disjoint (ball (((y + κ : ℝ)) : ℂ) ρ)
      ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (d.K ω) \
        fillH (γ '' Icc 0 q))) := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, hz, rfl⟩
    refine Set.disjoint_left.1 hdisj ?_ ⟨z, hz, rfl⟩
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    simp only [physF]
    push_cast; ring
  have hF' : F ≤ 𝓟 (H \ fillH (d.K ω)) := hF
  have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) F
      (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) F
          (𝓝 ((y : ℂ) + κ)) := hfy.add_const (κ : ℂ)
      have e : (((y + κ : ℝ)) : ℂ) = (y : ℂ) + κ := by push_cast; ring
      rw [e]
      exact h1
    · filter_upwards [hF' (mem_principal_self _)] with z hz
      exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
  exact ReverseArc.tendsto_im_sub_of_le hK hB (fillH_mono hsub) hgm (ConformalImage.isMapOut_mapOut hB) hL
    (isCanonicalDerivLog_canonDerivLog hB) hF' hρ hdisj' hq'

/-- **A side height of the union mean under prime-end clearance** (the variant of `Lemma76G.tendsto_side` for points
where the retained union is not locally one prefix): from the mean comparison along the chart approach, the clearance
of the single-path chart value and the single-path side height, `(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to the side height. -/
theorem tendsto_side_of_clear (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}
    {W : ℝ≥0 → ℝ} {q : ℝ≥0} (hg : IsGeneratingTrace W ζ (fun t => γ t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ)
    (hsub : γ '' Icc 0 q ⊆ d.K ω) {u₀ v vA : ℂ → ℝ} {χ c : ℝ} {w y ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : Disjoint (ball (y : ℂ) ρ) (physF W q x '' (fillH (d.K ω) \ fillH (γ '' Icc 0 q))))
    (hmean : Tendsto (fun z => v z - vA z) (map (d.inv ω) (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 0))
    (hfy : Tendsto (fun z => physF W q x (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ)))
    (hsh : Tendsto (fun z => vA z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im)
      (map (d.inv ω) (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c)) :
    Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + χ * d.lift ω (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ))
      (𝓝 c) := by
  obtain ⟨hT, -⟩ := RetData.IsMeasGood.tendsto_inv_real hd hE w
  have hF : map (d.inv ω) (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓟 (d.D ω) := hT.trans inf_le_right
  have h2 := tendsto_lift_sub_of_clear hd ω hg hWc hW0 hq hsub hρ hdisj hF (tendsto_map'_iff.2 hfy)
  have hsum := tendsto_map'_iff.1 (hmean.add (hsh.add (h2.const_mul χ)))
  rw [zero_add, mul_zero, add_zero] at hsum
  refine hsum.congr fun z => ?_
  simp only [Function.comp_apply]
  ring

/-- **The chart boundary values of the union mean at a touching pair, from clearance and mean comparison** (the
touching assembly `RetTouch.exists_finite_tendsto_touchWord` with its limits `hout₁`, `hout₂` at the old common points
on the outer sides derived here): at a common point `w ∈ (M₁, R₁)` on the first prefix's right side the individual
chart value is positive (`hfun₁`), its clearance (`hcl₁`) gives the mean comparison (`hm₁`) and the lift comparison
(`tendsto_lift_sub_of_clear`), and the single-path side height `hsh₁` applies with a non-real side point further
right (`exists_mem_H_of_forall_mem`); symmetrically on the second prefix's left side `(L₂, 0)`. -/
theorem exists_finite_tendsto_touchWord_of_clear (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {z : ZW} (ht : IsTouchZones α d.u β d.r (d.inv ω) z)
    (hC : IsRetChart α d.u β d.r (d.fwd ω) (d.inv ω) (d.lift ω))
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hu : (d.u : ℝ≥0∞) < ζ₁) (hr : (d.r : ℝ≥0∞) < ζ₂)
    (hu0 : 0 < d.u) (hr0 : 0 < d.r) (hK : d.K ω = prefixSet α d.u β d.r) {W₁ W₂ : ℝ≥0 → ℝ}
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hWc₁ : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW0₁ : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hWc₂ : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW0₂ : W₂ 0 = 0)
    (hfun₁ : (∀ w : ℝ, z.R₂ < w → Tendsto (fun y => physF W₁ d.u x₁ (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((bdryVal (physF W₁ d.u x₁) (d.inv ω) w : ℝ) : ℂ))) ∧
      StrictMonoOn (bdryVal (physF W₁ d.u x₁) (d.inv ω)) (Ioi z.R₂) ∧
      bdryVal (physF W₁ d.u x₁) (d.inv ω) z.M₁ = 0)
    (hfun₂ : (∀ w : ℝ, w < z.R₂ → Tendsto (fun y => physF W₂ d.r x₂ (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((bdryVal (physF W₂ d.r x₂) (d.inv ω) w : ℝ) : ℂ))) ∧
      StrictMonoOn (bdryVal (physF W₂ d.r x₂) (d.inv ω)) (Iio z.R₂) ∧
      bdryVal (physF W₂ d.r x₂) (d.inv ω) 0 = 0)
    {χ g₁ g₂ g₃ g₄ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {u₀ v vA₁ vA₂ : ℂ → ℝ}
    (hu₀ : ∀ y ∉ J, Tendsto u₀ (𝓝[H] ((y : ℝ) : ℂ)) (𝓝 (b y)))
    (hdec : ∀ x : ℝ, (∃ r > 0, Disjoint (ball ((x : ℝ) : ℂ) r) (d.K ω ∩ H)) →
      Tendsto v (𝓝[H \ (d.K ω ∩ H)] ((x : ℝ) : ℂ)) (𝓝 0))
    (hcmp₁ : ∀ p : ℂ, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} → p ∈ α '' Icc 0 d.u ∩ H ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, α '' Icc 0 d.u ∩ H ∩ ball p ρ ⊆ d.K ω ∩ H) → (∃ ρ > 0, d.K ω ∩ H ∩ ball p ρ ⊆ α '' Icc 0 d.u ∩ H) →
      Tendsto (fun z => v z - vA₁ z) (𝓝[H \ (d.K ω ∩ H ∪ α '' Icc 0 d.u ∩ H)] p) (𝓝 0))
    (hcmp₂ : ∀ p : ℂ, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} → p ∈ β '' Icc 0 d.r ∩ H ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, β '' Icc 0 d.r ∩ H ∩ ball p ρ ⊆ d.K ω ∩ H) → (∃ ρ > 0, d.K ω ∩ H ∩ ball p ρ ⊆ β '' Icc 0 d.r ∩ H) →
      Tendsto (fun z => v z - vA₂ z) (𝓝[H \ (d.K ω ∩ H ∪ β '' Icc 0 d.r ∩ H)] p) (𝓝 0))
    (hsh₁ : ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p → ∀ y : ℝ,
      Tendsto (physF W₁ d.u x₁) F (𝓝 (y : ℂ)) →
      (0 < y → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p' ∧
          Tendsto (physF W₁ d.u x₁) G (𝓝 (y' : ℂ)) ∧ y < y' ∧ p' ∈ H) →
        Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal) d.u
          (z - x₁)).im) F (𝓝 g₄)) ∧
      (y < 0 → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p' ∧
          Tendsto (physF W₁ d.u x₁) G (𝓝 (y' : ℂ)) ∧ y' < y ∧ p' ∈ H) →
        Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal) d.u
          (z - x₁)).im) F (𝓝 g₃)))
    (hsh₂ : ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p → ∀ y : ℝ,
      Tendsto (physF W₂ d.r x₂) F (𝓝 (y : ℂ)) →
      (0 < y → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p' ∧
          Tendsto (physF W₂ d.r x₂) G (𝓝 (y' : ℂ)) ∧ y < y' ∧ p' ∈ H) →
        Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal) d.r
          (z - x₂)).im) F (𝓝 g₂)) ∧
      (y < 0 → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p' ∧
          Tendsto (physF W₂ d.r x₂) G (𝓝 (y' : ℂ)) ∧ y' < y ∧ p' ∈ H) →
        Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal) d.r
          (z - x₂)).im) F (𝓝 g₁)))
    (hcl₁ : ∀ w : ℝ, z.M₁ < w → w < z.R₁ → d.inv ω w ∈ β '' Icc 0 d.r → ∃ ρ > 0,
      Disjoint (ball ((bdryVal (physF W₁ d.u x₁) (d.inv ω) w : ℝ) : ℂ) ρ)
        (physF W₁ d.u x₁ '' (fillH (prefixSet α d.u β d.r) \ fillH (α '' Icc 0 d.u))))
    (hcl₂ : ∀ w : ℝ, z.L₂ < w → w < 0 → d.inv ω w ∈ α '' Icc 0 d.u → ∃ ρ > 0,
      Disjoint (ball ((bdryVal (physF W₂ d.r x₂) (d.inv ω) w : ℝ) : ℂ) ρ)
        (physF W₂ d.r x₂ '' (fillH (prefixSet α d.u β d.r) \ fillH (β '' Icc 0 d.r))))
    (hm₁ : ∀ y ρ : ℝ, 0 < ρ →
      Disjoint (ball (y : ℂ) ρ) (physF W₁ d.u x₁ '' (fillH (prefixSet α d.u β d.r) \ fillH (α '' Icc 0 d.u))) →
      ∀ F : Filter ℂ, F ≤ 𝓟 (d.D ω) → Tendsto (physF W₁ d.u x₁) F (𝓝 (y : ℂ)) →
        Tendsto (fun z => v z - vA₁ z) F (𝓝 0))
    (hm₂ : ∀ y ρ : ℝ, 0 < ρ →
      Disjoint (ball (y : ℂ) ρ) (physF W₂ d.r x₂ '' (fillH (prefixSet α d.u β d.r) \ fillH (β '' Icc 0 d.r))) →
      ∀ F : Filter ℂ, F ≤ 𝓟 (d.D ω) → Tendsto (physF W₂ d.r x₂) F (𝓝 (y : ℂ)) →
        Tendsto (fun z => v z - vA₂ z) F (𝓝 0))
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = J)
    (hc₀b : ∀ y ∉ J, c₀.fn y = b y) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
      Tendsto (fun y => v (d.inv ω y) + u₀ (d.inv ω y) + χ * d.lift ω (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((z.word c₀ g₁ g₂ g₃ g₄).fn w)) := by
  have hz := ht.good
  set ψ := d.inv ω with hψdef
  have h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₂]; simp
  have hψc : ContinuousOn ψ Hbar := hC.continuousOn_inv
  have hψd : DifferentiableOn ℂ ψ H := hC.differentiableOn_inv
  have hbij : BijOn ψ H (activeDomain α d.u β d.r) := hC.bijOn h0₂
  have hψi : InjOn ψ H := hbij.injOn
  have hψim : ∀ w ∈ Hbar, 0 ≤ (ψ w).im := fun w hw =>
    Lemma76E.im_nonneg_of_mapsTo hψc (fun _ hv => (hbij.mapsTo hv).1.1) hw
  have hD : d.D ω = H \ fillH (prefixSet α d.u β d.r) := by
    show H \ fillH (d.K ω) = _
    rw [hK]
  have happ : ∀ w : ℝ, map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[d.D ω] (ψ w) := fun w =>
    (RetData.IsMeasGood.tendsto_inv_real hd hE w).1
  have hne : ∀ w : ℝ, (map ψ (𝓝[H] ((w : ℝ) : ℂ))).NeBot := fun w => (neBot_nhdsWithin_H w).map _
  have hD₁ : d.D ω ⊆ H \ fillH (α '' Icc 0 d.u) := hD ▸ IsSetting.fill₁_subset
  have hD₂ : d.D ω ⊆ H \ fillH (β '' Icc 0 d.r) := hD ▸ IsSetting.fill₂_subset
  have hRM : z.R₂ < z.M₁ := ht.R₂_lt_M₁
  have h0R : (0 : ℝ) < z.R₂ := ht.zero_lt_R₂
  have hmem₁ : ∀ t : ℝ, z.R₂ < t → t < z.R₁ → ψ t ∈ α '' Icc 0 d.u := fun t h1 h2 => by
    rcases lt_trichotomy t z.M₁ with h | rfl | h
    · exact (ht.side₃ t (ht.junction ▸ h1) h).1
    · rw [ht.tip₁]; exact ⟨d.u, ⟨zero_le, le_rfl⟩, rfl⟩
    · exact ht.side₄ t h h2
  have hsub₁ : α '' Icc 0 d.u ⊆ d.K ω := hK ▸ subset_union_left
  have hsub₂ : β '' Icc 0 d.r ⊆ d.K ω := hK ▸ subset_union_right
  -- the first prefix's right side at an old common point
  have hout₁ : ∀ w : ℝ, z.M₁ < w → w < z.R₁ → ψ w ∈ β '' Icc 0 d.r →
      Tendsto (fun y => v (ψ y) + u₀ (ψ y) + χ * d.lift ω (ψ y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₄) := by
    intro w hgt h2 hβw
    have h1 : z.R₂ < w := hRM.trans hgt
    obtain ⟨hlim, hmono, htip⟩ := hfun₁
    have hy : 0 < bdryVal (physF W₁ d.u x₁) ψ w := htip ▸ hmono hRM h1 hgt
    obtain ⟨ρ, hρ, hdisj⟩ := hcl₁ w hgt h2 hβw
    have hfy := hlim w h1
    have hF : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓟 (d.D ω) := (happ w).trans inf_le_right
    have hmean := hm₁ _ ρ hρ hdisj _ hF (tendsto_map'_iff.2 hfy)
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₁)
    have hsh := hsh₁ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₁ hu.le hψc hψd hψi hψim h2
      fun t ht' => hmem₁ t (h1.trans ht'.1) ht'.2
    rw [← hK] at hdisj
    exact tendsto_side_of_clear hd hE hg₁ hWc₁ hW0₁ hu hsub₁ hρ hdisj hmean hfy
      (hsh.1 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₁),
        tendsto_map'_iff.2 (hlim w' (h1.trans hw'.1)), hmono h1 (h1.trans hw'.1) hw'.1, hw'H⟩)
  -- the second prefix's left side at an old common point
  have hout₂ : ∀ w : ℝ, z.L₂ < w → w < 0 → ψ w ∈ α '' Icc 0 d.u →
      Tendsto (fun y => v (ψ y) + u₀ (ψ y) + χ * d.lift ω (ψ y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₁) := by
    intro w h1 hlt hαw
    have h2 : w < z.R₂ := hlt.trans h0R
    obtain ⟨hlim, hmono, htip⟩ := hfun₂
    have hy : bdryVal (physF W₂ d.r x₂) ψ w < 0 := htip ▸ hmono h2 h0R hlt
    obtain ⟨ρ, hρ, hdisj⟩ := hcl₂ w h1 hlt hαw
    have hfy := hlim w h2
    have hF : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓟 (d.D ω) := (happ w).trans inf_le_right
    have hmean := hm₂ _ ρ hρ hdisj _ hF (tendsto_map'_iff.2 hfy)
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₂)
    have hsh := hsh₂ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₂ hr.le hψc hψd hψi hψim h1
      fun t ht' => ht.side₂ t ht'.1 (ht'.2.trans h2)
    rw [← hK] at hdisj
    exact tendsto_side_of_clear hd hE hg₂ hWc₂ hW0₂ hr hsub₂ hρ hdisj hmean hfy
      (hsh.2 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₂),
        tendsto_map'_iff.2 (hlim w' (hw'.2.trans h2)), hmono (hw'.2.trans h2) h2 hw'.2, hw'H⟩)
  exact exists_finite_tendsto_touchWord hd hE ht hC hp₁ hp₂ hu hr hu0 hr0 hK hg₁ hWc₁ hW0₁ hg₂ hWc₂ hW0₂ hfun₁
    hfun₂ hu₀ hdec hcmp₁ hcmp₂ hsh₁ hsh₂ hout₁ hout₂ hc₀ hc₀J hc₀b

end RetChart

end RLC

end InteractingSLE
