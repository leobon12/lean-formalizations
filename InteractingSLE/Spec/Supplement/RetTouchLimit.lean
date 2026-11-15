/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetTouchZones
import InteractingSLE.Spec.Sec7.Lemma76GLimit

/-!
# The chart boundary values of the union mean at a touching retained pair (pathwise assembly)

Packet PROVE-T15-RET4 (Aux. lemma 86's boundary part, supplement p. 301). The touching analogue of PROVE-LEMMA76G's
`Sec7.Lemma76G.exists_finite_tendsto_word`: at a touching retained pair whose chart has the outer boundary (OF2)
(`IsTouchZones`), outside the jumps of the touching word and the five transition chart points `L₂, 0, J, M₁, R₁`,
`(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to the word datum. The inputs are those of the disjoint case:

* the decay of the union mean at untouched real points (`hdec`), the ball-local comparisons with the two single-path
  range means (`hcmp₁`, `hcmp₂`), the single-path side heights (`hsh₁`, `hsh₂`);
* the two single-path side functions along the sides (`hfun₁` on `(J, ∞)`, `hfun₂` on `(−∞, J)`: limits,
  monotonicity and the tips; the form of `Sec7.Lemma76G.IsSetting.side₁` / `side₂`);

and, new in the touching case, the limits at the **old common points on the two outer sides** (`hout₁` on the first
prefix's right side `(M₁, R₁)`, `hout₂` on the second prefix's left side `(L₂, 0)`): there the other prefix accumulates,
so the ball-local comparisons do not apply; these are the protected prime-end collars of Aux. lemmas 82–83. At every
other side point the image is at positive distance from the other prefix (`IsTouchZones.side₂'`, `side₃`, and the
outer sides off the common points), so the disjoint-case argument applies verbatim.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetTouch

open Restart Sec7 Sec7.Lemma76G Sec7.Lemma76G.ZW Supp7

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **The chart boundary values of the union mean at a touching pair** (pathwise; see the module docstring). -/
theorem exists_finite_tendsto_touchWord (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ}
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
    (hout₁ : ∀ w : ℝ, z.M₁ < w → w < z.R₁ → d.inv ω w ∈ β '' Icc 0 d.r →
      Tendsto (fun y => v (d.inv ω y) + u₀ (d.inv ω y) + χ * d.lift ω (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₄))
    (hout₂ : ∀ w : ℝ, z.L₂ < w → w < 0 → d.inv ω w ∈ α '' Icc 0 d.u →
      Tendsto (fun y => v (d.inv ω y) + u₀ (d.inv ω y) + χ * d.lift ω (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₁))
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = J)
    (hc₀b : ∀ y ∉ J, c₀.fn y = b y) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
      Tendsto (fun y => v (d.inv ω y) + u₀ (d.inv ω y) + χ * d.lift ω (d.inv ω y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((z.word c₀ g₁ g₂ g₃ g₄).fn w)) := by
  have hz := ht.good
  set c := z.word c₀ g₁ g₂ g₃ g₄ with hcdef
  set ψ := d.inv ω with hψdef
  have h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₂]; simp
  have hψc : ContinuousOn ψ Hbar := hC.continuousOn_inv
  have hψd : DifferentiableOn ℂ ψ H := hC.differentiableOn_inv
  have hbij : BijOn ψ H (activeDomain α d.u β d.r) := hC.bijOn h0₂
  have hψi : InjOn ψ H := hbij.injOn
  have hψim : ∀ w ∈ Hbar, 0 ≤ (ψ w).im := fun w hw =>
    Lemma76E.im_nonneg_of_mapsTo hψc (fun _ hv => (hbij.mapsTo hv).1.1) hw
  have hK₁ : IsCompact (α '' Icc 0 d.u) := Sec7.IsPathGood.isCompact_image hp₁ hu.le
  have hK₂ : IsCompact (β '' Icc 0 d.r) := Sec7.IsPathGood.isCompact_image hp₂ hr.le
  have him₁ : ∀ p ∈ α '' Icc 0 d.u, 0 ≤ p.im := by
    rintro _ ⟨s, hs', rfl⟩
    exact Sec7.IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs'.2).trans hu.le)
  have him₂ : ∀ p ∈ β '' Icc 0 d.r, 0 ≤ p.im := by
    rintro _ ⟨t, ht', rfl⟩
    exact Sec7.IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht'.2).trans hr.le)
  have hD : d.D ω = H \ fillH (prefixSet α d.u β d.r) := by
    show H \ fillH (d.K ω) = _
    rw [hK]
  have happ : ∀ w : ℝ, map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[d.D ω] (ψ w) := fun w =>
    (RetData.IsMeasGood.tendsto_inv_real hd hE w).1
  have hne : ∀ w : ℝ, (map ψ (𝓝[H] ((w : ℝ) : ℂ))).NeBot := fun w => (neBot_nhdsWithin_H w).map _
  have hD₁ : d.D ω ⊆ H \ fillH (α '' Icc 0 d.u) := hD ▸ IsSetting.fill₁_subset
  have hD₂ : d.D ω ⊆ H \ fillH (β '' Icc 0 d.r) := hD ▸ IsSetting.fill₂_subset
  have hmemB : ∀ p ∈ prefixSet α d.u β d.r, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact Or.inl ⟨hK ▸ hp, hpH⟩
    · right
      have h0 : 0 ≤ p.im := by
        rcases hp with hp | hp
        exacts [him₁ p hp, him₂ p hp]
      exact le_antisymm (not_lt.1 hpH) h0
  have hRM : z.R₂ < z.M₁ := ht.R₂_lt_M₁
  have h0R : (0 : ℝ) < z.R₂ := ht.zero_lt_R₂
  have hmem₁ : ∀ t : ℝ, z.R₂ < t → t < z.R₁ → ψ t ∈ α '' Icc 0 d.u := fun t h1 h2 => by
    rcases lt_trichotomy t z.M₁ with h | rfl | h
    · exact (ht.side₃ t (ht.junction ▸ h1) h).1
    · rw [ht.tip₁]; exact ⟨d.u, ⟨zero_le, le_rfl⟩, rfl⟩
    · exact ht.side₄ t h h2
  -- the first prefix, at a side point off the second prefix
  have hside₁ : ∀ w : ℝ, z.R₂ < w → w < z.R₁ → w ≠ z.M₁ → ψ w ∉ β '' Icc 0 d.r →
      (w < z.M₁ → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₃)) ∧
      (z.M₁ < w → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₄)) := by
    intro w h1 h2 hwM hβw
    have hα := hmem₁ w h1 h2
    obtain ⟨hlim, hmono, htip⟩ := hfun₁
    obtain ⟨ρ, hρ, hρβ⟩ := Metric.isOpen_iff.1 hK₂.isClosed.isOpen_compl (ψ w) hβw
    have hloc : d.K ω ∩ ball (ψ w) ρ ⊆ α '' Icc 0 d.u := by
      rintro q ⟨hqK, hqb⟩
      rw [hK] at hqK
      rcases hqK with hq | hq
      · exact hq
      · exact absurd hq (hρβ hqb)
    have hA₁ : α '' Icc 0 d.u ∩ H ⊆ d.K ω ∩ H := fun q hq => ⟨hK ▸ Or.inl hq.1, hq.2⟩
    have hcmp := hcmp₁ (ψ w) (hmemB _ (Or.inl hα)) (by
        by_cases hpH : ψ w ∈ H
        · exact Or.inl ⟨hα, hpH⟩
        · exact Or.inr (le_antisymm (not_lt.1 hpH) (him₁ _ hα)))
      ⟨1, one_pos, fun q hq => hA₁ hq.1⟩ ⟨ρ, hρ, fun q hq => ⟨hloc ⟨hq.1.1, hq.2⟩, hq.1.2⟩⟩
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₁)
    have hfy := hlim w h1
    have hsh := hsh₁ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    have htend := fun c' (hsh' : Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd
        (fun s : ℝ => W₁ s.toNNReal) d.u (z - x₁)).im) (map ψ (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c')) =>
      tendsto_side (c := c') hd hE hp₁ hg₁ hWc₁ hW0₁ hu hu0 (hK ▸ subset_union_left) hA₁ hρ hloc hcmp hfy hsh'
    refine ⟨fun hlt => ?_, fun hgt => ?_⟩
    · have hy : bdryVal (physF W₁ d.u x₁) ψ w < 0 := htip ▸ hmono h1 hRM hlt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₁ hu.le hψc hψd hψi hψim h1
        fun t ht' => hmem₁ t ht'.1 (ht'.2.trans h2)
      exact htend _ (hsh.2 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₁),
        tendsto_map'_iff.2 (hlim w' hw'.1), hmono hw'.1 h1 hw'.2, hw'H⟩)
    · have hy : 0 < bdryVal (physF W₁ d.u x₁) ψ w := htip ▸ hmono hRM h1 hgt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₁ hu.le hψc hψd hψi hψim h2
        fun t ht' => hmem₁ t (h1.trans ht'.1) ht'.2
      exact htend _ (hsh.1 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₁),
        tendsto_map'_iff.2 (hlim w' (h1.trans hw'.1)), hmono h1 (h1.trans hw'.1) hw'.1, hw'H⟩)
  -- the second prefix, at a side point off the first prefix
  have hside₂ : ∀ w : ℝ, z.L₂ < w → w < z.R₂ → ψ w ∉ α '' Icc 0 d.u →
      (w < 0 → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₁)) ∧
      (0 < w → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₂)) := by
    intro w h1 h2 hαw
    have hβ := ht.side₂ w h1 h2
    obtain ⟨hlim, hmono, htip⟩ := hfun₂
    obtain ⟨ρ, hρ, hρα⟩ := Metric.isOpen_iff.1 hK₁.isClosed.isOpen_compl (ψ w) hαw
    have hloc : d.K ω ∩ ball (ψ w) ρ ⊆ β '' Icc 0 d.r := by
      rintro q ⟨hqK, hqb⟩
      rw [hK] at hqK
      rcases hqK with hq | hq
      · exact absurd hq (hρα hqb)
      · exact hq
    have hA₂ : β '' Icc 0 d.r ∩ H ⊆ d.K ω ∩ H := fun q hq => ⟨hK ▸ Or.inr hq.1, hq.2⟩
    have hcmp := hcmp₂ (ψ w) (hmemB _ (Or.inr hβ)) (by
        by_cases hpH : ψ w ∈ H
        · exact Or.inl ⟨hβ, hpH⟩
        · exact Or.inr (le_antisymm (not_lt.1 hpH) (him₂ _ hβ)))
      ⟨1, one_pos, fun q hq => hA₂ hq.1⟩ ⟨ρ, hρ, fun q hq => ⟨hloc ⟨hq.1.1, hq.2⟩, hq.1.2⟩⟩
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₂)
    have hfy := hlim w h2
    have hsh := hsh₂ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    have htend := fun c' (hsh' : Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd
        (fun s : ℝ => W₂ s.toNNReal) d.r (z - x₂)).im) (map ψ (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c')) =>
      tendsto_side (c := c') hd hE hp₂ hg₂ hWc₂ hW0₂ hr hr0 (hK ▸ subset_union_right) hA₂ hρ hloc hcmp hfy hsh'
    refine ⟨fun hlt => ?_, fun hgt => ?_⟩
    · have hy : bdryVal (physF W₂ d.r x₂) ψ w < 0 := htip ▸ hmono h2 h0R hlt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₂ hr.le hψc hψd hψi hψim h1
        fun t ht' => ht.side₂ t ht'.1 (ht'.2.trans h2)
      exact htend _ (hsh.2 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₂),
        tendsto_map'_iff.2 (hlim w' (hw'.2.trans h2)), hmono (hw'.2.trans h2) h2 hw'.2, hw'H⟩)
    · have hy : 0 < bdryVal (physF W₂ d.r x₂) ψ w := htip ▸ hmono h0R h2 hgt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hp₂ hr.le hψc hψd hψi hψim h2
        fun t ht' => ht.side₂ t (h1.trans ht'.1) ht'.2
      exact htend _ (hsh.1 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₂),
        tendsto_map'_iff.2 (hlim w' hw'.2), hmono h2 hw'.2 hw'.1, hw'H⟩)
  -- the exceptional set and the case analysis
  refine ⟨(c.jumps : Set ℝ) ∪ {z.L₂, 0, z.R₂, z.M₁, z.R₁},
    (Finset.finite_toSet _).union (toFinite _), fun w hw => ?_⟩
  simp only [mem_union, Finset.mem_coe, mem_insert_iff, mem_singleton_iff, not_or] at hw
  obtain ⟨hwj, hwL₂, hw0, hwR₂, hwM₁, hwR₁⟩ := hw
  rcases lt_or_gt_of_ne hwL₂ with h | hL₂
  · obtain ⟨hre, hx0, hT⟩ := ht.zone₀ w h
    have he : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq hre).symm
    have hxK : (((ψ w).re : ℝ) : ℂ) ∉ d.K ω := hK ▸ ht.notMem_zone _ (Or.inl hx0)
    have hxJ : (ψ w).re ∉ J := fun hj => hwj (hT ▸ ZW.mem_jumps_zone₀ hx0 (hc₀J ▸ hj) hc₀)
    have hval : c.fn w = b (ψ w).re := by
      rw [show c.fn w = c.fn (z.T (ψ w).re) from congrArg c.fn hT.symm, hz.fn_zone₀ hc₀ hx0, hc₀b _ hxJ]
    rw [hval]
    exact tendsto_untouched hd hE hu₀ rfl hdec he hxK hxJ
  rcases lt_or_gt_of_ne hw0 with h | h0
  · rw [hz.fn_side₁ hc₀ hL₂ (ht.M₂_eq ▸ h)]
    by_cases hα : ψ w ∈ α '' Icc 0 d.u
    · exact hout₂ w hL₂ h hα
    · exact (hside₂ w hL₂ (h.trans h0R) hα).1 h
  rcases lt_or_gt_of_ne hwR₂ with h | hR₂
  · rw [hz.fn_side₂ hc₀ (ht.M₂_eq ▸ h0) h]
    exact (hside₂ w (lt_of_le_of_lt ht.L₂_le_zero h0) h (ht.side₂' w h0 h)).2 h0
  rcases lt_or_gt_of_ne hwM₁ with h | hM₁
  · rw [hz.fn_side₃ hc₀ (ht.junction ▸ hR₂) h]
    exact (hside₁ w hR₂ (h.trans_le hz.M₁_le) (ne_of_lt h) (ht.side₃ w (ht.junction ▸ hR₂) h).2).1 h
  rcases lt_or_gt_of_ne hwR₁ with h | hR₁
  · rw [hz.fn_side₄ hc₀ hM₁ h]
    by_cases hβ : ψ w ∈ β '' Icc 0 d.r
    · exact hout₁ w hM₁ h hβ
    · exact (hside₁ w (hRM.trans hM₁) h (ne_of_gt hM₁) hβ).2 hM₁
  · obtain ⟨hre, hx2, hT⟩ := ht.zone₂ w hR₁
    have he : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq hre).symm
    have hxK : (((ψ w).re : ℝ) : ℂ) ∉ d.K ω := hK ▸ ht.notMem_zone _ (Or.inr hx2)
    have hxJ : (ψ w).re ∉ J := fun hj => hwj (hT ▸ ZW.mem_jumps_zone₂ hx2 (hc₀J ▸ hj) hc₀)
    have hval : c.fn w = b (ψ w).re := by
      rw [show c.fn w = c.fn (z.T (ψ w).re) from congrArg c.fn hT.symm, hz.fn_zone₂ hc₀ hx2, hc₀b _ hxJ]
    rw [hval]
    exact tendsto_untouched hd hE hu₀ rfl hdec he hxK hxJ

end RetTouch

end RLC

end InteractingSLE
