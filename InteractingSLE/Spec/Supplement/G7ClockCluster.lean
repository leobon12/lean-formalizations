/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# The cluster-set lemma along a filter with preconnected sets (terminal points of chart paths)

Packet PROVE-G7B. Lemma G7's proof (`source/spec/p481-528.md`, p. 497): "At a terminal contact with `A`, the image
curve has a single limiting prime end. The inverse map extends continuously […] The cluster set of a continuous
curve at a finite terminal time is connected. It is contained in that […] fiber, so it is a singleton."

Here the fibre need not be finite: it suffices that the inverse map `F` is not constant on any real interval
(`exists_ne_of_injOn`, Schwarz reflection). This file generalizes `exists_tendsto_of_tendsto_comp` (`YuanFiber`,
stated for `𝓝[ℍ] x`) to any filter `l` that has arbitrarily small preconnected sets on which `G` is continuous
(`exists_tendsto_of_tendsto_comp_filter`), and specializes it to left limits of paths on `ℝ≥0`
(`exists_tendsto_left_of_tendsto_comp`): a bounded continuous path in `ℍ̄` on `[b, c)` whose image under `F` has a
limit at `c` has a limit itself.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

/-- **Cluster-set lemma along a filter.** Let `F` be continuous on `ℍ̄`, holomorphic and injective on `ℍ`, mapping no
real point into `F(ℍ)`. Let `G` take values in `ℍ̄`, bounded along `l`, where `l` has arbitrarily small preconnected
sets on which `G` is continuous. If `F ∘ G → v` along `l`, then `G` converges along `l` to a point of the fibre of
`v`. -/
theorem exists_tendsto_of_tendsto_comp_filter {α : Type*} [TopologicalSpace α] {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F H) (hc : ContinuousOn F Hbar) (hinj : InjOn F H)
    (hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H) {l : Filter α} [l.NeBot] {G : α → ℂ}
    (hGH : ∀ᶠ x in l, G x ∈ Hbar) {R : ℝ} (hGR : ∀ᶠ x in l, ‖G x‖ ≤ R)
    (hconn : ∀ U ∈ l, ∃ S ∈ l, S ⊆ U ∧ IsPreconnected S ∧ ContinuousOn G S) {v : ℂ}
    (hFG : Tendsto (fun x => F (G x)) l (𝓝 v)) :
    ∃ ξ ∈ Hbar, F ξ = v ∧ Tendsto G l (𝓝 ξ) := by
  set s : Set ℂ := closedBall 0 R ∩ Hbar with hs
  have hsc : IsCompact s := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hmem : ∀ᶠ x in l, G x ∈ s := by
    filter_upwards [hGR, hGH] with x hxR hxH
    exact ⟨mem_closedBall_zero_iff.2 hxR, hxH⟩
  have hmemHbar : ∀ᶠ x in l, G x ∈ Hbar := hmem.mono fun _ h => h.2
  have hfib : ∀ ξ ∈ s, MapClusterPt ξ l G → F ξ = v := fun ξ hξ hcl =>
    eq_of_mapClusterPt hc hmemHbar hFG hξ.2 hcl
  obtain ⟨ξ₀, hξ₀s, hξ₀⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 hmem)
  have huniq : ∀ ξ₁ ∈ s, MapClusterPt ξ₁ l G → ∀ ξ₂ ∈ s, MapClusterPt ξ₂ l G →
      ξ₁.re < ξ₂.re → False := by
    intro ξ₁ h₁s h₁ ξ₂ h₂s h₂ hlt
    have hF₁ := hfib ξ₁ h₁s h₁
    have hF₂ := hfib ξ₂ h₂s h₂
    have hvD : v ∉ F '' H := by
      rintro ⟨z, hzH, hzv⟩
      have hreal : ∀ ξ ∈ s, F ξ = v → ξ ∈ H := by
        intro ξ hξ hFξ
        by_contra hξH
        have h0 : ξ.im = 0 := le_antisymm (not_lt.1 hξH) (show 0 ≤ ξ.im from hξ.2)
        exact hR ξ h0 ⟨z, hzH, hzv.trans hFξ.symm⟩
      have := hinj (hreal ξ₁ h₁s hF₁) (hreal ξ₂ h₂s hF₂) (hF₁.trans hF₂.symm)
      rw [this] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hd hc hinj hlt v
    set l' : Filter α := l ⊓ 𝓟 {x | (G x).re = m} with hl'
    have hl'ne : l'.NeBot := by
      rw [hl', inf_principal_neBot_iff]
      intro U hU
      obtain ⟨S, hSl, hSU, hSc, hGS⟩ := hconn U hU
      have hlo : ∃ x₁ ∈ S, (G x₁).re < m := by
        have hfr : ∃ᶠ x in l, G x ∈ ball ξ₁ (m - ξ₁.re) :=
          h₁.frequently (ball_mem_nhds ξ₁ (by linarith [hm.1]))
        obtain ⟨x, hxb, hxS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨x, hxS, ?_⟩
        have := Complex.abs_re_le_norm (G x - ξ₁)
        rw [mem_ball, dist_eq_norm] at hxb
        rw [Complex.sub_re] at this
        linarith [le_abs_self ((G x).re - ξ₁.re)]
      have hhi : ∃ x₂ ∈ S, m < (G x₂).re := by
        have hfr : ∃ᶠ x in l, G x ∈ ball ξ₂ (ξ₂.re - m) :=
          h₂.frequently (ball_mem_nhds ξ₂ (by linarith [hm.2]))
        obtain ⟨x, hxb, hxS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨x, hxS, ?_⟩
        have := Complex.abs_re_le_norm (G x - ξ₂)
        rw [mem_ball, dist_eq_norm] at hxb
        rw [Complex.sub_re] at this
        linarith [neg_abs_le ((G x).re - ξ₂.re)]
      obtain ⟨x₁, hx₁S, hx₁⟩ := hlo
      obtain ⟨x₂, hx₂S, hx₂⟩ := hhi
      have hGS' : ContinuousOn (fun x => (G x).re) S := Complex.continuous_re.comp_continuousOn hGS
      obtain ⟨x, hxS, hxm⟩ := hSc.intermediate_value hx₁S hx₂S hGS' ⟨hx₁.le, hx₂.le⟩
      exact ⟨x, hSU hxS, hxm⟩
    have hl'le : l' ≤ l := inf_le_left
    obtain ⟨ζ, hζs, hζ⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 (hl'le hmem))
    have hζre : ζ.re = m := by
      by_contra hne
      have hopen : {y : ℂ | y.re ≠ m} ∈ 𝓝 ζ :=
        (isOpen_ne_fun Complex.continuous_re continuous_const).mem_nhds hne
      have hev : ∀ᶠ x in l', (G x).re = m := mem_inf_of_right (mem_principal_self _)
      obtain ⟨x, hx1, hx2⟩ := ((hζ.frequently hopen).and_eventually hev).exists
      exact hx1 hx2
    have hFζ : F ζ = v := eq_of_mapClusterPt hc (hl'le hmemHbar) (hFG.mono_left hl'le) hζs.2 hζ
    by_cases hζH : ζ ∈ H
    · exact hvD ⟨ζ, hζH, hFζ⟩
    · have h0 : ζ.im = 0 := le_antisymm (not_lt.1 hζH) (show 0 ≤ ζ.im from hζs.2)
      have : ζ = (m : ℂ) := by rw [eq_ofReal_re_of_im_eq_zero h0, hζre]
      exact hFm (this ▸ hFζ)
  have hall : ∀ ξ ∈ s, MapClusterPt ξ l G → ξ = ξ₀ := by
    intro ξ hξs hξ
    have hF := hfib ξ hξs hξ
    have hF₀ := hfib ξ₀ hξ₀s hξ₀
    rcases lt_trichotomy ξ.re ξ₀.re with h | h | h
    · exact (huniq ξ hξs hξ ξ₀ hξ₀s hξ₀ h).elim
    · by_cases hvD : v ∈ F '' H
      · obtain ⟨z, hzH, hzv⟩ := hvD
        have hreal : ∀ η ∈ s, F η = v → η ∈ H := by
          intro η hη hFη
          by_contra hηH
          have h0 : η.im = 0 := le_antisymm (not_lt.1 hηH) (show 0 ≤ η.im from hη.2)
          exact hR η h0 ⟨z, hzH, hzv.trans hFη.symm⟩
        exact hinj (hreal ξ hξs hF) (hreal ξ₀ hξ₀s hF₀) (hF.trans hF₀.symm)
      · have him : ∀ η ∈ s, F η = v → η.im = 0 := by
          intro η hη hFη
          by_contra hne
          exact hvD ⟨η, show 0 < η.im from lt_of_le_of_ne (show 0 ≤ η.im from hη.2) (Ne.symm hne), hFη⟩
        exact Complex.ext h ((him ξ hξs hF).trans (him ξ₀ hξ₀s hF₀).symm)
    · exact (huniq ξ₀ hξ₀s hξ₀ ξ hξs hξ h).elim
  exact ⟨ξ₀, hξ₀s.2, hfib ξ₀ hξ₀s hξ₀, hsc.tendsto_nhds_of_unique_mapClusterPt hmem hall⟩

/-- **Left limits of chart paths** (Lemma G7, p. 497, the terminal contact). Let `F` be as in
`exists_tendsto_of_tendsto_comp_filter` and let `γ` be continuous and bounded on `[b, c)`, `b < c`, with values in
`ℍ̄`. If `F ∘ γ → v` from the left at `c`, then `γ` has a left limit at `c`, in the fibre of `v`. -/
theorem exists_tendsto_left_of_tendsto_comp {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    (hc : ContinuousOn F Hbar) (hinj : InjOn F H) (hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H)
    {γ : ℝ≥0 → ℂ} {b c : ℝ≥0} (hbc : b < c) (hγc : ContinuousOn γ (Ico b c)) (hγH : ∀ t ∈ Ico b c, γ t ∈ Hbar)
    {R : ℝ} (hγR : ∀ t ∈ Ico b c, ‖γ t‖ ≤ R) {v : ℂ} (hFγ : Tendsto (fun t => F (γ t)) (𝓝[<] c) (𝓝 v)) :
    ∃ ξ ∈ Hbar, F ξ = v ∧ Tendsto γ (𝓝[<] c) (𝓝 ξ) := by
  have hIco : Ico b c ∈ 𝓝[<] c := Ico_mem_nhdsLT hbc
  have : (𝓝[<] c).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨b, hbc⟩]
    exact Set.mem_Iic.2 le_rfl
  refine exists_tendsto_of_tendsto_comp_filter hd hc hinj hR (Filter.mem_of_superset hIco hγH)
    (Filter.mem_of_superset hIco hγR) (fun U hU => ?_) hFγ
  obtain ⟨d, hd', hdU⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hbc).1 hU
  refine ⟨Ioo (max b d) c, Ioo_mem_nhdsLT (max_lt hbc hd'), fun t ht => hdU ⟨(le_max_right _ _).trans_lt ht.1,
    ht.2⟩, isPreconnected_Ioo, hγc.mono fun t ht => ⟨(le_max_left _ _).trans ht.1.le, ht.2⟩⟩

end Supp7

end InteractingSLE
