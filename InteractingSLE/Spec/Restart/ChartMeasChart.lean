/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataChart
import InteractingSLE.Spec.Restart.ChartMeasPath

/-!
# The first-contact chart with its canonical forward map

Packet PROVE-RESTART-CPL4. PROVE-RESTART-CPL3's `exists_isFirstContactChart` constructs the first-contact chart with
`φ = g − x₀`, where `g` is the canonical mapping-out function of the filled prefixes and `x₀` the forward limit of `g`
at the contact point, and an arbitrary branch of `arg φ′`; its statement hides both. For a measurable choice the
forward map and the lift must be given explicitly, so this file restates the construction (the same proof) with
`φ = g − x₀` and **any** continuous branch `lift` of `arg φ′` prescribed (`exists_isFirstContactChart_mapOut`): the
inverse `ψ` is the only remaining existential, and it enters the chart field only through its values on `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

section Chart

variable {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0}

/-- **The active chart at a first contact, with its canonical forward map** `φ = g − x₀` (`g` the mapping-out function
of the filled prefixes): `g` has a real forward limit `x₀` at the contact point, and for every continuous branch `lift`
of `arg φ′` some inverse `ψ` completes `IsFirstContactChart`. -/
theorem exists_isFirstContactChart_mapOut (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hH₁ : MapsTo η₁ (Icc 0 s₀) Hbar) (hH₂ : MapsTo η₂ (Icc 0 t₀) Hbar) (h0₁ : (η₁ 0).im = 0)
    (h0₂ : (η₂ 0).im = 0) (hp : η₁ s₀ = η₂ t₀) (hne₁ : ∀ s < s₀, η₁ s ≠ η₁ s₀)
    (hne₂ : ∀ t < t₀, η₂ t ≠ η₁ s₀) (hcl : η₁ s₀ ∈ closure (activeDomain η₁ s₀ η₂ t₀)) :
    ∃ x₀ : ℝ, Tendsto (ConformalImage.mapOut (fillH (prefixSet η₁ s₀ η₂ t₀)))
      (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₁ s₀)) (𝓝 (x₀ : ℂ)) ∧
    ∀ lift : ℂ → ℝ, ContinuousOn lift (activeDomain η₁ s₀ η₂ t₀) →
      (∀ z ∈ activeDomain η₁ s₀ η₂ t₀,
        deriv (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) z - x₀) z =
          (‖deriv (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) z - x₀) z‖ : ℂ) *
            exp (I * (lift z : ℂ))) →
      ∃ ψ : ℂ → ℂ, IsFirstContactChart η₁ s₀ η₂ t₀
        (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) z - x₀) ψ lift := by
  set K := prefixSet η₁ s₀ η₂ t₀ with hKdef
  set p := η₁ s₀ with hpdef
  have hS : (0 : ℝ) ≤ (s₀ : ℝ) + t₀ := by positivity
  have hζc := continuousOn_joinPath hc₁ hc₂ hp
  have hζH := mapsTo_joinPath (η₁ := η₁) (η₂ := η₂) hH₁ hH₂
  have hζ0 : (joinPath η₁ s₀ η₂ t₀ 0).im = 0 := by rw [joinPath_zero]; exact h0₁
  have himg : joinPath η₁ s₀ η₂ t₀ '' Icc 0 ((s₀ : ℝ) + t₀) = K := image_joinPath hp
  have hKc : IsCompact K := himg ▸ isCompact_Icc.image_of_continuousOn hζc
  have hAD : activeDomain η₁ s₀ η₂ t₀ = H \ fillH K := activeDomain_eq hKc.isClosed
  have hA : IsHPHull (fillH K) := himg ▸ YuanCharacterisation.isHPHull_fillH_image_of_im hζc hS hζ0
  obtain ⟨F, hF1, hF2, hFd, hFc, hFi, -, hFinf, hFbd, M, hM⟩ :=
    YuanCharacterisation.exists_extension_symm hS hζc hζH hζ0
  rw [himg] at hF1 hF2 hFbd
  set A := fillH K with hAdef
  set D := H \ A with hDdef
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨M', hM'⟩ := hg.exists_norm_sub_le hA
  have hDo : IsOpen D := hA.isOpen
  have hDH : D ⊆ H := sdiff_subset
  have hFD : MapsTo F H D := fun w hw => (hF1 w hw).1
  have hFs : SurjOn F H D := fun z hz => ⟨g z, hg.1.2.mapsTo hz, hF2 z hz⟩
  have hGD : ∀ z ∈ D, g z ∈ H ∧ F (g z) = z := fun z hz => ⟨hg.1.2.mapsTo hz, hF2 z hz⟩
  set E : Set ℂ := {z : ℂ | z.im = 0} ∪ K with hEdef
  have hDE : Disjoint D E := by
    refine Set.disjoint_left.2 fun z hzD hzE => ?_
    rcases hzE with h | h
    · exact (ne_of_gt (show 0 < z.im from hzD.1)) h
    · exact hzD.2 ⟨hzD.1, Or.inl (subset_closure h)⟩
  have hfrE : frontier D ⊆ E := by
    have := frontier_H_diff_fillH_subset hKc.isBounded (A := K)
    rwa [hKc.isClosed.closure_eq] at this
  have hfrD : ∀ w ∈ frontier D, w ∉ D := fun w hw hwD => by
    rw [hDo.frontier_eq] at hw; exact hw.2 hwD
  have hpK : p ∈ K := Or.inl ⟨s₀, ⟨zero_le, le_rfl⟩, rfl⟩
  have hpD : p ∉ D := fun h => Set.disjoint_left.1 hDE h (Or.inr hpK)
  have hqp : IsUnboundedLinked (E \ {p}) :=
    isUnboundedLinked_firstContact hc₁ hc₂ h0₁ h0₂ hp hne₁ hne₂
  have hfib : ∀ q : ℂ, IsUnboundedLinked (E \ {q}) → ∀ x y : ℝ, F x = q → F y = q → x = y :=
    fun q hq x y hx hy => eq_of_apply_eq_of_linked hDo hFd hFc hFi hFD hFs hFbd hFinf hDE hfrE hq hx hy
  rw [hAD] at hcl
  obtain ⟨x₁, hFx₀, hgx₀⟩ := exists_tendsto_of_fibre hFc hFD hGD hM' hcl hpD (hfib p hqp)
  refine ⟨x₁, by rw [hAD]; exact hgx₀, fun lift hlc hlift => ?_⟩
  rw [hAD] at hlc hlift
  unfold IsFirstContactChart
  rw [hAD]
  set x₀ := x₁ with hx₀def
  set φ : ℂ → ℂ := fun z => g z - x₀ with hφdef
  set ψ : ℂ → ℂ := fun w => if 0 ≤ w.im then F (w + x₀) else w with hψdef
  have hψH : ∀ w ∈ Hbar, ψ w = F (w + x₀) := fun w hw => by
    simp only [hψdef, show (0 : ℝ) ≤ w.im from hw, ↓reduceIte]
  have hφd : DifferentiableOn ℂ φ D := hg.1.1.sub_const _
  have hφH : ∀ z ∈ D, φ z ∈ H := fun z hz => sub_ofReal_mem_H (hg.1.2.mapsTo hz) x₀
  have hφinj : InjOn φ D := fun z hz z' hz' h => hg.1.2.injOn hz hz' (sub_left_inj.1 h)
  have hψφ : ∀ z ∈ D, ψ (φ z) = z := fun z hz => by
    rw [hψH _ (QuantumZipper.H_subset_Hbar (hφH z hz)), hφdef, sub_add_cancel]; exact hF2 z hz
  have hφψ : ∀ w ∈ H, φ (ψ w) = w := fun w hw => by
    rw [hψH _ (QuantumZipper.H_subset_Hbar hw)]
    show g (F (w + x₀)) - x₀ = w
    rw [(hF1 _ (add_ofReal_mem_H hw x₀)).2, add_sub_cancel_right]
  -- the preimages under `ψ` in `ℍ̄` of a point of `D` and of a boundary point with one real preimage
  have hreal_off : ∀ w ∈ Hbar, w.im = 0 → ψ w ∉ D := fun w hw him => by
    rw [hψH w hw]
    refine hfrD _ (hFbd ⟨show (0 : ℝ) ≤ (w + x₀).im by simp [him], fun h => ?_⟩)
    have : (0 : ℝ) < (w + x₀).im := h
    simp [him] at this
  have huniqD : ∀ z ∈ D, ∀ w' ∈ Hbar, ψ w' = z → w' = φ z := by
    intro z hz w' hw' hψz
    rcases mem_H_or_im_eq_zero hw' with h | h
    · have h1 : F (w' + x₀) = F (g z) := by rw [← hψH w' hw', hψz, hF2 z hz]
      have := hFi (add_ofReal_mem_H h x₀) (hg.1.2.mapsTo hz) h1
      show w' = g z - x₀
      rw [← this, add_sub_cancel_right]
    · exact absurd (hψz ▸ hz) (hreal_off w' hw' h)
  have hbdry : ∀ q ∈ closure D, q ∉ D → (∀ x y : ℝ, F x = q → F y = q → x = y) →
      ∃ w ∈ Hbar, Tendsto φ (𝓝[D] q) (𝓝 w) ∧ ψ w = q ∧ ∀ w' ∈ Hbar, ψ w' = q → w' = w := by
    intro q hq hqD hfq
    obtain ⟨x₁, hFx₁, hgx₁⟩ := exists_tendsto_of_fibre hFc hFD hGD hM' hq hqD hfq
    have hw : ((x₁ - x₀ : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x₁ - x₀ : ℝ) : ℂ).im by simp
    refine ⟨((x₁ - x₀ : ℝ) : ℂ), hw, ?_, ?_, ?_⟩
    · have := hgx₁.sub_const (x₀ : ℂ)
      rwa [← ofReal_sub] at this
    · rw [hψH _ hw, ← ofReal_add, sub_add_cancel, hFx₁]
    · intro w' hw' hψw'
      rcases mem_H_or_im_eq_zero hw' with h | h
      · exact absurd (hψw' ▸ hψH w' hw' ▸ hFD (add_ofReal_mem_H h x₀)) hqD
      · have hw'r : w' = ((w'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
        have h1 : F ((w'.re + x₀ : ℝ) : ℂ) = q := by
          rw [ofReal_add, ← hw'r, ← hψH w' hw', hψw']
        have h2 := hfq _ _ h1 hFx₁
        rw [hw'r, show w'.re = x₁ - x₀ by linarith]
  refine ⟨ψ, ⟨⟨fun z hz => hφH z hz, hφinj, fun w hw => ?_⟩, hφd, ?_, ?_⟩,
    ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun z hz => ⟨φ z, hφH z hz, hψφ z hz⟩⟩, hφψ, ?_,
    hlc, hlift, ?_, ?_, ?_, ⟨M + |x₀|, fun w hw => ?_⟩, ?_⟩
  · -- `φ` is onto `ℍ`
    obtain ⟨z, hz, hgz⟩ := hg.1.2.surjOn (add_ofReal_mem_H hw x₀)
    exact ⟨z, hz, show g z - x₀ = w by rw [hgz, add_sub_cancel_right]⟩
  · -- `φ → 0` at the contact point
    have := hgx₀.sub_const (x₀ : ℂ)
    rwa [sub_self] at this
  · -- `φ → ∞` at `∞`
    have h1 : Tendsto (fun z : ℂ => ‖z‖ - (M' + |x₀|)) (Bornology.cobounded ℂ ⊓ 𝓟 D) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_ h1)
    filter_upwards [mem_inf_of_right (mem_principal_self D)] with z hz
    have h2 := hM' z hz
    have h3 : ‖φ z‖ ≥ ‖z‖ - ‖g z - z‖ - ‖(x₀ : ℂ)‖ := by
      have : φ z = z + (g z - z) - x₀ := show g z - x₀ = _ by ring
      rw [this]
      have := norm_sub_norm_le (z + (g z - z)) (x₀ : ℂ)
      have := norm_sub_norm_le z (-(g z - z))
      rw [sub_neg_eq_add] at this
      linarith [norm_neg (g z - z)]
    rw [norm_real, Real.norm_eq_abs] at h3
    linarith
  · -- `ψ` maps `ℍ` into `D`
    rw [hψH w (QuantumZipper.H_subset_Hbar hw)]; exact hFD (add_ofReal_mem_H hw x₀)
  · -- `ψ` is injective on `ℍ`
    rw [hψH w (QuantumZipper.H_subset_Hbar hw), hψH w' (QuantumZipper.H_subset_Hbar hw')] at h
    exact add_left_injective (x₀ : ℂ) (hFi (add_ofReal_mem_H hw x₀) (add_ofReal_mem_H hw' x₀) h)
  · -- off `ℍ`, `ψ` takes values off `D`
    intro w hw
    by_cases hw0 : 0 ≤ w.im
    · exact hreal_off w hw0 (le_antisymm (not_lt.1 hw) hw0)
    · simp only [hψdef, hw0, ↓reduceIte]; exact fun h => hw (hDH h)
  · -- `ψ` is holomorphic on `ℍ`
    refine (hFd.comp (differentiableOn_id.add_const _) fun w hw => add_ofReal_mem_H hw x₀).congr ?_
    intro w hw; exact hψH w (QuantumZipper.H_subset_Hbar hw)
  · -- `ψ` is continuous on `ℍ̄`
    refine (hFc.comp ((by fun_prop : Continuous fun w : ℂ => w + (x₀ : ℂ)).continuousOn) fun w hw => ?_).congr ?_
    · show (0 : ℝ) ≤ (w + x₀).im; simpa using (show (0 : ℝ) ≤ w.im from hw)
    · intro w hw; exact hψH w hw
  · -- `ψ 0 = η₁ s₀`
    rw [hψH 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp), zero_add, hFx₀]
  · -- bounded displacement
    rw [hψH w hw]
    have h1 := hM (w + x₀) (show (0 : ℝ) ≤ (w + x₀).im by simpa using (show (0 : ℝ) ≤ w.im from hw))
    calc ‖F (w + x₀) - w‖ = ‖(F (w + x₀) - (w + x₀)) + x₀‖ := by ring_nf
      _ ≤ ‖F (w + x₀) - (w + x₀)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ ≤ M + |x₀| := by rw [norm_real, Real.norm_eq_abs]; linarith
  · -- forward limits at the regular points
    intro z hz hreg
    by_cases hzD : z ∈ D
    · exact ⟨φ z, QuantumZipper.H_subset_Hbar (hφH z hzD), (hφd.continuousOn z hzD).tendsto.mono_left le_rfl,
        hψφ z hzD, fun w' hw' h => huniqD z hzD w' hw' h⟩
    · rcases hreg with hzD' | hlink
      · rw [hAD] at hzD'; exact (hzD hzD').elim
      · exact hbdry z hz hzD (hfib z hlink)

end Chart

end Restart

end InteractingSLE
