/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullTD
import QuantumZipper.Proofs.Loewner.CoreArc3d
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# Aux. lemma 10: the inverse capacity clock and the compact filled hulls

Packet PROVE-T14-BR9. Auxiliary facts for the assembly of Aux. lemma 10 (`Aux10Full`):

* `exists_clock_inv`: a continuous strictly increasing clock `τ` on `[0, T]` with `τ 0 = 0` has a continuous
  monotone inverse on `[0, τ T]`;
* the compact filled hull `compactHull W γ t = closure K_t ∪ γ[0, t]` of a generating trace: compact, increasing in `t`,
  inside `ℍ̄`, and its points in `ℍ` are exactly `K_t` (`compactHull_inter_H`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Aux10

/-- **The inverse clock.** -/
theorem exists_clock_inv {τ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hτm : StrictMonoOn τ (Icc 0 T))
    (hτc : ContinuousOn τ (Icc 0 T)) (hτ0 : τ 0 = 0) :
    ∃ ι : ℝ → ℝ, ContinuousOn ι (Icc 0 (τ T)) ∧ MapsTo ι (Icc 0 (τ T)) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ι (τ t) = t) ∧ (∀ u ∈ Icc 0 (τ T), τ (ι u) = u) ∧ MonotoneOn ι (Icc 0 (τ T)) := by
  have himg : τ '' Icc 0 T = Icc 0 (τ T) := by
    rw [hτc.image_Icc_of_monotoneOn hT hτm.monotoneOn, hτ0]
  set ι := Function.invFunOn τ (Icc 0 T) with hι
  have hmem : ∀ u ∈ Icc 0 (τ T), ι u ∈ Icc 0 T ∧ τ (ι u) = u := fun u hu => by
    rw [← himg] at hu
    exact ⟨Function.invFunOn_mem hu, Function.invFunOn_eq hu⟩
  have hleft : ∀ t ∈ Icc 0 T, ι (τ t) = t := fun t ht => hτm.injOn.leftInvOn_invFunOn ht
  have hmono : MonotoneOn ι (Icc 0 (τ T)) := by
    intro u₁ hu₁ u₂ hu₂ h12
    by_contra h
    push Not at h
    have := hτm (hmem u₂ hu₂).1 (hmem u₁ hu₁).1 h
    rw [(hmem u₁ hu₁).2, (hmem u₂ hu₂).2] at this
    linarith
  refine ⟨ι, ?_, fun u hu => (hmem u hu).1, hleft, fun u hu => (hmem u hu).2, hmono⟩
  rcases hT.lt_or_eq with hT' | rfl
  · have hτT : 0 ≤ τ T := by rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    have hsurj : Icc (0 : ℝ) 1 ⊆ (fun u => ι u / T) '' Icc 0 (τ T) := by
      intro v hv
      have hvT : v * T ∈ Icc 0 T := ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩
      have h1 : 0 ≤ τ (v * T) := by
        rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, hT⟩ hvT hvT.1
      have h2 : τ (v * T) ≤ τ T := hτm.monotoneOn hvT ⟨hT, le_rfl⟩ hvT.2
      refine ⟨τ (v * T), ⟨h1, h2⟩, ?_⟩
      simp only
      rw [hleft _ hvT, mul_div_assoc, div_self hT'.ne', mul_one]
    have hg := QuantumZipper.CoreArc.continuousOn_Icc_of_monotoneOn_of_surj (τ := fun u => ι u / T) hτT
      (fun u hu v hv huv => div_le_div_of_nonneg_right (hmono hu hv huv) hT)
      (by
        show ι 0 / T = 0
        have h0 := hleft 0 ⟨le_rfl, hT⟩
        rw [hτ0] at h0
        rw [h0, zero_div])
      (by show ι (τ T) / T = 1; rw [hleft T ⟨hT, le_rfl⟩, div_self hT'.ne']) hsurj
    have : ι = fun u => T * (ι u / T) := funext fun u => by field_simp
    rw [this]
    exact continuousOn_const.mul hg
  · rw [hτ0, Icc_self]
    exact continuousOn_singleton ι 0

/-- `K_t` is relatively closed in `ℍ`. -/
theorem closure_fwdHull_inter_H {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    closure (QuantumZipper.fwdHull W t) ∩ H ⊆ QuantumZipper.fwdHull W t := by
  rintro z ⟨hzc, hzH⟩
  by_contra hzK
  have ho := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  obtain ⟨w, hw, hwK⟩ := mem_closure_iff.1 hzc _ ho ⟨hzH, hzK⟩
  exact hw.2 hwK

section CompactHull

variable {W : ℝ≥0 → ℝ} {T : ℝ≥0} {γ : ℝ≥0 → ℂ}

theorem continuous_toNNReal_drive (hW : Continuous W) : Continuous fun s : ℝ => W s.toNNReal :=
  hW.comp continuous_real_toNNReal

theorem isCompact_compactHull (hW : Continuous W) (htr : IsGeneratingTrace W T γ) {t : ℝ≥0} (ht : t ≤ T) :
    IsCompact (compactHull W γ t) := by
  refine IsCompact.union ?_ ?_
  · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isHPHull_fwdHull (continuous_toNNReal_drive hW) t.coe_nonneg).2.1.closure
  · refine isCompact_Icc.image_of_continuousOn (htr.2.1.mono fun s hs => ?_)
    exact (ENNReal.coe_le_coe.2 (hs.2.trans ht))

theorem compactHull_mono {s t : ℝ≥0} (hst : s ≤ t) : compactHull W γ s ⊆ compactHull W γ t :=
  union_subset_union (closure_mono ((QuantumZipper.fwdHull_mono
    (W := fun s : ℝ => W s.toNNReal)).1 (NNReal.coe_le_coe.2 hst)))
    (image_mono (Icc_subset_Icc_right hst))

theorem compactHull_subset_Hbar (hW : Continuous W) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W T γ)
    {t : ℝ≥0} (ht : t ≤ T) : compactHull W γ t ⊆ Hbar := by
  rintro z (hz | ⟨s, hs, rfl⟩)
  · refine closure_minimal (fun w hw => ?_) QuantumZipper.isClosed_Hbar hz
    have : 0 < w.im := (isHPHull_fwdHull (continuous_toNNReal_drive hW) t.coe_nonneg).1 hw
    exact this.le
  · exact Sec7.IsGeneratingTrace.mem_Hbar htr hW.continuousOn hW0 (ENNReal.coe_le_coe.2 (hs.2.trans ht))

/-- The points of the compact filled hull in `ℍ` are exactly the swallowed points. -/
theorem compactHull_inter_H (hW : Continuous W) (htr : IsGeneratingTrace W T γ) {t : ℝ≥0} (ht : t ≤ T) :
    compactHull W γ t ∩ H = QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) t := by
  have hWc := continuous_toNNReal_drive hW
  refine Subset.antisymm ?_ fun z hz => ⟨Or.inl (subset_closure hz),
    (isHPHull_fwdHull hWc t.coe_nonneg).1 hz⟩
  rintro z ⟨hz | ⟨s, hs, rfl⟩, hzH⟩
  · exact closure_fwdHull_inter_H hWc t.coe_nonneg ⟨hz, hzH⟩
  · have hmono : ∀ r : ℝ≥0, r ≤ t → QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) r ⊆
        QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) t := fun r hr =>
      (QuantumZipper.fwdHull_mono (W := fun s : ℝ => W s.toNNReal)).1 (NNReal.coe_le_coe.2 hr)
    have hlt : ∀ r : ℝ≥0, (r : ℝ≥0∞) < T → γ r ∈ H → r ≤ t →
        γ r ∈ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) t := fun r hr hrH hrt =>
      hmono r hrt (Sec5.CrossRestart.inter_H_subset_of_isFilling (htr.2.2 r hr) ⟨⟨r, ⟨zero_le, le_rfl⟩, rfl⟩, hrH⟩)
    rcases (ENNReal.coe_le_coe.2 (hs.2.trans ht) : (s : ℝ≥0∞) ≤ T).lt_or_eq with hsT | hsT
    · exact hlt s hsT hzH hs.2
    · have hsT' : s = T := by exact_mod_cast hsT
      have htT : t = T := le_antisymm ht (hsT' ▸ hs.2)
      have hs0 : s ≠ 0 := fun h => by
        rw [h, htr.1] at hzH
        simp [QuantumZipper.H] at hzH
      -- `γ(T)` is a limit of earlier trace points in `ℍ`, which lie in `K_T`
      have hc : ContinuousWithinAt γ (Iio s) s :=
        (htr.2.1 s (show (s : ℝ≥0∞) ≤ T by rw [hsT'])).mono fun r hr => by
          show (r : ℝ≥0∞) ≤ T
          exact (ENNReal.coe_le_coe.2 (le_of_lt hr)).trans (by rw [hsT'])
      have hcl : s ∈ closure (Iio s) := by
        rw [closure_Iio' ⟨0, pos_iff_ne_zero.2 hs0⟩]
        exact le_refl s
      have hev : ∀ᶠ r in 𝓝[<] s, γ r ∈ H := hc.eventually (QuantumZipper.isOpen_H.mem_nhds hzH)
      have hmem : γ s ∈ closure (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) t) := by
        have hne : (𝓝[<] s).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
        refine mem_closure_of_tendsto hc ?_
        filter_upwards [hev, self_mem_nhdsWithin] with r hrH hr
        exact hlt r (by rw [← hsT']; exact ENNReal.coe_lt_coe.2 hr) hrH ((le_of_lt hr).trans hs.2)
      exact closure_fwdHull_inter_H hWc t.coe_nonneg ⟨hmem, hzH⟩

end CompactHull

end Aux10

end InteractingSLE
