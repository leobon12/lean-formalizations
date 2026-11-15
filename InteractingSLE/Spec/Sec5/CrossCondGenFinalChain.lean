/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawImage
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfSide
import InteractingSLE.Spec.Supplement.GB6Restart

/-!
# The relative image chain before a finite original continuation threshold

PROVE-CROSSCOND-GEN. Glue the checked compact restrictions by uniqueness of the
clock and driver. This extends GB6's existing gluing argument to a source driver
continuous only before its possibly finite lifetime. The construction is pathwise;
measurability and force-coordinate transport are separate obligations.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito Supp8.GB6

variable {Wc : ℝ≥0 → ℝ} {ζ Tc : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
  {U : ℝ → ℝ} {σ : ℝ} {p : ℂ}

/-- One relative driver and intrinsic clock on every precontact buffer strictly
before the original lifetime, with filled hulls and boundary contacts allowed. -/
theorem exists_relativeImage_before_lifetime
    (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < ζ}) (hWc0 : Wc 0 = 0) (hU : Continuous U) (hU0 : U 0 = 0)
    (hσ : 0 < σ) (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hTc : 0 < Tc) (hTcζ : Tc ≤ ζ) (hγ : IsGeneratingTrace Wc ζ γ)
    (hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) T))) :
    ∃ W' : ℝ≥0 → ℝ, W' 0 = 0 ∧ relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < relClock U σ (fun r : ℝ => Wc r.toNNReal) t} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
        QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t))
          (relMap U σ '' (γ '' Icc 0 t ∩ H)) := by
  have hbuf : ∀ T : ℝ≥0, ∃ V : ℝ → ℝ,
      (T : ℝ≥0∞) < Tc → Continuous V ∧ V 0 = 0 ∧ relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0 ∧
      StrictMonoOn (relClock U σ (fun r : ℝ => Wc r.toNNReal)) (Icc 0 (T : ℝ)) ∧
      ContinuousOn (relClock U σ (fun r : ℝ => Wc r.toNNReal)) (Icc 0 (T : ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ relClock U σ (fun r : ℝ => Wc r.toNNReal) t ∧
        QuantumZipper.fwdHull V (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull V (relClock U σ (fun r : ℝ => Wc r.toNNReal) t))
          (relMap U σ '' ((fun r : ℝ => γ r.toNNReal) '' Icc 0 t ∩ H)) := by
    intro T
    by_cases hT : (T : ℝ≥0∞) < Tc
    · obtain ⟨V, hV⟩ := exists_relativeImage_Icc hWc hWc0 hγ hU hU0 hσ htip
        (hT.trans_le hTcζ) (hd T hT)
      exact ⟨V, fun _ => hV⟩
    · exact ⟨0, fun h => False.elim (hT h)⟩
  choose V hV using hbuf
  set a : ℝ → ℝ := relClock U σ (fun r : ℝ => Wc r.toNNReal) with ha
  have hTc0 : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := by rwa [ENNReal.coe_zero]
  have ha0 : a 0 = 0 := (hV 0 hTc0).2.2.1
  -- the drivers of two intervals agree on the common capacity interval
  have hcons : ∀ T₁ T₂ : ℝ≥0, (T₁ : ℝ≥0∞) < Tc → (T₂ : ℝ≥0∞) < Tc → T₁ ≤ T₂ →
      EqOn (V T₁) (V T₂) (Icc 0 (a T₁)) := by
    intro T₁ T₂ h₁ h₂ h12
    have hsub : Icc (0 : ℝ) T₁ ⊆ Icc 0 T₂ := Icc_subset_Icc_right (by exact_mod_cast h12)
    refine (Sec6.eqOn_clock_and_driver_of_fwdHull_eq (hV T₁ h₁).1 (hV T₂ h₂).1 (hV T₁ h₁).2.1 (hV T₂ h₂).2.1
      T₁.2 ha0 (hV T₁ h₁).2.2.2.1.monotoneOn (hV T₁ h₁).2.2.2.2.1 (fun t ht => ((hV T₁ h₁).2.2.2.2.2 t ht).1)
      fun t ht => ?_).2
    rw [((hV T₁ h₁).2.2.2.2.2 t ht).2.1, ((hV T₂ h₂).2.2.2.2.2 t (hsub ht)).2.1]
  classical
  set W' : ℝ≥0 → ℝ := fun u =>
    if h : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ (u : ℝ) < a T then V h.choose u else 0 with hW'
  have hkey : ∀ (u T : ℝ≥0), (T : ℝ≥0∞) < Tc → (u : ℝ) < a T → W' u = V T u := by
    intro u T hT hu
    have hex : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ (u : ℝ) < a T := ⟨T, hT, hu⟩
    simp only [hW', hex, ↓reduceDIte]
    obtain ⟨hT', hu'⟩ := hex.choose_spec
    rcases le_total hex.choose T with h | h
    · exact hcons _ T hT' hT h ⟨u.2, hu'.le⟩
    · exact (hcons T _ hT hT' h ⟨u.2, hu.le⟩).symm
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ∃ T' : ℝ≥0, (T' : ℝ≥0∞) < Tc ∧ t < T' := fun t ht => by
    obtain ⟨T', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact ⟨T', h2, ENNReal.coe_lt_coe.1 h1⟩
  have hsm : StrictMonoOn (fun t : ℝ≥0 => a t) {t | (t : ℝ≥0∞) < Tc} := by
    intro t₁ _ t₂ ht₂ h
    exact (hV t₂ ht₂).2.2.2.1 ⟨t₁.2, by exact_mod_cast h.le⟩ ⟨t₂.2, le_rfl⟩ (by exact_mod_cast h)
  refine ⟨W', ?_, ha0, hsm, ?_, ?_, fun t ht => ?_⟩
  · by_cases hex : ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ ((0 : ℝ≥0) : ℝ) < a T
    · obtain ⟨T, hT, h0⟩ := hex
      rw [hkey 0 T hT h0]
      simpa using (hV T hT).2.1
    · simp only [hW', hex, ↓reduceDIte]
  · intro t₀ ht₀
    obtain ⟨T', hT', ht₀T'⟩ := hlt t₀ ht₀
    have hc : ContinuousOn (fun t : ℝ≥0 => a t) {t | t < T'} :=
      (hV T' hT').2.2.2.2.1.comp NNReal.continuous_coe.continuousOn fun t ht =>
        ⟨t.2, by exact_mod_cast (le_of_lt ht)⟩
    exact (hc.continuousAt ((isOpen_lt continuous_id continuous_const).mem_nhds ht₀T')).continuousWithinAt
  · rintro u₀ ⟨T₀, hT₀, hu₀⟩
    have hev : (fun u : ℝ≥0 => V T₀ u) =ᶠ[𝓝 u₀] W' := by
      have hopen : IsOpen {u : ℝ≥0 | (u : ℝ) < a T₀} := isOpen_lt NNReal.continuous_coe continuous_const
      exact Filter.mem_of_superset (hopen.mem_nhds hu₀) fun u hu => (hkey u T₀ hT₀ hu).symm
    exact (((hV T₀ hT₀).1.comp NNReal.continuous_coe).continuousAt.congr hev).continuousWithinAt
  · obtain ⟨T', hT', htT'⟩ := hlt t ht
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) T' := ⟨t.2, by exact_mod_cast htT'.le⟩
    obtain ⟨hat, hK, hF⟩ := (hV T' hT').2.2.2.2.2 t htI
    have hat' : a t < a T' := hsm ht hT' htT'
    have hhull : QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (a t) = QuantumZipper.fwdHull (V T') (a t) := by
      refine fwdHull_eq_of_eqOn hat (t₂ := (a t + a T') / 2) (by linarith) fun r hr => ?_
      have hr0 : (0 : ℝ) ≤ r := hr.1
      have hrT : ((r.toNNReal : ℝ≥0) : ℝ) < a T' := by
        rw [Real.coe_toNNReal _ hr0]; linarith [hr.2]
      show W' r.toNNReal = V T' r
      rw [hkey _ T' hT' hrT, Real.coe_toNNReal _ hr0]
    rw [hhull]
    refine ⟨hK, ?_⟩
    rwa [image_Icc_toNNReal] at hF


end InteractingSLE.Sec5.CrossCond.Gen
