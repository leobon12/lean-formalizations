/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdrySeed

/-!
# Passing capacity safe laws through an exhaustion

Both (S) and (L) pass from an increasing sequence of observed live windows
to the full lifetime. The Gaussian right side is integrable on safe events
from ambient coordinate measurability, without assuming that the full
lifetime is a stopping time in the smaller driver filtration.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open DomainMarkov DomainMarkov.K2 Coupling Sec7.PocketTraversal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Equality of two integrals on an increasing measurable exhaustion implies
equality on its almost-sure union. -/
theorem setIntegral_eq_of_ae_exhaustion {D : Set Ω} {E : ℕ → Set Ω} {f g : Ω → ℂ}
    (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) (hsub : ∀ n, E n ⊆ D)
    (hcover : ∀ᵐ ω ∂P, ω ∈ D → ∃ n, ω ∈ E n)
    (hf : IntegrableOn f D P) (hg : IntegrableOn g D P)
    (he : ∀ n, (∫ ω in E n, f ω ∂P) = ∫ ω in E n, g ω ∂P) :
    (∫ ω in D, f ω ∂P) = ∫ ω in D, g ω ∂P := by
  have hu : (⋃ n, E n) =ᵐ[P] D := by
    filter_upwards [hcover] with ω hω
    exact propext ⟨fun h => by obtain ⟨n, hn⟩ := mem_iUnion.1 h; exact hsub n hn,
      fun h => mem_iUnion.2 (hω h)⟩
  have hUD : (⋃ n, E n) ⊆ D := iUnion_subset hsub
  have htf := tendsto_setIntegral_of_monotone hEm hmono (hf.mono_set hUD)
  have htg := tendsto_setIntegral_of_monotone hEm hmono (hg.mono_set hUD)
  rw [setIntegral_congr_set hu] at htf htg
  exact tendsto_nhds_unique htf (htg.congr (fun n => (he n).symm))

variable [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0∞}

/-- Integrability of the Gaussian right side on every safe event. The
auxiliary full-information filtration is used only to establish ambient
measurability, not as the conditioning filtration of a safe law. -/
theorem integrableOn_cfAt_of_safe (hU : Measurable U)
    (hW : ∀ q, Measurable (W q)) (hVL : ∀ i q, Measurable (VL i q))
    (hVR : ∀ j q, Measurable (VR j q)) (hw : IsWeakEverywhere W VL VR U)
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) {D : Set Ω} (hD : MeasurableSet D)
    (hDs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ avoidSet W U ψ q) :
    IntegrableOn (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q)) D P := by
  let 𝒜 : Filtration ℝ≥0 mΩ := ⊤
  have hstop (t : ℝ≥0) : MeasurableSet[𝒜 t] {ω | U ω ≤ t} :=
    measurableSet_le hU measurable_const
  have hWa : AdaptedBefore 𝒜 U W := MartChar.adaptedBefore_of_stronglyAdapted hstop
    (fun t => (hW t).stronglyMeasurable)
  have hLa (i) : AdaptedBefore 𝒜 U (VL i) := MartChar.adaptedBefore_of_stronglyAdapted hstop
    (fun t => (hVL i t).stronglyMeasurable)
  have hRa (j) : AdaptedBefore 𝒜 U (VR j) := MartChar.adaptedBefore_of_stronglyAdapted hstop
    (fun t => (hVR j t).stronglyMeasurable)
  have hm := measurable_safeU_indicator_cfAt_bhe (κ := κ) (ρL := ρL) (ρR := ρR)
    hw hWa hLa hRa ψ q
  have hi : Integrable ((safeU W U univ ψ q).indicator
      (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q))) P :=
    Integrable.of_bound ((hm.mono (𝒜.le q) le_rfl).aestronglyMeasurable) 1
      (ae_of_all P (norm_safeU_indicator_cfAt_le hw ψ q))
  apply hi.integrableOn.congr
  filter_upwards [(ae_restrict_iff' hD).2 hDs] with ω hω
  exact indicator_of_mem (mem_safeU_of_mem_avoidSet hw ψ (mem_univ ω) hω) _

variable {𝓕 : Filtration ℝ≥0 mΩ} {F : Set Ω} {V : ℕ → Ω → ℝ≥0∞}
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- Full-lifetime (S) from an observed live exhaustion. No force-threshold
equality and no stopping-time property of U in 𝓕 is assumed. -/
theorem hasSafeLaw_of_live_exhaustion (hX : Measurable X) (hU : Measurable U)
    (hW : ∀ q, Measurable (W q)) (hVL : ∀ i q, Measurable (VL i q))
    (hVR : ∀ j q, Measurable (VR j q)) (hw : IsWeakEverywhere W VL VR U)
    (hVm : ∀ n q, MeasurableSet[𝓕 q] {ω | (q : ℝ≥0∞) < V n ω})
    (hmono : ∀ ω, Monotone fun n => V n ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∀ q : ℝ≥0, (q : ℝ≥0∞) < U ω → ∃ n, (q : ℝ≥0∞) < V n ω)
    (hl : ∀ n, HasSafeLaw κ ρL ρR P 𝓕 F (V n) W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓕 F U W VL VR X := by
  intro ψ q D hD hs
  let E : ℕ → Set Ω := fun n => D ∩ {ω | (q : ℝ≥0∞) < V n ω}
  have hEm (n) : MeasurableSet[𝓕 q] (E n) := hD.inter (hVm n q)
  apply setIntegral_eq_of_ae_exhaustion (fun n => 𝓕.le q _ (hEm n))
    (fun n m hnm _ hω => ⟨hω.1, hω.2.trans_le (hmono _ hnm)⟩)
    (fun _ => inter_subset_left) ?_
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hX)).integrableOn
    (integrableOn_cfAt_of_safe hU hW hVL hVR hw ψ q (𝓕.le q _ hD)
      (hs.mono fun _ hω hDω => (hω hDω).2)) ?_
  · filter_upwards [hs, hcover] with ω hsω hc hωD
    obtain ⟨n, hn⟩ := hc (hsω hωD).1 q (hsω hωD).2.1
    exact ⟨n, hωD, hn⟩
  · intro n
    apply hl n ψ q (E n) (hEm n)
    filter_upwards [hs] with ω hsω hωE
    exact ⟨(hsω hωE.1).1, hωE.2, (hsω hωE.1).2.2⟩

/-- Full-lifetime (L) from the same observed live exhaustion. Only the
integrable exponential pairings enter this limit. -/
theorem hasSafeMembers_of_live_exhaustion (hX : Measurable X)
    (hVm : ∀ n q, MeasurableSet[𝓕 q] {ω | (q : ℝ≥0∞) < V n ω})
    (hmono : ∀ ω, Monotone fun n => V n ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∀ q : ℝ≥0, (q : ℝ≥0∞) < U ω → ∃ n, (q : ℝ≥0∞) < V n ω)
    (hl : ∀ n, HasSafeMembers P 𝓕 F (V n) W X) :
    HasSafeMembers P 𝓕 F U W X := by
  intro q Fb hFb D hD hs f Ξ
  let E : ℕ → Set Ω := fun n => D ∩ {ω | (q : ℝ≥0∞) < V n ω}
  have hEm (n) : MeasurableSet[𝓕 q] (E n) := hD.inter (hVm n q)
  rw [← integral_const_mul]
  apply setIntegral_eq_of_ae_exhaustion (fun n => 𝓕.le q _ (hEm n))
    (fun n m hnm _ hω => ⟨hω.1, hω.2.trans_le (hmono _ hnm)⟩)
    (fun _ => inter_subset_left) ?_
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hX)).integrableOn
    ((GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply Ξ).comp hX)).const_mul
      (projFactor (ballsOpen Fb) f Ξ)).integrableOn ?_
  · filter_upwards [hs, hcover] with ω hsω hc hωD
    obtain ⟨n, hn⟩ := hc (hsω hωD).1 q (hsω hωD).2.1
    exact ⟨n, hωD, hn⟩
  · intro n
    rw [integral_const_mul]
    apply hl n q Fb hFb (E n) (hEm n) ?_ f Ξ
    filter_upwards [hs] with ω hsω hωE
    exact ⟨(hsω hωE.1).1, hωE.2, (hsω hωE.1).2.2⟩

end InteractingSLE.Restart.FCPlumb
