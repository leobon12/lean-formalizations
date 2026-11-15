/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Sep

/-!
# Target separation is announced for a local evolution

Continuity versions and the existing hitting-time theorem give stopping times
which announce target separation, including when the target is the first mark.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Version6

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}

/-- Announcing sequences depend only on the almost-sure value of their horizon. -/
theorem isAnnouncingSeq_congr_horizon {τ : Ω → ℝ≥0∞}
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) (he : e =ᵐ[P] τ) :
    Coupling.IsAnnouncingSeq 𝓕 P τ A := by
  refine ⟨hA.1, hA.2.1, ?_, ?_⟩
  · intro n
    filter_upwards [hA.2.2.1 n, he] with ω hn hω
    exact hω ▸ hn
  · filter_upwards [hA.2.2.2, he] with ω hcof hω
    exact hω ▸ hcof

/-- The capped gap stops are stopping times of any right-continuous evolution filtration. -/
theorem isStoppingTime_sepAnnounce [𝓕.IsRightContinuous]
    (hE : Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B e)
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < e ω})
    (hL : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hR : ∀ i ω, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) (k : Fin nR) (n : ℕ) :
    IsStoppingTime 𝓕 fun ω => (sepAnnounce W (VR k) e A n ω : WithTop ℝ≥0) := by
  have hh := Coupling.isStoppingTime_hitBelow_state hE.adapted_W hE.adapted_VL hE.adapted_VR
    (G := univ) MeasurableSet.univ
    (fun ω _ => (hW ω).prodMk ((continuousOn_pi.2 fun i => hL i ω).prodMk
      (continuousOn_pi.2 fun i => hR i ω)))
    (Φ := fun st => st.2.2 k - st.1) (by fun_prop) (1 / ((n : ℝ) + 1))
  have hhit : IsStoppingTime 𝓕 fun ω =>
      Coupling.hitBelow (fun s => VR k s ω - W s ω) (e ω) (1 / ((n : ℝ) + 1)) := by
    simpa only [mem_univ, ↓reduceIte, Coupling.stateAt] using hh
  exact Sec2.TwoSeed.isStoppingTime_capTime (hA.1 n) hhit

/-- The capped gap stops announce target separation in a continuous local evolution. -/
theorem isAnnouncingSeq_sepTime [𝓕.IsRightContinuous]
    (hE : Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B e)
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < e ω})
    (hL : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hR : ∀ i ω, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) {k : Fin nR}
    (h0 : ∀ᵐ ω ∂P, W 0 ω < VR k 0 ω) :
    Coupling.IsAnnouncingSeq 𝓕 P (fun ω => sepTime (W · ω) (VR k · ω) (e ω))
      (sepAnnounce W (VR k) e A) := by
  refine ⟨isStoppingTime_sepAnnounce hE hW hL hR hA k, monotone_sepAnnounce hA.2.1, ?_, ?_⟩
  · intro n
    filter_upwards [hA.2.2.1 n, h0] with ω hn hzero
    exact sepAnnounce_lt_sepTime ((hR k ω).sub (hW ω)) hzero hn
  · filter_upwards [hA.2.2.2] with ω hcof t ht
    exact exists_le_sepAnnounce ((hR k ω).sub (hW ω)) (hA.2.1 ω) hcof ht

/-- A positive-seed target's separation time is announced for every announced local evolution. -/
theorem exists_isAnnouncingSeq_sepTime
    (hE : Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) {k : Fin nR} (hk : 0 < xR k) :
    ∃ S : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
      (fun ω => sepTime (W · ω) (VR k · ω) (e ω)) S := by
  obtain ⟨W', VL', VR', hE', hW', hL', hR', hagree⟩ := exists_continuous_state_modification hE
  have h0 : ∀ᵐ ω ∂P, W' 0 ω < VR' k 0 ω := by
    filter_upwards [hE'.ae_path] with ω hp
    rw [hp.w_zero, hp.vR_zero]
    exact hk
  have hS := isAnnouncingSeq_sepTime hE' hW' hL' hR' (isAnnouncingSeq_usualAugmentation hA) h0
  refine ⟨sepAnnounce W' (VR' k) e A, isAnnouncingSeq_congr_horizon hS ?_⟩
  filter_upwards [hagree] with ω heq
  have hv : (VR' k · ω) = (VR k · ω) := congrArg (fun f => f k) heq.2.2
  rw [heq.1, hv]

end InteractingSLE.Sec5.TwoMark.Version6
