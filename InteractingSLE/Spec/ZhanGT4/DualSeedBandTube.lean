/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedClosePasting

/-!
# A simultaneous remainder modulus on a moving tube

Packet PROVE-ZHAN-GT4-A22. The moving cutoff below localizes the remainder
fields only. No time derivative of that cutoff is asserted or used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- The open tube in which the actual random fields are regular. -/
def seedPathTube (β : ℝ → ℝ) (b c R : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc b c ∧ |p.2 - β p.1| < R}

/-- A moving cutoff for a remainder field. It is not a differentiated log field. -/
def seedMovingCut (ψ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (ρ t x : ℝ) : ℝ :=
  cutChi 0 (β t) ρ x * ψ t x

/-- Along the inner tube the remainder field is unchanged. -/
theorem seedMovingCut_eq {ψ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {ρ t x : ℝ}
    (hρ : 0 < ρ) (hx : |x - β t| < ρ) : seedMovingCut ψ β ρ t x = ψ t x := by
  rw [seedMovingCut, cutChi_zero_eq_one hρ hx, one_mul]

/-- Joint continuity on the moving tube gives a globally continuous
remainder cutoff over the same time interval. -/
theorem continuousOn_seedMovingCut {ψ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {b c ρ : ℝ}
    (hρ : 0 < ρ) (hβ : ContinuousOn β (Icc b c))
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (seedPathTube β b c (3 * ρ))) :
    ContinuousOn (fun p : ℝ × ℝ => seedMovingCut ψ β ρ p.1 p.2) (Icc b c ×ˢ univ) := by
  let J : Set (ℝ × ℝ) := Icc b c ×ˢ univ
  let N : Set (ℝ × ℝ) := Icc b c ×ˢ {x | |x - 0| < 3 * ρ}
  let F : ℝ × ℝ → ℝ := fun p => cutChi 0 0 ρ p.2 * ψ p.1 (p.2 + β p.1)
  have hbc : ContinuousOn (fun p : ℝ × ℝ => β p.1) J :=
    hβ.comp continuousOn_fst (fun _ hp => hp.1)
  have hm : MapsTo (fun p : ℝ × ℝ => (p.1, p.2 + β p.1)) N (seedPathTube β b c (3 * ρ)) := by
    intro p hp
    exact ⟨hp.1, by simpa only [add_sub_cancel_right, sub_zero, mem_ofPred_eq] using hp.2⟩
  have hsub : N ⊆ J := fun _ hp => ⟨hp.1, trivial⟩
  have hn : ContinuousOn F N :=
    ((continuous_cutChi 0 0 ρ).comp continuous_snd).continuousOn.mul
      (hψ.comp (continuousOn_fst.prodMk (continuousOn_snd.add (hbc.mono hsub))) hm)
  have hF : ContinuousOn F J := IsLogField.continuousOn_of_near_far hρ hn (fun p hp => by
    dsimp only [F]
    rw [cutChi_eq_zero_of_lt hρ hp, zero_mul])
  have hb : ContinuousOn (fun p : ℝ × ℝ => F (p.1, p.2 - β p.1)) J :=
    hF.comp (continuousOn_fst.prodMk (continuousOn_snd.sub hbc)) (fun _ hp => ⟨hp.1, trivial⟩)
  convert hb using 1
  funext p
  dsimp only [F, seedMovingCut]
  rw [cutChi_shift, sub_add_cancel]

/-- On a short path segment the actual step remainder equals that of the
globally continuous moving cutoffs. -/
theorem seedMovingCut_fieldStepRem_eq {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {ρ a b : ℝ}
    (hρ : 0 < ρ) (hab : a ≤ b)
    (hnear : ∀ u ∈ Icc a b, |β b - β u| < ρ) :
    Ito.fieldStepRem (seedMovingCut ψ β ρ) (seedMovingCut φ β ρ) β a b =
      Ito.fieldStepRem ψ φ β a b := by
  have hz : ∀ u, |β u - β u| < ρ := fun u => by simpa only [sub_self, abs_zero] using hρ
  unfold Ito.fieldStepRem
  rw [seedMovingCut_eq hρ (hz a)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    dsimp only
    rw [seedMovingCut_eq hρ (hnear u hu), seedMovingCut_eq hρ (hz u)]
  · congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [seedMovingCut_eq hρ (hz u)]

/-- One modulus works for all short cells on the moving tube, regardless
of their frozen spatial centers. This supplies simultaneous band pasting. -/
theorem exists_seed_tube_stepRem_le {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {b c ρ η : ℝ}
    (hρ : 0 < ρ) (hβ : ContinuousOn β (Icc b c))
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (seedPathTube β b c (3 * ρ)))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (seedPathTube β b c (3 * ρ)))
    (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ a z : ℝ, b ≤ a → a ≤ z → z ≤ c → z - a < δ →
      Ito.fieldStepRem ψ φ β a z ≤ η * (z - a) := by
  obtain ⟨δ, hδ, hrem⟩ := Ito.exists_fieldStepRem_le
    (continuousOn_seedMovingCut hρ hβ hψ) (continuousOn_seedMovingCut hρ hβ hφ) hβ hη
  obtain ⟨ε, hε, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hβ) ρ hρ
  refine ⟨min δ ε, lt_min hδ hε, fun a z ha haz hz hmesh => ?_⟩
  have hnear (u : ℝ) (hu : u ∈ Icc a z) : |β z - β u| < ρ := by
    have hdist : dist z u < ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.2)]
      exact (sub_le_sub_left hu.1 z).trans_lt (hmesh.trans_le (min_le_right _ _))
    simpa only [Real.dist_eq] using hosc z ⟨ha.trans haz, hz⟩ u ⟨ha.trans hu.1, hu.2.trans hz⟩ hdist
  rw [← seedMovingCut_fieldStepRem_eq hρ haz hnear]
  exact hrem a z ha haz hz (hmesh.trans_le (min_le_left _ _))

end InteractingSLE.ZhanGT4
