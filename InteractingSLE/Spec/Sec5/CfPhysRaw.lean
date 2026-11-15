/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysPassage
import InteractingSLE.Spec.Sec5.CfPhysPieces
import InteractingSLE.Spec.Restart.DomainMarkovK2Loc

/-!
# Raw physical members from the deterministic physical-line member identities

Packet PROVE-CFCHART2. Strict stopped-history observations, filled-prefix
measurability and persistence of compact avoidance discharge the whole
inverse-capacity passage. The input is the physical identity at deterministic
lines, where the landed history-marked union locality applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Coupling LocalSets
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart.DomainMarkov Restart.DomainMarkov.K2
open WangWu.ChartConst (dyq dyIdx dyF)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR mL mR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
  {xL : Fin mL → ℝ} {xR : Fin mR → ℝ} {μ : Measure (Ω × HistorySpace 0 0)} [IsProbabilityMeasure μ]

/-- The entire raw image member identity follows from deterministic physical
lines. In particular no inclusive clock-cut measurability premise is needed. -/
theorem hasSafeMembers_qRaw_of_lineMembers (hY : IsMeasurableKilledDriving W VL VR ζ)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E) {X : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hX : Measurable X)
    (hline : ∀ (n k : ℕ) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ H →
      ∀ D : Set (Ω × HistorySpace 0 0),
        MeasurableSet[CrossCond.cfGlueMarks W VL VR ζ s (dyq n k)] D →
        (∀ᵐ p ∂μ, p ∈ D → p ∈ imageLineSafe W VL VR ζ s E (ballsK Fb) (dyq n k)) →
        ∀ (f : LQGMetric.MarkovZB.zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
          ∫ p in D, Complex.exp (Complex.I * (X p (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂μ =
            projFactor (ballsOpen Fb) f Ξ * ∫ p in D, Complex.exp (Complex.I * (X p Ξ : ℂ)) ∂μ) :
    HasSafeMembers μ (qRaw xL xR W VL VR ζ s E) univ
      (fun p => qT W VL VR ζ s E p) (qW W VL VR ζ s E) X := by
  intro r Fb hFb D hD hDs f Ξ
  have hDm : MeasurableSet D := (qRaw xL xR W VL VR ζ s E).le r D hD
  have hlive : ∀ᵐ p ∂μ, p ∈ D → (r : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
    hDs.mono fun _ hp hDp => (hp hDp).2.1
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun p => Complex.exp (Complex.I * (X p φ : ℂ))) μ := fun φ => by
    refine Integrable.of_bound
      (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)).aestronglyMeasurable 1 ?_
    exact ae_of_all _ fun p => by rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hm : ∀ n k, ∃ B, MeasurableSet[CrossCond.cfGlueMarks W VL VR ζ s (dyq n k)] B ∧ B =ᵐ[μ]
      D ∩ {p | dyIdx n (qTheta W VL VR ζ s E r p) = k} ∩
        imageLineSafe W VL VR ζ s E (ballsK Fb) (dyq n k) :=
    imageLineSafe_piece_marks hEg hgood hD hlive (isCompact_ballsK Fb) hFb
  have hnull : ∀ n k, NullMeasurableSet
      (D ∩ {p | dyIdx n (qTheta W VL VR ζ s E r p) = k} ∩
        imageLineSafe W VL VR ζ s E (ballsK Fb) (dyq n k)) μ := by
    intro n k
    obtain ⟨B, hB, he⟩ := hm n k
    exact ((CrossCond.cfGlueMarks_le _ _ hY) B hB).nullMeasurableSet.congr he
  refine setIntegral_mul_eq_of_dyadic (hint _) (hint _) hDm (projFactor (ballsOpen Fb) f Ξ)
    hnull ?_ ?_
  · intro n k
    obtain ⟨B, hB, he⟩ := hm n k
    rw [← setIntegral_congr_set he, ← setIntegral_congr_set he]
    refine hline n k Fb hFb B hB ?_ f Ξ
    refine eventuallyEqSet_iff.1 he |>.mono fun p hp hBp => ?_
    exact (hp.mp hBp).2
  · filter_upwards [hDs] with p hp hDp
    exact eventually_imageLineSafe hEg (hp hDp).2.1 (isCompact_ballsK Fb) hFb (hp hDp).2.2

end InteractingSLE.Sec5.CfPhys
