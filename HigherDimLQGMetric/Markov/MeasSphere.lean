import HigherDimLQGMetric.Markov.OfFun

/-! The recentered interior sigma algebra is contained in the sphere-centered one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- Recentring at a supported test can be computed from a restriction to the same open set. -/
theorem markov_restrictTo_recenter_from_inside (V : Opens (Rd d))
    {ρ : TestRd d} (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) (g : DistRd d) :
    restrictTo V (recenter ρ g) =
      markovShiftOn V (restrictTo V g)
        (-(restrictTo V g (testOnOf V ρ hρV))) := by
  rw [recenter, markov_restrictTo_addConst, restrictTo_testOnOf]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The interior sigma algebra of smooth recentering is contained in the sigma algebra of the
sphere-normalized interior restriction. -/
theorem markov_smoothSigma_le_sphereSigma
    (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) :
    fieldSigmaRd (fun ω => recenter ρ (h ω)) V ≤
      fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) V := by
  let Z : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r z)
  let T : DistOn V → DistOn V := fun u =>
    markovShiftOn V u (-(u (testOnOf V ρ hρV)))
  have hTm : Measurable T := by
    exact (markov_measurableShiftOn V).comp
      (measurable_id.prodMk ((measurable_distOn_apply _).neg))
  have heq : (fun ω => restrictTo V (recenter ρ (h ω))) =
      T ∘ (fun ω => restrictTo V (Z ω)) := by
    funext ω
    dsimp [T, Z]
    rw [← markov_restrictTo_recenter_from_inside V hρV,
      recenter_addConst hρ]
  have hm : Measurable[fieldSigmaRd Z V]
      (fun ω => restrictTo V (recenter ρ (h ω))) := by
    rw [heq]
    exact hTm.comp (comap_measurable _)
  exact hm.comap_le

/-- Each point Riesz vector has an almost surely measurable version in the sphere-centered
interior sigma algebra. -/
theorem markov_pointVec_ae_sphereMeas (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (z : Rd d) (r : ℝ) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) :
    AEStronglyMeasurable[fieldSigmaRd
      (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) V]
      (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ) P := by
  have h0 : AEStronglyMeasurable[fieldSigmaRd (fun ω => recenter ρ (h ω)) V]
      (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ) P :=
    mem_lpMeas_iff_aestronglyMeasurable.mp
      (markov_insideSpace_le_lpMeas hh V hρ
        (markovPointVec_mem hd hh V hVb hρ hρV x hx))
  exact h0.mono (markov_smoothSigma_le_sphereSigma V z r hρ hρV)

end HigherDimLQGMetric
