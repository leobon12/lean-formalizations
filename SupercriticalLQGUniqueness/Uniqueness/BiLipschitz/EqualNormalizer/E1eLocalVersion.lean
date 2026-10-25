import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.RawEquiv




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC restrictTo addConst circleAvg)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
open LQGMetric.Blueprint

private theorem e1e_radius_pos (n j : ℕ) : 0 < e1eRadius n j := by
  unfold e1eRadius e1eEps
  positivity

private theorem e1e_reference_pos (n k : ℕ) : 0 < e1eReference n k := by
  unfold e1eReference e1eEps
  positivity

private theorem centered_collar_relation (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∀ y : ℂ, y ∈ annulus 0 ((r : ℝ) / 2) (4 * (r : ℝ)) ↔
      (1 : ℝ) • y + z ∈ BiLipschitz.OneScale.collarOpen z r := by
  intro y
  change ((r : ℝ) / 2 < ‖y - 0‖ ∧ ‖y - 0‖ < 4 * (r : ℝ)) ↔
    (1 : ℝ) • y + z ∈ (BiLipschitz.OneScale.collarAnnulus z r).toSet
  change ((r : ℝ) / 2 < ‖y - 0‖ ∧ ‖y - 0‖ < 4 * (r : ℝ)) ↔
    (1 : ℝ) • y + z ∈ Metric.ball z (4 * (r : ℝ)) \
      closure (Metric.ball z ((r : ℝ) / 2))
  rw [closure_ball z (ne_of_gt (div_pos r.2 (by norm_num)))]
  simp only [Set.mem_diff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm, sub_zero, one_smul, add_sub_cancel_right]
  exact and_comm

def translatedField {Ω : Type} (h : Ω → DistC) (x : ℂ) (ω : Ω) : DistC :=
  addConst (translateDist x (h ω)) (-circleAvg (h ω) 1 x)

 

theorem exists_e1e_local_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (A : ℝ)
    (hAround : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), ∀ d e : LSCMetric,
      d.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) =
        e.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) →
      aroundDist d (BiLipschitz.OneScale.separatorAt z r) = aroundDist e (BiLipschitz.OneScale.separatorAt z r))
    (n : ℕ) (x : ℂ) (j : ℕ) :
    ∃ B : Set Ω,
      MeasurableSet[fieldSigma
        (fun ω => addConst (translatedField h x ω)
          (-circleAvg (translatedField h x ω) (e1eReference n (j + 1)) 0))
        (annulus 0 ((1 / 10) * e1eReference n (j + 1))
          ((4 / 5) * e1eReference n (j + 1)))] B ∧
      B =ᵐ[P] e1eGood ξ Q D D' A h n x j := by
  let r : Set.Ioi (0 : ℝ) := ⟨e1eRadius n j, e1e_radius_pos n j⟩
  let R : Set.Ioi (0 : ℝ) := ⟨e1eReference n (j + 1), e1e_reference_pos n (j + 1)⟩
  obtain ⟨S, -, hBm, hBeq⟩ := BiLipschitz.OneScale.ebl_raw_centered_event_of_e1a
    P h hh ξ Q hQ D D' hD hD' x r A (hAround x r) R
  let B₀ : Set Ω := {ω | BiLipschitz.OneScale.gaussianSmooth (BiLipschitz.OneScale.collarOpen x r) S
    (restrictTo (BiLipschitz.OneScale.collarOpen x r)
      (addConst (h ω) (-circleAvg (h ω) R x))) > 1 / 2}
  have hBm' : MeasurableSet[fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) R x))
      (BiLipschitz.OneScale.collarOpen x r)] B₀ := hBm
  have hraw : B₀ =ᵐ[P] e1eGood ξ Q D D' A h n x j := by
    rw [raw_event_eq]
    exact hBeq
  have hAE : AEEventIn P
      (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R x))
        (BiLipschitz.OneScale.collarOpen x r)) (e1eGood ξ Q D D' A h n x j) :=
    ⟨B₀, hBm', hraw.symm⟩
  have htranslated := aeEventIn_centered_translate hh x R
    (BiLipschitz.OneScale.collarOpen x r)
    (annulus 0 ((r : ℝ) / 2) (4 * (r : ℝ)))
    (centered_collar_relation x r) hAE
  obtain ⟨B, hBl, hBeq'⟩ := htranslated
  refine ⟨B, ?_, hBeq'.symm⟩
  rw [e1e_iteration_annulus_eq_collar n j]
  exact hBl

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
