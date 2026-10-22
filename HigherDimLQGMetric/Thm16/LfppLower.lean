import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Sharp.TightLower
import HigherDimLFPP.Paths.DistOn

/-! Uniform off-diagonal control for a family of normalized LFPP laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_tightFamily_toTightOver {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightFamily P X S) : TightOver P X S :=
  ⟨hT.1, hT.2.1, fun μ hμ => (hT.2.2 μ hμ).mono fun _ h => h.1⟩

private theorem l9c_dist_e₁_neg_e₁ {d : ℕ} (hd : 0 < d) :
    dist (e₁ d) (-e₁ d) = 2 := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ (e₁ d), norm_smul,
    HigherDimLFPP.norm_e₁ hd]
  norm_num

theorem l9c_pairBalls_offDiag {d : ℕ} (hd : 0 < d)
    {p : Rd d × Rd d}
    (hp : p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
      closedBall (-e₁ d) (1 / 4)) : p.1 ≠ p.2 := by
  intro heq
  have hdist : dist (e₁ d) (-e₁ d) ≤ (1 / 4 : ℝ) + 1 / 4 := by
    calc
      dist (e₁ d) (-e₁ d) ≤ dist (e₁ d) p.1 + dist p.1 (-e₁ d) := dist_triangle _ _ _
      _ ≤ (1 / 4 : ℝ) + 1 / 4 := by
        gcongr
        · simpa only [mem_closedBall, dist_comm] using hp.1
        · simpa only [heq, mem_closedBall, dist_comm] using hp.2
  rw [l9c_dist_e₁_neg_e₁ hd] at hdist
  norm_num at hdist

theorem l9c_tightFamily_pairLower {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightFamily P X S) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ ∈ S,
      P {ω | ¬ ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
          closedBall (-e₁ d) (1 / 4), η < X δ ω p} < θ := by
  exact (l9c_tightFamily_toTightOver hT).lower_offDiag
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    (fun p hp => l9c_pairBalls_offDiag hd hp) hθ

theorem l9c_tightFamily_pairLower_of_map_eq {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {X Y : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightFamily P X S)
    (hYm : ∀ δ ∈ S, AEMeasurable (Y δ) P)
    (hmap : ∀ δ ∈ S, P.map (Y δ) = P.map (X δ))
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ ∈ S,
      P {ω | ¬ ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
          closedBall (-e₁ d) (1 / 4), η < Y δ ω p} < θ := by
  obtain ⟨η, hη, hX⟩ := l9c_tightFamily_pairLower hd hT hθ
  refine ⟨η, hη, ?_⟩
  let A : Set (Rd d × Rd d) :=
    closedBall (e₁ d) (1 / 4) ×ˢ closedBall (-e₁ d) (1 / 4)
  let E : Set C(Rd d × Rd d, ℝ) := {M | ¬ MapsTo M A (Ioi η)}
  have hE : MeasurableSet E :=
    (LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      isOpen_Ioi).measurableSet
  intro δ hδ
  have heq : P {ω | ¬ ∀ p ∈ A, η < Y δ ω p} =
      P {ω | ¬ ∀ p ∈ A, η < X δ ω p} := by
    calc
      P {ω | ¬ ∀ p ∈ A, η < Y δ ω p} = (P.map (Y δ)) E := by
        rw [Measure.map_apply₀ (hYm δ hδ) hE.nullMeasurableSet]
        rfl
      _ = (P.map (X δ)) E := by rw [hmap δ hδ]
      _ = P {ω | ¬ ∀ p ∈ A, η < X δ ω p} := by
        rw [Measure.map_apply₀ (hT.1 δ hδ) hE.nullMeasurableSet]
        rfl
  exact heq.trans_lt (hX δ hδ)

end HigherDimLQGMetric
