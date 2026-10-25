import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LQGMetric.Metric.Internal




 






set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 


theorem len_eq_internalPartitionSup (D : LSCMetric) {Y : Set ℂ}
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    D.len P a b =
      ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
        ∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩) := by
  change (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
      ∑ i ∈ Finset.range p.1,
        edist (D.pt (P (p.2.1 (i + 1)))) (D.pt (P (p.2.1 i)))) = _
  apply le_antisymm
  · refine iSup_le fun p => le_iSup_of_le p ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [edist_comm]
    change D (P (p.2.1 i), P (p.2.1 (i + 1))) ≤ _
    exact BiLipschitz.Barrier.edist_le_internal' D Y
      (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
       ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩)
  · refine iSup_le fun p => ?_
    have hsum :
        (∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩)) ≤
        ∑ i ∈ Finset.range p.1, D.len P (p.2.1 i) (p.2.1 (i + 1)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hsub : Icc (p.2.1 i) (p.2.1 (i + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (p.2.2.2 i).1 (p.2.2.2 (i + 1)).2
      exact BiLipschitz.Barrier.internal_le_len' D
        ⟨p.2.2.1 (Nat.le_succ i), hP.2.mono hsub⟩
        (fun t ht => hY t (hsub ht))
    calc
      (∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩))
          ≤ ∑ i ∈ Finset.range p.1, D.len P (p.2.1 i) (p.2.1 (i + 1)) := hsum
      _ = D.len P (p.2.1 0) (p.2.1 p.1) := by
        exact LQGMetric.MetricGeometry.sum_curveLength_eq (D.pt ∘ P) p.2.2.1 p.1
      _ ≤ D.len P a b :=
        LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P)
          (p.2.2.2 0).1 (p.2.2.2 p.1).2

def eblAcrossAnn (x : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(x, r, 2 * r), hr, by linarith⟩

def eblCollar (x : ℂ) (r : ℝ) : Set ℂ :=
  {z | r / 2 < ‖z - x‖ ∧ ‖z - x‖ < 4 * r}

private theorem closedAnn_subset_eblCollar (x : ℂ) {r : ℝ} (hr : 0 < r) :
    BiLipschitz.Barrier.closedAnn x r (2 * r) ⊆ eblCollar x r := by
  intro z hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

 

theorem ambientAcross_eq_closedAnn_pathInf (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    acrossDist D (eblAcrossAnn x r hr) =
      ⨅ (p : (BiLipschitz.Barrier.closedAnn x r (2 * r)) × (BiLipschitz.Barrier.closedAnn x r (2 * r)))
        (_ : ‖(p.1 : ℂ) - x‖ = r) (_ : ‖(p.2 : ℂ) - x‖ = 2 * r),
          D.internal (BiLipschitz.Barrier.closedAnn x r (2 * r)) p := by
  exact BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hB hL (eblAcrossAnn x r hr) (Y :=
    BiLipschitz.Barrier.closedAnn x r (2 * r)) (by
      change BiLipschitz.Barrier.closedAnn x r (2 * r) ⊆ BiLipschitz.Barrier.closedAnn x r (2 * r)
      exact Subset.rfl)

 


theorem ambientAcross_eq_closedAnn_curveLengthInf (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    acrossDist D (eblAcrossAnn x r hr) =
      ⨅ (p : (BiLipschitz.Barrier.closedAnn x r (2 * r)) × (BiLipschitz.Barrier.closedAnn x r (2 * r))),
      ⨅ (_ : ‖(p.1 : ℂ) - x‖ = r),
      ⨅ (_ : ‖(p.2 : ℂ) - x‖ = 2 * r),
      ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
        (_ : ∀ t ∈ Icc a b, P t ∈ BiLipschitz.Barrier.closedAnn x r (2 * r))
        (_ : P a = (p.1 : ℂ)) (_ : P b = (p.2 : ℂ)), D.len P a b := by
  rw [ambientAcross_eq_closedAnn_pathInf D hB hL x hr]
  rfl

 

theorem ambientAcross_eq_collar_pathInf (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    acrossDist D (eblAcrossAnn x r hr) =
      ⨅ (p : (eblCollar x r) × (eblCollar x r))
        (_ : ‖(p.1 : ℂ) - x‖ = r) (_ : ‖(p.2 : ℂ) - x‖ = 2 * r),
          D.internal (eblCollar x r) p := by
  exact BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hB hL (eblAcrossAnn x r hr)
    (closedAnn_subset_eblCollar x hr)

 

theorem ambientAcross_eq_of_collar_internal_eq (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hB' : BiLipschitz.Barrier.Barrier D')
    (hL : D.IsLengthSpace) (hL' : D'.IsLengthSpace)
    (x : ℂ) {r : ℝ} (hr : 0 < r)
    (hint : D.internal (eblCollar x r) = D'.internal (eblCollar x r)) :
    acrossDist D (eblAcrossAnn x r hr) =
      acrossDist D' (eblAcrossAnn x r hr) := by
  rw [ambientAcross_eq_collar_pathInf D hB hL x hr,
    ambientAcross_eq_collar_pathInf D' hB' hL' x hr, hint]


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
