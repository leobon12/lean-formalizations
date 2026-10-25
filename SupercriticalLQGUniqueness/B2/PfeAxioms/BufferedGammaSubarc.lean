import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaFiniteRecovery

 







set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem buffered_subarc_internal_le_len
    (D : LSCMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b s t : ℝ}
    (hP : D.IsCurve P a b)
    (hV : ∀ u ∈ Icc a b, P u ∈ V)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) :
    D.internal V (⟨P s, hV s hs⟩, ⟨P t, hV t ht⟩) ≤
      D.len P s t := by
  rw [LSCMetric.internal_eq_internalEDist]
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact LQGMetric.MetricGeometry.internalEDist_le_curveLength
    (X := D.Space) (Y := D.pt '' V) (P := D.pt ∘ P) hst
    (hP.2.mono hsub) (fun u hu => ⟨P u, hV u (hsub hu), rfl⟩)

end SupercriticalLQGUniqueness.B2.PfeAxioms
