import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSubarc

 










set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem near_minimal_buffered_loop_short
    (D : LSCMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b s t : ℝ}
    (hP : D.IsCurve P a b)
    (hV : ∀ u ∈ Icc a b, P u ∈ V)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hloop : P s = P t) {ε : ℝ≥0∞}
    (hnear : D.len P a b <
      D.internal V
        (⟨P a, hV a ⟨le_rfl, hP.1⟩⟩,
          ⟨P b, hV b ⟨hP.1, le_rfl⟩⟩) + ε)
    (hfinite : D.len P a b < ∞) :
    D.len P s t < ε := by
  let pa : V := ⟨P a, hV a ⟨le_rfl, hP.1⟩⟩
  let ps : V := ⟨P s, hV s hs⟩
  let pt : V := ⟨P t, hV t ht⟩
  let pb : V := ⟨P b, hV b ⟨hP.1, le_rfl⟩⟩
  have hpst : ps = pt := Subtype.ext hloop
  have hfirst : D.internal V (pa, ps) ≤ D.len P a s :=
    buffered_subarc_internal_le_len D hP hV
      ⟨le_rfl, hP.1⟩ hs hs.1
  have hlast : D.internal V (pt, pb) ≤ D.len P t b :=
    buffered_subarc_internal_le_len D hP hV ht
      ⟨hP.1, le_rfl⟩ ht.2
  have hbase : D.internal V (pa, pb) ≤ D.len P a s + D.len P t b := by
    calc
      D.internal V (pa, pb) ≤ D.internal V (pa, ps) + D.internal V (ps, pb) :=
        (D.isExtMetric_internal V).2.2.2 pa ps pb
      _ = D.internal V (pa, ps) + D.internal V (pt, pb) := by rw [hpst]
      _ ≤ D.len P a s + D.len P t b := add_le_add hfirst hlast
  have hsplit : D.len P a b = D.len P a s + D.len P s t + D.len P t b := by
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b = _
    rw [← LQGMetric.MetricGeometry.curveLength_add _ hs.1 hs.2,
      ← LQGMetric.MetricGeometry.curveLength_add _ hst ht.2]
    ac_rfl
  have hprele : D.len P a s + D.len P t b ≤ D.len P a b := by
    rw [hsplit]
    calc
      D.len P a s + D.len P t b ≤
          D.len P a s + (D.len P s t + D.len P t b) := by
        gcongr
        exact le_add_self
      _ = D.len P a s + D.len P s t + D.len P t b := by ac_rfl
  have hpreFinite : D.len P a s + D.len P t b ≠ ∞ :=
    ne_top_of_le_ne_top hfinite.ne hprele
  have hstrict :
      (D.len P a s + D.len P t b) + D.len P s t <
        (D.len P a s + D.len P t b) + ε := by
    calc
      _ = D.len P a b := by rw [hsplit]; ac_rfl
      _ < D.internal V (pa, pb) + ε := hnear
      _ ≤ (D.len P a s + D.len P t b) + ε := add_le_add hbase le_rfl
  exact (ENNReal.add_lt_add_iff_left hpreFinite).mp hstrict

end SupercriticalLQGUniqueness.B2.PfeAxioms
