import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaChain

 









set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem exists_buffered_annular_bridge
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    {V : Set ℂ} (A : EuclideanAnnulus) (hAV : A.toSet ⊆ V)
    (P Q : BufferedMetricTrace E V) {δ : ℝ}
    (hPa : P.path P.start ∉ Metric.ball A.center A.outerRadius)
    (hPb : P.path P.stop ∈ Metric.closedBall A.center A.innerRadius)
    (hQc : Q.path Q.start ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q.path Q.stop ∉ Metric.ball A.center A.outerRadius)
    (hδ : aroundDist E A < ENNReal.ofReal δ) :
    ∃ R : BufferedMetricTrace E V,
      (P.trace ∩ R.trace).Nonempty ∧
      (R.trace ∩ Q.trace).Nonempty ∧
      R.cost < ENNReal.ofReal δ := by
  obtain ⟨π, s, t, hπ, hπA, hsep, hlen⟩ :=
    PfeWeyl.aroundDist_exists_curve_lt E A hδ
  let R : BufferedMetricTrace E V :=
    ⟨π, s, t, hπ, fun u hu => hAV (hπA u hu)⟩
  obtain ⟨hPR, hRQ⟩ := buffered_annular_trace_contacts E hforget A
    P.curve Q.curve R.curve P.stays Q.stays R.stays
    hsep hPa hPb hQc hQd
  exact ⟨R, hPR, hRQ, hlen⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
