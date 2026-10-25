import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaContact

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

def bufferedTrace {V : Set ℂ} (P : ℝ → ℂ) (a b : ℝ)
    (hPV : ∀ u ∈ Icc a b, P u ∈ V) : Set V :=
  {x | ∃ u ∈ Icc a b, (x : ℂ) = P u}

theorem buffered_trace_pair_cost (E : LSCMetric)
    {V : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : E.IsCurve P a b)
    (hPV : ∀ u ∈ Icc a b, P u ∈ V)
    {x y : V} (hx : x ∈ bufferedTrace P a b hPV)
    (hy : y ∈ bufferedTrace P a b hPV) :
    E.internal V (x, y) ≤ E.len P a b := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  have hx' : x = ⟨P s, hPV s hs⟩ := Subtype.ext hsx
  have hy' : y = ⟨P t, hPV t ht⟩ := Subtype.ext hty
  subst x
  subst y
  exact internal_trace_pair_le_len E hP hPV hs ht

theorem buffered_annular_trace_contacts
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    {V : Set ℂ} (A : EuclideanAnnulus)
    {P Q π : ℝ → ℂ} {a b c d s t : ℝ}
    (hP : E.IsCurve P a b) (hQ : E.IsCurve Q c d)
    (hπ : E.IsCurve π s t)
    (hPV : ∀ u ∈ Icc a b, P u ∈ V)
    (hQV : ∀ u ∈ Icc c d, Q u ∈ V)
    (hπV : ∀ u ∈ Icc s t, π u ∈ V)
    (hsep : Disconnects (π '' Icc s t) A.innerBoundary A.outerBoundary)
    (hPa : P a ∉ Metric.ball A.center A.outerRadius)
    (hPb : P b ∈ Metric.closedBall A.center A.innerRadius)
    (hQc : Q c ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q d ∉ Metric.ball A.center A.outerRadius) :
    (bufferedTrace P a b hPV ∩ bufferedTrace π s t hπV).Nonempty ∧
      (bufferedTrace π s t hπV ∩ bufferedTrace Q c d hQV).Nonempty := by
  have hPc : ContinuousOn P (Icc a b) := by
    have hcomp := hforget.continuousOn.comp hP.2 (fun _ _ => Set.mem_univ _)
    convert hcomp using 1
    funext x
    rfl
  have hQcont : ContinuousOn Q (Icc c d) := by
    have hcomp := hforget.continuousOn.comp hQ.2 (fun _ _ => Set.mem_univ _)
    convert hcomp using 1
    funext x
    rfl
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      (Metric.sphere A.center A.innerRadius)
      (Metric.sphere A.center A.outerRadius) :=
    Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨u, hu, huπ⟩ := outside_to_inside_hits_separator
    hP.1 hPc A.2.2.le hsep' hPa hPb
  obtain ⟨v, hv, hvπ⟩ := inside_to_outside_hits_separator
    hQ.1 hQcont A.2.2.le hsep' hQc hQd
  obtain ⟨uπ, huπ, hPπ⟩ := huπ
  obtain ⟨vπ, hvπ, hQπ⟩ := hvπ
  constructor
  · refine ⟨⟨P u, hPV u hu⟩, ?_, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨uπ, huπ, hPπ.symm⟩
  · refine ⟨⟨Q v, hQV v hv⟩, ?_, ?_⟩
    · exact ⟨vπ, hvπ, hQπ.symm⟩
    · exact ⟨v, hv, rfl⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
