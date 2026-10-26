import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.GeodesicCode
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.GeodesicBridge
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.PointLoop
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround
import LQGMetric.Meas.UM

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.Regular
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness

abbrev Path := Measurability.GeodesicCodes.Path
abbrev Witness := Path × (ℂ × ℂ)
abbrev MetricPair := LSCMetric × LSCMetric
abbrev Input := MetricPair × Witness

/-- The paper's countable scale set Δ, line 239. -/
def dyadic (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))
def DyadicScale (δ : ℝ) : Prop := ∃ j : ℕ, δ = dyadic j

/-- Closed trace carrier for an annular geodesic; the paper does not specify its boundary convention. -/
def closedAnnulus (z : ℂ) (inner outer : ℝ) : Set ℂ :=
  Metric.closedBall z outer \ Metric.ball z inner

theorem closedAnnulus_isClosed (z : ℂ) (inner outer : ℝ) :
    IsClosed (closedAnnulus z inner outer) :=
  Metric.isClosed_closedBall.sdiff Metric.isOpen_ball

theorem closedAnnulus_isCompact (z : ℂ) (inner outer : ℝ) :
    IsCompact (closedAnnulus z inner outer) :=
  (isCompact_closedBall z outer).of_isClosed_subset
    (closedAnnulus_isClosed z inner outer) (fun _ hx => hx.1)

private def uvCost (p : Input) : ℝ≥0∞ := p.1.1 p.2.2
private def comparisonCost (p : Input) : ℝ≥0∞ := p.1.2 p.2.2
private def pointCost (p : Input) (x : ℂ) (δ r : ℝ) : ℝ≥0∞ :=
  TwoScale.S36Events.pointSphereDist p.1.1 x (δ * r)
private def loopCost (p : Input) (x : ℂ) (δ r : ℝ) : ℝ≥0∞ :=
  TwoScale.Consolidated.aroundRat (p.1.1, (x, δ * r, Real.sqrt δ * r))

/-- A literal dyadic endpoint test of (8), with ambient (whole-plane) D costs. -/
def EndpointRegular (r θ α : ℝ) (p : Input) (x : ℂ) : Prop :=
  ∀ j : ℕ, 0 < dyadic j → dyadic j ≤ (1 - α) ^ 2 →
    pointCost p x (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p ∧
    loopCost p x (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p

/-- Source (7)–(8), with a constant-speed rational geodesic code in the closed annulus. -/
def DyadicallyRegular (z : ℂ) (r α θ m : ℝ) (p : Input) : Prop :=
  Measurability.GeodesicCodes.GeoCode (p.1.1, p.2) ∧
  MapsTo p.2.1 Set.univ (closedAnnulus z (α * r) r) ∧
  p.2.2.1 ∈ Metric.sphere z (α * r) ∧
  p.2.2.2 ∈ Metric.sphere z r ∧
  uvCost p ≤ ENNReal.ofReal ((1 - α)⁻¹ * m) ∧
  EndpointRegular r θ α p p.2.2.1 ∧
  EndpointRegular r θ α p p.2.2.2

/-- Source-level regular pair: an actual finite-length geodesic in the annulus,
    plus exactly the two endpoint tests at dyadic scales. -/
def SourceRegularPair (D : LSCMetric) (z u v : ℂ) (r α θ m : ℝ) : Prop :=
  (∃ (P : ℝ → ℂ) (a b : ℝ),
    OptimalConstants.Ratios.Geodesic D P a b u v ∧
      P '' Icc a b ⊆ closedAnnulus z (α * r) r) ∧
  u ∈ Metric.sphere z (α * r) ∧ v ∈ Metric.sphere z r ∧
  D (u, v) ≤ ENNReal.ofReal ((1 - α)⁻¹ * m) ∧
  (∀ j : ℕ, 0 < dyadic j → dyadic j ≤ (1 - α) ^ 2 →
    TwoScale.S36Events.pointSphereDist D u (dyadic j * r) ≤
        ENNReal.ofReal ((dyadic j) ^ θ) * D (u, v) ∧
    TwoScale.Consolidated.aroundRat
        (D, (u, dyadic j * r, Real.sqrt (dyadic j) * r)) ≤
        ENNReal.ofReal ((dyadic j) ^ θ) * D (u, v)) ∧
  (∀ j : ℕ, 0 < dyadic j → dyadic j ≤ (1 - α) ^ 2 →
    TwoScale.S36Events.pointSphereDist D v (dyadic j * r) ≤
        ENNReal.ofReal ((dyadic j) ^ θ) * D (u, v) ∧
    TwoScale.Consolidated.aroundRat
        (D, (v, dyadic j * r, Real.sqrt (dyadic j) * r)) ≤
        ENNReal.ofReal ((dyadic j) ^ θ) * D (u, v))

theorem sourceRegularPair_iff_code (D E : LSCMetric) (z u v : ℂ)
    (r α θ m : ℝ) :
    SourceRegularPair D z u v r α θ m ↔
      ∃ Q : Path, DyadicallyRegular z r α θ m ((D, E), (Q, (u, v))) := by
  have hK := closedAnnulus_isCompact z (α * r) r
  constructor
  · rintro ⟨hgeo, hu, hv, h7, h8u, h8v⟩
    obtain ⟨Q, hcode, htrace⟩ :=
      (Measurability.AttainedEvents.compact_geodesic_iff_geoCode D
        (closedAnnulus z (α * r) r) hK u v).mp hgeo
    refine ⟨Q, hcode, ?_, hu, hv, h7, h8u, h8v⟩
    exact fun t _ => htrace t
  · rintro ⟨Q, hcode, htrace, hu, hv, h7, h8u, h8v⟩
    have hgeo :=
      (Measurability.AttainedEvents.compact_geodesic_iff_geoCode D
        (closedAnnulus z (α * r) r) hK u v).mpr
          ⟨Q, hcode, fun t => htrace (Set.mem_univ t)⟩
    exact ⟨hgeo, hu, hv, h7, h8u, h8v⟩

/-- Paper Lemma 4.2's full witnessing relation, on two global metrics and Euclidean path data. -/
def FailureWitness (z : ℂ) (r α θ m M b η : ℝ) (p : Input) : Prop :=
  DyadicallyRegular z r α θ m p ∧
  uvCost p ≤ ENNReal.ofReal M ∧
  b ≤ dist p.2.2.1 p.2.2.2 ∧
  ENNReal.ofReal (1 + η) * uvCost p ≤ comparisonCost p

def SourceFailure (D E : LSCMetric) (z u v : ℂ) (r α θ m M b η : ℝ) : Prop :=
  SourceRegularPair D z u v r α θ m ∧
  D (u, v) ≤ ENNReal.ofReal M ∧
  b ≤ dist u v ∧
  ENNReal.ofReal (1 + η) * D (u, v) ≤ E (u, v)

theorem sourceFailure_iff_witness (D E : LSCMetric) (z u v : ℂ)
    (r α θ m M b η : ℝ) :
    SourceFailure D E z u v r α θ m M b η ↔
      ∃ Q : Path, FailureWitness z r α θ m M b η ((D, E), (Q, (u, v))) := by
  constructor
  · rintro ⟨hreg, hM, hb, hcmp⟩
    obtain ⟨Q, hQ⟩ := (sourceRegularPair_iff_code D E z u v r α θ m).mp hreg
    exact ⟨Q, hQ, hM, hb, hcmp⟩
  · rintro ⟨Q, hQ, hM, hb, hcmp⟩
    exact ⟨(sourceRegularPair_iff_code D E z u v r α θ m).mpr ⟨Q, hQ⟩,
      hM, hb, hcmp⟩

private theorem measurable_uv : Measurable uvCost := by
  exact TwoScale.S36Events.jointEval_lsc.measurable.comp
    (measurable_fst.comp measurable_fst |>.prodMk (measurable_snd.comp measurable_snd))

private theorem measurable_comparison : Measurable comparisonCost := by
  exact TwoScale.S36Events.jointEval_lsc.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

private theorem measurable_point (x : Input → ℂ) (hx : Measurable x) (δ r : ℝ) :
    Measurable (fun p : Input => pointCost p (x p) δ r) := by
  let f : LSCMetric × (ℂ × ℝ) → ℝ≥0∞ :=
    fun q => TwoScale.S36Events.pointSphereDist q.1 q.2.1 q.2.2
  have hf : Measurable f := TwoScale.S36Events.pointSphereDist_joint_measurable
  have hp : Measurable (fun p : Input => (p.1.1, (x p, δ * r))) :=
    (measurable_fst.comp measurable_fst).prodMk (hx.prodMk measurable_const)
  have hc : Measurable (f ∘ fun p : Input => (p.1.1, (x p, δ * r))) := hf.comp hp
  exact hc

private theorem measurable_loop (x : Input → ℂ) (hx : Measurable x) (δ r : ℝ) :
    Measurable (fun p : Input => loopCost p (x p) δ r) := by
  exact TwoScale.Consolidated.measurable_aroundRat.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (hx.prodMk (measurable_const.prodMk measurable_const)))

private theorem endpointRegular_borel (r θ α : ℝ) (x : Input → ℂ)
    (hx : Measurable x) :
    MeasurableSet {p : Input | EndpointRegular r θ α p (x p)} := by
  have h : MeasurableSet (⋂ j : ℕ, {p : Input |
      0 < dyadic j → dyadic j ≤ (1 - α) ^ 2 →
      pointCost p (x p) (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p ∧
      loopCost p (x p) (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p}) := by
    apply MeasurableSet.iInter
    intro j
    by_cases hj : 0 < dyadic j ∧ dyadic j ≤ (1 - α) ^ 2
    · have hbound : Measurable (fun p : Input =>
          ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p) :=
        (measurable_const : Measurable (fun _ : Input =>
          ENNReal.ofReal ((dyadic j) ^ θ))).mul measurable_uv
      have hp := measurableSet_le (measurable_point x hx (dyadic j) r) hbound
      have hl := measurableSet_le (measurable_loop x hx (dyadic j) r) hbound
      simpa only [hj.1, hj.2, true_implies, Set.ofPred_and] using hp.inter hl
    · have heq : {p : Input | 0 < dyadic j → dyadic j ≤ (1 - α) ^ 2 →
          pointCost p (x p) (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p ∧
          loopCost p (x p) (dyadic j) r ≤ ENNReal.ofReal ((dyadic j) ^ θ) * uvCost p} =
          Set.univ := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro h1 h2
        exact False.elim (hj ⟨h1, h2⟩)
      rw [heq]
      exact MeasurableSet.univ
  convert h using 1
  ext p
  simp only [EndpointRegular, Set.mem_ofPred_eq, Set.mem_iInter]

private theorem dyadicallyRegular_borel (z : ℂ) (r α θ m : ℝ) :
    MeasurableSet {p : Input | DyadicallyRegular z r α θ m p} := by
  let hW : Measurable (fun p : Input => p.2) := measurable_snd
  let hgeo : Measurable (fun p : Input => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk hW
  have h0 : MeasurableSet {p : Input |
      Measurability.GeodesicCodes.GeoCode (p.1.1, p.2)} :=
    Measurability.GeodesicCodes.geoCode_borel.preimage hgeo
  have hPath : Measurable (fun p : Input => p.2.1) :=
    measurable_fst.comp measurable_snd
  have htrace : MeasurableSet {p : Input |
      MapsTo p.2.1 Set.univ (closedAnnulus z (α * r) r)} :=
    ((ContinuousMap.isClosed_setOfPred_mapsTo
      (closedAnnulus_isClosed z (α * r) r) Set.univ).measurableSet).preimage hPath
  have hu : Measurable (fun p : Input => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : Input => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hU : MeasurableSet {p : Input | p.2.2.1 ∈ Metric.sphere z (α * r)} :=
    (Metric.isClosed_sphere.measurableSet : MeasurableSet (Metric.sphere z (α * r))).preimage hu
  have hV : MeasurableSet {p : Input | p.2.2.2 ∈ Metric.sphere z r} :=
    (Metric.isClosed_sphere.measurableSet : MeasurableSet (Metric.sphere z r)).preimage hv
  have h7 := measurableSet_le measurable_uv
    (measurable_const : Measurable (fun _ : Input => ENNReal.ofReal ((1 - α)⁻¹ * m)))
  have h8u := endpointRegular_borel r θ α _ hu
  have h8v := endpointRegular_borel r θ α _ hv
  simpa only [DyadicallyRegular, Set.ofPred_and, Set.inter_assoc] using
    h0.inter (htrace.inter (hU.inter (hV.inter (h7.inter (h8u.inter h8v)))))

/-- Repaired Borel assertion of Lemma 4.2. -/
theorem failureWitness_borel (z : ℂ) (r α θ m M b η : ℝ) :
    MeasurableSet {p : Input | FailureWitness z r α θ m M b η p} := by
  have hu : Measurable (fun p : Input => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : Input => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hM := measurableSet_le measurable_uv
    (measurable_const : Measurable (fun _ : Input => ENNReal.ofReal M))
  have hb : MeasurableSet {p : Input | b ≤ dist p.2.2.1 p.2.2.2} :=
    measurableSet_le measurable_const (hu.dist hv)
  have hc : MeasurableSet {p : Input |
      ENNReal.ofReal (1 + η) * uvCost p ≤ comparisonCost p} :=
    measurableSet_le
      ((measurable_const : Measurable (fun _ : Input => ENNReal.ofReal (1 + η))).mul
        measurable_uv) measurable_comparison
  simpa only [FailureWitness, Set.ofPred_and, Set.inter_assoc] using
    (dyadicallyRegular_borel z r α θ m).inter (hM.inter (hb.inter hc))

/-- Repaired projection statement: a standard-Borel source carrying two measurable metrics. -/
theorem failureProjection_um {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    LQGMetric.UMeasurableSet {a : X | ∃ w : Witness,
      FailureWitness z r α θ m M b η ((D a, E a), w)} := by
  have hp : Measurable (fun p : X × Witness => ((D p.1, E p.1), p.2)) :=
    ((hD.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd
  exact LQGMetric.UMeasurableSet.setOf_exists
    ((failureWitness_borel z r α θ m M b η).preimage hp)

/-- On a Polish parameter space, the same repaired projection is analytic. -/
theorem failureProjection_analytic {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    AnalyticSet {a : X | ∃ w : Witness,
      FailureWitness z r α θ m M b η ((D a, E a), w)} := by
  have hp : Measurable (fun p : X × Witness => ((D p.1, E p.1), p.2)) :=
    ((hD.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd
  have h := ((failureWitness_borel z r α θ m M b η).preimage hp).analyticSet_image measurable_fst
  convert h using 1
  ext a
  simp

theorem sourceFailureProjection_eq {X : Type*} (D E : X → LSCMetric)
    (z : ℂ) (r α θ m M b η : ℝ) :
    {a : X | ∃ u v : ℂ, SourceFailure (D a) (E a) z u v r α θ m M b η} =
      {a : X | ∃ w : Witness, FailureWitness z r α θ m M b η ((D a, E a), w)} := by
  ext a
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨Q, hQ⟩ :=
      (sourceFailure_iff_witness (D a) (E a) z u v r α θ m M b η).mp h
    exact ⟨(Q, (u, v)), hQ⟩
  · rintro ⟨⟨Q, ⟨u, v⟩⟩, hQ⟩
    exact ⟨u, v,
      (sourceFailure_iff_witness (D a) (E a) z u v r α θ m M b η).mpr ⟨Q, hQ⟩⟩

theorem sourceFailureProjection_um {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (D E : X → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    LQGMetric.UMeasurableSet
      {a : X | ∃ u v : ℂ, SourceFailure (D a) (E a) z u v r α θ m M b η} := by
  rw [sourceFailureProjection_eq D E z r α θ m M b η]
  exact failureProjection_um D E hD hE z r α θ m M b η

theorem sourceFailureProjection_analytic {X : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    AnalyticSet
      {a : X | ∃ u v : ℂ, SourceFailure (D a) (E a) z u v r α θ m M b η} := by
  rw [sourceFailureProjection_eq D E z r α θ m M b η]
  exact failureProjection_analytic D E hD hE z r α θ m M b η

end SupercriticalConformalCovariance.Regular
