import HigherDimLQGMetric.Select.Lex
import LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# A Borel canonical geodesic in each bounded fiber

Packet M3a, MA1 A10. The separating coordinates are distances to a countable dense
sequence in the Polish path space. We express each strict lexicographic improvement as
a countable union of closed proper projections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology unitInterval

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

private abbrev PathSpace (d : ℕ) := C(unitInterval, Rd d)

local instance : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

local instance : PolishSpace (PathSpace d) :=
  LQGMetric.polishSpace_continuousMap _ _

local instance : SecondCountableTopology (ContMetric d) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance : Nonempty (PathSpace d) := ⟨ContinuousMap.const _ 0⟩

/-- Continuous separating coordinates on the Polish path space. -/
noncomputable def geodCoord (m : ℕ) (η : PathSpace d) : ℝ :=
  dist η (TopologicalSpace.denseSeq (PathSpace d) m)

theorem continuous_geodCoord (m : ℕ) : Continuous (geodCoord (d := d) m) := by
  unfold geodCoord
  fun_prop

theorem geodCoord_separates (η ζ : PathSpace d)
    (h : ∀ m, geodCoord m η = geodCoord m ζ) : η = ζ := by
  by_contra hne
  have hpos : 0 < dist η ζ := dist_pos.mpr hne
  obtain ⟨m, hm⟩ :=
    (TopologicalSpace.denseRange_denseSeq (PathSpace d)).exists_dist_lt η
      (half_pos hpos)
  have he := h m
  unfold geodCoord at he
  have htri := dist_triangle ζ (TopologicalSpace.denseSeq (PathSpace d) m) η
  rw [dist_comm ζ, ← he, dist_comm (TopologicalSpace.denseSeq (PathSpace d) m) η] at htri
  linarith

/-- Geodesic relation restricted to metrics and a Euclidean ball. -/
def metricGeodRel (x y : Rd d) (n : ℕ) :
    Set (ContMetric d × PathSpace d) :=
  {p | (p.1.1, p.2) ∈ geodBoundRel x y n}

theorem isClosed_metricGeodRel (x y : Rd d) (n : ℕ) :
    IsClosed (metricGeodRel x y n) := by
  exact (isClosed_geodBoundRel x y n).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem metricGeodRel_fiber (D : ContMetric d) (x y : Rd d) (n : ℕ)
    (η : PathSpace d) :
    (D, η) ∈ metricGeodRel x y n ↔ η ∈ geodBoundFiber D x y n := Iff.rfl

/-- The set of metrics admitting a geodesic in the `n`th ball is closed. -/
def geodExistsSet (x y : Rd d) (n : ℕ) : Set (ContMetric d) :=
  Prod.fst '' metricGeodRel x y n

theorem isClosed_geodExistsSet (x y : Rd d) (n : ℕ) :
    IsClosed (geodExistsSet x y n) :=
  isClosed_geodProjection x y n id continuous_id
    (isClosed_metricGeodRel x y n) (fun _p hp => hp)

/-- A positive scalar multiple has exactly the same bounded geodesics. -/
theorem geodBoundFiber_smul (D : ContMetric d) (x y : Rd d) (n : ℕ)
    (c : ℝ) (hc : 0 < c) :
    geodBoundFiber (D.smul c hc) x y n = geodBoundFiber D x y n := by
  ext η
  change (IsConstSpeedGeodFn (D.smul c hc).1 x y η ∧ ∀ t, ‖η t‖ ≤ n) ↔
    (IsConstSpeedGeodFn D.1 x y η ∧ ∀ t, ‖η t‖ ≤ n)
  rw [show (D.smul c hc).1 = c • D.1 from rfl,
    isConstSpeedGeodFn_smul_iff D.1 x y η c hc]


/-- Closed relation describing a witness that improves a path's `m`th coordinate
by at least `1/(k+1)` while matching all earlier coordinates. -/
def geodBadRel (x y : Rd d) (n m k : ℕ) :
    Set ((ContMetric d × PathSpace d) × PathSpace d) :=
  {p | (p.1.1, p.2) ∈ metricGeodRel x y n ∧
    (∀ i < m, geodCoord i p.2 = geodCoord i p.1.2) ∧
    geodCoord m p.2 + 1 / ((k : ℝ) + 1) ≤ geodCoord m p.1.2}

theorem isClosed_geodBadRel (x y : Rd d) (n m k : ℕ) :
    IsClosed (geodBadRel x y n m k) := by
  have hgeod : IsClosed {p : (ContMetric d × PathSpace d) × PathSpace d |
      (p.1.1, p.2) ∈ metricGeodRel x y n} :=
    (isClosed_metricGeodRel x y n).preimage
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hprefix : IsClosed {p : (ContMetric d × PathSpace d) × PathSpace d |
      ∀ i < m, geodCoord i p.2 = geodCoord i p.1.2} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_geodCoord i).comp continuous_snd)
        ((continuous_geodCoord i).comp (continuous_snd.comp continuous_fst))
  have hstep : IsClosed {p : (ContMetric d × PathSpace d) × PathSpace d |
      geodCoord m p.2 + 1 / ((k : ℝ) + 1) ≤ geodCoord m p.1.2} :=
    isClosed_le (((continuous_geodCoord m).comp continuous_snd).add continuous_const)
      ((continuous_geodCoord m).comp (continuous_snd.comp continuous_fst))
  change IsClosed ({p : (ContMetric d × PathSpace d) × PathSpace d |
      (p.1.1, p.2) ∈ metricGeodRel x y n} ∩
      ({p | ∀ i < m, geodCoord i p.2 = geodCoord i p.1.2} ∩
        {p | geodCoord m p.2 + 1 / ((k : ℝ) + 1) ≤ geodCoord m p.1.2}))
  exact hgeod.inter (hprefix.inter hstep)

/-- The set of parameter/path pairs admitting such an improving witness. -/
def geodBadSet (x y : Rd d) (n m k : ℕ) :
    Set (ContMetric d × PathSpace d) :=
  {p | ∃ w : PathSpace d,
    (p.1, w) ∈ metricGeodRel x y n ∧
    (∀ i < m, geodCoord i w = geodCoord i p.2) ∧
    geodCoord m w + 1 / ((k : ℝ) + 1) ≤ geodCoord m p.2}

theorem isClosed_geodBadSet (x y : Rd d) (n m k : ℕ) :
    IsClosed (geodBadSet x y n m k) := by
  have heq : geodBadSet x y n m k = Prod.fst '' geodBadRel x y n m k := by
    ext p
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(p, w), hw, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨p', w⟩ := q
      cases hqp
      exact ⟨w, hq⟩
  rw [heq]
  exact isClosed_geodProjection x y n Prod.fst continuous_fst
    (isClosed_geodBadRel x y n m k) (fun p hp => hp.1)

/-- The canonical path within the `n`th fiber. -/
def metricLexRel (x y : Rd d) (n : ℕ) :
    Set (ContMetric d × PathSpace d) :=
  {p | p ∈ metricGeodRel x y n ∧
    IsLexMin (geodBoundFiber p.1 x y n) geodCoord p.2}

theorem metricLexRel_iff (x y : Rd d) (n : ℕ)
    (p : ContMetric d × PathSpace d) :
    p ∈ metricLexRel x y n ↔
      p ∈ metricGeodRel x y n ∧
      ∀ m k : ℕ, p ∉ geodBadSet x y n m k := by
  constructor
  · rintro ⟨hp, hlex⟩
    refine ⟨hp, fun m k hbad => ?_⟩
    obtain ⟨w, hw, hpre, hgap⟩ := hbad
    have hle := hlex.2 m w ((metricGeodRel_fiber p.1 x y n w).mp hw) hpre
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨hp, hno⟩
    refine ⟨hp, (metricGeodRel_fiber p.1 x y n p.2).mp hp, ?_⟩
    intro m w hw hpre
    by_contra hne
    have hlt : geodCoord m w < geodCoord m p.2 := lt_of_not_ge hne
    have hdiff : 0 < geodCoord m p.2 - geodCoord m w := by linarith
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hdiff
    apply hno m k
    refine ⟨w, (metricGeodRel_fiber p.1 x y n w).mpr hw, hpre, ?_⟩
    linarith

theorem measurableSet_metricLexRel (x y : Rd d) (n : ℕ) :
    MeasurableSet (metricLexRel x y n) := by
  have heq : metricLexRel x y n = metricGeodRel x y n ∩
      ⋂ m : ℕ, ⋂ k : ℕ, (geodBadSet x y n m k)ᶜ := by
    ext p
    simp only [metricLexRel_iff, mem_inter_iff, mem_iInter, mem_compl_iff]
  rw [heq]
  exact (isClosed_metricGeodRel x y n).measurableSet.inter
    (MeasurableSet.iInter fun m => MeasurableSet.iInter fun k =>
      (isClosed_geodBadSet x y n m k).measurableSet.compl)


/-- Choose the first Euclidean ball containing a geodesic, then its lexicographic minimum. -/
def geodMinGraph (x y : Rd d) : Set (ContMetric d × PathSpace d) :=
  {p | ∃ n : ℕ, p ∈ metricLexRel x y n ∧
    ∀ m < n, p.1 ∉ geodExistsSet x y m}

theorem measurableSet_geodMinGraph (x y : Rd d) :
    MeasurableSet (geodMinGraph x y) := by
  have hn : ∀ n : ℕ, MeasurableSet {p : ContMetric d × PathSpace d |
      p ∈ metricLexRel x y n ∧ ∀ m < n, p.1 ∉ geodExistsSet x y m} := by
    intro n
    have hno : MeasurableSet {p : ContMetric d × PathSpace d |
        ∀ m < n, p.1 ∉ geodExistsSet x y m} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
        (isClosed_geodExistsSet x y m).measurableSet.compl.preimage measurable_fst
    exact (measurableSet_metricLexRel x y n).inter hno
  have heq : geodMinGraph x y = ⋃ n : ℕ,
      {p : ContMetric d × PathSpace d |
        p ∈ metricLexRel x y n ∧ ∀ m < n, p.1 ∉ geodExistsSet x y m} := by
    ext p
    simp only [geodMinGraph, mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hn

/-- Every continuous path has a Euclidean ball containing its image. -/
theorem exists_geodBoundFiber (D : ContMetric d) (x y : Rd d)
    (η : PathSpace d) (hη : IsConstSpeedGeod D x y η) :
    ∃ n : ℕ, η ∈ geodBoundFiber D x y n := by
  have hK : IsCompact (range (η : unitInterval → Rd d)) := isCompact_range η.continuous
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, ?_⟩
  change IsConstSpeedGeodFn D.1 x y η ∧ ∀ t, ‖η t‖ ≤ n
  refine ⟨hη, fun t => ?_⟩
  have ht := hR ⟨t, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at ht
  exact ht.trans (by exact_mod_cast hn)

/-- If a geodesic exists, the canonical graph has exactly one path above that metric. -/
theorem existsUnique_geodMinGraph (x y : Rd d) (D : ContMetric d)
    (hex : ∃ η, IsConstSpeedGeod D x y η) :
    ∃! η : PathSpace d, (D, η) ∈ geodMinGraph x y := by
  classical
  obtain ⟨η₀, hη₀⟩ := hex
  obtain ⟨n₀, hn₀⟩ := exists_geodBoundFiber D x y η₀ hη₀
  have hN : ∃ n : ℕ, D ∈ geodExistsSet x y n :=
    ⟨n₀, (D, η₀), (metricGeodRel_fiber D x y n₀ η₀).mpr hn₀, rfl⟩
  let n : ℕ := Nat.find hN
  have hn : D ∈ geodExistsSet x y n := Nat.find_spec hN
  have hnexists := hn
  obtain ⟨q, hq, hqD⟩ := hn
  obtain ⟨D', η⟩ := q
  have hD' : D' = D := hqD
  subst D'
  have hη : η ∈ geodBoundFiber D x y n :=
    (metricGeodRel_fiber D x y n η).mp hq
  obtain ⟨ξ, hξ, hu⟩ := existsUnique_isLexMin
    (geodBoundFiber D x y n) (isCompact_geodBoundFiber D x y n) ⟨η, hη⟩
    geodCoord continuous_geodCoord geodCoord_separates
  have hno : ∀ m < n, D ∉ geodExistsSet x y m := by
    intro m hm
    change m < Nat.find hN at hm
    exact Nat.find_min hN hm
  refine ⟨ξ, ⟨n, ⟨(metricGeodRel_fiber D x y n ξ).mpr hξ.1, hξ⟩, hno⟩, ?_⟩
  intro ζ hζ
  obtain ⟨m, hm, hmno⟩ := hζ
  have hmn : n = m := by
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact hmno n hlt hnexists
    · exact hno m hgt ⟨(D, ζ), hm.1, rfl⟩
  subst m
  exact hu ζ hm.2

end HigherDimLQGMetric
