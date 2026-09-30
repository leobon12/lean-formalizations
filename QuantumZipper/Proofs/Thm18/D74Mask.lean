import QuantumZipper.Statements.Thm18Off
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.RS.TipA
import QuantumZipper.Proofs.Loewner.TwoPoint
import Mathlib.Data.NNRat.Encodable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74: measurability of the curve mask, and full law equality ⇒ masked law equality

`Statements/Thm18Off.lean` (D74) states Theorem 1.8 (3) for the masked law `configLawOff`, which
ignores circle coordinates and test pairings that meet the configuration's curve
`curveOf W = closure (trace W '' ℚ≥0)`. This file proves

* `curveMaskMeas` (the node `CurveMaskMeasStmt` of handoff/MATCH-PAPER-18.md §3): there is a
  measurable map `maskSel` on the `configLawFull` data space such that
  `maskSel (cfgData x) = (lawDataOff x, x.2|[0,∞))` for every configuration `x` whose driver is
  continuous with `x.2 0 = 0`. The curve is read through the path-measurable trace
  `G1Pkg.traceSel` (G1PkgTrace.lean: the trace of the continuous regularization of the path,
  measurable in the path, equal to the true trace on continuous paths);
* `configLawOff_eq_of_configLawFull_eq`: equality of `configLawFull` implies equality of
  `configLawOff`, for configurations with a.s. continuous drivers vanishing at `0`.

Topological reductions (own elementary argument): a compact set is disjoint from the closure of a
set `S` iff it keeps a uniform positive distance from `S`; `CircleOff` is a countable union of
disjointness conditions for compact folded closed annuli. No published source is needed (plain
measurability bookkeeping, handoff/MATCH-PAPER-18.md §3).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace D74

open G1Pkg

/-! ## Topology -/

/-- A compact set is disjoint from the closure of `S` iff it keeps a uniform distance from `S`. -/
theorem disjoint_closure_iff {C S : Set ℂ} (hC : IsCompact C) :
    Disjoint C (closure S) ↔ ∃ m : ℕ, ∀ p ∈ S, ∀ c ∈ C, 1 / ((m : ℝ) + 1) ≤ dist p c := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hd⟩ := h.exists_cthickenings hC isClosed_closure
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun p hp c hc => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 : p ∈ Metric.cthickening δ C :=
      Metric.mem_cthickening_of_dist_le p c δ C hc (by linarith)
    have h2 : p ∈ Metric.cthickening δ (closure S) :=
      Metric.self_subset_cthickening _ (subset_closure hp)
    exact Set.disjoint_left.1 hd h1 h2
  · rintro ⟨m, hm⟩
    rw [Set.disjoint_left]
    intro x hxC hxS
    obtain ⟨p, hpS, hpx⟩ := Metric.mem_closure_iff.1 hxS (1 / ((m : ℝ) + 1)) (by positivity)
    have := hm p hpS x hxC
    rw [dist_comm] at hpx
    linarith

/-- The closed annulus of half-width `ε` around the circle `∂B(z,r)`. -/
def closedAnn (z : ℂ) (r ε : ℝ) : Set ℂ := {w | |dist w z - r| ≤ ε}

theorem isCompact_closedAnn (z : ℂ) (r ε : ℝ) : IsCompact (closedAnn z r ε) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_le (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := z) (r := r + ε)).subset fun w hw => ?_
    have := (abs_le.1 (show |dist w z - r| ≤ ε from hw)).2
    simp only [Metric.mem_closedBall]
    linarith

theorem isCompact_foldH_closedAnn (z : ℂ) (r ε : ℝ) : IsCompact (foldH '' closedAnn z r ε) :=
  (isCompact_closedAnn z r ε).image TwoPoint.continuous_foldH

/-- `CircleOff` as a countable union of disjointness conditions for compact sets. -/
theorem circleOff_iff_exists {K : Set ℂ} {z : ℂ} {r : ℝ} :
    CircleOff K z r ↔ ∃ n : ℕ, Disjoint (foldH '' closedAnn z r (1 / ((n : ℝ) + 1))) K := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, Set.disjoint_left.2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact h w (lt_of_le_of_lt hw hn)
  · rintro ⟨n, hn⟩
    refine ⟨1 / ((n : ℝ) + 1), by positivity, fun w hw hK => ?_⟩
    exact Set.disjoint_left.1 hn ⟨w, le_of_lt hw, rfl⟩ hK

/-! ## The path-measurable curve -/

/-- The curve read from a path through the path-measurable trace `traceSel 1`. -/
def curveSel (a : ℝ≥0 → ℝ) : Set ℂ :=
  closure (Set.range fun q : ℚ≥0 => traceSel 1 a (q : ℝ))

theorem measurable_traceSel_apply (t : ℝ) : Measurable fun a : ℝ≥0 → ℝ => traceSel 1 a t :=
  (measurable_pi_apply t).comp (measurable_traceSel 1)

theorem isClosed_farFrom (C : Set ℂ) (ε : ℝ) : IsClosed {p : ℂ | ∀ c ∈ C, ε ≤ dist p c} := by
  have : {p : ℂ | ∀ c ∈ C, ε ≤ dist p c} = ⋂ c ∈ C, {p | ε ≤ dist p c} := by
    ext p; simp
  rw [this]
  exact isClosed_biInter fun c _ =>
    isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem measurableSet_disjoint_curveSel {C : Set ℂ} (hC : IsCompact C) :
    MeasurableSet {a : ℝ≥0 → ℝ | Disjoint C (curveSel a)} := by
  have e : {a : ℝ≥0 → ℝ | Disjoint C (curveSel a)} = ⋃ m : ℕ, ⋂ q : ℚ≥0,
      (fun a : ℝ≥0 → ℝ => traceSel 1 a (q : ℝ)) ⁻¹'
        {p : ℂ | ∀ c ∈ C, 1 / ((m : ℝ) + 1) ≤ dist p c} := by
    ext a
    simp only [mem_ofPred_eq, curveSel, disjoint_closure_iff hC, mem_iUnion, mem_iInter,
      mem_preimage, Set.forall_mem_range]
  rw [e]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q =>
    measurable_traceSel_apply _ (isClosed_farFrom C _).measurableSet

theorem measurableSet_circleOff_curveSel (z : ℂ) (r : ℝ) :
    MeasurableSet {a : ℝ≥0 → ℝ | CircleOff (curveSel a) z r} := by
  have e : {a : ℝ≥0 → ℝ | CircleOff (curveSel a) z r} = ⋃ n : ℕ,
      {a | Disjoint (foldH '' closedAnn z r (1 / ((n : ℝ) + 1))) (curveSel a)} := by
    ext a
    simp only [mem_ofPred_eq, circleOff_iff_exists, mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_disjoint_curveSel (isCompact_foldH_closedAnn _ _ _)

theorem measurableSet_testOff_curveSel (ρ : TestFun H) :
    MeasurableSet {a : ℝ≥0 → ℝ | Disjoint (tsupport ρ.1) (curveSel a)} :=
  measurableSet_disjoint_curveSel ρ.2.2.1

/-- On continuous paths vanishing at `0`, the path-measurable curve is the curve. -/
theorem curveSel_eq_curveOf {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    curveSel (fun t : ℝ≥0 => W t) = curveOf W := by
  unfold curveSel curveOf
  congr 2
  funext q
  have ha : Continuous fun t : ℝ≥0 => W t := hW.comp NNReal.continuous_coe
  have ha0 : (fun t : ℝ≥0 => W t) 0 = 0 := by simpa using hW0
  have hq : (0 : ℝ) ≤ (q : ℝ) := q.cast_nonneg
  rw [traceSel_eq ha ha0 hq, pathTrace]
  simp only [Real.sqrt_one, one_mul]
  have hV : Continuous fun t : ℝ => W ((t.toNNReal : ℝ≥0) : ℝ) :=
    hW.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)
  have hV0 : (fun t : ℝ => W ((t.toNNReal : ℝ≥0) : ℝ)) 0 = 0 := by simp [hW0]
  exact RS.trace_congr_Ici hV hV0 hW hW0 (fun t ht => by
    simp only
    rw [Real.coe_toNNReal t ht]) hq

/-! ## The mask on the data space -/

open scoped Classical in
/-- The mask on the `configLawFull` data space: the circle coordinates and test pairings that meet
the path-measurable curve of the driver are set to `0`. -/
def maskSel (d : E6.FullData) : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  ((fun i => if CircleOff (curveSel d.2) (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      then d.1.1 i else 0,
    fun ρ => if Disjoint (tsupport ρ.1) (curveSel d.2) then d.1.2 ρ else 0), d.2)

theorem measurable_maskSel : Measurable maskSel := by
  classical
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) measurable_snd
  · refine measurable_pi_iff.2 fun i => ?_
    exact Measurable.ite (measurable_snd (measurableSet_circleOff_curveSel _ _))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)) measurable_const
  · refine measurable_pi_iff.2 fun ρ => ?_
    exact Measurable.ite (measurable_snd (measurableSet_testOff_curveSel ρ))
      ((measurable_pi_apply ρ).comp (measurable_snd.comp measurable_fst)) measurable_const

/-- The mask reproduces the masked data of every configuration with a continuous driver vanishing
at `0`. -/
theorem maskSel_cfgData {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2) (h0 : x.2 0 = 0) :
    maskSel (cfgData x) = (lawDataOff x, fun t : ℝ≥0 => x.2 t) := by
  classical
  have hk := curveSel_eq_curveOf hc h0
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) rfl
  · simp only [maskSel, cfgData, lawDataOff, CoordsFull.coordsFull]
    exact if_congr (by rw [hk]) rfl rfl
  · simp only [maskSel, cfgData, lawDataOff]
    exact if_congr (by rw [hk]) rfl rfl

/-! ## Full law equality ⇒ masked law equality -/

theorem configLawOff_eq_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c : Ω → FieldSample × (ℝ → ℝ)} (hm : AEMeasurable (fun ω => cfgData (c ω)) P)
    (hc : ∀ᵐ ω ∂P, Continuous (c ω).2 ∧ (c ω).2 0 = 0) :
    configLawOff c P = (configLawFull c P).map maskSel := by
  rw [configLawFull_eq_map_cfgData,
    AEMeasurable.map_map_of_aemeasurable measurable_maskSel.aemeasurable hm]
  unfold configLawOff
  exact Measure.map_congr (hc.mono fun ω hω => (maskSel_cfgData hω.1 hω.2).symm)

/-- **Equality of `configLawFull` implies equality of `configLawOff`**, for configurations whose
drivers are a.s. continuous and vanish at `0`, the second one with a.e.-measurable data whose law
is not a Dirac mass (with the pinned mathlib, `Measure.map` of a non-a.e.-measurable map is a Dirac
mass, so this is what makes the first one's data a.e.-measurable). -/
theorem configLawOff_eq_of_configLawFull_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {c₁ c₂ : Ω → FieldSample × (ℝ → ℝ)}
    (h : configLawFull c₁ P = configLawFull c₂ P)
    (hm : AEMeasurable (fun ω => cfgData (c₂ ω)) P)
    (hnd : ∀ d : E6.FullData, configLawFull c₂ P ≠ Measure.dirac d)
    (h₁ : ∀ᵐ ω ∂P, Continuous (c₁ ω).2 ∧ (c₁ ω).2 0 = 0)
    (h₂ : ∀ᵐ ω ∂P, Continuous (c₂ ω).2 ∧ (c₂ ω).2 0 = 0) :
    configLawOff c₁ P = configLawOff c₂ P := by
  have hm₁ : AEMeasurable (fun ω => cfgData (c₁ ω)) P := by
    by_contra hn
    have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hn (IsProbabilityMeasure.ne_zero P)
    rw [← configLawFull_eq_map_cfgData, h] at h0
    exact hnd _ h0
  rw [configLawOff_eq_map hm₁ h₁, configLawOff_eq_map hm h₂, h]

end D74
end Thm18Asm
end QuantumZipper
