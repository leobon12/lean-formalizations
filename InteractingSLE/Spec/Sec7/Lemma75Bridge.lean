/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Sec7.DeterminationGraph
import InteractingSLE.Spec.Coupling.LawUniqueTransfer
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Sec4.Thm12Special

/-!
# Lemma 7.5: from per-coupling determination to one universal Borel graph

Packet PROVE-PROP73D, item (1). Specification Lemma 7.5 (`source/spec/p241-288.md` L261–L264, p. 252) in the
universal form used by Theorem 7.12C (supplement p. 542, "Universal finite-force determination gives one canonical
path function") and Corollary 7.12E (p. 461); Aux. 55's last step (p. 250: "Its determining function is the same for
every such reference coupling. […] Thus one reference version may be fixed once and for all"); §D.2.3 of Astra's
follow-up note (ruling R38: "all those couplings use the same measurable graph modulo the fixed field law").

LOCEXT proves Lemma 7.5 **per coupling**, `LP.Lemma75DeterminationStatement` (every coupling of every ordered force
word satisfying the frozen optional hull specification has a field-determined killed driving history). Theorem 1.5
uses it in the **universal** form `Theorem15.Lemma75Statement`: for each datum, seed and angle there is **one** Borel
map of the field giving the lifetime and the path of every flow line of every field with that datum. This file proves

* **`lemma75Statement_of_lemma75DeterminationStatement`**: `LP.Lemma75DeterminationStatement.{u}` implies
  `Theorem15.Lemma75Statement.{u}`;
* **`exists_flowLineMap_of_lawUnique`**: for one datum, seed and angle, the universal map from the uniqueness of the
  joint law (`LawUnique.IsOptionalHullLawUnique`) and **one** field-determined reference coupling;
* **`exists_flowLineMap_of_admissible`**: in the non-boundary-intersecting regime (admissible side partial sums,
  Remark 4.1's regime) the uniqueness of the joint law is Aux. lemma 23 (`Sec4.isOptionalHullLawUnique_of_admissible`,
  proved), so one reference coupling gives the universal map **without Proposition 7.3 or Aux. lemmas 52–55** (the
  form in which Lemma 7.1's three-curve construction uses Lemma 7.5, avoiding a circular dependence on Proposition 7.3).

The argument:

1. The coupling field of a flow line is `h(· + x) + θχ`, a fixed Borel function of `h`
   (`eq_flowField_of_isTranslateAddConst`).
2. Fix one reference coupling of the flow-line word (if there is none in the universe `u`, there is no flow line and
   any map works) and a Borel graph `Ψ₀` of its killed driving history.
3. Universal determination makes the joint law of the field and the killed driving history the same in every coupling
   (`Determination.map_field_killedHistory_eq`, the mixture argument of §D.2.3). Through the dyadic killed history
   (a standard Borel space, so the graph event is measurable) the reference graph transfers to every coupling, with
   the paths reconstructed by dyadic limits from below (`isHistoryGraph_pathsOfDyadic_of_reference`). This is the
   proof of `LawUnique.isFieldDeterminedHistory_of_map_eq` with its determining map made explicit: it is
   `pathsOfDyadic ∘ Ψ₀`, the same for every coupling.
4. LP11's deterministic reconstruction `LP.drivingTrace` turns the driving path into the trace
   (`LP.drivingTrace_eq`), and the seed `x` is added back.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Lemma75Bridge

open LawUnique (historyOfPaths pathsOfDyadic measurable_historyOfPaths measurable_pathsOfDyadic dyadicTime
  lowerDyadic HistorySpace)

/-! ### The coupling field of a flow line is a Borel function of the field -/

/-- The frozen relation `IsTranslateAddConst x c h h'` determines `h'`: it is `h(· + x) + c`
(`Exist.flowField x c h`). -/
theorem eq_flowField_of_isTranslateAddConst {x c : ℝ} {h h' : LQGMetric.DistOn upperHalfPlaneOpens}
    (ht : IsTranslateAddConst x c h h') : h' = Exist.flowField x c h := by
  ext φ'
  have e := ht (Chart.pushTest (Exist.isConformal_shiftChart x) φ') φ' fun z => by
    rw [Exist.pushTest_shiftChart_apply, add_sub_cancel_right]
  rw [e, Exist.flowField_apply]

/-! ### The full and the dyadic killed histories -/

section Killed

variable {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The killed history at every time is measurable when the killed driving is (the full-time form of
`LawUnique.measurable_killedHistory`). -/
theorem measurable_killedHistory (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable (Determination.killedHistory W VL VR ζ) := by
  refine (LawUnique.measurable_lifetime hX).prodMk (measurable_pi_iff.2 fun t => ?_)
  intro S hS
  have hpre : (fun ω => if (t : ℝ≥0∞) < ζ ω then
      (W t ω, (fun i => VL i t ω), fun i => VR i t ω) else 0) ⁻¹' S =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ (W t ω, (fun i => VL i t ω), fun i => VR i t ω) ∈ S} ∪
        ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) ∈ S}) := by
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h]
  rw [hpre]
  exact (hX _ S hS).union ((LawUnique.measurableSet_lt_lifetime hX _).compl.inter (MeasurableSet.const _))

/-- Reading a full killed history at the dyadic times. -/
def toDyadic (k : ℝ≥0∞ × (ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : HistorySpace nL nR :=
  (k.1, fun p => k.2 (dyadicTime p))

theorem measurable_toDyadic : Measurable (toDyadic (nL := nL) (nR := nR)) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd)

omit [MeasurableSpace Ω] in
theorem toDyadic_killedHistory (ω : Ω) :
    toDyadic (Determination.killedHistory W VL VR ζ ω) = LawUnique.killedHistory W VL VR ζ ω := rfl

/-- **The paths of a history graph, read off dyadic values** (the second half of the proof of
`LawUnique.isFieldDeterminedHistory_of_map_eq`, with its determining map explicit): if the dyadic killed history is
`historyOfPaths (Ψ h)` almost surely and the driving process is continuous before its lifetime, then
`pathsOfDyadic ∘ Ψ` is a graph of the killed driving history. -/
theorem isHistoryGraph_pathsOfDyadic {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}
    (hK : (fun ω => LawUnique.killedHistory W VL VR ζ ω) =ᵐ[P] fun ω => historyOfPaths (Ψ (h ω)))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    Determination.IsHistoryGraph P h W VL VR ζ fun d => pathsOfDyadic (Ψ d) := by
  filter_upwards [hK, hcont] with ω hω hc
  have hζ : (Ψ (h ω)).1 = ζ ω := (congrArg Prod.fst hω).symm
  have hdy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ n,
      (W (dyadicTime (lowerDyadic t n)) ω, (fun i => VL i (dyadicTime (lowerDyadic t n)) ω),
        fun i => VR i (dyadicTime (lowerDyadic t n)) ω) =
      ((Ψ (h ω)).2.1 (dyadicTime (lowerDyadic t n)),
        (fun i => (Ψ (h ω)).2.2.1 i (dyadicTime (lowerDyadic t n))),
        fun i => (Ψ (h ω)).2.2.2 i (dyadicTime (lowerDyadic t n))) := by
    intro t ht n
    have hlt : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (LawUnique.dyadicTime_lowerDyadic_le t n)) ht
    have e := congrFun (congrArg Prod.snd hω) (lowerDyadic t n)
    simp only [LawUnique.killedHistory, historyOfPaths, hζ, hlt, ↓reduceIte] at e
    exact e
  refine ⟨hζ, fun t ht => ⟨?_, fun i => ?_, fun i => ?_⟩⟩
  · refine (Tendsto.limUnder_eq ?_)
    refine (LawUnique.tendsto_lowerDyadic_of_continuousOn hc.1 ht).congr fun n => ?_
    exact congrArg Prod.fst (hdy t ht n)
  · refine (Tendsto.limUnder_eq ?_)
    refine (LawUnique.tendsto_lowerDyadic_of_continuousOn (hc.2.1 i) ht).congr fun n => ?_
    exact congrFun (congrArg (fun x => x.2.1) (hdy t ht n)) i
  · refine (Tendsto.limUnder_eq ?_)
    refine (LawUnique.tendsto_lowerDyadic_of_continuousOn (hc.2.2 i) ht).congr fun n => ?_
    exact congrFun (congrArg (fun x => x.2.2) (hdy t ht n)) i

/-- A history graph gives the dyadic killed history as `historyOfPaths ∘ Ψ` of the field. -/
theorem IsHistoryGraph.dyadic_ae_eq {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}
    (hΨ : Determination.IsHistoryGraph P h W VL VR ζ Ψ) :
    (fun ω => LawUnique.killedHistory W VL VR ζ ω) =ᵐ[P] fun ω => historyOfPaths (Ψ (h ω)) := by
  filter_upwards [hΨ] with ω hω
  obtain ⟨hζ, hpath⟩ := hω
  simp only [LawUnique.killedHistory, historyOfPaths, hζ, Prod.mk.injEq, true_and]
  funext p
  split_ifs with hp
  · obtain ⟨e1, e2, e3⟩ := hpath _ hp
    rw [e1, funext e2, funext e3]
  · rfl

end Killed

/-! ### One reference graph serves every coupling -/

section Reference

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
  {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞} {h₁ : Ω₁ → LQGMetric.DistOn upperHalfPlaneOpens}
  {h₂ : Ω₂ → LQGMetric.DistOn upperHalfPlaneOpens}

/-- Under universal determination, the joint laws of the field and the **dyadic** killed history agree in any two
couplings (`Determination.map_field_killedHistory_eq`, read at the dyadic times). -/
theorem map_field_dyadicHistory_eq [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fun ω => (h₁ ω, LawUnique.killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => (h₂ ω, LawUnique.killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
  have hlaw := Determination.map_field_killedHistory_eq hdet hC₁ hC₂
  have hD : Measurable (Prod.map id (toDyadic (nL := nL) (nR := nR)) :
      LQGMetric.DistOn upperHalfPlaneOpens × _ → _) := measurable_id.prodMap measurable_toDyadic
  have e₁ : (fun ω => (h₁ ω, LawUnique.killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      Prod.map id toDyadic ∘ fun ω => (h₁ ω, Determination.killedHistory W₁ VL₁ VR₁ ζ₁ ω) := rfl
  have e₂ : (fun ω => (h₂ ω, LawUnique.killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      Prod.map id toDyadic ∘ fun ω => (h₂ ω, Determination.killedHistory W₂ VL₂ VR₂ ζ₂ ω) := rfl
  rw [e₁, e₂, ← Measure.map_map hD (hC₁.2.1.prodMk (measurable_killedHistory hC₁.2.2.2.1)),
    ← Measure.map_map hD (hC₂.2.1.prodMk (measurable_killedHistory hC₂.2.2.2.1)), hlaw]

/-- **A graph transfers along equal joint laws** (the proof of `LawUnique.isFieldDeterminedHistory_of_map_eq` with
its determining map explicit). If two couplings have the same joint law of the field and the dyadic killed history
and `Ψ` is a Borel graph of the killed driving history of the first one, then `pathsOfDyadic ∘ Ψ` is a graph of the
killed driving history of the second one. -/
theorem isHistoryGraph_pathsOfDyadic_of_map_eq {Ω₁' Ω₂' : Type*} {m₁' : MeasurableSpace Ω₁'}
    {m₂' : MeasurableSpace Ω₂'} {P₁' : Measure Ω₁'} {P₂' : Measure Ω₂'} {𝓕₁' : Filtration ℝ≥0 m₁'}
    {𝓕₂' : Filtration ℝ≥0 m₂'} {W₁' : ℝ≥0 → Ω₁' → ℝ} {W₂' : ℝ≥0 → Ω₂' → ℝ} {VL₁' : Fin nL → ℝ≥0 → Ω₁' → ℝ}
    {VL₂' : Fin nL → ℝ≥0 → Ω₂' → ℝ} {VR₁' : Fin nR → ℝ≥0 → Ω₁' → ℝ} {VR₂' : Fin nR → ℝ≥0 → Ω₂' → ℝ}
    {B₁' : ℝ≥0 → Ω₁' → ℝ} {B₂' : ℝ≥0 → Ω₂' → ℝ} {ζ₁' : Ω₁' → ℝ≥0∞} {ζ₂' : Ω₂' → ℝ≥0∞}
    {h₁' : Ω₁' → LQGMetric.DistOn upperHalfPlaneOpens} {h₂' : Ω₂' → LQGMetric.DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁' 𝓕₁' W₁' VL₁' VR₁' B₁' ζ₁' h₁')
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂' 𝓕₂' W₂' VL₂' VR₂' B₂' ζ₂' h₂')
    (hlaw : P₁'.map (fun ω => (h₁' ω, LawUnique.killedHistory W₁' VL₁' VR₁' ζ₁' ω)) =
      P₂'.map (fun ω => (h₂' ω, LawUnique.killedHistory W₂' VL₂' VR₂' ζ₂' ω)))
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}
    (hΨm : Measurable Ψ) (hΨ : Determination.IsHistoryGraph P₁' h₁' W₁' VL₁' VR₁' ζ₁' Ψ) :
    Determination.IsHistoryGraph P₂' h₂' W₂' VL₂' VR₂' ζ₂' fun d => pathsOfDyadic (Ψ d) := by
  have hK₂ := Sec7.ae_eq_comp_of_map_eq
    (hC₁.2.1.prodMk (LawUnique.measurable_killedHistory hC₁.2.2.2.1)).aemeasurable
    (hC₂.2.1.prodMk (LawUnique.measurable_killedHistory hC₂.2.2.2.1)).aemeasurable
    hlaw (measurable_historyOfPaths.comp hΨm) (IsHistoryGraph.dyadic_ae_eq hΨ)
  exact isHistoryGraph_pathsOfDyadic hK₂ (LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving hC₂.1)

/-- **The reference graph transfers under universal determination.** If every coupling of the force word is
field-determined and `Ψ` is a Borel graph of the killed driving history of one coupling, then `pathsOfDyadic ∘ Ψ` is a
graph of the killed driving history of every coupling (on a probability space in the same universe). -/
theorem isHistoryGraph_pathsOfDyadic_of_reference [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}
    (hΨm : Measurable Ψ) (hΨ : Determination.IsHistoryGraph P₁ h₁ W₁ VL₁ VR₁ ζ₁ Ψ) :
    Determination.IsHistoryGraph P₂ h₂ W₂ VL₂ VR₂ ζ₂ fun d => pathsOfDyadic (Ψ d) :=
  isHistoryGraph_pathsOfDyadic_of_map_eq hC₁ hC₂ (map_field_dyadicHistory_eq hdet hC₁ hC₂) hΨm hΨ

end Reference

/-! ### The universal Lemma 7.5 -/

/-- The universal determining map of the flow lines from seed `x` at angle `θ`, built from a graph `Ψ` of the
killed driving history of the flow-line word: translate the field (`h ↦ h(· + x) + θχ`), read the driving path
through `pathsOfDyadic ∘ Ψ`, reconstruct the trace (`LP.drivingTrace`) and add the seed back. -/
def flowLineMap (κ x θ : ℝ) {nL nR : ℕ}
    (Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ))
    (d : LQGMetric.DistOn upperHalfPlaneOpens) : ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  ((LP.drivingTrace ((pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).1,
      (pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).2.1)).1,
    fun t => (LP.drivingTrace ((pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).1,
      (pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).2.1)).2 t + x)

theorem measurable_flowLineMap (κ x θ : ℝ) {nL nR : ℕ}
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}
    (hΨ : Measurable Ψ) : Measurable (flowLineMap κ x θ Ψ) := by
  have hP : Measurable fun d => pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d)) :=
    measurable_pathsOfDyadic.comp (hΨ.comp (Exist.measurable_flowField _ _))
  have hT : Measurable fun d => LP.drivingTrace
      ((pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).1,
        (pathsOfDyadic (Ψ (Exist.flowField x (θ * QuantumZipper.chiC κ) d))).2.1) :=
    LP.measurable_drivingTrace.comp ((measurable_fst.comp hP).prodMk (measurable_fst.comp (measurable_snd.comp hP)))
  refine (measurable_fst.comp hT).prodMk (measurable_pi_iff.2 fun t => ?_)
  exact ((measurable_pi_apply t).comp (measurable_snd.comp hT)).add_const _

section FlowLine

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ}

/-- **The flow line from a graph of its coupling.** If `pathsOfDyadic ∘ Ψ` is a graph of the killed driving history
of the coupling of a flow line (with the coupling field `h(· + x) + θχ`), then `flowLineMap κ x θ Ψ` of the field gives
almost surely the lifetime and the path up to the lifetime. -/
theorem ae_flowLineMap_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) P 𝓕 W VL VR B ζ fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x))
    {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin (flowLineNL b jumps x) → ℝ≥0 → ℝ) ×
      (Fin (flowLineNR b jumps x) → ℝ≥0 → ℝ)}
    (hG : Determination.IsHistoryGraph P (fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω)) W VL VR ζ
      fun d => pathsOfDyadic (Ψ d)) :
    ∀ᵐ ω ∂P, (flowLineMap κ x θ Ψ (h ω)).1 = ζ ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (flowLineMap κ x θ Ψ (h ω)).2 t = η ω t := by
  filter_upwards [hG, htrace, hC.1.2.2.2.2] with ω hGω htrω hpath
  obtain ⟨hζ, hW⟩ := hGω
  obtain ⟨hw0, -, -, hcw, -⟩ := hpath
  have e := LP.drivingTrace_eq htrω hcw hw0 fun s hs => (hW s hs).1
  simp only [flowLineMap]
  rw [hζ, e]
  refine ⟨rfl, fun t ht => ?_⟩
  simp only [min_eq_left ht, ENNReal.toNNReal_coe, sub_add_cancel]

/-- **One universal map from one reference and the uniqueness of the joint law.** For a flow-line word whose
optional hull couplings (in the universe `u`) all have one joint law of the field and the killed driving history, one
coupling with a field-determined killed driving history gives one Borel map of the field which yields the lifetime and
the path of every flow line (of every field) with this datum, seed and angle. -/
theorem exists_flowLineMap_of_lawUnique
    (hU : LawUnique.IsOptionalHullLawUnique.{u, u} κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ))
    (href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓕₀ : Filtration ℝ≥0 m₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
      (h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
        (flowLineRhoR κ b jumps x θ) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ ∧ LP.IsFieldDeterminedHistory P₀ h₀ W₀ VL₀ VR₀ ζ₀) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t := by
  obtain ⟨Ω₀, m₀, P₀, _, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, Ψ₀, hΨ₀m, hΨ₀⟩ := href
  refine ⟨flowLineMap κ x θ Ψ₀, measurable_flowLineMap κ x θ hΨ₀m, ?_⟩
  intro Ω mΩ P _ h _ η ζ hFL
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, htrace⟩ := hFL
  have hh' : h' = fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => eq_flowField_of_isTranslateAddConst (htr ω)
  subst hh'
  exact ae_flowLineMap_eq hC htrace (isHistoryGraph_pathsOfDyadic_of_map_eq hC₀ hC
    (hU P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀ P 𝓕 W VL VR B ζ _ hC) hΨ₀m hΨ₀)

/-- **Lemma 7.5, universal form, in the non-boundary-intersecting regime, from one reference.** For `0 < κ ≤ 4` and
a flow-line word with admissible side partial sums (every partial sum `≥ κ/2 − 2`: Remark 4.1's regime, where the
flow line does not touch `ℝ ∖ {x}`), the joint law of the field and the killed driving history is the same in every
coupling (Aux. lemma 23, `Sec4.isOptionalHullLawUnique_of_admissible`, proved), so one coupling with a
field-determined killed driving history (Theorem 1.2 in §4.2's regime) gives one Borel map of the field for every
flow line with this datum, seed and angle. Neither Proposition 7.3 nor Aux. lemmas 52–55 are used. -/
theorem exists_flowLineMap_of_admissible (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hadm : Sec4.HasAdmissiblePartialSums κ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ)
      (flowLineXL b jumps x) (flowLineXR b jumps x))
    (href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓕₀ : Filtration ℝ≥0 m₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
      (h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
        (flowLineRhoR κ b jumps x θ) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ ∧ LP.IsFieldDeterminedHistory P₀ h₀ W₀ VL₀ VR₀ ζ₀) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t :=
  exists_flowLineMap_of_lawUnique
    (Sec4.isOptionalHullLawUnique_of_admissible hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b jumps x) hadm) href

end FlowLine

/-- **Lemma 7.5, universal form, from Lemma 7.5 per coupling.** If every coupling of every ordered force word
satisfying the frozen optional hull specification has a field-determined killed driving history (for `0 < κ < 4`;
`LP.Lemma75DeterminationStatement`, proved by LOCEXT from Proposition 7.3 and Aux. 53–55), then for every datum, seed
and angle one Borel map of the field gives the lifetime and the path of every flow line of every field with that
datum (`Theorem15.Lemma75Statement`). -/
theorem lemma75Statement_of_lemma75DeterminationStatement (h75 : LP.Lemma75DeterminationStatement.{u}) :
    Theorem15.Lemma75Statement.{u} := by
  intro κ hκ hκ4 b jumps _hb x θ
  have hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) :=
    h75 κ hκ hκ4 (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) (Theorem15.isOrderedForceWord_flowLine b jumps x)
  by_cases href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓕₀ : Filtration ℝ≥0 m₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
      (h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
        (flowLineRhoR κ b jumps x θ) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀
  · obtain ⟨Ω₀, m₀, P₀, _, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀⟩ := href
    obtain ⟨Ψ₀, hΨ₀m, hΨ₀⟩ := hdet P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀
    refine ⟨flowLineMap κ x θ Ψ₀, measurable_flowLineMap κ x θ hΨ₀m, ?_⟩
    intro Ω mΩ P _ h _ η ζ hFL
    obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, htrace⟩ := hFL
    have hh' : h' = fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω) :=
      funext fun ω => eq_flowField_of_isTranslateAddConst (htr ω)
    subst hh'
    exact ae_flowLineMap_eq hC htrace (isHistoryGraph_pathsOfDyadic_of_reference hdet hC₀ hC hΨ₀m hΨ₀)
  · refine ⟨fun _ => (0, fun _ => 0), measurable_const, ?_⟩
    intro Ω mΩ P _ h _ η ζ hFL
    obtain ⟨h', 𝓕, W, VL, VR, B, -, hC, -⟩ := hFL
    exact absurd ⟨Ω, mΩ, P, inferInstance, 𝓕, W, VL, VR, B, ζ, h', hC⟩ href

end Lemma75Bridge

end InteractingSLE
