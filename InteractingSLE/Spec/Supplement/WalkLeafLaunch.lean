/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLeafRead
import InteractingSLE.Spec.Supplement.WalkLeafChart
import InteractingSLE.Spec.Supplement.WalkStageLocalKernel
import InteractingSLE.Spec.Supplement.StagedDet
import InteractingSLE.Spec.Restart.StagedEntranceStaged

/-!
# Theorem 1.4's walk leaves: a launched piece is marked local under the stage kernel

Packet PROVE-T14-WALK. **`walkStageLaunchLocalStatement_of_thm12_thm13`** proves the named input
`WalkLaw.WalkStageLaunchLocalStatement θ right` of PROVE-T14-WALKLAW3 (the per-piece content of the follow-up note's
Part D.2, `source/external/AstraIG1/ig1_followup_a_e_audited.txt` L771–L832: "Given the old marked datum, a new
ordinary stage is the canonical finite-word flow of that conditional field") from Theorems 1.2 (parametric form) and
1.3, which ruling R48 allows for Theorem 1.4. It holds for every staged history whose instruction `k` launches flows
of a fixed angle and infinite instruction time (`launchLocal_of_thm12_thm13`); both boundary walks are such.

## The argument, for almost every `ω₀` at which instruction `k` launches a piece

Write `ν` for the regular conditional law given the retained past `pastSigma k` at `ω₀`, `c₀` for the chart of the
state after `k` instructions at `ω₀`, `h'' = h ∘ c₀⁻¹ + χ lift` for the chart field.

1. Under `ν` the run before `k` is that of `ω₀` (`CondDriverBridge.ae_ae_run_eq_of_le`): the launch, the chart `c₀`
   and the explored set `K = stageSet k ω₀` are frozen; the staged clause makes `(E k)` the angle-`θ` flow-line driver
   of `h''` (`IsStagedHistory.exists_isCondFlowLineDriverOn`); `StagedPiecesRegular` makes the piece regular.
2. **The path of the piece** `p = recPath (recOf ⊤ (E k))` (its trace frozen at the lifetime; `WalkLeafRead`) is
   continuous at every sample and, by SB7's field determination (`StagedDet.ae_recOf_eq_stageRec`, Theorems 1.2/1.3),
   `ν`-almost surely a Borel function of the centred chart field.
3. For an open `U ⊆ ℍ \ K` and a Markov decomposition `G` of the centred field along `U` under `ν`: Aux. lemma 56 and
   Lemma 6.2 for the flow line `p` of `h''` (`StagedEntrance.measurable_entranceHist_of_isFlowLine_capped`, at every
   integer cap, then `measurable_entranceHist_of_frozen`) make the entrance history of `p` into `V = chartPre c₀ U` a
   function of the Markov complement of the chart field along `V`; the chart transport of the Markov complement
   (`MarkovChart.ae_markovCompl_pushTest_eq`; `U \ dom c₀` is open since the frontier of `dom c₀` in `ℍ` lies on `K`,
   `WalkLeafChart.mem_stageSet_of_frontier`) makes it a function of `Y = h⁰ − G h⁰`.
4. **The event**: `{piece ∩ U = ∅} ∩ {record ∈ B}` is `ν`-almost surely the event "the entrance history of `p` into
   `V` has infinite entrance time and its coordinates, read by `readRec`, lie in `B`" (`disjoint_pieceSet_iff`: the
   chart's boundary values on the trace are on `K` or real, hence off `U`; `readRec_pathCoord`: the record is read
   from the rational coordinates of `p`). So the event is `ν`-almost surely an event of `Y`, and its conditional
   probability given the field is the indicator of that event (`exists_condExp_eq_of_mem_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkLeaf

open LocalSets Exist.Staged Exist.StagedLaw Sec6 Restart.StagedEntrance

/-! ### Generic facts -/

section Generic

/-- The path coordinates stopped at `⊤` are the path coordinates. -/
theorem stopCoord_top (c : ℚ≥0 → ℂ) : stopCoord c ⊤ = c := by
  funext q
  simp only [stopCoord, le_top, ↓reduceIte]

/-- **The marked criterion from an event almost surely determined by the Markov complement**: if `S` is, under `ν`,
almost surely an event of `h − G h`, its conditional probability given `h` is a Borel function of `h − G h`. -/
theorem exists_condExp_eq_of_mem_aeSigma {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G) {S : Set Ω}
    (hS : MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance) ν] S) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      ν⟦S | MeasurableSpace.comap X inferInstance⟧ =ᵐ[ν] fun ω => g (markovCompl G (X ω)) := by
  obtain ⟨K, ⟨B, hB, rfl⟩, hSK⟩ := hS
  have hle : MeasurableSpace.comap X inferInstance ≤ mΩ := hXm.comap_le
  have hYm : Measurable[MeasurableSpace.comap X inferInstance] fun ω => markovCompl G (X ω) :=
    (measurable_markovCompl hG).comp (comap_measurable X)
  have hKm : MeasurableSet[MeasurableSpace.comap X inferInstance] ((fun ω => markovCompl G (X ω)) ⁻¹' B) := hYm hB
  refine ⟨B.indicator fun _ => (1 : ℝ), measurable_const.indicator hB, ?_⟩
  refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hSK)).trans ?_
  rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator hKm).stronglyMeasurable)
    ((integrable_const (1 : ℝ)).indicator (hle _ hKm))]
  exact Eventually.of_forall fun ω => by
    by_cases hω : markovCompl G (X ω) ∈ B
    · simp [hω]
    · simp [hω]

/-- A path on `[0, S]` frozen at `S` is continuous when it is continuous on `[0, S]`. -/
theorem continuous_frozenAt {α : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S}) :
    Continuous fun r : ℝ≥0 => α (min (r : ℝ≥0∞) S).toNNReal := by
  have hne : ∀ r : ℝ≥0, min (r : ℝ≥0∞) S ≠ ⊤ := fun r =>
    (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top).ne
  have hφ : Continuous fun r : ℝ≥0 => (min (r : ℝ≥0∞) S).toNNReal :=
    ENNReal.continuousOn_toNNReal.comp_continuous (ENNReal.continuous_coe.min continuous_const) hne
  refine hα.comp_continuous hφ fun r => ?_
  show (((min (r : ℝ≥0∞) S).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S
  rw [ENNReal.coe_toNNReal (hne r)]
  exact min_le_right _ _

/-- Freezing at an integer time and at the lifetime commute with the capped time of Lemma 6.2's capped paths. -/
theorem frozen_capTime (ζ : ℝ≥0∞) (n : ℕ) (t : ℝ≥0) :
    (min ((min t (n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ζ).toNNReal =
      (min ((Restart.capTime (n : ℝ≥0) ζ t : ℝ≥0) : ℝ≥0∞) ζ).toNNReal := by
  induction ζ using ENNReal.recTopCoe with
  | top =>
    simp only [min_top_right, ENNReal.toNNReal_coe, Restart.capTime, min_top_left, ENNReal.coe_natCast,
      ENNReal.toNNReal_natCast]
  | coe z =>
    have e : Restart.capTime (n : ℝ≥0) (z : ℝ≥0∞) t = min t (min z (n : ℝ≥0)) := by
      simp only [Restart.capTime]
      rw [show (((n : ℝ≥0) : ℝ≥0∞)) = ((n : ℝ≥0) : ℝ≥0∞) from rfl, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
    rw [e, ← ENNReal.coe_min, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rw [min_eq_left ((min_le_right _ _).trans (min_le_left _ _) : min t (min z (n : ℝ≥0)) ≤ z), min_assoc,
      min_comm (n : ℝ≥0) z]

end Generic


/-! ### The path of a launched piece -/

section PiecePath

variable {Ω : Type*}

/-- **The path of the piece launched by instruction `k`** (its trace frozen at the lifetime), read from its record on
a set `M` of samples, `0` off `M`. -/
def piecePath (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (M : Set Ω) (ω : Ω) (t : ℝ≥0) : ℂ :=
  haveI := Classical.propDecidable
  if ω ∈ M then recPath (recOf ⊤ (E k ω)) t else 0

variable {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {M : Set Ω}

theorem piecePath_of_mem {ω : Ω} (hω : ω ∈ M) (t : ℝ≥0) :
    piecePath E k M ω t = recPath (recOf ⊤ (E k ω)) t := by
  simp only [piecePath, hω, ↓reduceIte]

/-- On `M` (a regular piece) the path is any generating trace frozen at the lifetime. -/
theorem piecePath_eq {ω : Ω} (hω : ω ∈ M) (hr : GW1P.PieceRegular (E k ω).1 (E k ω).2) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (E k ω).1 (E k ω).2 α) (t : ℝ≥0) :
    piecePath E k M ω t = α (min (t : ℝ≥0∞) (E k ω).2).toNNReal := by
  rw [piecePath_of_mem hω, recPath_recOf_top hr.2.1 hr.1 hα]

theorem piecePath_zero (hM : ∀ ω ∈ M, GW1P.PieceRegular (E k ω).1 (E k ω).2) (ω : Ω) :
    piecePath E k M ω 0 = 0 := by
  by_cases hω : ω ∈ M
  · obtain ⟨-, -, α, hα, -⟩ := hM ω hω
    rw [piecePath_eq hω (hM ω hω) hα]
    simpa using hα.1
  · simp only [piecePath, hω, ↓reduceIte]

theorem continuous_piecePath (hM : ∀ ω ∈ M, GW1P.PieceRegular (E k ω).1 (E k ω).2) (ω : Ω) :
    Continuous (piecePath E k M ω) := by
  by_cases hω : ω ∈ M
  · obtain ⟨-, -, α, hα, -⟩ := hM ω hω
    have e : piecePath E k M ω = fun t : ℝ≥0 => α (min (t : ℝ≥0∞) (E k ω).2).toNNReal :=
      funext (piecePath_eq hω (hM ω hω) hα)
    rw [e]
    exact continuous_frozenAt hα.2.1
  · have e : piecePath E k M ω = fun _ => 0 := funext fun t => by simp only [piecePath, hω, ↓reduceIte]
    rw [e]
    exact continuous_const

theorem measurable_piecePath [MeasurableSpace Ω] (hM : MeasurableSet M) (hEm : Measurable (E k))
    (hreg : ∀ ω, IsRegularDriver (E k ω)) (t : ℝ≥0) : Measurable fun ω => piecePath E k M ω t := by
  classical
  exact Measurable.ite hM ((measurable_recPath t).comp (measurable_recOf hEm hreg ⊤)) measurable_const

/-- On `M`, the path is a generating trace of the piece's driver on `[0, ζ]`. -/
theorem isGeneratingTrace_piecePath {ω : Ω} (hω : ω ∈ M) (hr : GW1P.PieceRegular (E k ω).1 (E k ω).2) :
    IsGeneratingTrace (E k ω).1 (E k ω).2 (piecePath E k M ω) := by
  obtain ⟨-, -, α, hα, -⟩ := id hr
  have e : piecePath E k M ω = fun t : ℝ≥0 => α (min (t : ℝ≥0∞) (E k ω).2).toNNReal :=
    funext (piecePath_eq hω hr hα)
  rw [e]
  exact isGeneratingTrace_frozen hα

end PiecePath

/-! ### One launched piece under one conditional law -/

section Kernel

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- **A flow line of a chart field, read physically, is marked local off the old explored set, for the marks of its
own record.** Let `c₀` be a conformal chart whose domain has its frontier in `ℍ` on `K`, `h''` the chart field of `h`,
and `e` the driver of an angle-`θ` flow line of `h''` (data `bc`, `jc`) under `ν`, with a path `p` (continuous at every
sample, from `0`) that is `ν`-almost surely a generating trace of `e` on `[0, ζ]` frozen at `ζ`, the driver continuous
on `[0, ζ]`, and `p` determined by `h''`. If a random set `B` avoids every open `U ⊆ ℍ` off `K` exactly when `p` avoids
the chart pre-image of `U`, then `B` is history-avoidance local off `K` for the centred field and the marks
`σ(recOf ⊤ e)`. -/
theorem isHistoryAvoidanceLocalOff_of_chartFlow {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) (u₀ : ℂ → ℝ)
    {c₀ : Chart} (hcc₀ : c₀.IsConformal) {K : Set ℂ}
    (hfr : ∀ z ∈ H, z ∈ closure (c₀.dom : Set ℂ) → z ∉ c₀.dom → z ∈ K)
    {bc : ℝ → ℝ} {jc : Finset ℝ} (hbp : IsPiecewiseConstantBoundaryData bc jc)
    {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hfl : IsFlowLineDriver κ bc jc θ ν (fun ω => Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω))
      (fun t ω => (e ω).1 t) (fun ω => (e ω).2))
    {p : Ω → ℝ≥0 → ℂ} (hpc : ∀ ω, Continuous (p ω)) (hpm : ∀ t, Measurable fun ω => p ω t)
    (hp0 : ∀ ω, p ω 0 = 0)
    (hpg : ∀ᵐ ω ∂ν, IsGeneratingTrace (e ω).1 (e ω).2 (p ω) ∧
      ContinuousOn (e ω).1 {t | (t : ℝ≥0∞) ≤ (e ω).2} ∧ ∀ t, p ω t = p ω (min (t : ℝ≥0∞) (e ω).2).toNNReal)
    (hdet : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => p ω t) =ᵐ[ν] fun ω => f (Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω)))
    {B : Ω → Set ℂ}
    (hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → Disjoint K U →
      ∀ᵐ ω ∂ν, (Disjoint (B ω) U ↔ ∀ t, p ω t ∉ Restart.MarkovChart.chartPre c₀ U)) :
    WalkLaw.IsHistoryAvoidanceLocalOff (MeasurableSpace.comap (fun ω => recOf ⊤ (e ω)) inferInstance) K B
      (WholeField.centredField h u₀) ν := by
  intro U G hUH hKU hG hd F hF
  obtain ⟨Bm, hBm, rfl⟩ := hF
  set h'' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω) with hh''
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbp hfl
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbp
  set X'' : Ω → DistOn upperHalfPlaneOpens := WholeField.centredField h'' u' with hX''
  have hZB : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X'' ν :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu'
  set Vo : Opens ℂ := Restart.MarkovChart.chartPreOpens hcc₀ U with hVo
  obtain ⟨G', hG'm, hG'⟩ := LocalSets.exists_markovMap Vo (Restart.MarkovChart.chartPre_subset_H _ _)
  have hd' := hG' hZB
  -- the flow line with trace `p`
  obtain ⟨h₃, 𝓕, VL, VR, Bw, ht3, hC⟩ := hfl
  have hflp : IsFlowLine κ bc jc 0 θ ν h'' p (fun ω => (e ω).2) := by
    refine ⟨h₃, 𝓕, fun t ω => (e ω).1 t, VL, VR, Bw, ht3, hC, ?_⟩
    filter_upwards [hpg] with ω hω
    simpa only [Complex.ofReal_zero, sub_zero] using hω.1
  -- Lemma 6.2 for the capped paths, then for the path
  have hcap : ∀ n : ℕ, Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (X'' ω)) inferInstance) ν]
      fun ω => histOf (pathCoord (frozenPath (p ω) n)) (firstEntrance Vo (pathCoord (frozenPath (p ω) n))) := by
    intro n
    refine measurable_entranceHist_of_isFlowLine_capped hκ hκ4 hbp hgff hflp hu' (n : ℝ≥0)
      (ηc := fun ω => frozenPath (p ω) n) (fun ω => continuous_frozenPath (hpc ω)) (fun t => hpm _) ?_ ?_ ?_
      Vo (Restart.MarkovChart.chartPre_subset_H _ _) G' hG'm hd'
    · intro ω hH
      rw [frozenPath_zero, hp0] at hH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
    · filter_upwards [hpg] with ω hω t
      change p ω (min t (n : ℝ≥0)) = p ω (Restart.capTime (n : ℝ≥0) (e ω).2 t)
      rw [hω.2.2 (min t (n : ℝ≥0)), hω.2.2 (Restart.capTime (n : ℝ≥0) (e ω).2 t), frozen_capTime]
    · intro t
      obtain ⟨f, hf, hfe⟩ := hdet (min t (n : ℝ≥0))
      refine ⟨fun X => f (X + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u'),
        hf.comp (Coupling.measurable_add_distOnConst _), ?_⟩
      filter_upwards [hfe] with ω hω
      change p ω (min t (n : ℝ≥0)) = _
      rw [hω]
      simp only [WholeField.centredField, sub_add_cancel, hh'']
  have hHp := measurable_entranceHist_of_frozen hpc Vo.isOpen hcap
  -- the Markov complement of the chart field is a function of that of the field
  have hUD : IsOpen ((U : Set ℂ) \ c₀.dom) := Restart.StagedEntrance.isOpen_sdiff_dom U.isOpen hUH hfr hKU
  set m : TestOn upperHalfPlaneOpens → ℝ := fun φ =>
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ (Chart.pushTest hcc₀ φ) +
      chiC κ * Chart.liftDist c₀ φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u' φ
    with hm
  have hh' : ∀ φ, ∀ᵐ ω ∂ν, X'' ω φ = WholeField.centredField h u₀ ω (Chart.pushTest hcc₀ φ) + m φ :=
    fun φ => Eventually.of_forall fun ω => by
      have e1 : h'' ω φ = 1 * h ω (Chart.pushTest hcc₀ φ) + 0 * Chart.oneDist φ +
          chiC κ * Chart.liftDist c₀ φ := Chart.chartTransport_apply' _ _ _ _ _ _
      simp only [hX'', WholeField.centredField, sub_apply, e1, hm]
      ring
  have hU' : U ≤ upperHalfPlaneOpens := hUH
  have hY' : Measurable[aeSigma (MeasurableSpace.comap
      (fun ω => markovCompl G (WholeField.centredField h u₀ ω)) inferInstance) ν]
      fun ω => markovCompl G' (X'' ω) := by
    refine Restart.StagedEntrance.measurable_aeSigma_of_ae_eq fun φ =>
      ⟨fun T => T (Chart.pushTest hcc₀ φ) + m φ, (LQGMetric.measurable_distOn_apply _).add_const _, ?_⟩
    filter_upwards [Restart.MarkovChart.ae_markovCompl_pushTest_eq hcc₀ hUH hUD hd.isZBGFFExtOn
      (ae_isHarmonicDistOn_of_isMarkovDecomposition hU' hd) hd' m hh' φ] with ω hω
    show (X'' ω - G' (X'' ω)) φ =
      (WholeField.centredField h u₀ ω - G (WholeField.centredField h u₀ ω)) (Chart.pushTest hcc₀ φ) + m φ
    rw [sub_apply, sub_apply]
    exact hω
  -- the event, read from the entrance history of `p`
  set xL := flowLineXL bc jc 0
  set xR := flowLineXR bc jc 0
  set ρL := flowLineRhoL κ bc jc 0 θ
  set ρR := flowLineRhoR κ bc jc 0 θ
  set Bset : Set Hist := {x | x.1 = ⊤ ∧ readRec κ xL xR ρL ρR x.2 ∈ Bm} with hBset
  have hBsetm : MeasurableSet Bset :=
    (measurable_fst (measurableSet_singleton ⊤)).inter ((measurable_readRec xL xR ρL ρR hκ).comp measurable_snd hBm)
  have hS : ({ω | Disjoint (B ω) U} ∩ (fun ω => recOf ⊤ (e ω)) ⁻¹' Bm : Set Ω) =ᵐ[ν]
      (fun ω => histOf (pathCoord (p ω)) (firstEntrance Vo (pathCoord (p ω)))) ⁻¹' Bset := by
    filter_upwards [hev U hUH hKU, hpg, hC.1.2.2.2.2] with ω hevω hg hpath
    have hrec : readRec κ xL xR ρL ρR (pathCoord (p ω)) = recOf ⊤ (e ω) :=
      readRec_pathCoord hκ hpath hg.1 hg.2.1
    have hfe : firstEntrance Vo (pathCoord (p ω)) = ⊤ ↔ Disjoint (B ω) U := by
      rw [firstEntrance_eq_top_iff Vo.isOpen (hpc ω), hevω]
      rfl
    apply propext
    change Disjoint (B ω) U ∧ recOf ⊤ (e ω) ∈ Bm ↔ firstEntrance Vo (pathCoord (p ω)) = ⊤ ∧
      readRec κ xL xR ρL ρR (stopCoord (pathCoord (p ω)) (firstEntrance Vo (pathCoord (p ω)))) ∈ Bm
    constructor
    · rintro ⟨hdj, hB⟩
      have htop := hfe.2 hdj
      rw [htop, stopCoord_top, hrec]
      exact ⟨rfl, hB⟩
    · rintro ⟨htop, hB⟩
      rw [htop, stopCoord_top, hrec] at hB
      exact ⟨hfe.1 htop, hB⟩
  obtain ⟨S', hS', hSS'⟩ := hHp hBsetm
  have hmem : MeasurableSet[aeSigma (MeasurableSpace.comap
      (fun ω => markovCompl G (WholeField.centredField h u₀ ω)) inferInstance) ν]
      ({ω | Disjoint (B ω) U} ∩ (fun ω => recOf ⊤ (e ω)) ⁻¹' Bm) :=
    aeSigma_le_aeSigma hY'.comap_le _ ⟨S', hS', hS.trans hSS'⟩
  exact exists_condExp_eq_of_mem_aeSigma (WholeField.measurable_centredField hhm u₀) hG hmem

end Kernel

/-! ### The launched pieces of a staged history -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A launched piece of a staged history is marked local off the explored set under the stage kernel** (Theorems
1.2–1.3; R48 allows them for Theorem 1.4). For a staged history with `StagedPiecesRegular`, drivers regular at every
sample, and an instruction `k` whose flows have the angle `θ` and an infinite instruction time: for almost every `ω₀`
at which `k` launches a piece, under the regular conditional law given the retained past `pastSigma k`, the piece is
history-avoidance local for the centred field, the marks of its own record, on the open sets off `stageSet k ω₀`. -/
theorem launchLocal_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (u₀ : ℂ → ℝ) (k : ℕ)
    {θ : ℝ} (hk : ∀ θ' t, spec.2.2[k]? = some (Sum.inl (θ', t)) → θ' = θ ∧ t = ⊤) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      WalkLaw.IsHistoryAvoidanceLocalOff
        (MeasurableSpace.comap (fun ω => recOf (instrTime spec k) (E k ω)) inferInstance)
        (WalkLaw.stageSet κ b jumps spec E k ω₀) (WalkLaw.pieceSet κ b jumps spec E k)
        (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) := by
  classical
  by_cases hT : instrTime spec k = ⊤
  swap
  · refine Eventually.of_forall fun ω₀ hl => absurd ?_ hT
    obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    exact (hk _ _ (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω₀) hl').1).2
  rw [hT]
  have hB := runMeasStatement.{u}
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  have hhm : Measurable h := hh.1
  have hpm : Measurable (pastMap κ b jumps spec E k) :=
    measurable_pastMap hB hb spec (fun j _ => hE.1 j) (fun j _ => hreg j) k le_rfl
  have hcont := StagedDet.piecesContinuous_of_stagedPiecesRegular hR
  obtain ⟨Y, hYm, hY⟩ := StagedDet.exists_stageField hb hE.1 hreg hcont k
  have hYm' : Measurable Y := hYm.mono (StagedDet.pastFieldSigma_le hpm hhm) le_rfl
  obtain ⟨Wd, hWdm, hrec⟩ := StagedDet.ae_recOf_eq_stageRec h12p h13 hκ hκ4 hb hh hE hreg hcont k hYm' hY
  rw [hT] at hrec
  obtain ⟨bc, jc, hcond⟩ := hE.exists_isCondFlowLineDriverOn k θ
  -- the good samples
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hLm : MeasurableSet L := measurableSet_launch_self hB hb (fun j _ => hE.1 j) (fun j _ => hreg j)
  set Bad : Set Ω := {ω | ¬ ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
    (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)} with hBaddef
  have hBad : P Bad = 0 := ae_iff.1 hR.ae_pieceRegular
  set M : Set Ω := L ∩ (toMeasurable P Bad)ᶜ with hMdef
  have hMm : MeasurableSet M := hLm.inter (measurableSet_toMeasurable P Bad).compl
  have hgoodR : ∀ ω, ω ∉ toMeasurable P Bad → ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
        GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P Bad hc)
  have hMreg : ∀ ω ∈ M, GW1P.PieceRegular (E k ω).1 (E k ω).2 := fun ω hω => by
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
    have := hgoodR ω hω.2 k c θ' hl
    rwa [hT, min_top_left] at this
  have hBae : ∀ᵐ ω ∂P, ω ∉ toMeasurable P Bad := by
    have h0 : P (toMeasurable P Bad) = 0 := by rw [measure_toMeasurable]; exact hBad
    exact ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using h0)
  have hpc : ∀ ω, Continuous (piecePath E k M ω) := continuous_piecePath hMreg
  have hpm' : ∀ t, Measurable fun ω => piecePath E k M ω t := measurable_piecePath hMm (hE.1 k) (hreg k)
  have hp0 : ∀ ω, piecePath E k M ω 0 = 0 := piecePath_zero hMreg
  -- the facts under the regular conditional laws
  filter_upwards [hcond, hY, hBae, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hBae,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hrec, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hY,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl] with ω₀ hc₀ hY₀ hB₀ hBν hrecν hYν hrun hl₀
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hl₀
  obtain ⟨hspec, -, hc₀def⟩ :=
    eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω₀) hl
  obtain ⟨hθ, -⟩ := hk _ _ hspec
  subst hθ
  obtain ⟨hcc₀, hℓc₀, -⟩ := hY₀ hl₀
  rw [← hc₀def] at hcc₀ hℓc₀
  have hℓ₀ : LocallyIntegrableOn (fun w => c₀.2.2 (c₀.2.1 w)) H :=
    hℓc₀.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet
  have hlc : SB.launchChart κ b jumps spec (fun j => E j ω₀) k = c₀ := by
    simp only [SB.launchChart, hl, Option.elim]
  obtain ⟨hbp, h', ht', hfl⟩ := hc₀ ⟨c₀, hl⟩
  rw [hlc] at ht'
  have e' : h' = fun ω => Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω) :=
    funext fun ω => (ht' ω).eq_chartTransport hcc₀ hℓ₀
  rw [e'] at hfl
  -- the good event under the kernel
  have hgood : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      ExplState.run κ b jumps spec (fun j => E j ω) k = ExplState.run κ b jumps spec (fun j => E j ω₀) k ∧
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c₀, θ₀) ∧ ω ∈ M ∧
      recOf ⊤ (E k ω) = StagedDet.stageRec h12p hκ Wd (instrAngle spec k) ⊤ (pastMap κ b jumps spec E k ω₀)
        (Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω)) := by
    filter_upwards [hrun, hBν, hrecν, hYν] with ω hr h1 h2 h3
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c₀, θ₀) := by
      rw [congrFun (launches_run_succ_of_run_eq spec hr) k, hl]
    have hLω : ω ∈ L := by
      show _ ≠ none
      rw [hlω]
      exact Option.some_ne_none _
    have hpast : pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E k ω₀ := by
      unfold pastMap
      rw [hr]
    obtain ⟨-, -, htr⟩ := h3 hLω
    rw [hr, ← hc₀def] at htr
    refine ⟨hr, hlω, ⟨hLω, h1⟩, ?_⟩
    rw [h2 hLω, hpast, htr.eq_chartTransport hcc₀ hℓ₀]
  -- the kernel statement
  refine isHistoryAvoidanceLocalOff_of_chartFlow hκ hκ4 hhm u₀ hcc₀ ?_ hbp hfl hpc hpm' hp0 ?_ ?_ ?_
  · intro z hzH hzcl hzD
    rw [hc₀def] at hzcl hzD
    exact mem_stageSet_of_frontier spec E ω₀ (hgoodR ω₀ hB₀) k z hzH hzcl hzD
  · filter_upwards [hgood] with ω hω
    obtain ⟨-, -, hM, -⟩ := hω
    have hr := hMreg ω hM
    refine ⟨isGeneratingTrace_piecePath hM hr, hr.2.1, fun t => ?_⟩
    obtain ⟨-, -, α, hα, -⟩ := id hr
    rw [piecePath_eq hM hr hα, piecePath_eq hM hr hα,
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)), min_assoc, min_self]
  · intro t
    refine ⟨fun X => recPath (StagedDet.stageRec h12p hκ Wd (instrAngle spec k) ⊤
      (pastMap κ b jumps spec E k ω₀) X) t, ?_, ?_⟩
    · have hsr := StagedDet.measurable_stageRec h12p hκ hWdm (instrAngle spec k) ⊤
      have e : (fun X : DistOn upperHalfPlaneOpens => StagedDet.stageRec h12p hκ Wd (instrAngle spec k) ⊤
          (pastMap κ b jumps spec E k ω₀) X) = (fun q : PastData k × DistOn upperHalfPlaneOpens =>
            StagedDet.stageRec h12p hκ Wd (instrAngle spec k) ⊤ q.1 q.2) ∘
          (fun X : DistOn upperHalfPlaneOpens => (pastMap κ b jumps spec E k ω₀, X)) := rfl
      have hX : Measurable fun X : DistOn upperHalfPlaneOpens => StagedDet.stageRec h12p hκ Wd (instrAngle spec k) ⊤
          (pastMap κ b jumps spec E k ω₀) X := by
        rw [e]
        exact hsr.comp (measurable_const.prodMk measurable_id)
      exact (measurable_recPath t).comp hX
    · filter_upwards [hgood] with ω hω
      obtain ⟨-, -, hM, hrω⟩ := hω
      rw [piecePath_of_mem hM, hrω]
  · intro U hUH hKU
    filter_upwards [hgood] with ω hω
    obtain ⟨hr, hlω, hM, -⟩ := hω
    have hrg := hMreg ω hM
    obtain ⟨-, -, α, hα, -⟩ := id hrg
    have hstage : WalkLaw.stageSet κ b jumps spec E k ω = WalkLaw.stageSet κ b jumps spec E k ω₀ := by
      unfold WalkLaw.stageSet
      rw [hr]
    have hα' : IsGeneratingTrace (E k ω).1 (min (instrTime spec k) (E k ω).2) α := by
      rw [hT, min_top_left]
      exact hα
    rw [disjoint_pieceSet_iff spec E ω (hgoodR ω hM.2) hlω hUH (hstage ▸ hKU) hα', ← forall_frozen_notMem_iff,
      hT, min_top_left]
    simp only [piecePath_eq hM hrg hα]

end Main

/-! ### The two boundary walks -/

section Walks

/-- **Every ordinary instruction of a boundary walk has the walk's angle and an infinite instruction time.** -/
theorem boundaryWalkSpec_inl {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {k : ℕ} {θ' : ℝ} {t : ℝ≥0∞}
    (hk : (boundaryWalkSpec b jumps θ right).2.2[k]? = some (Sum.inl (θ', t))) : θ' = θ ∧ t = ⊤ := by
  have hmem := List.mem_of_getElem? hk
  simp only [boundaryWalkSpec, List.mem_flatten, List.mem_replicate] at hmem
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Sum.inl.injEq, Prod.mk.injEq] at hl
  exact hl

/-- **`WalkLaw.WalkStageLaunchLocalStatement θ right` from Theorems 1.2 (parametric) and 1.3**, for every angle in
`[−π/2, π/2]` (R48 allows them for Theorem 1.4). -/
theorem walkStageLaunchLocalStatement_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    WalkLaw.WalkStageLaunchLocalStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ _ k
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  exact launchLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh (hE _ hw) (hR _ hw) (hreg _) u₀ k
    fun _ _ h => boundaryWalkSpec_inl h

/-- The right walk (`θ = −π/2`): the leaf `WalkStageLaunchLocalStatement (−π/2) true`. -/
theorem walkStageLaunchLocalStatement_right_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : WalkLaw.WalkStageLaunchLocalStatement.{u} (-(Real.pi / 2)) true :=
  walkStageLaunchLocalStatement_of_thm12_thm13 h12p h13 ⟨le_rfl, by linarith [Real.pi_pos]⟩ true

/-- The left walk (`θ = π/2`): the leaf `WalkStageLaunchLocalStatement (π/2) false`. -/
theorem walkStageLaunchLocalStatement_left_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : WalkLaw.WalkStageLaunchLocalStatement.{u} (Real.pi / 2) false :=
  walkStageLaunchLocalStatement_of_thm12_thm13 h12p h13 ⟨by linarith [Real.pi_pos], le_rfl⟩ false

end Walks

end InteractingSLE.Theorem14.WalkLeaf
