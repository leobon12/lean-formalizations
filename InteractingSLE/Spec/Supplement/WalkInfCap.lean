/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLeafLaunch

/-!
# Theorem 1.4's walk leaves: a flow line stopped at a deterministic own time is marked local

Packet PROVE-T14-WALKINF. The capped analogue of `WalkLeaf.isHistoryAvoidanceLocalOff_of_chartFlow`: a flow line of a
chart field, **stopped at a deterministic own time `τ`**, read physically, is marked local off the old explored set for
the marks of its record stopped at `τ` (`recOf τ e`: the driver stopped at `min τ ζ`, the stop `min τ ζ` and the flag
`ζ ≤ τ`).

The flag `ζ ≤ τ` is not read from the trace stopped at `τ` (on `{ζ = τ}` that would need the threshold state at `τ`).
Instead the avoidance event with a record condition is split along `{ζ ≤ τ}`:

* on `{ζ ≤ τ}` the stopped piece **is** the whole piece and the stopped record **is** the full record, so the event is
  read from the entrance history of the whole trace (Aux. lemma 56 at every integer cap and the limit
  `StagedEntrance.measurable_entranceHist_of_frozen`), as in the uncapped lemma;
* on `{τ < ζ}` the stopped record is read from the trace frozen at `τ` (`capRead`: the driver code read from the
  dyadic trace values before `τ`, `capRead_pathCoord_frozen`), whose entrance history is again a function of the
  Markov complement (Aux. lemma 56 with the cap `τ`); the part `{ζ ≤ τ}` is removed by the first reading.

Main result: **`isHistoryAvoidanceLocalOff_of_chartFlow_cap`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open LocalSets Exist.Staged Exist.StagedLaw Sec6 Restart.StagedEntrance Sec2.Assembly Sec5.CrossRestart

/-! ### Frozen paths and capped times -/

/-- Freezing at a time `m` and at the lifetime commute with Lemma 6.2's capped time. -/
theorem frozen_capTime_nnreal (ζ : ℝ≥0∞) (m t : ℝ≥0) :
    (min ((min t m : ℝ≥0) : ℝ≥0∞) ζ).toNNReal =
      (min ((Restart.capTime m ζ t : ℝ≥0) : ℝ≥0∞) ζ).toNNReal := by
  induction ζ using ENNReal.recTopCoe with
  | top =>
    simp only [min_top_right, ENNReal.toNNReal_coe, Restart.capTime, min_top_left]
  | coe z =>
    have e : Restart.capTime m (z : ℝ≥0∞) t = min t (min z m) := by
      simp only [Restart.capTime]
      rw [← ENNReal.coe_min, ENNReal.toNNReal_coe]
    rw [e, ← ENNReal.coe_min, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rw [min_eq_left ((min_le_right _ _).trans (min_le_left _ _) : min t (min z m) ≤ z), min_assoc,
      min_comm m z]

/-! ### The stopped record read from the frozen trace -/

/-- **The record of a piece stopped at `τ`, read from the rational coordinates of its trace frozen at `τ`** (valid
when the lifetime exceeds `τ`): the driver code read from the dyadic trace values before `τ`, the stop `τ`, the flag
`false`. -/
def capRead (τ : ℝ≥0) (c : ℚ≥0 → ℂ) : RecData :=
  ((fun q : ℚ => drvPath (dInv (trCodeOf (WalkLeaf.ratExt c) τ)) (q : ℝ).toNNReal), (τ : ℝ≥0∞), false)

theorem measurable_capRead (τ : ℝ≥0) : Measurable (capRead τ) := by
  have hz : Measurable fun c : ℚ≥0 → ℂ => dInv (trCodeOf (WalkLeaf.ratExt c) τ) :=
    measurable_dInv.comp ((measurable_trCodeOf τ).comp WalkLeaf.measurable_ratExt)
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) (measurable_const.prodMk measurable_const)
  exact (measurable_pi_apply _).comp (measurable_drvPath.comp hz)

/-- The trace code at the horizon `τ` of a path frozen at `τ` is that of the path. -/
theorem trCodeOf_frozenPath (η : ℝ≥0 → ℂ) (τ : ℝ≥0) : trCodeOf (frozenPath η τ) τ = trCodeOf η τ := by
  refine Prod.ext rfl (funext fun n => funext fun k => ?_)
  change (if (dyad n k : ℝ≥0∞) < τ then frozenPath η τ (dyad n k) else 0) =
    (if (dyad n k : ℝ≥0∞) < τ then η (dyad n k) else 0)
  split_ifs with h
  · exact frozenPath_of_le (ENNReal.coe_le_coe.1 h.le)
  · rfl

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The stopped record is read from the frozen trace** when the lifetime exceeds `τ`. -/
theorem capRead_pathCoord_frozen (hwc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ ζ}) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w ζ η) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) :
    capRead τ (pathCoord (frozenPath η τ)) = recOf (τ : ℝ≥0∞) (w, ζ) := by
  have hητ : IsGeneratingTrace w (τ : ℝ≥0∞) η := isGeneratingTrace_of_eqOn_of_lt hη (fun _ _ => rfl) hτ
  have hwτ : ContinuousOn w {t | (t : ℝ≥0∞) < (τ : ℝ≥0∞)} :=
    hwc.mono fun t (ht : (t : ℝ≥0∞) < τ) => (le_of_lt (lt_trans ht hτ) : (t : ℝ≥0∞) ≤ ζ)
  have hwτ' : ContinuousOn w {t | (t : ℝ≥0∞) ≤ (τ : ℝ≥0∞)} :=
    hwc.mono fun t (ht : (t : ℝ≥0∞) ≤ τ) => (le_of_lt (lt_of_le_of_lt ht hτ) : (t : ℝ≥0∞) ≤ ζ)
  have htr : trCodeOf (WalkLeaf.ratExt (pathCoord (frozenPath η τ))) τ = dTrace (killCode w τ) := by
    rw [WalkLeaf.trCodeOf_ratExt, trCodeOf_frozenPath, dTrace_killCode hwτ hw0 hητ]
    rfl
  have hC : dInv (trCodeOf (WalkLeaf.ratExt (pathCoord (frozenPath η τ))) τ) = killCode w τ := by
    rw [htr, dInv_dTrace (killCode_mem_DSet hwτ hw0 hητ)]
  have hmin : min (τ : ℝ≥0∞) ζ = τ := min_eq_left hτ.le
  have hdec : decide (ζ ≤ (τ : ℝ≥0∞)) = false := decide_eq_false (not_le.2 hτ)
  change ((fun q : ℚ => drvPath (dInv (trCodeOf (WalkLeaf.ratExt (pathCoord (frozenPath η τ))) τ))
      (q : ℝ).toNNReal), (τ : ℝ≥0∞), false) =
    ((fun q : ℚ => w (min ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min (τ : ℝ≥0∞) ζ)).toNNReal), min (τ : ℝ≥0∞) ζ,
      decide (ζ ≤ (τ : ℝ≥0∞)))
  rw [hC, hmin, hdec]
  exact Prod.ext (funext fun q => WalkLeaf.drvPath_killCode hwτ' hw0 _) rfl

/-- At a lifetime `ζ ≤ τ` the stopped record is the full record. -/
theorem recOf_eq_top_of_le (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {τ : ℝ≥0∞} (hζ : e.2 ≤ τ) : recOf τ e = recOf ⊤ e := by
  have h1 : min τ e.2 = e.2 := min_eq_right hζ
  have h2 : min (⊤ : ℝ≥0∞) e.2 = e.2 := min_top_left _
  simp only [recOf, retOf, h1, h2, decide_eq_true hζ, le_top, decide_true]

/-- A continuous path never enters an open set exactly when its first entrance time is `⊤`. -/
theorem firstEntrance_eq_top_iff' {V : Set ℂ} (hV : IsOpen V) {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) :
    (histOf (pathCoord γ) (firstEntrance V (pathCoord γ))).1 = ⊤ ↔ ∀ t, γ t ∉ V :=
  WalkLeaf.firstEntrance_eq_top_iff hV hγ

/-! ### The capped flow line under one conditional law -/

section Kernel

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- **A flow line of a chart field stopped at a deterministic own time `τ`, read physically, is marked local off the
old explored set, for the marks of its stopped record.** Hypotheses as
`WalkLeaf.isHistoryAvoidanceLocalOff_of_chartFlow`
(`p` the trace frozen at the lifetime, determined by the chart field), except that `B` avoids an open `U ⊆ ℍ` off `K`
exactly when the trace **frozen at `τ`** avoids the chart pre-image of `U`; the marks are `σ(recOf τ e)`. -/
theorem isHistoryAvoidanceLocalOff_of_chartFlow_cap {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
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
    (τ : ℝ≥0) {B : Ω → Set ℂ}
    (hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → Disjoint K U →
      ∀ᵐ ω ∂ν, (Disjoint (B ω) U ↔ ∀ t, frozenPath (p ω) τ t ∉ Restart.MarkovChart.chartPre c₀ U)) :
    WalkLaw.IsHistoryAvoidanceLocalOff
      (MeasurableSpace.comap (fun ω => recOf (τ : ℝ≥0∞) (e ω)) inferInstance) K B
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
  -- Lemma 6.2 for the paths frozen at every time `m`
  have hcap : ∀ m : ℝ≥0, Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (X'' ω))
      inferInstance) ν] fun ω => histOf (pathCoord (frozenPath (p ω) m))
        (firstEntrance Vo (pathCoord (frozenPath (p ω) m))) := by
    intro m
    refine measurable_entranceHist_of_isFlowLine_capped hκ hκ4 hbp hgff hflp hu' m
      (ηc := fun ω => frozenPath (p ω) m) (fun ω => continuous_frozenPath (hpc ω)) (fun t => hpm _) ?_ ?_ ?_
      Vo (Restart.MarkovChart.chartPre_subset_H _ _) G' hG'm hd'
    · intro ω hH
      rw [frozenPath_zero, hp0] at hH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
    · filter_upwards [hpg] with ω hω t
      change p ω (min t m) = p ω (Restart.capTime m (e ω).2 t)
      rw [hω.2.2 (min t m), hω.2.2 (Restart.capTime m (e ω).2 t), frozen_capTime_nnreal]
    · intro t
      obtain ⟨f, hf, hfe⟩ := hdet (min t m)
      refine ⟨fun X => f (X + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u'),
        hf.comp (Coupling.measurable_add_distOnConst _), ?_⟩
      filter_upwards [hfe] with ω hω
      change p ω (min t m) = _
      rw [hω]
      simp only [WholeField.centredField, sub_add_cancel, hh'']
  have hHf := measurable_entranceHist_of_frozen hpc Vo.isOpen fun n => hcap (n : ℝ≥0)
  have hHc := hcap τ
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
  -- the event, read from the two entrance histories
  set xL := flowLineXL bc jc 0
  set xR := flowLineXR bc jc 0
  set ρL := flowLineRhoL κ bc jc 0 θ
  set ρR := flowLineRhoR κ bc jc 0 θ
  have hRm := WalkLeaf.measurable_readRec xL xR ρL ρR hκ
  set X1 : Set Hist := {x | x.1 = ⊤ ∧ WalkLeaf.readRec κ xL xR ρL ρR x.2 ∈ Bm ∧
    (WalkLeaf.readRec κ xL xR ρL ρR x.2).2.1 ≤ (τ : ℝ≥0∞)} with hX1
  set X2 : Set Hist := {x | x.1 = ⊤ ∧ capRead τ x.2 ∈ Bm} with hX2
  set X3 : Set Hist := {x | x.1 = ⊤ ∧ (WalkLeaf.readRec κ xL xR ρL ρR x.2).2.1 ≤ (τ : ℝ≥0∞) ∧
    capRead τ x.2 ∈ Bm} with hX3
  have hX1m : MeasurableSet X1 :=
    (measurable_fst (measurableSet_singleton ⊤)).inter ((hRm.comp measurable_snd hBm).inter
      (measurableSet_le ((measurable_fst.comp measurable_snd).comp (hRm.comp measurable_snd)) measurable_const))
  have hX2m : MeasurableSet X2 :=
    (measurable_fst (measurableSet_singleton ⊤)).inter ((measurable_capRead τ).comp measurable_snd hBm)
  have hX3m : MeasurableSet X3 :=
    (measurable_fst (measurableSet_singleton ⊤)).inter
      ((measurableSet_le ((measurable_fst.comp measurable_snd).comp (hRm.comp measurable_snd)) measurable_const).inter
        ((measurable_capRead τ).comp measurable_snd hBm))
  set Hf : Ω → Hist := fun ω => histOf (pathCoord (p ω)) (firstEntrance Vo (pathCoord (p ω))) with hHfdef
  set Hc : Ω → Hist := fun ω => histOf (pathCoord (frozenPath (p ω) τ))
    (firstEntrance Vo (pathCoord (frozenPath (p ω) τ))) with hHcdef
  have hS : ({ω | Disjoint (B ω) U} ∩ (fun ω => recOf (τ : ℝ≥0∞) (e ω)) ⁻¹' Bm : Set Ω) =ᵐ[ν]
      (Hf ⁻¹' X1 ∪ (Hc ⁻¹' X2 \ Hf ⁻¹' X3) : Set Ω) := by
    filter_upwards [hev U hUH hKU, hpg, hC.1.2.2.2.2] with ω hevω hg hpath
    have hrec : WalkLeaf.readRec κ xL xR ρL ρR (pathCoord (p ω)) = recOf ⊤ (e ω) :=
      WalkLeaf.readRec_pathCoord hκ hpath hg.1 hg.2.1
    have hlife : (recOf ⊤ (e ω)).2.1 = (e ω).2 := min_top_left _
    have hfe : (Hf ω).1 = ⊤ ↔ ∀ t, p ω t ∉ (Vo : Set ℂ) := firstEntrance_eq_top_iff' Vo.isOpen (hpc ω)
    have hfc : (Hc ω).1 = ⊤ ↔ ∀ t, frozenPath (p ω) τ t ∉ (Vo : Set ℂ) :=
      firstEntrance_eq_top_iff' Vo.isOpen (continuous_frozenPath (hpc ω))
    have hf2 : (Hf ω).1 = ⊤ → (Hf ω).2 = pathCoord (p ω) := fun h1 => by
      change stopCoord _ (Hf ω).1 = _
      rw [h1, WalkLeaf.stopCoord_top]
    have hc2 : (Hc ω).1 = ⊤ → (Hc ω).2 = pathCoord (frozenPath (p ω) τ) := fun h1 => by
      change stopCoord _ (Hc ω).1 = _
      rw [h1, WalkLeaf.stopCoord_top]
    apply propext
    change Disjoint (B ω) U ∧ recOf (τ : ℝ≥0∞) (e ω) ∈ Bm ↔
      Hf ω ∈ X1 ∨ (Hc ω ∈ X2 ∧ Hf ω ∉ X3)
    rw [hevω]
    rcases le_or_gt (e ω).2 (τ : ℝ≥0∞) with hζτ | hτζ
    · -- the piece dies before `τ`: the stopped piece is the whole piece
      have hfz : frozenPath (p ω) τ = p ω := funext fun t => by
        change p ω (min t τ) = p ω t
        rw [hg.2.2 (min t τ), hg.2.2 t]
        congr 2
        rw [ENNReal.coe_min, min_assoc, min_eq_right hζτ]
      have hrτ : recOf (τ : ℝ≥0∞) (e ω) = recOf ⊤ (e ω) := recOf_eq_top_of_le _ hζτ
      rw [hfz, hrτ]
      constructor
      · rintro ⟨hav, hB⟩
        have h1 : (Hf ω).1 = ⊤ := hfe.2 hav
        refine Or.inl ⟨h1, ?_, ?_⟩
        · rw [hf2 h1, hrec]; exact hB
        · rw [hf2 h1, hrec, hlife]; exact hζτ
      · rintro (⟨h1, hB, -⟩ | ⟨⟨h1, hB⟩, hn⟩)
        · rw [hf2 h1, hrec] at hB
          exact ⟨hfe.1 h1, hB⟩
        · exfalso
          have h1' : (Hf ω).1 = ⊤ := by
            rw [hfe]; rw [hfc, hfz] at h1; exact h1
          refine hn ⟨h1', ?_, ?_⟩
          · rw [hf2 h1', hrec, hlife]; exact hζτ
          · rw [hf2 h1']
            rw [hc2 h1, hfz] at hB
            exact hB
    · -- the piece lives past `τ`: the stopped record is read from the frozen trace
      have hcr : capRead τ (pathCoord (frozenPath (p ω) τ)) = recOf (τ : ℝ≥0∞) (e ω) :=
        capRead_pathCoord_frozen hg.2.1 hpath.1 hg.1 hτζ
      have hnX : ∀ x : Hist, x = Hf ω → x ∈ X1 ∨ x ∈ X3 → False := by
        rintro x rfl (⟨h1, -, hle⟩ | ⟨h1, hle, -⟩)
        · rw [hf2 h1, hrec, hlife] at hle; exact absurd hle (not_le.2 hτζ)
        · rw [hf2 h1, hrec, hlife] at hle; exact absurd hle (not_le.2 hτζ)
      constructor
      · rintro ⟨hav, hB⟩
        have h1 : (Hc ω).1 = ⊤ := hfc.2 hav
        refine Or.inr ⟨⟨h1, ?_⟩, fun h3 => hnX _ rfl (Or.inr h3)⟩
        rw [hc2 h1, hcr]
        exact hB
      · rintro (h1 | ⟨⟨h1, hB⟩, -⟩)
        · exact absurd (hnX _ rfl (Or.inl h1)) id
        · rw [hc2 h1, hcr] at hB
          exact ⟨hfc.1 h1, hB⟩
  have hRHS : MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (X'' ω)) inferInstance) ν]
      (Hf ⁻¹' X1 ∪ (Hc ⁻¹' X2 \ Hf ⁻¹' X3)) :=
    (hHf hX1m).union ((hHc hX2m).diff (hHf hX3m))
  obtain ⟨S', hS', hSS'⟩ := hRHS
  have hmem : MeasurableSet[aeSigma (MeasurableSpace.comap
      (fun ω => markovCompl G (WholeField.centredField h u₀ ω)) inferInstance) ν]
      ({ω | Disjoint (B ω) U} ∩ (fun ω => recOf (τ : ℝ≥0∞) (e ω)) ⁻¹' Bm) :=
    aeSigma_le_aeSigma hY'.comap_le _ ⟨S', hS', hS.trans hSS'⟩
  exact WalkLeaf.exists_condExp_eq_of_mem_aeSigma (WholeField.measurable_centredField hhm u₀) hG hmem

end Kernel

end InteractingSLE.Theorem14.WalkInf
