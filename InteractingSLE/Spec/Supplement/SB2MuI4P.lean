/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuI4

/-!
# (I4) at the code level, probabilistic part: the canonical flow line has no threshold before its lifetime

Packet PROVE-SB2-LCMEAN, round 13 (handoff §R13.4). Given a sub-σ-algebra `𝒢` and a `𝒢`-measurable word `c` such that,
on a `𝒢`-event `G`, the chart field `Y` is conditionally a GFF with the data of `c`, the canonical driver code of
`(c, Y)` drives an integrated path under the conditional law (Theorems 1.2–1.3). Read with the type's geometric force
points, it has no threshold before its lifetime. To pass from the conditional law to `P` with measurable events, the
statement is made for the canonical driver frozen at a fixed time `q`:

* `frozenCanon`: the canonical driver of `(c, Y)` frozen at `q` when `q` is below its lifetime, `0` otherwise
  (continuous at every sample);
* **`ae_lt_thr_frozenCanon`**: almost surely on every type cell of `c`, if `q` is below the canonical lifetime then
  the geometric threshold time of the type under the frozen canonical driver is after `q`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Lv Supp8.Q3Stop

/-- **The canonical driver of `(c, Y)` frozen at `q`**, when `q` is below its lifetime (and `0` otherwise). -/
def frozenCanon (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ) {Ω : Type*}
    (c : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (q : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if (q : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 then
    (driverOf h12p hκ ψ (c ω, Y ω)).1 (min t q) else 0

theorem continuous_frozenCanon (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ) {Ω : Type*}
    (c : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (q : ℝ≥0) (ω : Ω) :
    Continuous fun t => frozenCanon h12p hκ ψ c Y q t ω := by
  unfold frozenCanon
  by_cases hq : (q : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2
  · simp only [hq, ↓reduceIte]
    have hreg := (drvOf_regular (detCode (paramΦ h12p hκ (flowLineNL (c ω).fn (c ω).jumps 0)
      (flowLineNR (c ω).fn (c ω).jumps 0)) (((flowLineXL (c ω).fn (c ω).jumps 0,
        flowLineXR (c ω).fn (c ω).jumps 0), (flowLineRhoL κ (c ω).fn (c ω).jumps 0 ψ,
          flowLineRhoR κ (c ω).fn (c ω).jumps 0 ψ)), Exist.flowField 0 (ψ * QuantumZipper.chiC κ) (Y ω)))).1
    rw [← driverOf_mk] at hreg
    have hcI : ContinuousOn (driverOf h12p hκ ψ (c ω, Y ω)).1 (Iic q) := hreg.mono fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (mem_Iic.1 ht)) hq
    exact hcI.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right t q)
  · simp only [hq, ↓reduceIte]
    exact continuous_const

theorem measurable_frozenCanon (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] {c : Ω → BoundaryWord} (hc : Measurable c) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) (q : ℝ≥0) (t : ℝ≥0) : Measurable (frozenCanon h12p hκ ψ c Y q t) := by
  have hD : Measurable fun ω => driverOf h12p hκ ψ (c ω, Y ω) :=
    (measurable_driverOf h12p hκ ψ).comp (hc.prodMk hY)
  have hL : Measurable fun ω => (driverOf h12p hκ ψ (c ω, Y ω)).2 := measurable_snd.comp hD
  have hW : Measurable fun ω => (driverOf h12p hκ ψ (c ω, Y ω)).1 (min t q) :=
    (measurable_pi_apply _).comp (measurable_fst.comp hD)
  exact Measurable.ite (measurableSet_lt measurable_const hL) hW measurable_const

/-- **The canonical flow line has no threshold before its lifetime, frozen at `q`**: on every type cell of the word,
if `q` is below the canonical lifetime, the geometric threshold time of the type under the canonical driver frozen at
`q` is after `q`. -/
theorem ae_lt_thr_frozenCanon (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ) {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {G : Set Ω}
    (hG : MeasurableSet[𝒢] G) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y (c ω₀).fn (c ω₀).jumps)
    (w : WordType) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c G w → (q : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 →
      (q : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y q)
        (cellXL κ ψ c w) (cellXR κ ψ c w) ω := by
  have hcm : Measurable c := hc.mono h𝒢 le_rfl
  have hcell : MeasurableSet[𝒢] (wordTypeCell κ ψ c G w) :=
    @measurableSet_wordTypeCell Ω 𝒢 κ ψ c G hc hG w
  have hD : Measurable fun ω => driverOf h12p hκ ψ (c ω, Y ω) :=
    (measurable_driverOf h12p hκ ψ).comp (hcm.prodMk hY)
  have hL : Measurable fun ω => (driverOf h12p hκ ψ (c ω, Y ω)).2 := measurable_snd.comp hD
  have hthr : Measurable (FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y q)
      (cellXL κ ψ c w) (cellXR κ ψ c w)) :=
    FCDet.measurable_thr (𝓗 := Filtration.const ℝ≥0 mΩ le_rfl) (continuous_frozenCanon h12p hκ ψ c Y q)
      (fun t => (measurable_frozenCanon h12p hκ ψ hcm hY q t).stronglyMeasurable)
      (measurable_cellXL hcm w) (measurable_cellXR hcm w)
  set E : Set Ω := {ω | ω ∈ wordTypeCell κ ψ c G w → (q : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 →
      (q : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y q)
        (cellXL κ ψ c w) (cellXR κ ψ c w) ω} with hEdef
  have hE : MeasurableSet E :=
    ((h𝒢 _ hcell).compl.union ((measurableSet_lt measurable_const hL).compl.union
      (measurableSet_lt measurable_const hthr))).congr (by
        ext ω
        simp only [hEdef, mem_union, mem_compl_iff, mem_ofPred_eq]
        tauto)
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hE ?_
  filter_upwards [hlaw, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hc,
    Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) h𝒢 hcell] with ω₀ hl hceq hind
  by_cases h₀ : ω₀ ∈ wordTypeCell κ ψ c G w
  · have hgff := hl h₀.1
    -- the canonical driver of the fixed word under the conditional law drives an integrated path
    have hD₀ : Measurable fun ω => driverOf h12p hκ ψ (c ω₀, Y ω) :=
      (measurable_driverOf h12p hκ ψ).comp (measurable_const.prodMk hY)
    have hfl : IsFlowLineDriver κ (c ω₀).fn (c ω₀).jumps ψ (condExpKernel P 𝒢 ω₀) Y
        (fun t ω => (driverOf h12p hκ ψ (c ω₀, Y ω)).1 t) (fun ω => (driverOf h12p hκ ψ (c ω₀, Y ω)).2) := by
      refine Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ ψ h13 (c ω₀) hgff
        (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD₀)) (measurable_snd.comp hD₀)
        (fun ω => ?_) (Eventually.of_forall fun ω => ?_)
      · rw [driverOf_mk]
        exact (drvOf_regular _).1
      · refine ⟨rfl, ?_, fun n k _ => rfl⟩
        show (driverOf h12p hκ ψ (c ω₀, Y ω)).1 0 = (driverOf h12p hκ ψ (c ω₀, Y ω)).1 (dyad 0 0)
        rw [Exist.dyad_zero_zero]
    obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
    have hpath := hC.1.2.2.2.2
    obtain ⟨hnL, hnR, hw⟩ := k2_word_of_mem_wordTypeCell h₀
    filter_upwards [hpath, hceq] with ω hp hcω hω hq
    have hcω' : c ω = c ω₀ := hcω
    obtain ⟨vL', vR', hp'⟩ := exists_isIntegratedSLEPath_of_truncWord hnL hnR hw hp
    have hxL : cellXL κ ψ c w ω = FCDet.typeXL κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (c ω₀) := by
      simp only [cellXL, hcω']
    have hxR : cellXR κ ψ c w ω = FCDet.typeXR κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (c ω₀) := by
      simp only [cellXR, hcω']
    have hq' : (q : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω₀, Y ω)).2 := by rw [← hcω']; exact hq
    refine lt_thr_of_isIntegratedSLEPath hp' (continuous_frozenCanon h12p hκ ψ c Y q) hxL hxR hq' fun t ht => ?_
    simp only [frozenCanon, hcω', hq', ↓reduceIte, min_eq_left ht]
  · have h0 : condExpKernel P 𝒢 ω₀ (wordTypeCell κ ψ c G w) = 0 := by rw [hind, indicator_of_notMem h₀]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω hmem
    exact absurd hmem hω

end InteractingSLE.Theorem14.SB.Mu
