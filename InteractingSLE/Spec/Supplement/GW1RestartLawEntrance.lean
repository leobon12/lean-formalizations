/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLawKernel
import InteractingSLE.Spec.Restart.StagedEntranceStaged

/-!
# Reading capped entrance histories through terminal boundary values

The landed chart reader requires the chart path to stay in `ℍ` at every positive
time. A capped finite piece can instead be frozen at a real endpoint. Here a
measurable reader on its whole range suffices, provided entrance into the physical
test set agrees with entrance into the chart test set. Constructing that reader
for the actual terminal prime ends remains a separate geometric obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1RestartLaw

open Sec6 LocalSets Restart.StagedEntrance

/-- The old rational history followed by a Borel reading of the new history.
The explicit cutoff preserves the cemetery after the entrance time. -/
def readRestartHist (read : ℂ → ℂ) (q₀ : ℚ≥0) (a : ℚ≥0 → ℂ) (p : Hist) : Hist :=
  ((((q₀ : ℝ≥0) : ℝ≥0∞)) + p.1, fun q => if q ≤ q₀ then a q else
    if ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ p.1 then read (p.2 (q - q₀)) else 0)

theorem measurable_readRestartHist {read : ℂ → ℂ} (hm : Measurable read)
    (q₀ : ℚ≥0) (a : ℚ≥0 → ℂ) : Measurable (readRestartHist read q₀ a) := by
  have hcoord : ∀ q : ℚ≥0, Measurable fun p : Hist => (readRestartHist read q₀ a p).2 q := by
    intro q
    by_cases hq : q ≤ q₀
    · simp only [readRestartHist, hq, ↓reduceIte]
      exact measurable_const
    · simp only [readRestartHist, hq, ↓reduceIte]
      exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
        (hm.comp ((measurable_pi_apply _).comp measurable_snd)) measurable_const
  exact (measurable_const.add measurable_fst).prodMk (Measurable.of_eval hcoord)

/-- Boundary points of the new chart path are allowed. The only entrance
geometry used is the displayed equivalence, including the terminal value. -/
theorem histOf_eq_readRestartHist {α β a : ℝ≥0 → ℂ} {q₀ : ℚ≥0}
    {U V : Set ℂ} {read : ℂ → ℂ}
    (hpast : ∀ s ≤ (q₀ : ℝ≥0), α s = a s) (hpU : Disjoint (a '' Icc 0 q₀) U)
    (hβ0 : β 0 ∉ V)
    (hread : ∀ s, 0 < s → α ((q₀ : ℝ≥0) + s) = read (β s))
    (hpre : ∀ s, 0 < s → (read (β s) ∈ U ↔ β s ∈ V)) :
    histOf (pathCoord α) (firstEntrance U (pathCoord α)) =
      readRestartHist read q₀ (pathCoord a)
        (histOf (pathCoord β) (firstEntrance V (pathCoord β))) := by
  have hmem : ∀ q : ℚ≥0, α q ∈ U ↔ q₀ < q ∧ β ((q - q₀ : ℚ≥0) : ℝ≥0) ∈ V := by
    intro q
    by_cases hq : q ≤ q₀
    · have hαq := hpast (q : ℝ≥0) (by exact_mod_cast hq)
      exact ⟨fun hU => absurd hU (Set.disjoint_left.1 hpU
        ⟨q, ⟨zero_le, by exact_mod_cast hq⟩, hαq.symm⟩),
        fun h => absurd h.1 (not_lt.2 hq)⟩
    · have hlt := not_le.1 hq
      have hpos : (0 : ℝ≥0) < ((q - q₀ : ℚ≥0) : ℝ≥0) := by
        exact_mod_cast tsub_pos_of_lt hlt
      have he := hread _ hpos
      have hsum : (q₀ : ℝ≥0) + ((q - q₀ : ℚ≥0) : ℝ≥0) = (q : ℝ≥0) := by
        rw [← NNRat.cast_add, add_tsub_cancel_of_le hlt.le]
      rw [hsum] at he
      rw [he, hpre _ hpos]
      exact ⟨fun h => ⟨hlt, h⟩, And.right⟩
  have hmemβ : ∀ r : ℚ≥0, β r ∈ V → 0 < r := by
    intro r hr
    refine pos_iff_ne_zero.2 fun h0 => hβ0 ?_
    simpa only [h0, NNRat.cast_zero] using hr
  have hT : firstEntrance U (pathCoord α) =
      (((q₀ : ℝ≥0) : ℝ≥0∞)) + firstEntrance V (pathCoord β) := by
    refine le_antisymm ?_ ?_
    · rw [firstEntrance, firstEntrance, ENNReal.add_iInf]
      refine le_iInf fun r => ?_
      rw [ENNReal.add_iInf]
      refine le_iInf fun hr => ?_
      refine iInf₂_le (q₀ + r) ((hmem _).2 ⟨lt_add_of_pos_right _ (hmemβ r hr), ?_⟩) |>.trans ?_
      · rwa [add_tsub_cancel_left]
      · rw [NNRat.cast_add, ENNReal.coe_add]
    · refine le_iInf₂ fun q hq => ?_
      obtain ⟨hlt, hβq⟩ := (hmem q).1 hq
      rw [← coe_sub_add hlt.le]
      exact add_le_add_right (firstEntrance_le (c := pathCoord β) (q := q - q₀) hβq) _
  unfold histOf readRestartHist
  refine Prod.ext hT ?_
  funext q
  dsimp only
  by_cases hq : q ≤ q₀
  · simp only [hq, ↓reduceIte]
    have hle : (((q : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance U (pathCoord α) := by
      rw [hT]
      exact (ENNReal.coe_le_coe.2 (by exact_mod_cast hq)).trans le_self_add
    rw [stopCoord_of_le hle]
    exact hpast _ (by exact_mod_cast hq)
  · simp only [hq, ↓reduceIte]
    have hlt := not_le.1 hq
    have hiff : (((q : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance U (pathCoord α) ↔
        ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance V (pathCoord β) := by
      rw [hT, ← coe_sub_add hlt.le]
      exact ENNReal.add_le_add_iff_left ENNReal.coe_ne_top
    unfold stopCoord
    by_cases hle : ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance V (pathCoord β)
    · simp only [hiff.2 hle, hle, ↓reduceIte]
      have hpos : (0 : ℝ≥0) < ((q - q₀ : ℚ≥0) : ℝ≥0) := by
        exact_mod_cast tsub_pos_of_lt hlt
      have he := hread _ hpos
      have hsum : (q₀ : ℝ≥0) + ((q - q₀ : ℚ≥0) : ℝ≥0) = (q : ℝ≥0) := by
        rw [← NNRat.cast_add, add_tsub_cancel_of_le hlt.le]
      rw [hsum] at he
      exact he
    · have h1 : ¬ (((q : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance U (pathCoord α) :=
        fun h => hle (hiff.1 h)
      simp only [h1, hle, ↓reduceIte]

/-- A Borel boundary reader transports the entire stopped rational history,
including a capped real terminal endpoint, under any retained conditional law. -/
theorem measurable_entranceHist_restart_of_read
    {Ω : Type*} {m𝓗 : MeasurableSpace Ω} [MeasurableSpace Ω] {ν : Measure Ω}
    {α β : Ω → ℝ≥0 → ℂ} {a : ℝ≥0 → ℂ} {q₀ : ℚ≥0} {U V : Set ℂ}
    {read : ℂ → ℂ} (hm : Measurable read) (hpU : Disjoint (a '' Icc 0 q₀) U)
    (hgood : ∀ᵐ ω ∂ν, (∀ s ≤ (q₀ : ℝ≥0), α ω s = a s) ∧ β ω 0 ∉ V ∧
      (∀ s, 0 < s → α ω ((q₀ : ℝ≥0) + s) = read (β ω s)) ∧
      ∀ s, 0 < s → (read (β ω s) ∈ U ↔ β ω s ∈ V))
    (hβ : Measurable[aeSigma m𝓗 ν] fun ω =>
      histOf (pathCoord (β ω)) (firstEntrance V (pathCoord (β ω)))) :
    Measurable[aeSigma m𝓗 ν] fun ω =>
      histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) := by
  have heq : ∀ᵐ ω ∂ν, histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) =
      readRestartHist read q₀ (pathCoord a)
        (histOf (pathCoord (β ω)) (firstEntrance V (pathCoord (β ω)))) :=
    hgood.mono fun ω hω => histOf_eq_readRestartHist hω.1 hpU hω.2.1 hω.2.2.1 hω.2.2.2
  intro B hB
  obtain ⟨S', hS', hSS'⟩ := ((measurable_readRestartHist hm q₀ (pathCoord a)).comp hβ) hB
  refine ⟨S', hS', EventuallyEq.trans ?_ hSS'⟩
  filter_upwards [heq] with ω hω
  simp only [mem_preimage, Function.comp_apply, hω]

/-- The staged continuation criterion for a capped ordinary flow, allowing its
terminal value on the boundary. The Borel boundary reading and the entrance
equivalence are explicit geometric hypotheses; no infinite own lifetime or
strictly interior terminal point is imposed. -/
theorem restartCont_of_isFlowLine_capped_of_read
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData ν h b jumps)
    {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b jumps 0 θ ν h β ζ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0)
    {ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω))
    (hηm : ∀ t, Measurable fun ω => ηc ω t) (hη0 : ∀ ω, ηc ω 0 ∉ H)
    (hηβ : ∀ᵐ ω ∂ν, ∀ t, ηc ω t = β ω (Restart.capTime m (ζ ω) t))
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[ν] fun ω => f (WholeField.centredField h u₀ ω))
    {c : Chart} (hc : c.IsConformal) {read : ℂ → ℂ} (hm : Measurable read)
    {α : Ω → ℝ≥0 → ℂ} {a : ℝ≥0 → ℂ} {q₀ : ℚ≥0}
    (U : Opens ℂ) (hpU : Disjoint (a '' Icc 0 q₀) U)
    (hgood : ∀ᵐ ω ∂ν, (∀ s ≤ (q₀ : ℝ≥0), α ω s = a s) ∧
      (∀ s, 0 < s → α ω ((q₀ : ℝ≥0) + s) = read (ηc ω s)) ∧
      ∀ s, 0 < s → (read (ηc ω s) ∈ U ↔ ηc ω s ∈ Restart.MarkovChart.chartPre c U))
    (G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hG' : Measurable G')
    (hd' : GFF.IsMarkovDecomposition (Restart.MarkovChart.chartPreOpens hc U)
      upperHalfPlaneOpens (WholeField.centredField h u₀)
        (fun ω => G' (WholeField.centredField h u₀ ω)) ν) :
    Measurable[aeSigma (MeasurableSpace.comap
      (fun ω => LocalSets.markovCompl G' (WholeField.centredField h u₀ ω)) inferInstance) ν]
        fun ω => histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) := by
  refine measurable_entranceHist_restart_of_read hm hpU
    (hgood.mono fun ω hω => ⟨hω.1, fun hz => hη0 ω hz.1, hω.2⟩) ?_
  exact measurable_entranceHist_of_isFlowLine_capped hκ hκ4 hb hh hfl hu₀ m hηc hηm
    hη0 hηβ hdet (Restart.MarkovChart.chartPreOpens hc U)
      (Restart.MarkovChart.chartPre_subset_H c U) G' hG' hd'

/-- The missing geometric input for reading a completed ordinary piece:
a Borel extension of the own-chart inverse whose finite boundary values lie
on the retained old range or outside `ℍ`. No existence is asserted here. -/
def IsTerminalChartReader (c : Chart) (A : Set ℂ) (read : ℂ → ℂ) : Prop :=
  Measurable read ∧ EqOn read c.2.1 H ∧
    ∀ z ∈ closure H, z ∉ H → read z ∈ A ∨ read z ∉ H

/-- A terminal boundary reader only needs to send boundary values to the old
history or to the original real boundary, hence outside a test set avoided by
that history. On `ℍ` it is the chart inverse. This discharges the entrance
equivalence in the capped continuation criterion. -/
theorem terminalRead_mem_iff_chartPre {c : Chart} {read : ℂ → ℂ} {U : Set ℂ}
    (hint : EqOn read c.2.1 H) {z : ℂ} (hboundary : z ∉ H → read z ∉ U) :
    read z ∈ U ↔ z ∈ Restart.MarkovChart.chartPre c U := by
  by_cases hz : z ∈ H
  · change read z ∈ U ↔ z ∈ H ∧ c.2.1 z ∈ U
    rw [hint hz]
    exact ⟨fun h => ⟨hz, h⟩, And.right⟩
  · exact ⟨fun h => (hboundary hz h).elim, fun h => (hz h.1).elim⟩

/-- A test set in `ℍ` avoided by the older retained range sees exactly the
chart pre-image under a terminal reader, including at finite boundary values. -/
theorem terminalRead_mem_iff_chartPre_of_reader {c : Chart} {A U : Set ℂ}
    {read : ℂ → ℂ} (hr : IsTerminalChartReader c A read)
    (hUH : U ⊆ H) (hAU : Disjoint A U) {z : ℂ} (hz : z ∈ closure H) :
    read z ∈ U ↔ z ∈ Restart.MarkovChart.chartPre c U := by
  apply terminalRead_mem_iff_chartPre hr.2.1
  intro hzH hzU
  rcases hr.2.2 z hz hzH with hA | hH
  · exact Set.disjoint_left.1 hAU hA hzU
  · exact hH (hUH hzU)

end InteractingSLE.Theorem14.GW1RestartLaw
