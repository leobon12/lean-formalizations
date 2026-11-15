/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntrance
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# The continuation hypothesis of the restart gluing from a flow line in the chart

Packet PROVE-STAGEDLOC, items (2)–(4). `StagedEntrance.isEntranceHistoryLocal_of_restart` asks, under the regular
conditional law `ν` given the past, that the entrance history of the restarted path `α` into an open `U` avoided by
the past be determined by the Markov complement of the chart field along `inv⁻¹ U` (`hcont`). This file derives it
from the usual data of a continuation that is a flow line in the chart:

* **`measurable_entranceHist_of_frozen`**: the entrance history of a continuous path is the pointwise limit of the
  entrance histories of the paths frozen after `n` (eventually constant in every coordinate), so measurability for
  any σ-algebra passes to it;
* **`measurable_entranceHist_of_isFlowLine`**: for a flow line with infinite lifetime whose coordinates are
  determined by the field, Aux. lemma 56 at first entrance times (`WholeField.retainedRangeEntranceStatement`, applied
  to the frozen paths) and Lemma 6.2's determination (`Sec6.measurable_entranceHist`) make its entrance history into
  `U` almost surely a function of the Markov complement `h_{U^c}` — under any probability measure, in particular under
  a regular conditional law;
* **`measurable_entranceHist_restart`**: if, after the rational restart time `q₀`, the path is `α(q₀ + s) = inv(β(s))`
  for a chart path `β` staying in `ℍ` for `s > 0`, and the past is fixed and avoids `U`, the entrance history of `α`
  into `U` is a measurable function of the entrance history of `β` into `inv⁻¹ U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn measurable_distOn_apply)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

open Sec6 LocalSets

/-! ### Entrance histories as limits of frozen ones -/

section Limit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **The entrance history of a continuous path is the limit of the entrance histories of its frozen paths**, so it
is measurable (for any σ-algebra) as soon as they are. -/
theorem measurable_entranceHist_of_frozen {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ ω, Continuous (γ ω)) {U : Set ℂ}
    (hU : IsOpen U) (hcap : ∀ n : ℕ, Measurable[m] fun ω =>
      histOf (pathCoord (frozenPath (γ ω) n)) (firstEntrance U (pathCoord (frozenPath (γ ω) n)))) :
    Measurable[m] fun ω => histOf (pathCoord (γ ω)) (firstEntrance U (pathCoord (γ ω))) := by
  refine measurable_of_tendsto_metrizable hcap (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hU' : ∃ s, γ ω s ∈ U
  · obtain ⟨s, hs⟩ := hU'
    obtain ⟨N, hN⟩ := exists_nat_ge (s : ℝ≥0)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    refine histOf_frozenPath_eq hU (hγ ω) fun hd => Set.disjoint_left.1 hd ⟨s, ⟨zero_le, ?_⟩, rfl⟩ hs
    exact hN.trans (Nat.cast_le.2 hn)
  · push Not at hU'
    have htop : ∀ n : ℕ, firstEntrance U (pathCoord (frozenPath (γ ω) n)) = ⊤ := fun n =>
      (firstEntrance_frozenPath_eq_top_iff hU (hγ ω)).2
        (Set.disjoint_left.2 fun z hz hzU => by obtain ⟨s, -, rfl⟩ := hz; exact hU' s hzU)
    have htop' : firstEntrance U (pathCoord (γ ω)) = ⊤ := iInf₂_eq_top.2 fun q hq => absurd hq (hU' q)
    simp only [htop, htop']
    unfold histOf
    refine tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.2 fun q => ?_)
    obtain ⟨N, hN⟩ := exists_nat_ge ((q : ℝ≥0))
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    simp only [stopCoord, le_top, ite_true, pathCoord]
    exact frozenPath_of_le (hN.trans (Nat.cast_le.2 hn))

end Limit

/-! ### Flow lines with infinite lifetime -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}
  [IsProbabilityMeasure ν]

/-- **The entrance history of a capped flow line is a function of the Markov complement** (Aux. lemma 56 at first
entrance times and Lemma 6.2's determination), for any continuous version `ηc` of the flow line frozen at
`min(m, ζ)` whose coordinates are determined by the centred field; under any probability measure. This is the form
used for the later pieces of a staged history (finite horizons and lifetimes). -/
theorem measurable_entranceHist_of_isFlowLine_capped (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData ν h b jumps) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b jumps 0 θ ν h β ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0)
    {ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω)) (hηm : ∀ t, Measurable fun ω => ηc ω t)
    (hη0 : ∀ ω, ηc ω 0 ∉ H) (hηβ : ∀ᵐ ω ∂ν, ∀ t, ηc ω t = β ω (capTime m (ζ ω) t))
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[ν] fun ω => f (WholeField.centredField h u₀ ω))
    (U : Opens ℂ) (hUH : (U : Set ℂ) ⊆ H) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (WholeField.centredField h u₀)
      (fun ω => G (WholeField.centredField h u₀ ω)) ν) :
    Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (WholeField.centredField h u₀ ω))
      inferInstance) ν] (fun ω => histOf (pathCoord (ηc ω)) (firstEntrance U (pathCoord (ηc ω)))) := by
  have hloc := (WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb 0 θ ν h hh β ζ hfl u₀ hu₀ m
    ηc hηc hηm hηβ).isEntranceHistoryLocal
  exact measurable_entranceHist (WholeField.measurable_centredField hh.1 u₀) hηc hηm hdet hloc U G hUH hG hd
    fun ω hU => hη0 ω (hUH hU)

/-- **The entrance history of a field-determined flow line with infinite lifetime is a function of the Markov
complement** (Aux. lemma 56 at first entrance times for the frozen paths, Lemma 6.2's determination, and the limit
`measurable_entranceHist_of_frozen`). Stated for any probability measure `ν`, e.g. a regular conditional law. -/
theorem measurable_entranceHist_of_isFlowLine (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData ν h b jumps) {β : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b jumps 0 θ ν h β ζ) (hζ : ∀ᵐ ω ∂ν, ζ ω = ⊤) (hβc : ∀ ω, Continuous (β ω))
    (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[ν] fun ω => f (WholeField.centredField h u₀ ω))
    (U : Opens ℂ) (hUH : (U : Set ℂ) ⊆ H) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (WholeField.centredField h u₀)
      (fun ω => G (WholeField.centredField h u₀ ω)) ν) :
    Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (WholeField.centredField h u₀ ω))
      inferInstance) ν] (fun ω => histOf (pathCoord (β ω)) (firstEntrance U (pathCoord (β ω)))) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  have h0U : ∀ ω, β ω 0 ∉ (U : Set ℂ) := fun ω hU => by
    have h0 : (0 : ℝ) < (β ω 0).im := hUH hU
    rw [hβ0, Complex.zero_im] at h0
    exact lt_irrefl _ h0
  refine measurable_entranceHist_of_frozen hβc U.isOpen fun n => ?_
  have hcap : ∀ᵐ ω ∂ν, ∀ t, frozenPath (β ω) n t = β ω (capTime (n : ℝ≥0) (ζ ω) t) := by
    filter_upwards [hζ] with ω hω t
    simp only [frozenPath, capTime, hω, min_eq_right le_top, ENNReal.toNNReal_coe]
  have hloc := (WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb 0 θ ν h hh β ζ hfl u₀ hu₀ n
    (fun ω => frozenPath (β ω) n) (fun ω => continuous_frozenPath (hβc ω)) (fun t => hβm _)
    hcap).isEntranceHistoryLocal
  refine measurable_entranceHist hhm (fun ω => continuous_frozenPath (hβc ω)) (fun t => hβm _) (fun t => ?_) hloc
    U G hUH hG hd fun ω => by rw [frozenPath_zero]; exact h0U ω
  exact hdet _

end Flow

/-! ### The restarted path read off the chart path -/

section Read

variable {c : Chart}

open Classical in
/-- `inv` on `ℍ`, `0` elsewhere (a Borel version of the chart inverse). -/
def invH (c : Chart) : ℂ → ℂ := H.piecewise c.2.1 fun _ => 0

open Classical in
theorem invH_of_mem {z : ℂ} (hz : z ∈ H) : invH c z = c.2.1 z := Set.piecewise_eq_of_mem _ _ _ hz

open Classical in
theorem measurable_invH (hc : c.IsConformal) : Measurable (invH c) :=
  hc.1.continuousOn.measurable_piecewise continuousOn_const QuantumZipper.isOpen_H.measurableSet

/-- **The entrance history of the restarted path** from the entrance history `p` of the chart path: the frozen past
`a` up to `q₀`, then `inv` of the chart path shifted by `q₀`, the entrance time shifted by `q₀`. -/
def restartHist (q₀ : ℚ≥0) (a : ℚ≥0 → ℂ) (c : Chart) (p : Hist) : Hist :=
  ((((q₀ : ℝ≥0) : ℝ≥0∞)) + p.1, fun q => if q ≤ q₀ then a q else
    if ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ p.1 then invH c (p.2 (q - q₀)) else 0)

theorem measurable_restartHist (hc : c.IsConformal) (q₀ : ℚ≥0) (a : ℚ≥0 → ℂ) :
    Measurable (restartHist q₀ a c) := by
  have hcoord : ∀ q : ℚ≥0, Measurable fun p : Hist => (restartHist q₀ a c p).2 q := fun q => by
    by_cases hq : q ≤ q₀
    · simp only [restartHist, hq, ↓reduceIte]
      exact measurable_const
    · simp only [restartHist, hq, ↓reduceIte]
      exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
        ((measurable_invH hc).comp ((measurable_pi_apply _).comp measurable_snd)) measurable_const
  exact (measurable_const.add measurable_fst).prodMk (Measurable.of_eval hcoord)

theorem coe_sub_add {q₀ q : ℚ≥0} (h : q₀ ≤ q) :
    ((((q₀ : ℝ≥0) : ℝ≥0∞)) + ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞))) = (((q : ℝ≥0) : ℝ≥0∞)) := by
  rw [← ENNReal.coe_add, ← NNRat.cast_add, add_tsub_cancel_of_le h]

/-- **The restarted path's entrance history** (deterministic): if `α = a` up to `q₀`, `a` avoids `U` there, the chart
path `β` starts off `ℍ`, stays in `ℍ` afterwards and `α(q₀ + s) = inv(β(s))` for `s > 0`, then the entrance history of
`α` into `U` is `restartHist` of the entrance history of `β` into the chart pre-image of `U`. -/
theorem histOf_eq_restartHist {α β a : ℝ≥0 → ℂ} {q₀ : ℚ≥0} {U : Set ℂ}
    (hpast : ∀ s ≤ (q₀ : ℝ≥0), α s = a s) (hpU : Disjoint (a '' Icc 0 q₀) U) (hβ0 : β 0 ∉ H)
    (hβ : ∀ s, 0 < s → β s ∈ H ∧ α ((q₀ : ℝ≥0) + s) = c.2.1 (β s)) :
    histOf (pathCoord α) (firstEntrance U (pathCoord α)) =
      restartHist q₀ (pathCoord a) c
        (histOf (pathCoord β) (firstEntrance (MarkovChart.chartPre c U) (pathCoord β))) := by
  -- membership of rational times
  have hmem : ∀ q : ℚ≥0, α q ∈ U ↔ q₀ < q ∧ β ((q - q₀ : ℚ≥0) : ℝ≥0) ∈ MarkovChart.chartPre c U := by
    intro q
    by_cases hq : q ≤ q₀
    · have hαq : α q = a q := hpast _ (by exact_mod_cast hq)
      refine ⟨fun hU => absurd hU (Set.disjoint_left.1 hpU ⟨q, ⟨zero_le, by exact_mod_cast hq⟩, hαq.symm⟩),
        fun h => absurd h.1 (not_lt.2 hq)⟩
    · have hlt : q₀ < q := not_le.1 hq
      have hpos : (0 : ℝ≥0) < ((q - q₀ : ℚ≥0) : ℝ≥0) := by exact_mod_cast tsub_pos_of_lt hlt
      obtain ⟨hH, he⟩ := hβ _ hpos
      have hq' : ((q₀ : ℝ≥0)) + ((q - q₀ : ℚ≥0) : ℝ≥0) = (q : ℝ≥0) := by
        rw [← NNRat.cast_add, add_tsub_cancel_of_le hlt.le]
      rw [hq'] at he
      rw [he]
      exact ⟨fun hU => ⟨hlt, hH, hU⟩, fun h => h.2.2⟩
  have hmemβ : ∀ r : ℚ≥0, β r ∈ MarkovChart.chartPre c U → 0 < r := by
    intro r hr
    refine pos_iff_ne_zero.2 fun h0 => hβ0 ?_
    have : ((r : ℝ≥0)) = 0 := by rw [h0, NNRat.cast_zero]
    rw [← this]
    exact hr.1
  have hT : firstEntrance U (pathCoord α) =
      (((q₀ : ℝ≥0) : ℝ≥0∞)) + firstEntrance (MarkovChart.chartPre c U) (pathCoord β) := by
    refine le_antisymm ?_ ?_
    · rw [firstEntrance, firstEntrance, ENNReal.add_iInf]
      refine le_iInf fun r => ?_
      rw [ENNReal.add_iInf]
      refine le_iInf fun hr => ?_
      have hr0 := hmemβ r hr
      refine iInf₂_le (q₀ + r) ((hmem _).2 ⟨lt_add_of_pos_right _ hr0, ?_⟩) |>.trans ?_
      · rwa [add_tsub_cancel_left]
      · rw [NNRat.cast_add, ENNReal.coe_add]
    · refine le_iInf₂ fun q hq => ?_
      obtain ⟨hlt, hβq⟩ := (hmem q).1 hq
      rw [← coe_sub_add hlt.le]
      exact add_le_add_right (firstEntrance_le (c := pathCoord β) (q := q - q₀) hβq) _
  unfold histOf restartHist
  refine Prod.ext ?_ ?_
  · exact hT
  · funext q
    dsimp only
    by_cases hq : q ≤ q₀
    · simp only [hq, ↓reduceIte]
      have hle : ((((q : ℝ≥0) : ℝ≥0∞))) ≤ firstEntrance U (pathCoord α) := by
        rw [hT]
        exact (ENNReal.coe_le_coe.2 (by exact_mod_cast hq)).trans le_self_add
      rw [stopCoord_of_le hle]
      exact hpast _ (by exact_mod_cast hq)
    · simp only [hq, ↓reduceIte]
      have hlt : q₀ < q := not_le.1 hq
      have hiff : ((((q : ℝ≥0) : ℝ≥0∞))) ≤ firstEntrance U (pathCoord α) ↔
          ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance (MarkovChart.chartPre c U) (pathCoord β) := by
        rw [hT, ← coe_sub_add hlt.le]
        exact ENNReal.add_le_add_iff_left ENNReal.coe_ne_top
      unfold stopCoord
      by_cases hle : ((((q - q₀ : ℚ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance (MarkovChart.chartPre c U) (pathCoord β)
      · have h1 := hiff.2 hle
        simp only [h1, hle, ↓reduceIte]
        have hpos : (0 : ℝ≥0) < ((q - q₀ : ℚ≥0) : ℝ≥0) := by exact_mod_cast tsub_pos_of_lt hlt
        obtain ⟨hH, he⟩ := hβ _ hpos
        have hq' : ((q₀ : ℝ≥0)) + ((q - q₀ : ℚ≥0) : ℝ≥0) = (q : ℝ≥0) := by
          rw [← NNRat.cast_add, add_tsub_cancel_of_le hlt.le]
        rw [hq'] at he
        change α q = invH c (β ((q - q₀ : ℚ≥0) : ℝ≥0))
        rw [invH_of_mem hH, he]
      · have h1 : ¬ ((((q : ℝ≥0) : ℝ≥0∞))) ≤ firstEntrance U (pathCoord α) := fun h => hle (hiff.1 h)
        simp only [h1, hle, ↓reduceIte]

end Read

/-! ### The continuation hypothesis from a flow line in the chart -/

section Cont

variable {Ω : Type*} {m𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}

/-- **The restarted path's entrance history is determined as soon as the chart path's is** (for any σ-algebra
`m𝓗`, up to `ν`-null sets). -/
theorem measurable_entranceHist_restart {c : Chart} (hc : c.IsConformal) {α β : Ω → ℝ≥0 → ℂ} {a : ℝ≥0 → ℂ}
    {q₀ : ℚ≥0} {U : Set ℂ} (hpU : Disjoint (a '' Icc 0 q₀) U)
    (hgood : ∀ᵐ ω ∂ν, (∀ s ≤ (q₀ : ℝ≥0), α ω s = a s) ∧ β ω 0 ∉ H ∧
      ∀ s, 0 < s → β ω s ∈ H ∧ α ω ((q₀ : ℝ≥0) + s) = c.2.1 (β ω s))
    (hβ : Measurable[aeSigma m𝓗 ν] fun ω =>
      histOf (pathCoord (β ω)) (firstEntrance (MarkovChart.chartPre c U) (pathCoord (β ω)))) :
    Measurable[aeSigma m𝓗 ν] fun ω => histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) := by
  have heq : ∀ᵐ ω ∂ν, histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) =
      restartHist q₀ (pathCoord a) c
        (histOf (pathCoord (β ω)) (firstEntrance (MarkovChart.chartPre c U) (pathCoord (β ω)))) :=
    hgood.mono fun ω hω => histOf_eq_restartHist hω.1 hpU hω.2.1 hω.2.2
  intro B hB
  obtain ⟨S', hS', hSS'⟩ := ((measurable_restartHist hc q₀ (pathCoord a)).comp hβ) hB
  refine ⟨S', hS', EventuallyEq.trans ?_ hSS'⟩
  filter_upwards [heq] with ω hω
  simp only [mem_preimage, Function.comp_apply, hω]

end Cont

section ContFlow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}
  [IsProbabilityMeasure ν]

/-- **The continuation hypothesis of the restart gluing from a flow line in the chart.** Under one probability
measure `ν` (a regular conditional law given the past): let the chart field `h''` be a GFF with boundary data, `β` a
field-determined flow line of it from `0` with infinite lifetime, and suppose the restarted path `α` is the frozen past
`a` up to the rational time `q₀` and `inv ∘ β` afterwards, `β` staying in `ℍ`. Then for every open `U ⊆ ℍ` avoided by
the past and every Markov decomposition of the centred chart field along the chart pre-image of `U`, the entrance
history of `α` into `U` is `ν`-almost surely determined by the Markov complement (`hcont` of
`isEntranceHistoryLocal_of_restart`). -/
theorem restartCont_of_isFlowLine (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {h'' : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData ν h'' b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b jumps 0 θ ν h'' β ζ) (hζ : ∀ᵐ ω ∂ν, ζ ω = ⊤) (hβc : ∀ ω, Continuous (β ω))
    (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[ν] fun ω => f (WholeField.centredField h'' u₀ ω))
    {c : Chart} (hc : c.IsConformal) {α : Ω → ℝ≥0 → ℂ} {a : ℝ≥0 → ℂ} {q₀ : ℚ≥0}
    (hgood : ∀ᵐ ω ∂ν, (∀ s ≤ (q₀ : ℝ≥0), α ω s = a s) ∧
      ∀ s, 0 < s → β ω s ∈ H ∧ α ω ((q₀ : ℝ≥0) + s) = c.2.1 (β ω s))
    (U : Opens ℂ) (hpU : Disjoint (a '' Icc 0 q₀) U)
    (G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hG' : Measurable G')
    (hd' : GFF.IsMarkovDecomposition (MarkovChart.chartPreOpens hc U) upperHalfPlaneOpens
      (WholeField.centredField h'' u₀) (fun ω => G' (WholeField.centredField h'' u₀ ω)) ν) :
    Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (WholeField.centredField h'' u₀ ω))
      inferInstance) ν] (fun ω => histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω)))) := by
  have h0H : ∀ ω, β ω 0 ∉ H := fun ω hH => by
    have h0 : (0 : ℝ) < (β ω 0).im := hH
    rw [hβ0, Complex.zero_im] at h0
    exact lt_irrefl _ h0
  refine measurable_entranceHist_restart hc hpU (hgood.mono fun ω hω => ⟨hω.1, h0H ω, hω.2⟩) ?_
  exact measurable_entranceHist_of_isFlowLine hκ hκ4 hb hh hfl hζ hβc hβ0 hβm hu₀ hdet
    (MarkovChart.chartPreOpens hc U) (MarkovChart.chartPre_subset_H c U) G' hG' hd'

end ContFlow

/-! ### The past is frozen under the conditional laws -/

section Past

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Under almost every regular conditional law given the past, the path up to `t₀` is the conditioning path.** -/
theorem ae_ae_past_eq {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hαm : ∀ t, Measurable fun ω => α ω t)
    (t₀ : ℝ≥0) : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma α t₀) ω₀), ∀ s ≤ t₀, α ω s = α ω₀ s := by
  have hF : Measurable[pastSigma α t₀]
      (fun ω (_ : Fin 1) => histOf (pathCoord (frozenPath (α ω) t₀)) ((t₀ : ℝ≥0) : ℝ≥0∞)) := comap_measurable _
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (pastSigma_le hαm) hF] with ω₀ h
  filter_upwards [h] with ω hω s hs
  have hq : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t₀ → α ω q = α ω₀ q := fun q hq => by
    have e := congrFun (congrArg Prod.snd (congrFun hω 0)) q
    have hq' : (((q : ℝ≥0) : ℝ≥0∞)) ≤ ((t₀ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hq
    simp only [histOf] at e
    rw [stopCoord_of_le hq', stopCoord_of_le hq'] at e
    simpa only [pathCoord, frozenPath_of_le hq] using e
  have hd : ∀ n, α ω (Sec2.Assembly.dyad n (Sec2.Assembly.flr n s)) =
      α ω₀ (Sec2.Assembly.dyad n (Sec2.Assembly.flr n s)) := fun n => by
    have e : (((((Sec2.Assembly.flr n s : ℕ) : ℚ≥0) / 2 ^ n : ℚ≥0) : ℝ≥0)) =
        Sec2.Assembly.dyad n (Sec2.Assembly.flr n s) := by
      simp [Sec2.Assembly.dyad]
    have := hq (((Sec2.Assembly.flr n s : ℕ) : ℚ≥0) / 2 ^ n)
      (by rw [e]; exact (Sec2.Assembly.dyad_flr_le n s).trans hs)
    rwa [e] at this
  exact tendsto_nhds_unique (((hαc ω).tendsto s).comp (Sec2.Assembly.tendsto_dyad_flr s))
    ((((hαc ω₀).tendsto s).comp (Sec2.Assembly.tendsto_dyad_flr s)).congr fun n => (hd n).symm)

end Past

/-! ### The gluing theorem for a flow line continued in the chart -/

section Assembled

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Entrance-history locality of a path whose continuation after a rational time `q₀` is a flow line in a chart.**
The gluing theorem `isEntranceHistoryLocal_of_restart` with its continuation hypothesis discharged by
`restartCont_of_isFlowLine`: for almost every `ω₀`, under the regular conditional law `ν_{ω₀}` given the past,

* the chart field `h'' ω₀` is a GFF with the piecewise constant data `(b ω₀, jumps ω₀)` (harmonic extension
  `u₀ ω₀`), and its centred version is `h ∘ inv + m ω₀` (`inv` of the chart `c ω₀`);
* `β ω₀` is a continuous flow line of `h'' ω₀` from `0` at angle `θ ω₀` with infinite lifetime, its coordinates
  are determined by the centred chart field, and after `q₀` the path is `α(q₀ + s) = inv(β ω₀ (s))`, `β` staying in
  `ℍ` for `s > 0`.

Together with the locality and determination of the past and the frontier condition on the chart domains, `α` is
entrance-history local. -/
theorem isEntranceHistoryLocal_of_restart_isFlowLine (hκ : 0 < κ) (hκ4 : κ < 4) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t) {q₀ : ℚ≥0}
    (hdet₀ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P] fun ω => f (h ω))
    (hloc₀ : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀) h P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ α ω '' Icc 0 q₀)
    {b : Ω → ℝ → ℝ} {jumps : Ω → Finset ℝ} {θ : Ω → ℝ} {u₀ : Ω → ℂ → ℝ}
    {h'' : Ω → Ω → DistOn upperHalfPlaneOpens} {m : Ω → TestOn upperHalfPlaneOpens → ℝ}
    {β : Ω → Ω → ℝ≥0 → ℂ} {ζ : Ω → Ω → ℝ≥0∞}
    (hchart : ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (b ω₀) (jumps ω₀) ∧
      IsBoundedHarmonicExtension (b ω₀) (jumps ω₀) (u₀ ω₀) ∧
      IsGFFWithBoundaryData (condExpKernel P (pastSigma α q₀) ω₀) (h'' ω₀) (b ω₀) (jumps ω₀) ∧
      ∀ φ, ∀ᵐ ω ∂(condExpKernel P (pastSigma α q₀) ω₀),
        WholeField.centredField (h'' ω₀) (u₀ ω₀) ω φ = h ω (Chart.pushTest (hc ω₀) φ) + m ω₀ φ)
    (hflow : ∀ᵐ ω₀ ∂P,
      IsFlowLine κ (b ω₀) (jumps ω₀) 0 (θ ω₀) (condExpKernel P (pastSigma α q₀) ω₀) (h'' ω₀) (β ω₀) (ζ ω₀) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma α q₀) ω₀), ζ ω₀ ω = ⊤) ∧ (∀ ω, Continuous (β ω₀ ω)) ∧
      (∀ ω, β ω₀ ω 0 = 0) ∧ (∀ t, Measurable fun ω => β ω₀ ω t) ∧
      (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => β ω₀ ω t) =ᵐ[condExpKernel P (pastSigma α q₀) ω₀]
          fun ω => f (WholeField.centredField (h'' ω₀) (u₀ ω₀) ω)) ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma α q₀) ω₀), ∀ s, 0 < s →
        β ω₀ ω s ∈ H ∧ α ω ((q₀ : ℝ≥0) + s) = (c ω₀).2.1 (β ω₀ ω s)) :
    IsEntranceHistoryLocal α h P := by
  refine isEntranceHistoryLocal_of_restart hh hxH hαc hα0 hαm hdet₀ hloc₀ hc hfr
    (h' := fun ω₀ => WholeField.centredField (h'' ω₀) (u₀ ω₀)) (m := m) (hchart.mono fun ω₀ h => h.2.2.2) ?_ ?_
  · filter_upwards [hchart] with ω₀ hω₀
    exact isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hω₀.2.2.1 hω₀.2.1
  · filter_upwards [hchart, hflow, ae_ae_past_eq hαc hαm q₀] with ω₀ hch hfl hpast U hUH hdisj G' hG' hd'
    obtain ⟨hb, hu, hgff, -⟩ := hch
    obtain ⟨hfl, hζ, hβc, hβ0, hβm, hdet, hcont⟩ := hfl
    refine restartCont_of_isFlowLine hκ hκ4 hb hgff hu hfl hζ hβc hβ0 hβm hdet (hc ω₀) (a := α ω₀)
      (hpast.and hcont) U hdisj G' hG' hd'

end Assembled

end StagedEntrance

end Restart

end InteractingSLE
