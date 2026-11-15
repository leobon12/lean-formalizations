/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowSeedGerm
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Sec7.StripPocketPathWalls
import InteractingSLE.Spec.Sec5.CrossRestartLaw

/-!
# The counterflow's no-return without two-seed completeness: admissible counterflow words

Packet PROVE-CFNORETURN3 (ruling R59; PROVE-CFNORETURN2 §5.2). `CfNoReturn.counterflowNoReturnStatement_of_inputs`
proves `Theorem14.GW4Ident.CounterflowNoReturnStatement` for every word from two-seed completeness, which on the
landed route goes through Lemma 7.25 and is circular for Theorems 1.2–1.3. Every consumer on that route has an
**admissible** counterflow word (all partial sums `≥ κ′/2 − 2`, `κ′ = 16/κ`): Proposition 4.9's counterflow
(Cond. (4.4)), Proposition 5.13's strip counterflow, and the strip system's counterflow of Lemma 7.25's pocket word.
Then both seed weights are barriers (`seedWeightL_ge_of_admissible`, `seedWeightR_ge_of_admissible`), and
`CfNoReturn.ae_trace_ne_zero_of_aux7` gives the no-return from Aux. lemma 7 at `κ′` alone.

## Main results

* `seedWeightL_ge_of_admissible`, `seedWeightR_ge_of_admissible`: admissible partial sums bound the seed weights.
* `ae_trace_ne_zero_of_admissible`: an ordered admissible word with marks at `0⁻` and `0⁺` does not return to `0`,
  from `Sec4.Aux7Statement κ` (`κ > 4`).
* `ae_trace_ne_zero_of_isFlowLineDriver`: the same for a flow-line driver at `0` whose word is admissible.
* `ae_trace_ne_zero_of_centered`: a centred counterflow of a GFF whose data are `≤ −λ + πχ/2` on `ℝ₋` and
  `≥ λ − πχ/2` on `ℝ₊` (off the jumps) does not return to its start, from Aux. lemma 7 at `16/κ`.
* `CounterflowNoReturnAdmStatement` (this restricted form of `CounterflowNoReturnStatement`) and
  `counterflowNoReturnAdmStatement_of_partA`: it holds given `Sec5.PartAInputsSixteenDiv`.

R48: nothing used takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis, and no
two-seed completeness (`LP.TwoSeedComplete`) or Lemma 7.25 is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace CfNoReturn

namespace Route

/-! ### Admissible partial sums bound the seed weights -/

section Weights

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The right seed weight of an admissible word is a barrier**: an ordered word with a mark at `0⁺` and admissible
partial sums at `k` has `seedWeightR ≥ k/2 − 2` (the partial sum at `x = 0`). -/
theorem seedWeightR_ge_of_admissible (hord : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) {j : Fin nR} (hj : xR j = 0) :
    k / 2 - 2 ≤ seedWeightR xR ρR := by
  have h := hadm.2 0 le_rfl ⟨j, hj.le⟩
  have e : univ.filter (fun i => xR i ≤ 0) = univ.filter (fun i => xR i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => le_antisymm h (hord.2.2.2 i), fun h => h.le⟩
  rw [e] at h
  exact h

/-- **The left seed weight of an admissible word is a barrier**: an ordered word with a mark at `0⁻` and admissible
partial sums at `k` has `seedWeightL ≥ k/2 − 2` (the partial sum at a point `x < 0` right of every negative mark). -/
theorem seedWeightL_ge_of_admissible (hord : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) {j : Fin nL} (hj : xL j = 0) :
    k / 2 - 2 ≤ seedWeightL xL ρL := by
  have hev : ∀ᶠ x in 𝓝[<] (0 : ℝ), x < 0 ∧ ∀ i, (x < xL i ↔ xL i = 0) := by
    refine (eventually_mem_nhdsWithin (s := Iio (0 : ℝ))).and (Filter.eventually_all.2 fun i => ?_)
    rcases (hord.2.1 i).lt_or_eq with hi | hi
    · filter_upwards [Ioo_mem_nhdsLT hi] with x hx
      exact ⟨fun h => absurd h (not_lt.2 hx.1.le), fun h => absurd h hi.ne⟩
    · filter_upwards [eventually_mem_nhdsWithin (s := Iio (0 : ℝ))] with x hx
      exact ⟨fun _ => hi, fun _ => hi ▸ hx⟩
  obtain ⟨x, hx, hiff⟩ := hev.exists
  have h := hadm.1 x hx ⟨j, by rw [hj]; exact hx⟩
  have e : univ.filter (fun i => x < xL i) = univ.filter (fun i => xL i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff i
  rw [e] at h
  exact h

end Weights

/-! ### No return for admissible words -/

section Admissible

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **No return to the start for an admissible seeded word, from Aux. lemma 7** (`κ > 4`): an ordered word with a mark
at `0⁻` and a mark at `0⁺` and admissible partial sums at `κ`. Aux. lemma 7 gives `ζ = ∞`, and both seed weights are
barriers, so `CfNoReturn.ae_trace_ne_zero_of_aux7` applies. -/
theorem ae_trace_ne_zero_of_admissible [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (haux7 : Sec4.Aux7Statement.{u} κ) (hord : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {j : Fin nR} (hj : xR j = 0) {l : Fin nL} (hl : xL l = 0) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 :=
  ae_trace_ne_zero_of_aux7 hκ4 haux7 hord hE
    ((haux7 xL xR ρL ρR P 𝓕 W VL VR B ζ hord hadm hE).mono fun _ h => h.1) hj hl
    (seedWeightL_ge_of_admissible hord hadm hl) (seedWeightR_ge_of_admissible hord hadm hj)

end Admissible

/-- **No return to the start for a flow-line driver with an admissible word** (`κ′ > 4`, from Aux. lemma 7 at `κ′`):
the angle-`0` flow line from `0` of a field with data `b′`, whose word has admissible partial sums at `κ′`. -/
theorem ae_trace_ne_zero_of_isFlowLineDriver {κ' : ℝ} (hκ' : 4 < κ') (haux7 : Sec4.Aux7Statement.{u} κ')
    {b' : ℝ → ℝ} {J' : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ' b' J' 0 P h' W ζ)
    (hadm : Sec4.HasAdmissiblePartialSums κ' (flowLineRhoL κ' b' J' 0 0) (flowLineRhoR κ' b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  exact ae_trace_ne_zero_of_admissible hκ' haux7 (Theorem15.isOrderedForceWord_flowLine b' J' 0) hadm hC.1
    (j := ⟨0, by unfold flowLineNR; omega⟩) rfl (l := ⟨0, by unfold flowLineNL; omega⟩) rfl

/-- **A centred counterflow with barrier data does not return to its start** (`0 < κ < 4`, from Aux. lemma 7 at
`16/κ`): if the data `b` of the GFF are `≤ −λ + πχ/2` on `ℝ₋` and `≥ λ − πχ/2` on `ℝ₊` off the jumps, the
counterflow's word (the flow-line word of `counterflowData κ b` at `16/κ`) is admissible
(`Sec7.StripPocketPath.counterflowData_bounds_off`, `Sec4.hasAdmissiblePartialSums_flowLine`). -/
theorem ae_trace_ne_zero_of_centered {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ)) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hL : ∀ x : ℝ, x < 0 → x ∉ jumps → b x ≤ -sleLambda κ + π / 2 * chiC κ)
    (hR : ∀ x : ℝ, 0 < x → x ∉ jumps → sleLambda κ - π / 2 * chiC κ ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ Q h W ζ) :
    ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  have hbd := Sec7.StripPocketPath.counterflowData_bounds_off hκ hL hR
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine (by positivity : (0 : ℝ) < 16 / κ)
    (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb) hbd.1 hbd.2
  exact ae_trace_ne_zero_of_isFlowLineDriver hκ' haux7 hfl hadm

/-- **The counterflow's no-return for barrier data** (`CounterflowNoReturnStatement` restricted to GFF data `b` with
`b ≤ −λ + πχ/2` on `ℝ₋` and `b ≥ λ − πχ/2` on `ℝ₊` off the jumps — the data of every consumer on the route of
Theorems 1.2–1.3). No lifetime hypothesis is needed: Aux. lemma 7 gives `ζ = ∞`. -/
def CounterflowNoReturnAdmStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    (∀ x : ℝ, x < 0 → x ∉ jumps → b x ≤ -sleLambda κ + π / 2 * chiC κ) →
    (∀ x : ℝ, 0 < x → x ∉ jumps → sleLambda κ - π / 2 * chiC κ ≤ b x) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
    ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q h W ζ →
      ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0

/-- `CounterflowNoReturnAdmStatement` from Aux. lemma 7 at every `16/κ`, `0 < κ < 4`. -/
theorem counterflowNoReturnAdmStatement_of_aux7
    (haux7 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec4.Aux7Statement.{u} (16 / κ)) :
    CounterflowNoReturnAdmStatement.{u} := by
  intro κ hκ hκ4 b jumps hb hL hR Ω _ Q _ h hh W ζ hcf
  exact ae_trace_ne_zero_of_centered hκ hκ4 (haux7 κ hκ hκ4) hb hL hR hh hcf

/-- **`CounterflowNoReturnAdmStatement` from Zhan's Part A inputs at `16/κ`** (`Sec5.PartAInputsSixteenDiv`, which
yields Aux. lemma 7 at `16/κ`). -/
theorem counterflowNoReturnAdmStatement_of_partA (hA : Sec5.PartAInputsSixteenDiv) :
    CounterflowNoReturnAdmStatement.{u} :=
  counterflowNoReturnAdmStatement_of_aux7 fun _ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA hA hκ hκ4

end Route

end CfNoReturn

end InteractingSLE
