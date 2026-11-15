/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartSwMain
import InteractingSLE.Spec.Sec5.Prop513ScheduleData
import InteractingSLE.Spec.Sec7.Prop74BMain

/-!
# Lemma 4.7's conditional law under the (4.4) heights at the prefix angle and at `π/2`

Packet PROVE-QSCHED. The finite extreme-angle schedules of Proposition 5.13 (Figure 5.5, `a, b ≥ λ′`) have
conditional words with `ExtremeHeights` only: after an angle-`±π/2` piece the word carries the side values
`−λ ∓ (π/2)χ` and `λ ∓ (π/2)χ` (Figure 5.5, right panel). These never satisfy Aux. lemma 130's uniform heights
(`b + aχ ≤ −λ` on the left for every `a ∈ [−π/2, π/2]`), which are the hypotheses of
`RestartSw.CounterflowGivenPrefixStatement` and of the four CfChart leaves. The restart law at a switch of a
schedule is therefore stated here under exactly the heights that the CfChart chain uses
(`CfChart.exists_chartCanon_omega` reduces Aux. 130's heights to `IsHeightBounded44` at the prefix angle and at
`π/2` and uses nothing else), or their mirror image.

* `CounterflowGivenPrefix44Statement`: the named input (Lemma 4.7's conditional law, spec. p. 118; Lemma 5.7's
  proof, p. 138). It implies the existing `RestartSw.CounterflowGivenPrefixStatement`
  (`counterflowGivenPrefixStatement_of_44`).
* `isHeightBounded44_of_extremeHeights`, `isHeightBounded44_refl_of_extremeHeights`, `heights44_of_extreme`:
  `ExtremeHeights` gives the (4.4) heights at `π/2` and their mirror image.
* `isFlowLineDriver_congr_field`: a flow-line driver of a field drives the flow line of every null modification
  of the field that is a GFF with the same data.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.QSched

open WangWu (negInv)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps mem_reflJumps)
open Prop513Schedule (ExtremeHeights)
open Exist Exist.Staged Exist.StagedLaw

/-- **Named input: the counterflow given a stopped flow-line prefix, under the (4.4) heights** (Lemma 4.7's
conditional law at a deterministic own time, spec. p. 118; Lemma 5.7's proof, p. 138, "the boundary data for the
GFF which describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5"; Remark 5.8). It is
`RestartSw.CounterflowGivenPrefixStatement` with Aux. lemma 130's uniform heights replaced by the (4.4) heights at
the prefix angle `θ₀` and at `π/2` (resp. their mirror image `y ↦ −b(−y)` at `−θ₀` and `π/2`), the hypotheses of
the CfChart chain; the heights at `π/2` are the admissibility of the counterflow (`a, b ≥ λ′` in Figure 5.5).
Conclusion: under the regular conditional law given the record of `D` stopped at `t₀`, the counterflow read in the
record chart is the centred counterflow of the field read in that chart, with infinite lifetime; pathwise, a
continuous increasing clock `ℓ` carries the image counterflow `η″` to the physical one. -/
def CounterflowGivenPrefix44Statement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) →
    ((IsHeightBounded44 κ b J θ₀ ∧ IsHeightBounded44 κ b J (π / 2)) ∨
      (IsHeightBounded44 κ (reflData b) (reflJumps J) (-θ₀) ∧
        IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2))) →
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (W'' : ℝ≥0 → Ω → ℝ) (ζ'' : Ω → ℝ≥0∞) (η'' : Ω → ℝ≥0 → ℂ),
      (∀ᵐ ω₀ ∂P,
        IsCenteredCounterflowDriver κ
            (condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀)
            (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (D ω₀)) (h ω)) W'' ζ'' ∧
          ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀),
            ζ'' ω = ⊤) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- Aux. lemma 130's uniform heights give the (4.4) heights at every angle of `[−π/2, π/2]`. -/
theorem isHeightBounded44_of_uniform {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {a : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2)) : IsHeightBounded44 κ b J a := by
  have hπχ : 0 < π * chiC κ := mul_pos Real.pi_pos (Sec4.chiC_pos hκ hκ4)
  refine ⟨fun y hy hyJ => ?_, hright a ha⟩
  have := hleft a ha y hy hyJ
  linarith

/-- **The new input implies the input of the two-angle restart** (`RestartSw.CounterflowGivenPrefixStatement`,
Aux. lemma 130's uniform heights): those heights give the (4.4) heights at every angle of `[−π/2, π/2]`. -/
theorem counterflowGivenPrefixStatement_of_44 (hcg : CounterflowGivenPrefix44Statement.{u}) :
    RestartSw.CounterflowGivenPrefixStatement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ₀ D hDm hDr hD t₀ η hη
  have hπ : π / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  exact hcg κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ₀
    (Or.inl ⟨isHeightBounded44_of_uniform hκ hκ4 hleft hright hθ₀,
      isHeightBounded44_of_uniform hκ hκ4 hleft hright hπ⟩) D hDm hDr hD t₀ η hη

/-! ### The extreme heights -/

/-- `ExtremeHeights` is the (4.4) heights at `π/2`. -/
theorem isHeightBounded44_of_extremeHeights {κ : ℝ} {c : Restart.BoundaryWord} (hc : ExtremeHeights κ c) :
    IsHeightBounded44 κ c.fn c.jumps (π / 2) := by
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have := hc.1 y hy hyJ
    linarith
  · have := hc.2 y hy hyJ
    linarith

/-- `ExtremeHeights` gives the (4.4) heights at `π/2` of the mirror-image data `y ↦ −b(−y)`. -/
theorem isHeightBounded44_refl_of_extremeHeights {κ : ℝ} {c : Restart.BoundaryWord} (hc : ExtremeHeights κ c) :
    IsHeightBounded44 κ (reflData c.fn) (reflJumps c.jumps) (π / 2) := by
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have hyJ' : -y ∉ c.jumps := fun h' => hyJ (mem_reflJumps.2 h')
    have := hc.2 (-y) (neg_pos.2 hy) hyJ'
    simp only [reflData]
    linarith
  · have hyJ' : -y ∉ c.jumps := fun h' => hyJ (mem_reflJumps.2 h')
    have := hc.1 (-y) (neg_neg_iff_pos.2 hy) hyJ'
    simp only [reflData]
    linarith

/-- **The height hypothesis of the input at an extreme angle**: at `π/2` the (4.4) heights, at `−π/2` their mirror
image, both from `ExtremeHeights`. -/
theorem heights44_of_extreme {κ θ : ℝ} {c : Restart.BoundaryWord} (hc : ExtremeHeights κ c)
    (hθ : θ = -(π / 2) ∨ θ = π / 2) :
    (IsHeightBounded44 κ c.fn c.jumps θ ∧ IsHeightBounded44 κ c.fn c.jumps (π / 2)) ∨
      (IsHeightBounded44 κ (reflData c.fn) (reflJumps c.jumps) (-θ) ∧
        IsHeightBounded44 κ (reflData c.fn) (reflJumps c.jumps) (π / 2)) := by
  rcases hθ with rfl | rfl
  · refine Or.inr ⟨?_, isHeightBounded44_refl_of_extremeHeights hc⟩
    rw [neg_neg]
    exact isHeightBounded44_refl_of_extremeHeights hc
  · exact Or.inl ⟨isHeightBounded44_of_extremeHeights hc, isHeightBounded44_of_extremeHeights hc⟩

/-- An extreme angle lies in `[−π/2, π/2]`. -/
theorem mem_Icc_of_extreme {θ : ℝ} (hθ : θ = -(π / 2) ∨ θ = π / 2) : θ ∈ Icc (-(π / 2)) (π / 2) := by
  rcases hθ with rfl | rfl
  · exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  · exact ⟨by linarith [Real.pi_pos], le_rfl⟩

/-! ### Null modifications of the field -/

/-- **A flow-line driver drives the flow line of every null modification of the field** that is a GFF with the
same data (`IsOptionalHullCoupling.congr_field`, as `Sec7.Prop74B.IsFlowLine.congr_field`). -/
theorem isFlowLineDriver_congr_field {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h h₁ : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ P h W ζ) (hh₁ : IsGFFWithBoundaryData P h₁ b J) (he : h₁ =ᵐ[P] h) :
    IsFlowLineDriver κ b J θ P h₁ W ζ := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hc⟩ := hfl
  have hG := Exist.isGFFWithBoundaryData_flowField hκ hb 0 θ hh₁
  have he' : (fun ω => Exist.flowField 0 (θ * chiC κ) (h₁ ω)) =ᵐ[P] h' := he.mono fun ω hω => by
    show Exist.flowField 0 (θ * chiC κ) (h₁ ω) = h' ω
    rw [hω, Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
  exact ⟨fun ω => Exist.flowField 0 (θ * chiC κ) (h₁ ω), 𝓕, VL, VR, B,
    fun ω => Exist.isTranslateAddConst_flowField 0 _ (h₁ ω),
    Sec7.Prop74B.IsOptionalHullCoupling.congr_field hc hG.1 hG.2 he'⟩

end InteractingSLE.Sec5.QSched
