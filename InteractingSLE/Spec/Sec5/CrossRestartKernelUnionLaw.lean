/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelUnion
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# Lemma 4.7's direction, item (A): the field given the flow segment, the counterflow hull and both records

Packet PROVE-CFRESTART, field side. The conditional law of the centred strip field given the germ of the union of the
flow segment and the counterflow hull **and both stopped driving records** (the conditioning of the source's
p. 118: "conditional on `η|[0,σ]`" and the counterflow up to the image time):

* **`exists_condLaw_union_of_records`** (generic): two local sets `A₁`, `A₂` of a zero-boundary GFF `f`, measurable
  for σ-algebras `ℋ₁ ⟂ ℋ₂ | σ(f)`, with the union history-marked avoidance local for `ℋ₁ ∨ ℋ₂`: the union is a local
  set with a mean `g`, and for every test function `φ`, `g(φ) = E[f(φ) | germ ∨ ℋ₁ ∨ ℋ₂]` and
  `E[e^{i f(φ)} | germ ∨ ℋ₁ ∨ ℋ₂] = e^{i g(φ)} e^{−½ G_{ℍ∖A}(φ, φ)}`;
* **`exists_condLaw_union_strip`**: the strip instance (flow hull `x + K_{τ₁}`, counterflow hull `M_q⁻¹(K′_{τ₂})`,
  marks `𝓕_{τ₁} ∨ 𝓕′_{τ₂}`), from the strip hypothesis `CondIndep (σ(h)) (⨆ σ(η t)) (⨆ σ(W′ t))` alone.

The explicit identification of the mean `g` near each hull (Proposition 3.8 with the single means) is the next step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF CondIndepEv)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Sec5.CrossRestart

open Coupling LocalSets

section Generic

variable {Ω : Type*} {ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The field given the germ of a union and two conditionally independent records.** -/
theorem exists_condLaw_union_of_records {f : Ω → DistOn upperHalfPlaneOpens}
    (hf : IsZeroBoundaryGFF upperHalfPlaneOpens f P) (hℋ₁ : ℋ₁ ≤ mΩ) (hℋ₂ : ℋ₂ ≤ mΩ) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : Measurable[ℋ₁, hittingSigma] A₁) (hA₂ : Measurable[ℋ₂, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap f inferInstance) ℋ₁ ℋ₂ P)
    (h₁ : IsLocalSet A₁ f P) (h₂ : IsLocalSet A₂ f P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (ℋ₁ ⊔ ℋ₂) (fun ω => A₁ ω ∪ A₂ ω) f P) :
    IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) f P ∧ ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) f P g ∧ ∀ φ : TestOn upperHalfPlaneOpens,
        (fun ω => g ω φ) =ᵐ[P] P[fun ω => f ω φ | germSigma (fun ω => A₁ ω ∪ A₂ ω) f ⊔ (ℋ₁ ⊔ ℋ₂)] ∧
        (fun ω => Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A₁ ω ∪ A₂ ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
          P[fun ω => Complex.exp (Complex.I * (f ω φ : ℂ)) |
            germSigma (fun ω => A₁ ω ∪ A₂ ω) f ⊔ (ℋ₁ ⊔ ℋ₂)] := by
  have hA₁m : Measurable[mΩ, hittingSigma] A₁ := hA₁.mono hℋ₁ le_rfl
  have hA₂m : Measurable[mΩ, hittingSigma] A₂ := hA₂.mono hℋ₂ le_rfl
  have hAm := measurable_union_hitting hA₁m hA₂m
  have hci' : CondIndepEv (MeasurableSpace.comap f inferInstance) (MeasurableSpace.comap A₁ hittingSigma)
      (MeasurableSpace.comap A₂ hittingSigma) P :=
    condIndepEv_mono hci hA₁.comap_le hA₂.comap_le
  have hloc := IsLocalSet.isLocalSet_union hf hA₁m hA₂m hci' h₁ h₂
  have hℋ : ℋ₁ ⊔ ℋ₂ ≤ mΩ := sup_le hℋ₁ hℋ₂
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hf hAm hloc
  refine ⟨hloc, g, hg, fun φ => ?_⟩
  have hgM := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hf hAm hloc hℋ hmark hg φ
  obtain ⟨M, -, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hf hAm hℋ hmark hloc.2.1 φ
  refine ⟨hgM, ?_⟩
  filter_upwards [hgM, hM1, hM2] with ω h1 h2 h3
  rw [← h3, h1, ← h2]

end Generic

/-! ### The strip -/

section Strip

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The strip field given the flow segment, the counterflow hull and both stopped records.** Hypotheses as in
`isHistoryAvoidanceLocal_union_strip`. The union is a local set of the centred strip field `h − u₀` with a mean `g`
which, for every test function `φ`, is the conditional mean of `(h − u₀)(φ)` given the germ of the union and both
stopped records `𝓕_{τ₁} ∨ 𝓕′_{τ₂}`; given them, `(h − u₀)(φ)` is Gaussian with variance the Green energy of `φ` in the
complement of the union. -/
theorem exists_condLaw_union_strip {κ κ' q x c a k : ℝ} (hκ : 0 < κ) (hκ' : 0 < κ') (hq : 0 < q)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ u₀' : ℂ → ℝ}
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    -- the flow line
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h₁)
    (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h₁ ω))
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {η : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x))
    {τ₁ : Ω → WithTop ℝ≥0} (hτ₁ : IsStoppingTime (drivingFiltration P hX) τ₁)
    (hτ₁ζ : ∀ᵐ ω ∂P, (τ₁ ω : ℝ≥0∞) < ζ ω) {A₁ : Ω → Set ℂ} (hA₁ : Measurable[hτ₁.measurableSpace, hittingSigma] A₁)
    (hAK₁ : ∀ᵐ ω ∂P, A₁ ω =
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ₁ ω).untopD 0 : ℝ≥0))
    -- the counterflow
    {mL mR : ℕ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ}
    {𝓕' : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin mL → ℝ≥0 → Ω → ℝ} {VR' : Fin mR → ℝ≥0 → Ω → ℝ}
    {B' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {h₂ : Ω → DistOn upperHalfPlaneOpens}
    (hC' : IsOptionalHullCoupling κ' yL yR σL σR P 𝓕' W' VL' VR' B' ζ' h₂)
    (htr' : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h₂ ω))
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ')
    {τ₂ : Ω → WithTop ℝ≥0} (hτ₂ : IsStoppingTime (drivingFiltration P hX') τ₂)
    (hτ₂ζ : ∀ᵐ ω ∂P, (τ₂ ω : ℝ≥0∞) < ζ' ω) {A₂ : Ω → Set ℂ}
    (hA₂ : Measurable[hτ₂.measurableSpace, hittingSigma] A₂)
    (hAK₂ : ∀ᵐ ω ∂P, A₂ ω = (Sec4.stripCounterflowChart q).2.1 ''
      fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ₂ ω).untopD 0 : ℝ≥0))
    -- the strip hypothesis
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P) :
    IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P g ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          (fun ω => g ω φ) =ᵐ[P] P[fun ω => WholeField.centredField h u₀ ω φ |
            germSigma (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) ⊔
              (hτ₁.measurableSpace ⊔ hτ₂.measurableSpace)] ∧
          (fun ω => Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A₁ ω ∪ A₂ ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
            P[fun ω => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω φ : ℂ)) |
              germSigma (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) ⊔
                (hτ₁.measurableSpace ⊔ hτ₂.measurableSpace)] := by
  have hmark := isHistoryAvoidanceLocal_union_strip hκ hκ' hq hhm hh0 hu₀ hC htrans hu₀' hrel hX htr hτ₁ hτ₁ζ hA₁
    hAK₁ hC' htr' hX' hτ₂ hτ₂ζ hA₂ hAK₂ hci
  have hci' := condIndepEv_stopped_strip hκ hκ' hhm hC hX htr hτ₁ hC' hX' hτ₂ hci
  rw [← WholeField.comap_sub_dist h (smoothDist upperHalfPlaneOpens u₀)] at hci'
  -- the two local sets
  have hloc₁ : IsLocalSet A₁ (WholeField.centredField h u₀) P :=
    Coupling.IsLocalSet.congr_set (Sec7.SideHeight.isLocalSet_flowHull hC htrans hu₀ hu₀' hrel hX hτ₁ hτ₁ζ) hAK₁
  have hloc₂ : IsLocalSet A₂ (WholeField.centredField h u₀) P := by
    obtain ⟨-, -, -, hXc, hker⟩ := hC'
    have hK := (hker τ₂ hτ₂ hτ₂ζ).1
    exact Coupling.IsLocalSet.congr_set (WholeField.IsLocalSet.sub_dist (isLocalSet_stripInv_image hq hK htr')
      (WholeField.isHarmonicDistOn_smoothDist hu₀)) hAK₂
  exact exists_condLaw_union_of_records hh0 hτ₁.measurableSpace_le hτ₂.measurableSpace_le hA₁ hA₂ hci' hloc₁ hloc₂
    hmark

end Strip

end InteractingSLE.Sec5.CrossRestart
