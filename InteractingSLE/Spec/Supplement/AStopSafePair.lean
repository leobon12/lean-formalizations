/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Restart.RetPlumbProofFinalGaussian
import InteractingSLE.Spec.Supplement.RLCCondDetHistR1
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# Item 4 of `AStopSourceInputs`: the pairings of the A-stopped continuations

Packet PROVE-T15-ASTOP-SAFE (Theorem 1.5's leaf 3). The conjunct
`∀ φ, Integrable (fun ω => flowField 0 (θχ) (Hc ω) φ) (P.restrict M)` of `RLC.OrdModel.AStopSourceInputs`, for the
two continuations of an ordinary retained pair. RETPLUMB's `retPairing_integrable_of_meanIdent` needs disjoint pairs;
here the input is the mean identification on an arbitrary event (`RLC.IsRetMeanIdentOn`, which the two source
statements give on the ordinary pairs) and R1 on that event (`RLC.exists_r1_of_meanIdentOn`):

* `ae_condExp_cexp_apply_eq_gaussCF_on`: a conditional word characteristic functional known on a `𝒢`-event for every
  fixed test function holds there at every `𝒢`-measurable random test function (the regular-conditional-law argument of
  `RandomTest.condExp_cexp_apply_ae_eq_of_subset`, made trivial off the event as in `Restart.R1Glue`);
* `gaussCF_pushTest_shiftChart`, **`ae_condExp_cexp_flowField_eq_gaussCF_on`**: hence the field translated by a
  `𝒢`-measurable seed `τ` (`flowField τ 0`) has the characteristic functional of the translated word `shiftW τ β`;
* **`integrable_flowField_of_wordCF_on`**: a conditional word characteristic functional of one force type on an event
  gives integrable pairings there (`FCPlumb.initialPairingGaussian_of_wordCF`);
* **`integrable_pairing_of_meanIdentOn`** (second continuation: the chart field) and
  **`integrable_pairing_shift_of_meanIdentOn`** (first continuation: the chart field translated to the seed) on any
  `retSigma76` event lying almost surely in the identification event;
* **`integrable_pairing_ord_snd`**, **`integrable_pairing_ord_fst`**: the forms of the two source statements
  (`RLC.OrdModel.RetOrdAStopSourceSndStatement`, `RLC.RetOrdAStopSourceFstSeedStatement`) on the parts of
  PROVE-T15-ASTOP-PART's type partition.

Uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.AStopSafe

open Restart Restart.RetAux79 Supp7 Sec7.Lemma76F

universe u

/-! ### Random test functions on an event -/

section Random

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A test function on `ℍ` is supported in `ℍ`. -/
theorem tsupport_subset_H (ψ : TestOn upperHalfPlaneOpens) : tsupport ψ ⊆ H :=
  ψ.tsupport_subset

/-- **The conditional word characteristic functional at a random test function, on an event.** If, on the
`𝒢`-event `M`, the conditional characteristic functional of `X` at every fixed test function is that of the word
`β`, then on `M` it is also that of `β` at every `𝒢`-measurable random test function. -/
theorem ae_condExp_cexp_apply_eq_gaussCF_on (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) {M : Set Ω} (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord}
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {T : Ω → TestOn upperHalfPlaneOpens} (hT : ∀ z, Measurable[𝒢] fun ω => T ω z) :
    ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] ω = gaussCF (β ω) (T ω) := by
  classical
  set U' : Ω → Set ℂ := fun ω => if ω ∈ M then H else ∅ with hU'
  set Ψ' : Ω → TestOn upperHalfPlaneOpens → ℂ := fun ω ψ => if ω ∈ M then gaussCF (β ω) ψ
    else ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂(Measure.dirac (0 : DistOn upperHalfPlaneOpens)) with hΨ'
  set T' : Ω → TestOn upperHalfPlaneOpens := fun ω => if ω ∈ M then T ω else 0 with hT'
  have hT'm : ∀ z, Measurable[𝒢] fun ω => T' ω z := fun z => by
    have e : (fun ω => T' ω z) = M.piecewise (fun ω => T ω z) fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ M
      · simp only [hT', hω, ↓reduceIte, piecewise_eq_of_mem]
      · rw [piecewise_eq_of_notMem _ _ _ hω]
        simp only [hT', hω, ↓reduceIte]
        rfl
    rw [e]
    exact Measurable.piecewise hM (hT z) measurable_const
  have hT'U : ∀ ω, tsupport (T' ω) ⊆ U' ω := fun ω => by
    by_cases hω : ω ∈ M
    · simp only [hT', hU', hω, ↓reduceIte]
      exact tsupport_subset_H _
    · simp only [hT', hU', hω, ↓reduceIte]
      simp
  have hU'o : ∀ ω, IsOpen (U' ω) := fun ω => by
    by_cases hω : ω ∈ M
    · simp only [hU', hω, ↓reduceIte]; exact QuantumZipper.isOpen_H
    · simp only [hU', hω, ↓reduceIte]; exact isOpen_empty
  have hU'V : ∀ ω, U' ω ⊆ upperHalfPlaneOpens := fun ω => by
    by_cases hω : ω ∈ M
    · simp only [hU', hω, ↓reduceIte]; exact subset_rfl
    · simp only [hU', hω, ↓reduceIte]; exact empty_subset _
  have hΨ'law : ∀ ω, ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U' ω →
        ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂μ = Ψ' ω ψ := fun ω => by
    by_cases hω : ω ∈ M
    · refine ⟨(β ω).gffLaw, inferInstance, fun ψ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
      exact (gaussCF_eq_integral (β ω) ψ).symm
    · refine ⟨Measure.dirac 0, inferInstance, fun ψ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
  have hcond' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport ψ ⊆ U' ω →
      P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢] ω = Ψ' ω ψ := by
    intro ψ
    by_cases hψ : ψ = 0
    · subst hψ
      have hc1 : P[fun ω => Complex.exp (Complex.I * (X ω 0 : ℂ)) | 𝒢] = fun _ => (1 : ℂ) := by
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        exact condExp_const h𝒢 1
      filter_upwards [hcf 0] with ω h1 _
      by_cases hω : ω ∈ M
      · simp only [hΨ', hω, ↓reduceIte]
        exact h1 hω
      · simp only [hΨ', hω, ↓reduceIte, hc1]
        rw [integral_dirac' _ _ (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply 0)).stronglyMeasurable]
        simp
    · filter_upwards [hcf ψ] with ω h1 hsupp
      by_cases hω : ω ∈ M
      · simp only [hΨ', hω, ↓reduceIte]
        exact h1 hω
      · simp only [hU', hω, ↓reduceIte] at hsupp
        exact absurd (eq_zero_of_tsupport_subset_empty hsupp) hψ
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset h𝒢 hX hU'o hU'V hΨ'law hcond' hT'm hT'U
  have hT'X : Measurable fun ω => X ω (T' ω) :=
    RandomTest.measurable_apply_of_forall_measurable hX fun z => (hT'm z).mono h𝒢 le_rfl
  have hTX : Measurable fun ω => X ω (T ω) :=
    RandomTest.measurable_apply_of_forall_measurable hX fun z => (hT z).mono h𝒢 le_rfl
  have hloc := ae_condExp_congr_on (𝒦 := 𝒢) (P := P) hM (GFF.integrable_exp_I_mul hT'X)
    (GFF.integrable_exp_I_mul hTX) (X := fun ω => Complex.exp (Complex.I * (X ω (T' ω) : ℂ)))
    (Y := fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)))
    (Eventually.of_forall fun ω hω => by simp only [hT', hω, ↓reduceIte])
  filter_upwards [key, hloc] with ω hk hl hω
  rw [← hl hω, hk]
  simp only [hT', hΨ', hω, ↓reduceIte]


/-! ### The field translated to a seed -/

/-- **The word characteristic functional at a translated test function** is that of the translated word. -/
theorem gaussCF_pushTest_shiftChart (c : BoundaryWord) (x : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    gaussCF c (Chart.pushTest (Exist.isConformal_shiftChart x) φ) =
      gaussCF (Exist.StagedLaw.BoundaryWord.shiftW x c) φ := by
  have hcov := Chart.zeroGFFTestCov_pushTest (Exist.isConformal_shiftChart x) φ φ
  rw [Exist.shiftChart_dom] at hcov
  have hmean : (∫ z, c.mean z * Chart.pushTest (Exist.isConformal_shiftChart x) φ z) =
      ∫ z, (Exist.StagedLaw.BoundaryWord.shiftW x c).mean z * φ z := by
    simp only [Exist.pushTest_shiftChart_apply, OrdDet.mean_shiftW]
    rw [← integral_add_right_eq_self (fun z => c.mean z * φ (z - (x : ℂ))) (x : ℂ)]
    simp only [add_sub_cancel_right]
  unfold gaussCF
  rw [hmean]
  congr 3
  exact congrArg (fun r : ℝ => (r : ℂ)) hcov

/-- **The conditional characteristic functional of the field translated to a `𝒢`-measurable seed**, on an event:
that of the translated word. -/
theorem ae_condExp_cexp_flowField_eq_gaussCF_on (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) {M : Set Ω} (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord}
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {τ : Ω → ℝ} (hτ : Measurable[𝒢] τ) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (Exist.flowField (τ ω) 0 (X ω) φ : ℂ)) | 𝒢] ω =
        gaussCF (Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (β ω)) φ := by
  set T : Ω → TestOn upperHalfPlaneOpens := fun ω => Chart.pushTest (Exist.isConformal_shiftChart (τ ω)) φ with hT
  have hTm : ∀ z, Measurable[𝒢] fun ω => T ω z := fun z => by
    simp only [hT, Exist.pushTest_shiftChart_apply]
    exact φ.continuous.measurable.comp (measurable_const.sub (Complex.measurable_ofReal.comp hτ))
  have he : (fun ω => Complex.exp (Complex.I * (Exist.flowField (τ ω) 0 (X ω) φ : ℂ))) =
      fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) := by
    funext ω
    rw [Exist.flowField_apply, zero_mul, add_zero]
  rw [he]
  filter_upwards [ae_condExp_cexp_apply_eq_gaussCF_on h𝒢 hX hM hcf hTm] with ω hω hωM
  rw [hω hωM, gaussCF_pushTest_shiftChart]

/-! ### Integrable pairings from a conditional word characteristic functional -/

/-- **Integrable pairings on an event from a conditional word characteristic functional of one force type.** -/
theorem integrable_flowField_of_wordCF_on (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β) (hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) (a : ForceWordType)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → β ω ∈ forceTypeSet κ θ a) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict M) := by
  set B := FCPlumb.fcTypeBranch κ θ M β a with hB
  have hBm : MeasurableSet B := (h𝒢 _ hM).inter ((hβ.mono h𝒢 le_rfl) (measurableSet_forceTypeSet κ θ a))
  have hG : RetInitialPairingGaussian P 𝒢 B (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) :=
    fun ψ => FCPlumb.initialPairingGaussian_of_wordCF h𝒢 hM hβ hs hHc hcf hκ θ a ψ
  have hi := integrable_restrict_of_retInitialPairingGaussian hBm hG φ
  have hBM : B =ᵐ[P] M := by
    filter_upwards [htype] with ω hω
    exact propext ⟨fun h => h.1, fun h => ⟨h, hω h⟩⟩
  rwa [Measure.restrict_congr_set hBM] at hi

end Random

/-! ### The retained pairings -/

section Retained

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **R1 on an event of retained pairs, read on a smaller event**: a sub-σ-algebra `𝒢 ⊇ retSigma76` under which, almost
surely on `M` (an event lying almost surely in the identification event `O`), the chart field has the conditional
characteristic functional of the word `β`. -/
theorem exists_wordCF_of_meanIdentOn (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {O : Set Ω}
    (hO : ∀ᵐ ω ∂P, ω ∈ O → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) {M : Set Ω} (hMO : ∀ᵐ ω ∂P, ω ∈ M → ω ∈ O) :
    ∃ 𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}, retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ := by
  obtain ⟨𝒢, M₀, hR, -, hOM₀, -, hcf⟩ := exists_r1_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hO hβ hmean
  refine ⟨𝒢, hR, fun φ => ?_⟩
  filter_upwards [hcf φ, hOM₀, hMO] with ω h1 h2 h3 hω
  exact h1 (h2 (h3 hω))

/-- **Pairings of the chart field** (second continuation) on a retained event lying almost surely in the
identification event, on which the word is sorted and of one force type. -/
theorem integrable_pairing_of_meanIdentOn (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {O : Set Ω}
    (hO : ∀ᵐ ω ∂P, ω ∈ O → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) {M : Set Ω}
    (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M) (hMO : ∀ᵐ ω ∂P, ω ∈ M → ω ∈ O)
    (hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) (θ : ℝ) (a : ForceWordType)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → β ω ∈ forceTypeSet κ θ a) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (hd.chartField κ h ω) φ) (P.restrict M) := by
  obtain ⟨𝒢, hR, hcf⟩ := exists_wordCF_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hO hβ hmean hMO
  exact integrable_flowField_of_wordCF_on 𝒢.2 (hR _ hM) (hβ.mono hR le_rfl) hs (hd.measurable_chartField κ hh.1)
    hcf hκ θ a htype φ

/-- **Pairings of the chart field translated to a seed** (first continuation): with a `retSigma76`-measurable seed `τ`,
the translated field `flowField τ 0` of the chart field has integrable pairings on `M` when the translated word
`shiftW τ β` has one force type there. -/
theorem integrable_pairing_shift_of_meanIdentOn (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {O : Set Ω}
    (hO : ∀ᵐ ω ∂P, ω ∈ O → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) {M : Set Ω}
    (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M) (hMO : ∀ᵐ ω ∂P, ω ∈ M → ω ∈ O)
    (hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) {τ : Ω → ℝ} (hτ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ)
    (θ : ℝ) (a : ForceWordType)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (β ω) ∈ forceTypeSet κ θ a)
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Exist.flowField (τ ω) 0 (hd.chartField κ h ω)) φ)
      (P.restrict M) := by
  obtain ⟨𝒢, hR, hcf⟩ := exists_wordCF_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hO hβ hmean hMO
  have hX := hd.measurable_chartField κ hh.1
  have hτG : Measurable[𝒢.1] τ := hτ.mono hR le_rfl
  have hβG : Measurable[𝒢.1] β := hβ.mono hR le_rfl
  have hcf' := fun φ => ae_condExp_cexp_flowField_eq_gaussCF_on 𝒢.2 hX (hR _ hM) hcf hτG φ
  have hβ' : Measurable[𝒢.1] fun ω => Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (β ω) := by
    have hp : Measurable[𝒢.1] fun ω => (τ ω, β ω) := hτG.prodMk hβG
    have h2 := @Measurable.comp Ω (ℝ × BoundaryWord) BoundaryWord 𝒢.1 _ _ _ _
      Exist.StagedLaw.BoundaryWord.measurable_shiftW hp
    exact h2
  have hs' : ∀ᵐ ω ∂P, ω ∈ M → (Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (β ω)).IsSorted := by
    filter_upwards [hs] with ω hsω hω
    exact Exist.StagedLaw.BoundaryWord.isSorted_shiftW (hsω hω) _
  have hHc : Measurable fun ω => Exist.flowField (τ ω) 0 (hd.chartField κ h ω) := by
    have hp : Measurable fun ω => (τ ω, hd.chartField κ h ω) :=
      (hτ.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r) le_rfl).prodMk hX
    have h2 := Exist.StagedLaw.measurable_flowField_uncurry.comp hp
    exact h2
  exact integrable_flowField_of_wordCF_on 𝒢.2 (hR _ hM) hβ' hs' hHc hcf' hκ θ a htype φ

/-! ### The forms of the two source statements -/

omit [IsProbabilityMeasure P] in
/-- Ordinary pairs lie almost surely in the chart event with both cutoffs alive. -/
theorem ae_ord_live {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∀ᵐ ω ∂P, ω ∈ {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} →
      (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E := by
  filter_upwards [hag] with ω hagω hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  exact ⟨hord.1, hord.2.1, hd.mem_E_of_ordinary hG a₁ a₂ hord⟩

/-- **Item 4 of `AStopSourceInputs` for the A-stopped second continuation** (the pairings of
`RLC.OrdModel.RetOrdAStopSourceSndStatement`): on a `retSigma76` event lying almost surely in the ordinary pairs, on
which the word `β.1` has one force type for the angle `θ₂`, the shifted chart field has integrable pairings. -/
theorem integrable_pairing_ord_snd (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord × ℝ}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1))
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).1.IsSorted)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (a : ForceWordType) (htype : ∀ ω ∈ M, (β ω).1 ∈ FCDet.typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR)
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) φ) (P.restrict M) := by
  have hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted := by
    filter_upwards [hsort, hMord] with ω h1 h2 hω
    exact h1 (h2 hω)
  exact integrable_pairing_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ (ae_ord_live hd hag) hβ.fst hmean
    hM hMord hs θ₂ a (Eventually.of_forall fun ω hω => htype ω hω) φ

/-- **Item 4 of `AStopSourceInputs` for the A-stopped first continuation at its seed** (the pairings of
`RLC.RetOrdAStopSourceFstSeedStatement`): on a `retSigma76` event lying almost surely in the ordinary pairs, on which
the seeded word `shiftW β.2 β.1` has one force type for the angle `θ₁`, the chart field translated to the seed `β.2`
has integrable pairings. -/
theorem integrable_pairing_ord_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord × ℝ}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1))
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).1.IsSorted)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, Exist.StagedLaw.BoundaryWord.shiftW (β ω).2 (β ω).1 ∈
      FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (β ω).2 0 (hd.chartField κ h ω)) φ)
      (P.restrict M) := by
  have hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted := by
    filter_upwards [hsort, hMord] with ω h1 h2 hω
    exact h1 (h2 hω)
  exact integrable_pairing_shift_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ (ae_ord_live hd hag) hβ.fst
    hmean hM hMord hs hβ.snd θ₁ a (Eventually.of_forall fun ω hω => htype ω hω) φ

end Retained

end InteractingSLE.RLC.AStopSafe
