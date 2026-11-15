/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Assembly11Tau
import InteractingSLE.Spec.Coupling.ResampleBridge
import InteractingSLE.Spec.Coupling.Lemma311
import InteractingSLE.Spec.Sec7.LocalExtDGFF
import InteractingSLE.Spec.Sec7.Lemma71CTop
import InteractingSLE.Spec.Sec7.Lemma78MeanReal
import InteractingSLE.Spec.Coupling.LawUniqueHistory

/-!
# Lemma 7.1: the embedded pair as an optional hull coupling

Packet PROVE-LEMMA72. Specification §7.1, Lemma 7.1 (p. 223, `source/spec/p193-240.md` L576–L581): "The conditional
law of `η_ψ` is `SLE_κ(ρ^L; ρ^R)` with seed weights (CPF2) […] The joint pair with `h_ψ` has the original coupling
specification"; its proof, p. 225 (L600–L602): "For each bounded stopping time of this mapped path, the history-locality
statement of Lemma 6.2 applies […] The martingale characterization, Theorem 2.4, and integrated driving uniqueness
therefore give the stated conditional SLE law […] Its terminal capacity cannot be finite."

The landed pocket statements (`Lemma71C.Lemma71PocketChartStatement` and the forms reducing to it) give the coupling
clause of the mapped segment in the pocket chart. This file turns that clause into the **frozen optional hull
specification** for the pulled-back field `h_ψ`, on the same probability space and with the same field:

* generic, any force word (`Assembly`):
  * `usualAugmentation_eq_self`: a right-continuous filtration with the null sets at time `0` is its usual augmentation;
  * `condExp_clause_of_isCouplingCharFun`: the conditional-law conjunct at every stopping time of the frozen driving
    filtration, from the coupling clause at the stopping times of the usual augmentation (tower property on the
    driving-measurable avoidance event);
  * `isZBGFFProcess_of_isCouplingCharFun`: the GFF conjunct, from the clause at `τ = 0`;
  * **`isOptionalHullCoupling_of_isCouplingCharFun`**: evolution + clause + locality of `K_τ` ⇒ the frozen predicate;
* the pocket (`Pocket`, `Clean`):
  * `exists_isOptionalHullCoupling_pocket`: global driver, chart clause with infinite lifetime and locality ⇒ the pair
    `(W, h_ψ)` is an optional hull coupling of the two-seed word with the (CPF2) weights, with a transient trace;
  * `exists_global_pocketChart`: the chart clause killed at the terminal capacity time `T` (the landed form) ⇒ `T = ∞`
    almost surely and a global driver `W'` with the same clause;
  * **`exists_isOptionalHullCoupling_of_pocketChart`**: the composition, with the killed driving histories equal
    almost surely.

The locality of the hulls of `W` for `h_ψ` at the stopping times of the pocket filtration is a hypothesis of these
conditional helpers (Lemma 6.2's history locality in the original domain, transported by the pocket chart, p. 225); it
is the one clause of "the original coupling specification" that the chart clause does not contain. These helpers replace
no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71J

section Usual

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A right-continuous filtration whose time-zero σ-algebra contains the null sets is its own usual augmentation. -/
theorem usualAugmentation_eq_self (𝓖 : Filtration ℝ≥0 mΩ) [𝓖.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) :
    usualAugmentation 𝓖 P = 𝓖 := by
  have hN : Ito.nullAugmented 𝓖 P = 𝓖 := by
    refine Filtration.ext (funext fun t => ?_)
    show 𝓖 t ⊔ Ito.nullSets P = 𝓖 t
    refine sup_eq_left.2 (MeasurableSpace.generateFrom_le fun s hs => ?_)
    exact 𝓖.mono zero_le _ (hnull s hs.1 hs.2)
  rw [Ito.usualAugmentation_eq_rightCont, hN]
  exact Filtration.IsRightContinuous.eq

end Usual

section Clause

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The conditional-law conjunct of the frozen optional hull specification at every driving stopping time**, from
the coupling clause at the stopping times of the usual augmentation of the evolution's filtration. A driving stopping
time `τ < ζ`, read at `τ.untopD 0`, is a stopping time `τ'` of the usual augmentation with a larger σ-algebra; on the
driving-measurable event `E'` where `supp φ` avoids `K_τ` the right-hand side is driving-measurable, so the tower
property passes the identity from `𝓕_{τ'}` to the driving `𝓕_τ`. -/
theorem condExp_clause_of_isCouplingCharFun
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation 𝓕 P) W VL VR ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (uτ : Ω → ℂ → ℝ)
    (huτ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (uτ ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (uτ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, -, -, hE'sm⟩ :=
    Coupling.exists_drivingStopped_measurable hE hX φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply φ).comp hh)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (Coupling.norm_cexp_I_mul_ofReal _).le)
  have hτ𝓖 := Coupling.isStoppingTime_untopD_of_drivingFiltration hE hX hτ hτζ
  have hσle := Coupling.measurableSpace_driving_le_untopD hE hX hτ hτζ
  have hτζ' : ∀ᵐ ω ∂P, (((((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hcl := hcf _ hτ𝓖 hτζ' uτ huτ φ
  set g : Ω → ℂ := E'.indicator (Coupling.frozenRHS κ W uτ φ τ') with hg
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have hE'τ' : MeasurableSet[hτ𝓖.measurableSpace] E' := hσle _ hE'm
  -- on the larger σ-algebra, the indicator of the identity
  have h1 : condExp hτ𝓖.measurableSpace P (E'.indicator f) =ᵐ[P] g := by
    filter_upwards [condExp_indicator (m := hτ𝓖.measurableSpace) (μ := P) hfint hE'τ', hcl]
      with ω hω hω'
    rw [hω, hg]
    by_cases hmem : ω ∈ E'
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      exact hω' (hE'sub hmem)
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
  have hgint : Integrable g P := (integrable_condExp).congr h1
  -- the tower property
  have h2 : condExp hτ.measurableSpace P (E'.indicator f) =ᵐ[P] g := by
    have ht := condExp_condExp_of_le (μ := P) (f := E'.indicator f) hσle hτ𝓖.measurableSpace_le
    refine ht.symm.trans ?_
    refine (condExp_congr_ae h1).trans ?_
    rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le hgm hgint]
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [h2, hind, hE'ae] with ω hω2 hωi hω3 hdis
  have hω : ω ∈ E' := hω3 hdis
  have e1 : condExp hτ.measurableSpace P f ω = E'.indicator (condExp hτ.measurableSpace P f) ω :=
    (indicator_of_mem hω _).symm
  rw [e1, ← hωi, hω2, hg, indicator_of_mem hω]
  rfl

end Clause

section GFF

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The time-zero energy of the constant driver is the covariance of the zero-boundary GFF on `ℍ`. -/
theorem loewnerGreenEnergy_const_zero (φ : TestOn upperHalfPlaneOpens) :
    loewnerGreenEnergy (fun _ => 0) 0 φ = zeroGFFTestCov upperHalfPlaneOpens φ φ := by
  rw [← Coupling.greenEnergy0_eq_zeroGFFTestCov]
  have hfix : ∀ y, φ y ≠ 0 → QuantumZipper.fwdMap (fun _ => (0 : ℝ)) 0 y = y := fun y hy => by
    have hyH : y ∈ H := φ.tsupport_subset (subset_tsupport _ hy)
    have hy0 : y ≠ ((fun _ => (0 : ℝ)) 0 : ℂ) := by
      intro h0
      have hyH' : (0 : ℝ) < y.im := hyH
      rw [h0] at hyH'
      simp at hyH'
    rw [QuantumZipper.B5.fwdMap_zero_time (fun _ => (0 : ℝ)) hy0, Complex.ofReal_zero, sub_zero]
  unfold loewnerGreenEnergy Coupling.greenEnergy0
  congr 1
  funext y
  congr 1
  funext z
  by_cases hy : φ y = 0
  · simp only [hy, zero_mul]
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  rw [hfix y hy, hfix z hz]

/-- **The GFF conjunct from the coupling clause at time `0`.** If `h` satisfies the coupling clause
(`IsCouplingCharFun`, any filtration), the lifetime is almost surely positive, and almost surely the driver starts at
`0`, is continuous before the lifetime and the force points start at `xL`, `xR`, then `h − 𝔥₀` is a zero-boundary GFF
process on `ℍ` for every bounded harmonic extension `𝔥₀` of the time-zero data: each pairing has the law
`N(∫ 𝔥₀ φ, E₀(φ))` of the clause at `τ = 0` (`K₀ = ∅`), which is that of the reference field `fieldLaw0 𝔥₀`, and linear
random distributions with the same one-dimensional characteristic functions are equal in law
(`LocalExt.isZBGFFProcess_of_integral_cexp_eq`). -/
theorem isZBGFFProcess_of_isCouplingCharFun [IsProbabilityMeasure P] {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hh : Measurable h)
    (h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
      (∀ i, VL i 0 ω = xL i) ∧ ∀ i, VR i 0 ω = xR i)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P := by
  have hu₀c : ContinuousOn u₀ H := fun z hz => ((hu₀.1 z hz).1.continuousAt).continuousWithinAt
  have href := Coupling.isZBGFFProcess_fieldLaw0 hu₀c
  have hrefP : IsProbabilityMeasure (Coupling.fieldLaw0 u₀) := href.gaussian.isProbabilityMeasure
  -- the mean of the clause at time `0` is `𝔥₀`
  have hm := MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR 0 xL xR
  simp only [sub_zero] at hm
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) xL xR) hu₀ hm
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, MartChar.meanExt κ ρL ρR 0 xL xR z * φ z = ∫ z, u₀ z * φ z := fun φ => by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · simp only
      rw [heq (φ.tsupport_subset hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  -- equal laws of the pairings
  have hlaw : ∀ φ : TestOn upperHalfPlaneOpens,
      P.map (fun ω => h ω φ) = (Coupling.fieldLaw0 u₀).map (fun x => x φ) := fun φ => by
    rw [Coupling.MartMeans2.map_apply_eq_gaussianReal_of_isCouplingCharFun hcf h0 φ
        ((LQGMetric.measurable_distOn_apply φ).comp hh),
      Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess (h := fun x => x) href φ, hmean φ,
      loewnerGreenEnergy_const_zero φ]
  have e₁ : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₀ z * φ z =
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ := fun φ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eP : (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) = fun φ ω =>
      h ω φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ := by
    funext φ ω; rw [e₁ φ]
  have eR : (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, u₀ z * φ z) = fun φ x =>
      x φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ := by
    funext φ x; rw [e₁ φ]
  rw [eR] at href
  rw [eP]
  refine LocalExt.isZBGFFProcess_of_integral_cexp_eq (X := h) hh _ (X' := fun x => x) _ href fun φ => ?_
  rw [← e₁ φ]
  set c : ℝ := ∫ z, u₀ z * φ z
  have hF : Continuous fun x : ℝ => Complex.exp (Complex.I * ((x - c : ℝ) : ℂ)) := by fun_prop
  have hm1 : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh
  have h1 : ∫ y, Complex.exp (Complex.I * ((y - c : ℝ) : ℂ)) ∂(P.map fun ω => h ω φ) =
      ∫ ω, Complex.exp (Complex.I * ((h ω φ - c : ℝ) : ℂ)) ∂P :=
    integral_map hm1.aemeasurable hF.aestronglyMeasurable
  have h2 : ∫ y, Complex.exp (Complex.I * ((y - c : ℝ) : ℂ)) ∂((Coupling.fieldLaw0 u₀).map fun x => x φ) =
      ∫ x, Complex.exp (Complex.I * ((x φ - c : ℝ) : ℂ)) ∂(Coupling.fieldLaw0 u₀) :=
    integral_map (LQGMetric.measurable_distOn_apply φ).aemeasurable hF.aestronglyMeasurable
  rw [← h1, hlaw φ, h2]

end GFF

section Assembly

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The frozen optional hull specification from the coupling clause and locality.** An integrated evolution with an
almost surely positive lifetime, a measurable field satisfying the coupling clause at every stopping time of the usual
augmentation of the evolution's filtration, and the locality of `K_τ` at those stopping times, is an optional hull
coupling: the GFF conjunct is the clause at `τ = 0` (`isZBGFFProcess_of_isCouplingCharFun`) and the conditional-law
conjunct at the driving stopping times is `condExp_clause_of_isCouplingCharFun`. -/
theorem isOptionalHullCoupling_of_isCouplingCharFun
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hh : Measurable h)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation 𝓕 P) W VL VR ζ h)
    (hζ0 : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (usualAugmentation 𝓕 P) τ →
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) h P) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
      (∀ i, VL i 0 ω = xL i) ∧ ∀ i, VR i 0 ω = xR i := by
    filter_upwards [hE.2.2.2.2, hζ0] with ω hp hz
    exact ⟨hz, hp.2.2.2.1, hp.1, hp.2.1, hp.2.2.1⟩
  refine ⟨hE, hh, fun u₀ hu₀ => isZBGFFProcess_of_isCouplingCharFun hcf hh h0 hu₀,
    Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE, fun τ hτ hτζ => ⟨?_, fun uτ huτ φ =>
      condExp_clause_of_isCouplingCharFun hE hh hcf _ τ hτ hτζ uτ huτ φ⟩⟩
  exact hloc (fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0))
    (Coupling.isStoppingTime_untopD_of_drivingFiltration hE _ hτ hτζ)
    (hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h)

end Assembly

/-! ### The embedded pair of Lemma 7.1 -/

section Pocket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ θ₁ θ₂ : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **Lemma 7.1's embedded pair is an optional hull coupling, given the locality of its hulls** (specification §7.1,
p. 223: "The joint pair with `h_ψ` has the original coupling specification"). On a probability space with a
right-continuous filtration `𝓖` whose time-zero σ-algebra contains the null sets ("the filtration retaining the
complete outer curves", augmented), let
* `γ` be the mapped middle-curve segment (almost surely a continuous simple path in `ℍ̄` from `0` to `∞` whose real
  boundary times have empty interior), with a global continuous adapted driver `W`, `W₀ = 0`, generating every filled
  prefix of `γ`;
* `c` the `𝓖₀`-measurable pocket chart (conformal, lifts continuous on the pocket) and `h` the measurable field;
* the coupling clause of the two-seed word with the (CPF2) weights hold in the pocket (`IsChartCouplingCharFun`,
  infinite lifetime: Lemma 6.2's history locality, Remark 6.7's three-curve means, p. 225).
If the hulls of `W` at the stopping times of `𝓖` are local sets of the transported field
`h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′` (`Chart.chartTransport (c ω) 1 a k`), then `W` with its geometric force points, the
Brownian motion of the martingale characterization (Theorem 2.4) and the lifetime `∞` is an optional hull coupling
with field `h_ψ`, and `W` has a transient generating trace. -/
theorem exists_isOptionalHullCoupling_pocket (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      (fun _ => ⊤) c a k h)
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) P) :
    ∃ (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => cpf2RhoL κ θ₂) (fun _ => cpf2RhoR κ θ₁) P 𝓖 W
        (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) B ζ
        (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
      (∀ ω, ζ ω = ⊤) ∧ LP.HasTransientGeneratingTrace P W ζ := by
  have hL : -2 < cpf2RhoL κ θ₂ := neg_two_lt_cpf2RhoL hκ hκ4 hθ₂
  have hR : -2 < cpf2RhoR κ θ₁ := neg_two_lt_cpf2RhoR hκ hκ4 hθ₁
  have ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (Chart.chartTransport (hc ω) 1 a k (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport (hc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hc ω).continuousOn_lift_inv (hliftc ω))) 1 a k (h ω)
  have hmart := Coupling.MartMeans2.hasTwoSeedMartingaleMeans_of_isChartTransport hc hdom hfwd hliftm hliftc hh
    hW0 hWc hWa hcf ht
  have hE := MartChar.isIntegratedSLEEvolution_geom_of_couplingMean (ρL := fun _ : Fin 1 => cpf2RhoL κ θ₂)
    (ρR := fun _ : Fin 1 => cpf2RhoR κ θ₁) hκ Lemma71.isOrderedForceWord_twoSeed hW0 hWc hWa hmart
  set ζ : Ω → ℝ≥0∞ := fun ω => MartChar.thresholdTime (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
    (fun t => W t ω) (fun i t => MartChar.geomL W LP.twoSeedXL i t ω)
    (fun j t => MartChar.geomR W LP.twoSeedXR j t ω) with hζdef
  have hζ : ∀ ω, ζ ω = ⊤ := fun ω =>
    Lemma71.thresholdTime_eq_top_of_fin_one (ρL := fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (ρR := fun _ : Fin 1 => cpf2RhoR κ θ₁) hL hR _ _ _
  have hζe : ζ = fun _ => ⊤ := funext hζ
  have hψm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k
  have hcf' := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hc hdom hfwd hliftm hliftc hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn⟩) hcf ht
  have hU := usualAugmentation_eq_self 𝓖 hnull
  refine ⟨_, ζ, isOptionalHullCoupling_of_isCouplingCharFun hE hψm ?_ ?_ ?_, hζ, ?_⟩
  · rw [hU, hζe]; exact hcf'
  · exact Eventually.of_forall fun ω => by rw [hζ ω]; exact ENNReal.zero_lt_top
  · intro τ hτ hτζ
    rw [hU] at hτ
    refine hloc τ hτ (hτζ.mono fun ω hω => ?_)
    rw [hζ ω] at hω
    exact fun htop => by rw [htop] at hω; exact lt_irrefl _ hω
  · filter_upwards [Lemma71.ae_transientTrace_of_fwdHull_eq hW0 hWc hγ hK] with ω ⟨η, hη, hinf⟩
    exact ⟨η, by rw [hζ ω]; exact hη, fun _ => hinf⟩

end Pocket


section Clean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ θ₁ θ₂ : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **The pocket coupling with a global driver** (proof of Lemma 7.1, p. 225: "Its terminal capacity cannot be
finite"). From the chart form of the pocket coupling killed at the terminal capacity time `T` of the mapped segment
(the clauses of `Lemma71C.Lemma71PocketChartStatement`): `T = ∞` almost surely
(`Lemma71B.ae_eq_top_of_hasMartingaleMeansBefore` with the elementary hull bound), so on a `𝓖₀`-measurable full event
`G` the driver is global; replacing it by `0` off `G` gives a continuous adapted driver `W'` with the same filled
prefixes, and the chart coupling clause holds for `W'` with infinite lifetime. -/
theorem exists_global_pocketChart (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      T c a k h) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (G : Set Ω), MeasurableSet[𝓖 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧
      (∀ ω ∈ G, T ω = ⊤ ∧ ∀ t, W' t ω = W t ω) ∧
      (∀ ω, W' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W' t ω) ∧ StronglyAdapted 𝓖 W' ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
        fwdHull (fun s : ℝ => W' s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
        (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W' (MartChar.geomL W' LP.twoSeedXL)
        (MartChar.geomR W' LP.twoSeedXR) (fun _ => ⊤) c a k h := by
  classical
  have hL : -2 < cpf2RhoL κ θ₂ := neg_two_lt_cpf2RhoL hκ hκ4 hθ₂
  have hR : -2 < cpf2RhoR κ θ₁ := neg_two_lt_cpf2RhoR hκ hκ4 hθ₁
  have hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    filter_upwards [hγ, hK] with ω hγω hKω
    obtain ⟨hγc, -, hγH, hγ0, hγinf, hγR⟩ := hγω
    exact Lemma71B.unbounded_of_fwdHull_eq (hc ω) hγc hγH hγ0 hγinf hγR hKω
  have hm := Lemma71C.hasMartingaleMeansBefore_of_isChartTransport
    (h' := fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) hcc hdom hfwd hliftm hliftc hh hnull hW0 hc hWa
    hunb hcf fun ω => Chart.isChartTransport_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) 1 a k (h ω)
  have hT := Lemma71B.ae_eq_top_of_hasMartingaleMeansBefore hκ hL hR hm hW0 hc hWa hnull hunb
  -- the good event `G`, in `𝓖₀`, on which `T = ⊤`
  set Bad := {ω | ¬ T ω = ⊤} with hBad
  have hBad0 : P Bad = 0 := ae_iff.1 hT
  set G := (toMeasurable P Bad)ᶜ with hGdef
  have hG : MeasurableSet[𝓖 0] G :=
    (hnull _ (measurableSet_toMeasurable P Bad) (by rw [measure_toMeasurable]; exact hBad0)).compl
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono zero_le _ hG
  have hTG : ∀ ω ∈ G, T ω = ⊤ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P Bad h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hBad0
    rw [ae_iff]
    simpa only [compl_def] using hGc
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W t ω else 0 with hW'def
  have hW'G : ∀ ω ∈ G, ∀ t, W' t ω = W t ω := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'n : ∀ ω ∉ G, ∀ t, W' t ω = 0 := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hW'G ω hω, hW0]
    · exact hW'n ω hω 0
  have hW'c : ∀ ω, Continuous fun t => W' t ω := fun ω => by
    by_cases hω : ω ∈ G
    · have heq : (fun t => W' t ω) = fun t => W t ω := funext (hW'G ω hω)
      rw [heq]
      have hcu := hc ω
      have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < T ω} = univ := by
        ext t
        simp [hTG ω hω]
      rw [huniv] at hcu
      exact continuousOn_univ.1 hcu
    · have heq : (fun t => W' t ω) = fun _ => (0 : ℝ) := funext (hW'n ω hω)
      rw [heq]
      exact continuous_const
  have hW'a : StronglyAdapted 𝓖 W' := fun t => by
    have heq : (fun ω => W' t ω) = G.indicator (Girsanov.killed T W t) := funext fun ω => by
      by_cases hω : ω ∈ G
      · rw [hW'G ω hω, indicator_of_mem hω,
          Girsanov.killed_of_lt (by rw [hTG ω hω]; exact ENNReal.coe_lt_top)]
      · rw [hW'n ω hω, indicator_of_notMem hω]
    show StronglyMeasurable[𝓖 t] fun ω => W' t ω
    rw [heq]
    exact ((Girsanov.measurable_killed hWa t).indicator (hGt t)).stronglyMeasurable
  have hpath : ∀ ω ∈ G, (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω :=
    fun ω hω => funext fun s => hW'G ω hω _
  have hgeomL : ∀ ω ∈ G, ∀ i t, MartChar.geomL W' LP.twoSeedXL i t ω = MartChar.geomL W LP.twoSeedXL i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath (fun t ω => -W' t ω) ω = Bessel.realPath (fun t ω => -W t ω) ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [MartChar.geomL, this]
  have hgeomR : ∀ ω ∈ G, ∀ i t, MartChar.geomR W' LP.twoSeedXR i t ω = MartChar.geomR W LP.twoSeedXR i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath W' ω = Bessel.realPath W ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [MartChar.geomR, this]
  refine ⟨W', G, hG, hGae, fun ω hω => ⟨hTG ω hω, hW'G ω hω⟩, hW'0, hW'c, hW'a, ?_, ?_⟩
  · filter_upwards [hK, hGae] with ω hKω hω t ht
    obtain ⟨s, -, hs⟩ := hKω t ht
    refine ⟨s, s.coe_nonneg, ?_⟩
    rw [hpath ω hω]
    exact hs
  -- the chart clause for the global driver
  intro τ hτ hlt u' hu' φ
  set ρL : Fin 1 → ℝ := fun _ => cpf2RhoL κ θ₂ with hρL
  set ρR : Fin 1 → ℝ := fun _ => cpf2RhoR κ θ₁ with hρR
  set u : Ω → ℂ → ℝ := fun ω => if ω ∈ G then u' ω else
    MartChar.meanExt κ ρL ρR (W ((τ ω).untopD 0) ω) (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω)
      (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have h1 := hu' ω
      simp only [hgeomL ω hω, hgeomR ω hω, hW'G ω hω] at h1
      simp only [hudef, hω, ↓reduceIte]
      exact h1
    · simp only [hudef, hω, ↓reduceIte]
      exact MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  have hltT : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω := by
    filter_upwards [hlt, hGae] with ω h1 hω
    rw [hTG ω hω]
    exact h1
  have hold := hcf τ hτ hltT u hu φ
  filter_upwards [hold, hGae] with ω hω hωG hsub
  rw [hpath ω hωG] at hsub ⊢
  have huω : u ω = u' ω := by simp only [hudef, hωG, ↓reduceIte]
  rw [hω hsub, huω]

end Clean

/-! ### The composition -/

section Compose

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ θ₁ θ₂ : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- The left geometric force points of two drivers agree at a sample where the drivers agree. -/
theorem geomL_eq_of_forall_eq {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : ∀ t, W' t ω = W t ω) {nL : ℕ}
    (xL : Fin nL → ℝ) (i : Fin nL) (t : ℝ≥0) :
    MartChar.geomL W' xL i t ω = MartChar.geomL W xL i t ω := by
  have : Bessel.realPath (fun t ω => -W' t ω) ω = Bessel.realPath (fun t ω => -W t ω) ω :=
    funext fun s => by simp only [Bessel.realPath, hW]
  simp only [MartChar.geomL, this]

/-- The right geometric force points of two drivers agree at a sample where the drivers agree. -/
theorem geomR_eq_of_forall_eq {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : ∀ t, W' t ω = W t ω) {nR : ℕ}
    (xR : Fin nR → ℝ) (i : Fin nR) (t : ℝ≥0) :
    MartChar.geomR W' xR i t ω = MartChar.geomR W xR i t ω := by
  have : Bessel.realPath W' ω = Bessel.realPath W ω := funext fun s => by simp only [Bessel.realPath, hW]
  simp only [MartChar.geomR, this]

/-- **Lemma 7.1's embedded pair as an optional hull coupling, from the landed chart form of the pocket coupling**
(the clauses of `Lemma71C.Lemma71PocketChartStatement` on one space), given the locality of the hulls of the
mapped segment for `h_ψ` at the stopping times of the pocket filtration before the terminal capacity time. The
terminal capacity time is almost surely infinite; the global driver `W'` agrees with `W` almost surely
(`exists_global_pocketChart`), so its killed driving history is almost surely that of `(W, T)`. -/
theorem exists_isOptionalHullCoupling_of_pocketChart (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      T c a k h)
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) P) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => cpf2RhoL κ θ₂) (fun _ => cpf2RhoR κ θ₁) P 𝓖 W'
        (MartChar.geomL W' LP.twoSeedXL) (MartChar.geomR W' LP.twoSeedXR) B ζ
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) ∧
      LP.HasTransientGeneratingTrace P W' ζ ∧
      (fun ω => LawUnique.killedHistory W' (MartChar.geomL W' LP.twoSeedXL) (MartChar.geomR W' LP.twoSeedXR) ζ ω)
        =ᵐ[P] LawUnique.killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T := by
  obtain ⟨W', G, -, hGae, hGW, hW'0, hW'c, hW'a, hK', hcf'⟩ :=
    exists_global_pocketChart hκ hκ4 hθ₁ hθ₂ hnull hγ hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcf
  have hloc' : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) P := by
    intro τ hτ hfin
    have hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω := by
      filter_upwards [hfin, hGae] with ω h1 hω
      rw [(hGW ω hω).1]
      exact lt_top_iff_ne_top.2 h1
    refine Sec7.IsLocalSet.congr_ae (hloc τ hτ hlt) ?_
    filter_upwards [hGae] with ω hω
    have hp : (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω :=
      funext fun s => (hGW ω hω).2 _
    rw [hp]
  obtain ⟨B, ζ, hC, hζ, htr⟩ := exists_isOptionalHullCoupling_pocket hκ hκ4 hθ₁ hθ₂ hnull hγ hW'0 hW'c hW'a hK'
    hh hcc hdom hfwd hliftm hliftc hcf' hloc'
  refine ⟨W', B, ζ, hC, htr, ?_⟩
  filter_upwards [hGae] with ω hω
  obtain ⟨hT, hW⟩ := hGW ω hω
  simp only [LawUnique.killedHistory, hζ ω, hT, hW, geomL_eq_of_forall_eq hW, geomR_eq_of_forall_eq hW]

end Compose

end InteractingSLE.Sec7.Lemma71J
