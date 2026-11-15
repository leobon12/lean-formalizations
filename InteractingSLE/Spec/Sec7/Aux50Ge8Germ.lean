/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Green
import InteractingSLE.Spec.Coupling.WholeField9Mean
import InteractingSLE.Spec.Sec7.LocalExtA3Var
import InteractingSLE.Spec.Sec7.LocalExtDCov

/-!
# Aux. lemma 50 for `κ ≥ 8`: the entire field given the hull germ at a stopping time, (HGV2)

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof, (HGV2) (`source/spec/p193-240.md` L837–L843, p. 236):
"The entire-field conditional Gaussian law of a marked local set gives, for `X_φ = (h, φ)`,
`N_t(φ) = E[X_φ | 𝒢_t]`, `Cov(X_φ, X_ψ | 𝒢_t) = G_{D_t}(φ, ψ)`. […] Here `N_t` is the full conditional mean
distribution, including the field already contained in the filled hull."

For the frozen coupling, a stopping time `τ < ζ` of the frozen driving filtration and a hitting-measurable version
`A` of the hull `K_τ`, with the history-marked germ `Γ_τ = Γ(𝓕_τ, A)` of PROVE-WHOLEFIELD2 and the centred field
`h⁰ = h − 𝔥₀`:

* **`ae_condExp_exp_germ_eq`** (HGV2, characteristic-function form, **every** test `φ`, including tests meeting the
  hull): `E[e^{i(h⁰,φ)} | Γ_τ] = e^{i E[(h⁰,φ) | Γ_τ]} e^{−G_{D_τ}(φ,φ)/2}`, read off the germ law
  `LocalSets.exists_condExp_germSigmaK` exactly as in `WholeField.ae_condExp_histGerm_hull_eq` (which keeps only the
  tests avoiding the hull);
* **`ae_condExp_mul_germ_eq`** (HGV2, covariance form): `E[(h⁰,φ)(h⁰,ψ) | Γ_τ] = N_τ(φ) N_τ(ψ) + G_{D_τ}(φ,ψ)`, with
  `G_{D_τ}(φ, ψ) = covAt W τ φ ψ` the covariance of the zero-boundary GFF on `ℍ ∖ K_τ`
  (`= ∬ φ(a) ψ(b) G_τ(a, b)` by `zeroGFFTestCov_actDom_eq`);
* **`ae_condExp_germ_eq_of_active`**: for a test avoiding `K_τ`, `N_τ(ψ)` is the driving conditional mean
  `E[(h,ψ) | 𝓕_τ]` minus `∫ u₀ ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper LQGMetric LocalSets WholeField Coupling

/-- **The conditional covariance form** `G_{D_t}(φ, ψ)` at the path of `ω`: the covariance of the zero-boundary GFF
on the active domain `ℍ ∖ K_t`. -/
def covAt {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (φ ψ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℝ :=
  zeroGFFTestCov (actDom (fun s : ℝ => W s.toNNReal ω) t) φ ψ

section Germ

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
theorem centredField_smul (u₀ : ℂ → ℝ) (c : ℝ) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) :
    centredField h u₀ ω (c • φ) = c * centredField h u₀ ω φ := by
  rw [map_smul, smul_eq_mul]

omit mΩ in
theorem centredField_add (u₀ : ℂ → ℝ) (φ ψ : TestOn upperHalfPlaneOpens) (ω : Ω) :
    centredField h u₀ ω (φ + ψ) = centredField h u₀ ω φ + centredField h u₀ ω ψ := by
  rw [map_add]

omit [IsProbabilityMeasure P] in
/-- The pairings of the centred field are square integrable. -/
theorem memLp_centredField (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (φ : TestOn upperHalfPlaneOpens) : MemLp (fun ω => centredField h u₀ ω φ) 2 P :=
  ((isZeroBoundaryGFF_centredField hC hu₀).process.gaussian.hasGaussianLaw_eval φ).memLp_two

omit [IsProbabilityMeasure P] in
theorem measurable_centredField_apply (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (u₀ : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) : Measurable (fun ω => centredField h u₀ ω φ) :=
  (Sobolev.measurable_distOn_apply φ).comp (measurable_centredField hC.2.1 u₀)

variable (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
  (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
  (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → ℝ≥0}
  (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0))
  (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
  (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω))

include hC hκ hu₀ hτζ hA hAK in
/-- **(HGV2), characteristic-function form, for every test**: given the history-marked germ at a stopping time, the
centred field is Gaussian with the germ conditional mean and the covariance of the zero-boundary GFF on `ℍ ∖ K_τ`,
also for tests meeting the hull. -/
theorem ae_condExp_exp_germ_eq (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => cexp (I * (centredField h u₀ ω φ : ℂ)) | histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      fun ω => cexp (I * ((P[fun ω' => centredField h u₀ ω' φ |
          histGerm hτ.measurableSpace A (centredField h u₀)]) ω : ℂ)) *
        ((Real.exp (-(1 / 2) * covAt W (τ ω) φ φ ω) : ℝ) : ℂ) := by
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτζ
  have hAK' : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      (((τ ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := hAK.mono fun ω hω => by rw [hω, WithTop.untopD_coe]
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ hτζ' hA hAK'
  have hmk := isCoverMarking_history hh0 hA hℋ hloc
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [((hC.2.2.2.choose_spec _ hτ hτζ').1).2.1, hAK'] with ω h1 h2
    rw [h2]
    exact h1
  have h𝒦tr : ∀ j, histGerm hτ.measurableSpace A (centredField h u₀) ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace) j A
        (centredField h u₀)) P := by
    intro j
    refine (iInf_le _ (j + 1)).trans (sup_le ?_ ?_)
    · exact (le_sup_right : hτ.measurableSpace ≤ MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace).trans
        ((le_sup_left : _ ≤ coverSigmaM _ j A (centredField h u₀)).trans (le_aeSigma _ P))
    · rw [← coverRad_eq j]
      exact germSigmaAt_le_aeSigmaM hh0 le_sup_left j
  have h𝒦le := histGerm_le (h := centredField h u₀) hℋ hA hh0.measurable
  obtain ⟨M, -, -, hM1, hM2⟩ := exists_condExp_germSigmaK hh0 hA hmk hAc
    (germSigma_le_histGerm A (centredField h u₀)) h𝒦le h𝒦tr φ
  filter_upwards [hM1, hM2, hAc, hAK] with ω e1 e2 hac hak
  rw [← e2, ← e1, relClosureH_eq hac.1 hac.2, hak]
  rfl

omit [IsProbabilityMeasure P] in
theorem condExp_const_mul' {m : MeasurableSpace Ω} (c : ℝ) (f : Ω → ℝ) :
    P[fun ω => c * f ω | m] =ᵐ[P] fun ω => c * (P[f | m]) ω :=
  condExp_smul (μ := P) c f m

omit [IsProbabilityMeasure P] in
include hC hτ hτζ in
/-- The active domain at the stopping time is almost surely open. -/
theorem ae_isOpen_actDom : ∀ᵐ ω ∂P, IsOpen (actDom (fun s : ℝ => W s.toNNReal ω) (τ ω)) := by
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτζ
  filter_upwards [((hC.2.2.2.choose_spec _ hτ hτζ').1).2.1] with ω h1
  simpa only [WithTop.untopD_coe] using h1.2

omit mΩ in
/-- Polarization of the Green form: `G(φ + ψ) = G(φ) + 2 G(φ, ψ) + G(ψ)`. -/
theorem covAt_add_add {ω : Ω} {t : ℝ≥0} (ho : IsOpen (actDom (fun s : ℝ => W s.toNNReal ω) t))
    (φ ψ : TestOn upperHalfPlaneOpens) :
    covAt W t (φ + ψ) (φ + ψ) ω = covAt W t φ φ ω + 2 * covAt W t φ ψ ω + covAt W t ψ ψ ω := by
  unfold covAt
  have hUH : actDom (fun s : ℝ => W s.toNNReal ω) t ⊆ H := sdiff_subset
  rw [LocalExt.zeroGFFTestCov_add_left ho hUH, LocalExt.zeroGFFTestCov_add_right ho hUH,
    LocalExt.zeroGFFTestCov_add_right ho hUH, LocalExt.zeroGFFTestCov_comm ho hUH ψ φ]
  ring

omit mΩ in
theorem covAt_smul_smul {ω : Ω} {t : ℝ≥0} (ho : IsOpen (actDom (fun s : ℝ => W s.toNNReal ω) t)) (c : ℝ)
    (φ : TestOn upperHalfPlaneOpens) : covAt W t (c • φ) (c • φ) ω = c ^ 2 * covAt W t φ φ ω := by
  unfold covAt
  have hUH : actDom (fun s : ℝ => W s.toNNReal ω) t ⊆ H := sdiff_subset
  rw [LocalExt.zeroGFFTestCov_smul_left ho hUH, LocalExt.zeroGFFTestCov_smul_right ho hUH]
  ring

include hC hκ hu₀ hτζ hA hAK in
/-- **(HGV2), conditional second moment**: `E[(h⁰, φ)² | Γ_τ] = G_{D_τ}(φ, φ) + N_τ(φ)²`. -/
theorem ae_condExp_sq_germ_eq (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => (centredField h u₀ ω φ) ^ 2 | histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      fun ω => covAt W (τ ω) φ φ ω + ((P[fun ω' => centredField h u₀ ω' φ |
          histGerm hτ.measurableSpace A (centredField h u₀)]) ω) ^ 2 := by
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  have hΓle : histGerm hτ.measurableSpace A (centredField h u₀) ≤ mΩ :=
    histGerm_le hτ.measurableSpace_le hA hh0.measurable
  have hY := measurable_centredField_apply hC u₀ φ
  have h2 := memLp_centredField hC hu₀ φ
  have hc : ∀ c : ℝ, P[fun ω => cexp (I * ((c * centredField h u₀ ω φ : ℝ) : ℂ)) |
      histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      fun ω => LocalExt.cfVal (c * (P[fun ω' => centredField h u₀ ω' φ |
          histGerm hτ.measurableSpace A (centredField h u₀)]) ω) (c ^ 2 * covAt W (τ ω) φ φ ω) := by
    intro c
    have e1 : (fun ω => cexp (I * ((c * centredField h u₀ ω φ : ℝ) : ℂ))) =
        fun ω => cexp (I * (centredField h u₀ ω (c • φ) : ℂ)) := by
      funext ω; rw [centredField_smul]
    have e0 : (fun ω' => centredField h u₀ ω' (c • φ)) = fun ω' => c * centredField h u₀ ω' φ := by
      funext ω'; rw [centredField_smul]
    have e2 := condExp_const_mul' (P := P) (m := histGerm hτ.measurableSpace A (centredField h u₀)) c
      (fun ω' => centredField h u₀ ω' φ)
    rw [← e0] at e2
    rw [e1]
    filter_upwards [ae_condExp_exp_germ_eq hC hκ hu₀ hX hτ hτζ hA hAK (c • φ), e2,
      ae_isOpen_actDom hC hX hτ hτζ] with ω k1 k2 ho
    rw [k1, k2, covAt_smul_smul ho, LocalExt.cfVal, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : Integrable (fun ω => (centredField h u₀ ω φ - 0) ^ 2) P := by
    simpa only [sub_zero] using h2.integrable_sq
  have key := LocalExt.ae_condExp_sq_sub_of_condGauss hΓle hY hc 0 hint
  simp only [sub_zero] at key
  exact key

include hC hκ hu₀ hτζ hA hAK in
/-- **(HGV2), covariance form**: `E[(h⁰, φ)(h⁰, ψ) | Γ_τ] = N_τ(φ) N_τ(ψ) + G_{D_τ}(φ, ψ)`. -/
theorem ae_condExp_mul_germ_eq (φ ψ : TestOn upperHalfPlaneOpens) :
    P[fun ω => centredField h u₀ ω φ * centredField h u₀ ω ψ |
        histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      fun ω => (P[fun ω' => centredField h u₀ ω' φ | histGerm hτ.measurableSpace A (centredField h u₀)]) ω *
          (P[fun ω' => centredField h u₀ ω' ψ | histGerm hτ.measurableSpace A (centredField h u₀)]) ω +
        covAt W (τ ω) φ ψ ω := by
  have hsq : ∀ χ : TestOn upperHalfPlaneOpens, Integrable (fun ω => centredField h u₀ ω χ ^ 2) P := fun χ =>
    (memLp_centredField hC hu₀ χ).integrable_sq
  have hint : ∀ χ : TestOn upperHalfPlaneOpens, Integrable (fun ω => centredField h u₀ ω χ) P := fun χ =>
    (memLp_centredField hC hu₀ χ).integrable one_le_two
  have epol : (fun ω => centredField h u₀ ω φ * centredField h u₀ ω ψ) =
      fun ω => (1 / 2 : ℝ) * ((fun ω => centredField h u₀ ω (φ + ψ) ^ 2) - (fun ω => centredField h u₀ ω φ ^ 2) -
        (fun ω => centredField h u₀ ω ψ ^ 2)) ω := by
    funext ω
    simp only [Pi.sub_apply, centredField_add]
    ring
  have h1 := condExp_const_mul' (P := P) (m := histGerm hτ.measurableSpace A (centredField h u₀)) (1 / 2 : ℝ)
    ((fun ω => centredField h u₀ ω (φ + ψ) ^ 2) - (fun ω => centredField h u₀ ω φ ^ 2) -
      (fun ω => centredField h u₀ ω ψ ^ 2))
  have h2 := condExp_sub (m := histGerm hτ.measurableSpace A (centredField h u₀))
    ((hsq (φ + ψ)).sub (hsq φ)) (hsq ψ)
  have h3 := condExp_sub (m := histGerm hτ.measurableSpace A (centredField h u₀)) (hsq (φ + ψ)) (hsq φ)
  have e4 : (fun ω => centredField h u₀ ω (φ + ψ)) =
      (fun ω => centredField h u₀ ω φ) + fun ω => centredField h u₀ ω ψ := by
    funext ω; simp only [Pi.add_apply, centredField_add]
  have h4 := condExp_add (m := histGerm hτ.measurableSpace A (centredField h u₀)) (hint φ) (hint ψ)
  rw [← e4] at h4
  rw [epol]
  filter_upwards [h1, h2, h3, h4, ae_condExp_sq_germ_eq hC hκ hu₀ hX hτ hτζ hA hAK (φ + ψ),
    ae_condExp_sq_germ_eq hC hκ hu₀ hX hτ hτζ hA hAK φ, ae_condExp_sq_germ_eq hC hκ hu₀ hX hτ hτζ hA hAK ψ,
    ae_isOpen_actDom hC hX hτ hτζ] with ω k1 k2 k3 k4 k5 k6 k7 ho
  rw [k1, k2]
  simp only [Pi.sub_apply]
  rw [k3]
  simp only [Pi.sub_apply]
  rw [k5, k6, k7, k4]
  simp only [Pi.add_apply]
  rw [covAt_add_add ho]
  ring

include hC hu₀ hτζ hA hAK in
/-- **An active test**: on `{supp ψ ∩ K_τ = ∅}` the germ conditional mean of `(h⁰, ψ)` is the driving conditional
mean of `(h, ψ)` minus `∫ u₀ ψ`. -/
theorem ae_condExp_germ_eq_of_active (hκ : 0 < κ) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω)) →
      (P[fun ω' => centredField h u₀ ω' ψ | histGerm hτ.measurableSpace A (centredField h u₀)]) ω =
        (P[fun ω' => h ω' ψ | hτ.measurableSpace]) ω - ∫ z, u₀ z * ψ z := by
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτζ
  have hAK' : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      (((τ ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := hAK.mono fun ω hω => by rw [hω, WithTop.untopD_coe]
  obtain ⟨k1, -⟩ := ae_condExp_histGerm_hull_eq hC hκ hu₀ hX hτ hτζ' hA hAK'
    (u := fun ω => bheAt κ ρL ρR (W (τ ω) ω) (fun i => VL i (τ ω) ω) (fun i => VR i (τ ω) ω))
    (fun ω => by simp only [WithTop.untopD_coe]; exact bheAt_spec κ ρL ρR _ _ _) ψ
  filter_upwards [k1, ae_condExp_pairing_eq_actMean hC hX hτ hτζ ψ, hAK] with ω e1 e2 hak hd
  rw [e2 hd]
  have hd' : Disjoint (tsupport ψ) (A ω) := by rw [hak]; exact hd
  rw [e1 hd']
  simp only [WithTop.untopD_coe]
  rfl

end Germ

end Aux50Ge8

end InteractingSLE
