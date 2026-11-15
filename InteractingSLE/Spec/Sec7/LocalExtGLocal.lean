/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField2Kernel
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.GFF.LocalSets.GermVersion
import InteractingSLE.Spec.Sec7.LocalExtA2Cond
import InteractingSLE.Spec.Sec5.Markov

/-!
# Aux. lemma 53: locality conditionally on the recorded history

Packet PROVE-LOCEXT-G. Specification p. 245, proof of Aux. lemma 53: "History marking permits retention of the canonical
germ of `K_τ`. Its zero-boundary residual field in the active component has the same law for every germ with that recorded
history, and is therefore independent of the germ conditionally on the history. … Forgetting that germ preserves
locality". This file proves the locality half **in the original domain, conditionally on any event of the stopped
history**:

* `condExp_cond_ae_eq`: if `E[X | 𝒢'] = c` with `c` `𝒢`-measurable (`𝒢 ≤ 𝒢'`), then under `P[· | D]` for `D ∈ 𝒢'`,
  `E[X | 𝒢] = c`;
* `condExp_germ_history_eq`: for the frozen coupling, a stopping time `σ < ζ` of its driving filtration and a
  hitting-measurable version `A` of `K_σ`, with `h⁰ = h − 𝔥₀` and the germ conditional mean `h₁` of Lemma 3.6, the
  residual `h⁰ − h₁` has the zero-boundary characteristic functional on `ℍ ∖ A` **given the germ and the stopped
  history** `𝒜 ∨ 𝓓_σ` (history marking `isHistoryAvoidanceLocal_hull` and the marked germ law
  `exists_condExp_germSigma_history` of PROVE-WHOLEFIELD2, with the tower property against Lemma 3.6 (iii));
* **`isLocalSet_cond`**: for every event `D ∈ 𝓓_σ` of positive probability, the hull `K_σ` is a local set of `h` under
  `P[· | D]` (Lemma 3.6 (iii) ⇒ (iv) under the conditioned measure);
* **`isLocalSet_cond_restart`**: after a restart at a finite stopping time `T`, for every restarted stop `τ' < ζ − T`
  and every event `D ∈ 𝓓_T` of positive probability, `K_{T+τ'}` is a local set of `h` under `P[· | D]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace LocalExt

/-! ### Conditional expectations under a conditioned measure -/

section CondMeasure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- **Conditional expectation under `P[· | D]`**: if `E[X | 𝒢'] = c` almost surely, with `c`
`𝒢`-measurable and integrable (`𝒢 ≤ 𝒢'`), then for every `D ∈ 𝒢'` of positive probability, `E_{P[·|D]}[X | 𝒢] = c` almost surely
under `P[· | D]`. -/
theorem condExp_cond_ae_eq {𝒢 𝒢' : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ 𝒢') (h𝒢' : 𝒢' ≤ mΩ) {D : Set Ω}
    (hD : MeasurableSet[𝒢'] D) (hPD : P D ≠ 0) {X c : Ω → ℂ} (hX : Integrable X P)
    (hc : StronglyMeasurable[𝒢] c) (hcI : Integrable c P) (hXc : P[X | 𝒢'] =ᵐ[P] c) :
    (P[|D])[X | 𝒢] =ᵐ[P[|D]] c := by
  have hm : 𝒢 ≤ mΩ := h𝒢.trans h𝒢'
  have hDm : MeasurableSet[mΩ] D := h𝒢' D hD
  have hfin : (P D)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hPD
  have hQ : P[|D] = (P D)⁻¹ • P.restrict D := rfl
  have hcI' : Integrable c (P[|D]) := by rw [hQ]; exact hcI.restrict.smul_measure hfin
  have hprob : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm ?_ (fun s _ _ => hcI'.integrableOn) ?_
    hc.aestronglyMeasurable).symm
  · rw [hQ]
    exact hX.restrict.smul_measure hfin
  · intro s hs _
    have hsm : MeasurableSet[mΩ] s := hm s hs
    have hsD : MeasurableSet[𝒢'] (s ∩ D) := (h𝒢 s hs).inter hD
    rw [hQ]
    simp only [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hsm]
    congr 1
    rw [← setIntegral_condExp h𝒢' hX hsD]
    exact setIntegral_congr_ae (h𝒢' _ hsD) (hXc.mono fun ω hω _ => hω.symm)

end CondMeasure

/-! ### The germ law given the germ and the stopped history -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

open WholeField LocalSets

/-- **The marked germ law** (Aux. lemma 53's "independent of the germ conditionally on the history"): for a
hitting-measurable version `A` of `K_σ` and a germ-measurable `h₁` with the germ conditional law of Lemma 3.6 (iii) for
the centred field `h⁰ = h − 𝔥₀`, the residual `h⁰ − h₁` has the zero-boundary characteristic functional on `ℍ ∖ A`
given the germ **and** the stopped history: `E[e^{i(h⁰ − h₁)(φ)} | 𝒜 ∨ 𝓓_σ] = E[e^{i(h⁰ − h₁)(φ)} | 𝒜]`. -/
theorem condExp_germ_history_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0))
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) {h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hh₁ : Measurable[germSigma A (centredField h u₀)] h₁)
    (hcond : IsCondZeroBoundaryGFF P (germSigma A (centredField h u₀)) (fun ω => H \ A ω)
      (fun ω => centredField h u₀ ω - h₁ ω)) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * ((centredField h u₀ ω - h₁ ω) φ : ℂ)) |
        germSigma A (centredField h u₀) ⊔ hσ.measurableSpace] =ᵐ[P]
      P[fun ω => Complex.exp (Complex.I * ((centredField h u₀ ω - h₁ ω) φ : ℂ)) |
        germSigma A (centredField h u₀)] := by
  set h0 := centredField h u₀ with hh0def
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h0 P := isZeroBoundaryGFF_centredField hC hu₀
  have hh0m : Measurable h0 := measurable_centredField hC.2.1 u₀
  have hH : hσ.measurableSpace ≤ mΩ := hσ.measurableSpace_le
  have hG : germSigma A h0 ≤ mΩ := germSigma_le hA hh0m
  have hGH : (germSigma A h0 ⊔ hσ.measurableSpace) ≤ mΩ := sup_le hG hH
  have hhist := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hσ hσζ hA hAK
  obtain ⟨M, hM, -, hMcf⟩ := exists_condExp_germSigma_history hh0 hA hH hhist hAc φ
  -- the germ-measurable factors
  have hh₁φ : Measurable[germSigma A h0] fun ω => h₁ ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh₁
  have he₁ : StronglyMeasurable[germSigma A h0] fun ω => Complex.exp (Complex.I * ((-(h₁ ω φ) : ℝ) : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω (germSigma A h0) _ hh₁φ.neg).stronglyMeasurable
  have heM : StronglyMeasurable[germSigma A h0] fun ω => Complex.exp (Complex.I * (M ω : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω (germSigma A h0) _ hM).stronglyMeasurable
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hh0φ : Measurable fun ω => h0 ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh0m
  have hEi : Integrable (fun ω => Complex.exp (Complex.I * (h0 ω φ : ℂ))) P :=
    Integrable.of_bound (GFF.measurable_exp_I_mul hh0φ).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hnorm _).le)
  -- the residual's characteristic function as a product
  have hF : (fun ω => Complex.exp (Complex.I * ((h0 ω - h₁ ω) φ : ℂ))) = fun ω =>
      Complex.exp (Complex.I * ((-(h₁ ω φ) : ℝ) : ℂ)) * Complex.exp (Complex.I * (h0 ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    change Complex.I * (((h0 ω φ - h₁ ω φ : ℝ)) : ℂ) = _
    push_cast
    ring
  set F := fun ω => Complex.exp (Complex.I * ((h0 ω - h₁ ω) φ : ℂ)) with hFdef
  have hFi : Integrable F P := by
    rw [hF]
    exact hEi.bdd_mul (he₁.mono hG).aestronglyMeasurable (Eventually.of_forall fun ω => (hnorm _).le)
  -- `Y = E[F | germ ∨ history]` and `Z = E[F | germ]`
  have hY : P[F | (germSigma A h0 ⊔ hσ.measurableSpace)] =ᵐ[P] fun ω => Complex.exp (Complex.I * ((-(h₁ ω φ) : ℝ) : ℂ)) *
      P[fun ω => Complex.exp (Complex.I * (h0 ω φ : ℂ)) | (germSigma A h0 ⊔ hσ.measurableSpace)] ω := by
    have hpull := condExp_bilin_of_stronglyMeasurable_left (m := (germSigma A h0 ⊔ hσ.measurableSpace)) (μ := P)
      (ContinuousLinearMap.mul ℝ ℂ) (he₁.mono le_sup_left) (by rw [hF] at hFi; simpa using hFi) hEi
    rw [hF]
    simpa [ContinuousLinearMap.mul_apply'] using hpull
  have hZ := hcond φ
  have hrel : ∀ᵐ ω ∂P, relClosureH (A ω) = A ω := by
    filter_upwards [hAc] with ω hω
    exact relClosureH_eq hω.1 hω.2
  -- `V = e^{-i h₁(φ)} e^{iM} Z` is germ-measurable and almost surely equal to `Y`
  set Z := P[F | germSigma A h0] with hZdef
  set V := fun ω => Complex.exp (Complex.I * ((-(h₁ ω φ) : ℝ) : ℂ)) * Complex.exp (Complex.I * (M ω : ℂ)) *
    Z ω with hVdef
  have hVm : StronglyMeasurable[germSigma A h0] V := (he₁.mul heM).mul stronglyMeasurable_condExp
  have hVi : Integrable V P := by
    refine (integrable_condExp (m := germSigma A h0) (μ := P) (f := F)).bdd_mul ((he₁.mul heM).mono hG).aestronglyMeasurable
      (c := 1) (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, hnorm, hnorm, one_mul]
  have hYV : P[F | (germSigma A h0 ⊔ hσ.measurableSpace)] =ᵐ[P] V := by
    filter_upwards [hY, hMcf, hZ, hrel] with ω h1 h2 h3 h4
    rw [h1, ← h2]
    simp only [hVdef]
    rw [h3, h4, mul_assoc]
  -- the tower property
  have htower : P[P[F | (germSigma A h0 ⊔ hσ.measurableSpace)] | germSigma A h0] =ᵐ[P] Z := condExp_condExp_of_le le_sup_left hGH
  have hVV : P[P[F | (germSigma A h0 ⊔ hσ.measurableSpace)] | germSigma A h0] =ᵐ[P] V := by
    refine (condExp_congr_ae hYV).trans ?_
    rw [condExp_of_stronglyMeasurable hG hVm hVi]
  exact hYV.trans (hVV.symm.trans htower)


/-- **Aux. lemma 53, locality conditionally on the stopped history** (original domain; specification p. 245: "History
marking permits retention of the canonical germ … Forgetting that germ preserves locality"). For a coupling satisfying
the frozen optional hull specification, a stopping time `σ < ζ` of its driving filtration and an event `D ∈ 𝓓_σ` of
positive probability, the hull `K_σ` is a local set of `h` under `P[· | D]`. -/
theorem isLocalSet_cond (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω)
    {D : Set Ω} (hD : MeasurableSet[hσ.measurableSpace] D) (hPD : P D ≠ 0) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) h (P[|D]) := by
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  obtain ⟨hX', hker⟩ := hC.2.2.2
  have hloc := (hker σ hσ hσζ).1
  obtain ⟨A, hA, hAK, hlocA⟩ := IsLocalSet.exists_measurable_version hloc hC.2.1
  have hT := isHarmonicDistOn_smoothDist hu₀.1
  have hloc0 : IsLocalSet A (centredField h (bheAt κ ρL ρR xL xR)) P := IsLocalSet.sub_dist hlocA hT
  have hAc := hloc0.2.1
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hh0m := measurable_centredField hC.2.1 (bheAt κ ρL ρR xL xR)
  obtain ⟨h₁, hh₁, hharm, hcond⟩ := ((isLocalSet_tfae hh0 hA hAc).out 4 3).1 hloc0
  have hG := germSigma_le hA hh0m
  have hH := hσ.measurableSpace_le
  have hprob : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hac : P[|D] ≪ P := cond_absolutelyContinuous
  have hiii : IsGermConditionalLaw A (centredField h (bheAt κ ρL ρR xL xR)) (P[|D]) := by
    refine ⟨h₁, hh₁, hac.ae_le hharm, fun φ => ?_⟩
    have hY := condExp_germ_history_eq hC hκ hu₀ hX hσ hσζ hA hAK hAc hh₁ hcond φ
    have hm1 : Measurable fun ω => (centredField h (bheAt κ ρL ρR xL xR) ω - h₁ ω) φ := by
      have h1 := (LQGMetric.measurable_distOn_apply φ).comp hh0m
      have h2 := (LQGMetric.measurable_distOn_apply φ).comp (hh₁.mono hG le_rfl)
      exact h1.sub h2
    have hFi : Integrable (fun ω => Complex.exp (Complex.I *
        ((centredField h (bheAt κ ρL ρR xL xR) ω - h₁ ω) φ : ℂ))) P :=
      Integrable.of_bound (GFF.measurable_exp_I_mul hm1).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le)
    have h2 := condExp_cond_ae_eq (le_sup_left : germSigma A _ ≤ germSigma A _ ⊔ hσ.measurableSpace)
      (sup_le hG hH) ((le_sup_right : hσ.measurableSpace ≤ germSigma A _ ⊔ hσ.measurableSpace) D hD) hPD hFi
      stronglyMeasurable_condExp integrable_condExp hY
    exact h2.trans (hac.ae_le (hcond φ))
  have hloc' := IsGermConditionalLaw.isLocalSet hA hh0m (hac.ae_le hAc) hiii
  have hloc'' := Coupling.IsLocalSet.add_dist hloc' hT
  have e : (fun ω => centredField h (bheAt κ ρL ρR xL xR) ω +
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (bheAt κ ρL ρR xL xR)) = h :=
    funext fun ω => sub_add_cancel _ _
  rw [e] at hloc''
  exact Coupling.IsLocalSet.congr_set hloc'' (hac.ae_le hAK.symm)


/-- **Aux. lemma 53, locality after a restart, conditionally on the history at the restart** (original domain): for a
finite stopping time `T` of the driving filtration `𝓓`, a stopping time `τ'` of the restarted filtration
`𝓖'_s = 𝓓_{T+s}` with `τ' < ζ − T`, and an event `D ∈ 𝓓_T` of positive probability, the hull `K_{T+τ'}` is a local set
of `h` under `P[· | D]`. -/
theorem isLocalSet_cond_restart (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (Sec2.Restart.restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < Sec5.Markov.restartLife ζ T ω) {D : Set Ω}
    (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + (τ ω).untopD 0 : ℝ≥0) : ℝ)) h (P[|D]) := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t, MeasurableSet[drivingFiltration P hX t] s :=
    fun s hs h0 t => Ito.measurableSet_usualAugmentation_of_null hs h0 t
  have hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [hτζ] with ω hω htop
    rw [htop] at hω
    exact not_top_lt hω
  have hσ := Sec5.Markov.isStoppingTime_restartTime hT hnull hτ hτfin
  have hσζ : ∀ᵐ ω ∂P, (Sec5.Markov.restartTime T τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hτζ, hτfin] with ω hω hfin
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hfin
    rw [← hr] at hω
    have h1 : ((T ω : ℝ≥0∞)) + (r : ℝ≥0∞) < ζ ω := lt_tsub_iff_left.1 hω
    show (((T ω + (τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω
    rw [← hr, WithTop.untopD_coe]
    exact_mod_cast h1
  have hDσ : MeasurableSet[hσ.measurableSpace] D := by
    rw [← Sec5.Markov.measurableSpace_restartTime_eq hT hnull hτ hτfin]
    have h0 : hT.measurableSpace ≤ hτ.measurableSpace := by
      rw [← Sec2.Restart.restartFiltration_zero hT]
      exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
    exact h0 D hD
  exact isLocalSet_cond hC hκ hX hσ hσζ hDσ hPD

end Coupling

end LocalExt

end InteractingSLE
