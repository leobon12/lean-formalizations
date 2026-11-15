/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentLift
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Supplement.GW2JointKernelLaw
import InteractingSLE.Spec.Supplement.GB6RelDetGood

/-!
# Optional hull couplings lift along a first factor in any universe; the two canonical counterflow drivers agree

Packet PROVE-T14-BR (for `Theorem14.GW2Later.GB6PrefixPairStatement`). Two canonical drivers of the flow line of a
GFF are available in the project:

* the canonical driver code `F` of `Restart.IsCanonicalDriverCode` (its coupling and determination clauses quantify
  over sample spaces in `Type`);
* the field-determined driver `drvOf (detCode (paramΦ h12p …) (word, ·))` of `Exist.Staged` (`Exist.Staged.stagedDrv`),
  read off Theorem 1.2 at universe `u` (`Theorem12ParamStatement.{u}`), which is an optional hull coupling on every
  sample space in `Type u` (`Exist.Staged.isOptionalHullCoupling_drv`).

**`ae_drvOf_eq_drvDec`**: under the GFF law of a sorted word, the two agree (same lifetime, same path before it).
Proof: the canonical code's coupling on `(DistOn, gffLaw)` (`GW2JointKernel.isFlowLineDriver_gffLaw`) is lifted to the
space `DistOn × ULift.{u} PUnit` in `Type u` (`isOptionalHullCoupling_fstU`), where Theorem 1.2 at universe `u`
identifies the field-determined code (`Exist.Staged.ae_detCode_eq`).

`isLocalSet_fstU`, `exists_stop_factorU`, `hullClauses_fstU`, `isOptionalHullCoupling_fstU` are verbatim copies of
`Restart.FlowStopIdentLift.isLocalSet_fst`, `exists_stop_factor`, `hullClauses_fst`, `isOptionalHullCoupling_fst`
(PROVE-L1-CM), whose second factor is fixed in `Type`; here it lives in any universe `Type v`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Theorem14

namespace BRLeaf

open Restart Restart.FlowStopIdentLift


/-! ### Conditional expectations and local-set witnesses along `ULift` -/

/-- **Conditional expectation along a measurable equivalence.** -/
theorem condExp_comp_measurableEquiv {α β : Type*} {𝒢 : MeasurableSpace β} [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] (e : α ≃ᵐ β) {P : Measure β} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mβ) {f : β → ℂ}
    (hf : Integrable f P) :
    condExp (MeasurableSpace.comap e 𝒢) (P.map e.symm) (f ∘ e) =ᵐ[P.map e.symm] (condExp 𝒢 P f) ∘ e := by
  have hm : MeasurableSpace.comap e 𝒢 ≤ mα := (MeasurableSpace.comap_mono h𝒢).trans e.measurable.comap_le
  have hcomp : ∀ g : β → ℂ, (g ∘ e) ∘ e.symm = g := fun g => by
    funext y; simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  have hint : ∀ g : β → ℂ, Integrable g P → Integrable (g ∘ e) (P.map e.symm) := fun g hg => by
    rw [integrable_map_equiv, hcomp]; exact hg
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hint f hf)
    (fun s _ _ => (hint _ integrable_condExp).integrableOn) (fun s hs _ => ?_) ?_).symm
  · obtain ⟨t, ht, rfl⟩ := hs
    rw [setIntegral_map_equiv, setIntegral_map_equiv]
    have e1 : e.symm ⁻¹' (e ⁻¹' t) = t := by
      ext y; simp only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply]
    simp only [e1, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    exact setIntegral_condExp h𝒢 hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable (comap_measurable (⇑e))).aestronglyMeasurable

/-- The image of `μ.map e.symm` under `F ∘ e` is the image of `μ` under `F`, for any `F` (a measurable equivalence). -/
theorem map_map_symm_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (e : α ≃ᵐ β) (μ : Measure β) (F : β → γ) : (μ.map e.symm).map (F ∘ e) = μ.map F := by
  have hc : (F ∘ e) ∘ e.symm = F := by funext y; simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  by_cases hF : AEMeasurable F μ
  · have hg : AEMeasurable (F ∘ e) (μ.map e.symm) := by
      rw [aemeasurable_map_equiv_iff, hc]; exact hF
    rw [AEMeasurable.map_map_of_aemeasurable hg e.symm.measurable.aemeasurable, hc]
  · have hg : ¬ AEMeasurable (F ∘ e) (μ.map e.symm) := by
      rw [aemeasurable_map_equiv_iff, hc]; exact hF
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp
    · have hμ' : μ.map e.symm ≠ 0 := fun h0 =>
        hμ ((Measure.map_eq_zero_iff e.symm.measurable.aemeasurable).1 h0)
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg hμ', Measure.map_of_not_aemeasurable_of_ne_zero hF hμ]

/-- **A local-set witness space can be lifted to a larger universe** (through `ULift`). -/
theorem exists_localSetWitness_ulift {Ω' : Type u} [mΩ' : MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {A' : Ω' → Set ℂ} {h₁ h₂ : Ω' → DistOn upperHalfPlaneOpens}
    (hm1 : @Measurable _ _ _ hittingSigma A') (hm2 : Measurable h₁) (hm3 : Measurable h₂)
    (hsub : ∀ ω', A' ω' ⊆ H ∧ IsOpen (H \ A' ω'))
    (hharm : ∀ᵐ ω' ∂P', IsHarmonicDistOn (h₁ ω') (H \ A' ω'))
    (hcond : IsCondZeroBoundaryGFF P' (MeasurableSpace.comap A' hittingSigma ⊔
      MeasurableSpace.comap h₁ inferInstance) (fun ω' => H \ A' ω') h₂) :
    ∃ (Ω'' : Type (max u v)) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (_ : IsProbabilityMeasure P'')
      (A'' : Ω'' → Set ℂ) (g₁ g₂ : Ω'' → DistOn upperHalfPlaneOpens),
      @Measurable _ _ _ hittingSigma A'' ∧ Measurable g₁ ∧ Measurable g₂ ∧
      (∀ ω'', A'' ω'' ⊆ H ∧ IsOpen (H \ A'' ω'')) ∧
      (∀ᵐ ω'' ∂P'', IsHarmonicDistOn (g₁ ω'') (H \ A'' ω'')) ∧
      IsCondZeroBoundaryGFF P'' (MeasurableSpace.comap A'' hittingSigma ⊔
          MeasurableSpace.comap g₁ inferInstance) (fun ω'' => H \ A'' ω'') g₂ ∧
      @Measure.map _ _ _ (hittingSigma.prod inferInstance)
          (fun ω'' => (A'' ω'', g₁ ω'' + g₂ ω'')) P'' =
        @Measure.map _ _ _ (hittingSigma.prod inferInstance) (fun ω' => (A' ω', h₁ ω' + h₂ ω')) P' := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set e : ULift.{v} Ω' ≃ᵐ Ω' := MeasurableEquiv.ulift with he
  have : IsProbabilityMeasure (P'.map e.symm) :=
    (Measure.isProbabilityMeasure_map_iff e.symm.measurable.aemeasurable).2 inferInstance
  refine ⟨ULift.{v} Ω', inferInstance, P'.map e.symm, inferInstance, A' ∘ e, h₁ ∘ e, h₂ ∘ e,
    hm1.comp e.measurable, hm2.comp e.measurable, hm3.comp e.measurable, fun x => hsub (e x), ?_, ?_, ?_⟩
  · rw [e.symm.measurableEmbedding.ae_map_iff]
    filter_upwards [hharm] with ω' hω'
    simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using hω'
  · intro φ
    have hσ : MeasurableSpace.comap (A' ∘ e) hittingSigma ⊔ MeasurableSpace.comap (h₁ ∘ e) inferInstance =
        MeasurableSpace.comap e (MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance) := by
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    have h𝒢 : MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance ≤ mΩ' :=
      sup_le hm1.comap_le hm2.comap_le
    have hfm : Measurable fun ω' => Complex.exp (Complex.I * (h₂ ω' φ : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((LQGMetric.measurable_distOn_apply φ).comp hm3)))
    have hfi : Integrable (fun ω' => Complex.exp (Complex.I * (h₂ ω' φ : ℂ))) P' :=
      Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun ω' => by
        show ‖Complex.exp (Complex.I * (h₂ ω' φ : ℂ))‖ ≤ 1
        rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le)
    have h1 := condExp_comp_measurableEquiv e h𝒢 hfi
    rw [hσ]
    refine h1.trans ?_
    have h2 : ∀ᵐ x ∂(P'.map e.symm), condExp (MeasurableSpace.comap A' hittingSigma ⊔
        MeasurableSpace.comap h₁ inferInstance) P' (fun ω' => Complex.exp (Complex.I * (h₂ ω' φ : ℂ))) (e x) =
        ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ A' (e x)) φ φ) : ℝ) : ℂ) := by
      rw [e.symm.measurableEmbedding.ae_map_iff]
      filter_upwards [hcond φ] with ω' hω'
      simpa only [MeasurableEquiv.apply_symm_apply] using hω'
    filter_upwards [h2] with x hx
    simpa only [Function.comp_apply] using hx
  · exact map_map_symm_comp e P' (fun ω' => (A' ω', h₁ ω' + h₂ ω'))

section Lift

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {C : Type v} [mC : MeasurableSpace C] {P : Measure Ω}
  {μ : Measure (Ω × C)}

/-! ### Local sets -/

/-- **Local sets lift along `fst`** (copy of `isLocalSet_fst` in any universe; the witness space is lifted
by `exists_localSetWitness_ulift`): if `A` is a local set of `h` under `P = μ.map fst`, then every `A'` that agrees
`μ`-almost surely with `A ∘ fst` is a local set of `h ∘ fst` under `μ`. -/
theorem isLocalSet_fstU (hμ : μ.map Prod.fst = P) {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hA : IsLocalSet A h P) {A' : Ω × C → Set ℂ} (hAA : ∀ᵐ p ∂μ, A' p = A p.1) :
    IsLocalSet A' (fun p => h p.1) μ := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A'', h₁, h₂, hm1, hm2, hm3, hsub', hharm, hcond, hlaw⟩ := hA
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) μ := measurable_fst.aemeasurable
  have hAEμ : AEMeasurable (fun ω => (A ω, h ω)) (μ.map Prod.fst) := by rw [hμ]; exact hAE
  have hAE' : AEMeasurable (fun p : Ω × C => (A p.1, h p.1)) μ := hAEμ.comp_aemeasurable hfst
  have hcongr : (fun p : Ω × C => (A' p, h p.1)) =ᵐ[μ] fun p => (A p.1, h p.1) := by
    filter_upwards [hAA] with p hp
    rw [hp]
  obtain ⟨Ω'', mΩ'', P'', hP'', A₀, g₁, g₂, hn1, hn2, hn3, hsub'', hharm', hcond', hlaw'⟩ :=
    exists_localSetWitness_ulift.{u, max u v} hm1 hm2 hm3 hsub' hharm hcond
  refine ⟨hAE'.congr hcongr.symm, ?_, Ω'', mΩ'', P'', hP'', A₀, g₁, g₂, hn1, hn2, hn3, hsub'', hharm', hcond', ?_⟩
  · have h1 : ∀ᵐ p ∂μ, A p.1 ⊆ H ∧ IsOpen (H \ A p.1) := ae_of_ae_map hfst (by rw [hμ]; exact hsub)
    filter_upwards [h1, hAA] with p hp hpA
    rw [hpA]
    exact hp
  · rw [hlaw', hlaw, Measure.map_congr hcongr, ← hμ, AEMeasurable.map_map_of_aemeasurable hAEμ hfst]
    rfl


/-! ### The hull clauses at a lifted stopping time -/

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Doob–Dynkin for the lifted driving filtration**: an almost surely finite stopping time of the driving filtration
of the killed driving read through `fst` is almost surely `s ∘ fst` for a finite stopping time `s` of the driving
filtration on `Ω`. -/
theorem exists_stop_factorU (hμ : μ.map Prod.fst = P) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω × C → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration μ (Exist.isMeasurableKilledDriving_comp hX measurable_fst)) τ)
    (hτfin : ∀ᵐ p ∂μ, τ p ≠ ⊤) :
    ∃ s : Ω → ℝ≥0, IsStoppingTime (drivingFiltration P hX) (fun ω => (s ω : WithTop ℝ≥0)) ∧
      ∀ᵐ p ∂μ, τ p = (s p.1 : WithTop ℝ≥0) := by
  have hτ' : IsStoppingTime (usualAugmentation (Exist.filtrationComap Prod.fst measurable_fst
      (killedDrivingFiltration hX)) μ) τ := by
    rw [← Exist.drivingFiltration_comp hX measurable_fst μ]
    exact hτ
  obtain ⟨s, hs, hτs⟩ := Exist.exists_isStoppingTime_ae_eq_comp measurable_fst hμ hτ' hτfin
  exact ⟨s, hs, hτs⟩

/-- **The local-set and conditional-law clauses at a lifted stopping time.** If `τ` is a stopping time of the driving
filtration of the killed driving read through `fst`, almost surely `s ∘ fst` for a stopping time `s` on `Ω` at which
the two hull clauses of the frozen optional hull specification hold (and before which the driver is continuous), then
they hold at `τ` under `μ` for the field read through `fst`. -/
theorem hullClauses_fstU [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
    (hhm : Measurable h) (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω × C → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration μ (Exist.isMeasurableKilledDriving_comp hX measurable_fst)) τ)
    {s : Ω → ℝ≥0} (hs : IsStoppingTime (drivingFiltration P hX) fun ω => (s ω : WithTop ℝ≥0))
    (hτs : ∀ᵐ p ∂μ, τ p = (s p.1 : WithTop ℝ≥0))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 (s ω : ℝ)))
    (hloc : IsLocalSet (fun ω => fwdHull (fun r : ℝ => W r.toNNReal ω)
      (((s ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) h P)
    (hker : ∀ u : Ω → ℂ → ℝ,
      (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR
            (fun i => VL i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω)
            (fun i => VR i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω))
          (forceJumpSet
            (fun i => VL i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω)
            (fun i => VR i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω))
          (u ω)) →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Disjoint (tsupport φ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (((s ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) →
          condExp hs.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω)
                (((s ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω)
                (((s ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))) :
    IsLocalSet (fun p => fwdHull (fun r : ℝ => W r.toNNReal p.1) ((τ p).untopD 0 : ℝ≥0)) (fun p => h p.1) μ ∧
      ∀ u : Ω × C → ℂ → ℝ,
        (∀ p, IsBoundedHarmonicExtension
            (forceBoundaryData κ ρL ρR (fun i => VL i ((τ p).untopD 0) p.1 - W ((τ p).untopD 0) p.1)
              (fun i => VR i ((τ p).untopD 0) p.1 - W ((τ p).untopD 0) p.1))
            (forceJumpSet (fun i => VL i ((τ p).untopD 0) p.1 - W ((τ p).untopD 0) p.1)
              (fun i => VR i ((τ p).untopD 0) p.1 - W ((τ p).untopD 0) p.1))
            (u p)) →
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂μ,
          Disjoint (tsupport φ) (fwdHull (fun r : ℝ => W r.toNNReal p.1) ((τ p).untopD 0 : ℝ≥0)) →
            condExp hτ.measurableSpace μ (fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ))) p =
              Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal p.1)
                  ((τ p).untopD 0 : ℝ≥0) (u p) z * φ z : ℝ) : ℂ) -
                (((1 / 2 : ℝ) * loewnerGreenEnergy (fun r : ℝ => W r.toNNReal p.1)
                  ((τ p).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) μ := measurable_fst.aemeasurable
  have hτ' : IsStoppingTime (usualAugmentation (Exist.filtrationComap Prod.fst measurable_fst
      (killedDrivingFiltration hX)) μ) τ := by
    rw [← Exist.drivingFiltration_comp hX measurable_fst μ]
    exact hτ
  -- the hulls agree almost surely
  have hhull : ∀ᵐ p ∂μ, fwdHull (fun r : ℝ => W r.toNNReal p.1) ((τ p).untopD 0 : ℝ≥0) =
      fwdHull (fun r : ℝ => W r.toNNReal p.1) (((s p.1 : WithTop ℝ≥0)).untopD 0 : ℝ≥0) := by
    filter_upwards [hτs] with p hp
    rw [hp]
  refine ⟨isLocalSet_fstU hμ hloc hhull, fun u hu φ => ?_⟩
  -- the canonical bounded harmonic extensions at `s`
  set u₀ : Ω → ℂ → ℝ := fun ω => MartChar.meanExt κ ρL ρR (W (s ω) ω) (fun i => VL i (s ω) ω)
    (fun j => VR j (s ω) ω) with hu₀def
  have hu₀ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => VL i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet
        (fun i => VL i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i (((s ω : WithTop ℝ≥0)).untopD 0) ω - W (((s ω : WithTop ℝ≥0)).untopD 0) ω))
      (u₀ ω) := fun ω => by
    simp only [WithTop.untopD_coe]
    exact MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  have hk := hker u₀ hu₀ φ
  have hk' := ae_of_ae_map hfst (by rw [hμ]; exact hk)
  -- the conditional expectations transfer
  set g : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hgdef
  have hgm : Measurable g := Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp ((Sobolev.measurable_distOn_apply φ).comp hhm)))
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      show ‖Complex.exp (Complex.I * (h ω φ : ℂ))‖ ≤ 1
      rw [mul_comm]
      exact (Complex.norm_exp_ofReal_mul_I _).le)
  have hce := Exist.condExp_comp_ae_eq measurable_fst hμ hs hτ' hτs hgi
  have hms : hτ.measurableSpace = hτ'.measurableSpace :=
    Exist.measurableSpace_congr (Exist.drivingFiltration_comp hX measurable_fst μ) hτ hτ'
  have hcont' : ∀ᵐ p ∂μ, ContinuousOn (fun r : ℝ => W r.toNNReal p.1) (Icc 0 (s p.1 : ℝ)) :=
    ae_of_ae_map (p := fun ω => ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 (s ω : ℝ))) hfst
      (by rw [hμ]; exact hcont)
  filter_upwards [hce, hk', hτs, hcont'] with p hp1 hp2 hp3 hwc hdisj
  have hst : (τ p).untopD 0 = s p.1 := by rw [hp3, WithTop.untopD_coe]
  rw [hst] at hdisj ⊢
  have hdisj' : Disjoint (tsupport φ) (fwdHull (fun r : ℝ => W r.toNNReal p.1)
      (((s p.1 : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) := by
    rw [WithTop.untopD_coe]
    exact hdisj
  rw [hms, hp1]
  refine (hp2 hdisj').trans ?_
  simp only [WithTop.untopD_coe]
  -- the two coupling means agree off the hull
  have hu' := hu p
  rw [hst] at hu'
  have hφH : ∀ z, φ z ≠ 0 → z ∈ H := fun z hz => φ.tsupport_subset (subset_tsupport _ hz)
  have hmean : (∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal p.1) (s p.1 : ℝ≥0) (u₀ p.1) z * φ z) =
      ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal p.1) (s p.1 : ℝ≥0) (u p) z * φ z := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero]
    · have hzK : z ∉ fwdHull (fun r : ℝ => W r.toNNReal p.1) (s p.1 : ℝ) := fun hzK =>
        Set.disjoint_left.1 hdisj (subset_tsupport _ hz) hzK
      have hu₀p := hu₀ p.1
      simp only [WithTop.untopD_coe] at hu₀p
      rw [LocalExt.couplingMean_eq_of_isBoundedHarmonicExtension (NNReal.coe_nonneg _) hwc hu₀p hu'
        ⟨hφH z hz, hzK⟩]
  rw [hmean]


/-! ### Optional hull couplings -/

/-- **An optional hull coupling lifts along `fst`**: read through the first factor of any probability `μ` on `Ω × C`
whose first marginal is `P`, an optional hull coupling under `P` is one under `μ`, for the pulled-back filtration. -/
theorem isOptionalHullCoupling_fstU [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ xL xR ρL ρR μ (Coupling.filtrationFst 𝓕 C) (fun t p => W t p.1)
      (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun t p => B t p.1) (fun p => ζ p.1)
      (fun p => h p.1) := by
  obtain ⟨hE, hhm, hgff, hX, hcl⟩ := hC
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) μ := measurable_fst.aemeasurable
  refine ⟨Coupling.IsIntegratedSLEEvolution.fst hμ hE, hhm.comp measurable_fst, fun u₀ hu₀ => ?_,
    Exist.isMeasurableKilledDriving_comp hX measurable_fst, fun τ hτ hτζ => ?_⟩
  · have h1 := hgff u₀ hu₀
    rw [← hμ] at h1
    exact isZBGFFProcess_comp measurable_fst h1
  have hτfin : ∀ᵐ p ∂μ, τ p ≠ ⊤ := by
    filter_upwards [hτζ] with p hp hτp
    rw [hτp] at hp
    exact not_top_lt hp
  obtain ⟨s, hs, hτs⟩ := exists_stop_factorU hμ hX hτ hτfin
  have hsm : Measurable s := measurable_of_isStoppingTime_coe hs
  have hsζ : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω := by
    have hmeas : MeasurableSet {ω | (s ω : ℝ≥0∞) < ζ ω} :=
      measurableSet_lt (measurable_coe_nnreal_ennreal.comp hsm) (measurable_lifetime hX)
    rw [← hμ, ae_map_iff hfst hmeas]
    filter_upwards [hτζ, hτs] with p hp hps
    rw [hps] at hp
    exact hp
  obtain ⟨hloc, hker⟩ := hcl _ hs (hsζ.mono fun ω hω => hω)
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 (s ω : ℝ)) := by
    filter_upwards [hE.2.2.2.2, hsζ] with ω hω hsω
    exact continuousOn_Icc_of_lt hω.2.2.2.1 hsω
  exact hullClauses_fstU hμ hhm hX hτ hs hτs hcont hloc hker

end Lift

/-! ### The two canonical drivers of a word's GFF -/

section Compare

open Exist Exist.Staged Sec2.Assembly Supp8.GB6

/-- A translation by `0` with constant `0 · k` is the identity. -/
theorem eq_of_isTranslateAddConst_zero_mul {k : ℝ} {g g' : DistOn upperHalfPlaneOpens}
    (ht : IsTranslateAddConst 0 (0 * k) g g') : g' = g := by
  ext φ
  rw [ht φ φ fun z => by rw [Complex.ofReal_zero, add_zero], zero_mul, zero_mul, add_zero]

/-- **The field-determined driver of Theorem 1.2 at universe `u` is the decoded canonical driver code** under the GFF
law of a sorted word, for the flow line at angle `0` and any `k > 0`: same lifetime, same path before it. -/
theorem ae_drvOf_eq_drvDec (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {k : ℝ}
    (hk : 0 < k) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode k 0 F) {c : BoundaryWord} (hc : c.IsSorted) :
    ∀ᵐ g ∂c.gffLaw,
      (drvOf (detCode (paramΦ h12p hk (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL k c.fn c.jumps 0 0, flowLineRhoR k c.fn c.jumps 0 0)), g))).2 = (F (c, g)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (F (c, g)).2 →
        (drvOf (detCode (paramΦ h12p hk (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
          (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
            (flowLineRhoL k c.fn c.jumps 0 0, flowLineRhoR k c.fn c.jumps 0 0)), g))).1 t =
          drvDec (F (c, g)) t := by
  have hgood := Supp8.GB6.ae_isGoodDrvCode_gffLaw hk hF hc
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := GW2JointKernel.isFlowLineDriver_gffLaw hF hc hgood
  have hh' : h' = id := funext fun g => eq_of_isTranslateAddConst_zero_mul (htr g)
  subst hh'
  -- lift the canonical coupling to a sample space in `Type u`
  set ι : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens × ULift.{u} PUnit :=
    fun g => (g, ULift.up PUnit.unit) with hιdef
  have hι : Measurable ι := measurable_id.prodMk measurable_const
  set μ := c.gffLaw.map ι with hμdef
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hι.aemeasurable).2 inferInstance
  have hμ : μ.map Prod.fst = c.gffLaw := by
    rw [hμdef, Measure.map_map measurable_fst hι]
    exact Measure.map_id
  have hC' := isOptionalHullCoupling_fstU (C := ULift.{u} PUnit) hμ hC
  have hF' := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hΦ := (h12p k hk (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)).choose_spec.2 _ _ _ _ hF' hC'
  have hdet := ae_detCode_eq hk hF' h13 hC' hΦ
  have hback := ae_of_ae_map hι.aemeasurable hdet
  filter_upwards [hback] with g hg
  obtain ⟨x₀, hx₀, hζ, hpath, hdc⟩ := hg
  have hdc' : detCode (paramΦ h12p hk (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL k c.fn c.jumps 0 0, flowLineRhoR k c.fn c.jumps 0 0)), g) = dOf x₀ := hdc
  rw [hdc', drvOf_of_mem (dOf_mem_DSet hx₀)]
  refine ⟨hζ, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) < cζ x₀ := hζ ▸ ht
  show drvPath (dOf x₀) t = _
  rw [(drvPath_dOf_agree x₀).2 t ht']
  exact (hpath t ht).1

end Compare

end BRLeaf

end Theorem14

end InteractingSLE
