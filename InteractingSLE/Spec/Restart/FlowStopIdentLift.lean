/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.TransferHull
import InteractingSLE.Spec.Coupling.CompactTransfer
import InteractingSLE.Spec.Sec7.LocalExtDBridge
import InteractingSLE.Spec.Restart.FlowStopIdentG

/-!
# Optional hull couplings and flow lines lift along the first projection

Packet PROVE-L1-CM (the coupling lift, `planning/handoffs/PROVE-L1G.md` §4.1 (c), "L1-LIFT"). (L1) for shift pairs is
stated on an enlargement `Ω × C` (`FlowStopIdentCM.FlowLineStopIdentCMStatement`), where independent noise continues
the Brownian motion of the stopped coupling after its stop. Its proof starts from the original flow line read through
the first factor. For any probability `μ` on `Ω × C` whose first marginal is `P`:

* `isLocalSet_fst`: a local set of `h` under `P`, read through `fst` (up to a `μ`-null modification), is a local set
  of `h ∘ fst` under `μ` (the frozen definition is a statement about the joint law);
* **`isOptionalHullCoupling_fst`**: an optional hull coupling read through `fst` is an optional hull coupling under `μ`
  for the pulled-back filtration `Coupling.filtrationFst 𝓕 C`. The evolution is `Coupling.IsIntegratedSLEEvolution.fst`;
  the GFF clause is `Restart.isZBGFFProcess_comp`; the driving filtration under `μ` is the usual augmentation of the
  pulled-back one (`Exist.drivingFiltration_comp`), so a stopping time `τ < ζ ∘ fst` is almost surely `s ∘ fst` for a
  stopping time `s < ζ` on `Ω` (Doob–Dynkin, `Exist.exists_isStoppingTime_ae_eq_comp`); the conditional laws transfer
  (`Exist.condExp_comp_ae_eq`), and the coupling means of two bounded harmonic extensions of the same data agree off
  the hull (`LocalExt.couplingMean_eq_of_isBoundedHarmonicExtension`);
* **`isFlowLine_fst`**: a flow line read through `fst` is a flow line under `μ`;
* `exists_stop_factor`, `hullClauses_fst`: the common core (Doob–Dynkin for the lifted driving filtration; the two
  hull clauses at a lifted stopping time from the clauses at its factor);
* `isFilteredBrownianReal_fst`, `adaptedBefore_fst`, **`isStoppedHullCoupling_fst`**,
  **`isStoppedFlowLineL_fst`**: the same for couplings through a stop (`StoppedExtend.IsStoppedHullCoupling`) and for
  PROVE-L1G's stopped flow lines with the lifetime clause.

The second factor lives in `Type` (e.g. the noise space `ℕ → ℝ`), so `Ω × C` lives in the universe of `Ω`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentLift

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {C : Type} [mC : MeasurableSpace C] {P : Measure Ω}
  {μ : Measure (Ω × C)}

/-! ### Local sets -/

/-- **Local sets lift along `fst`**: if `A` is a local set of `h` under `P = μ.map fst`, then every `A'` that agrees
`μ`-almost surely with `A ∘ fst` is a local set of `h ∘ fst` under `μ`. -/
theorem isLocalSet_fst (hμ : μ.map Prod.fst = P) {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
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
  refine ⟨hAE'.congr hcongr.symm, ?_, Ω', mΩ', P', hP', A'', h₁, h₂, hm1, hm2, hm3, hsub', hharm, hcond, ?_⟩
  · have h1 : ∀ᵐ p ∂μ, A p.1 ⊆ H ∧ IsOpen (H \ A p.1) := ae_of_ae_map hfst (by rw [hμ]; exact hsub)
    filter_upwards [h1, hAA] with p hp hpA
    rw [hpA]
    exact hp
  · rw [hlaw, Measure.map_congr hcongr, ← hμ, AEMeasurable.map_map_of_aemeasurable hAEμ hfst]
    rfl

/-! ### Measurability of the lifetime and of finite stopping times -/

/-- The lifetime of a measurable killed driving is measurable. -/
theorem measurable_lifetime {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) : Measurable ζ := by
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top =>
    have e : ζ ⁻¹' Ioi ⊤ = ∅ := eq_empty_of_forall_notMem fun ω (hω : ⊤ < ζ ω) => not_top_lt hω
    rw [e]
    exact MeasurableSet.empty
  | coe r =>
    have e : ζ ⁻¹' Ioi (r : ℝ≥0∞) =
        {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ (univ : Set _)} := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_univ, and_true, mem_ofPred_eq]
    rw [e]
    exact hX r univ MeasurableSet.univ

/-- A finite stopping time of any filtration is measurable. -/
theorem measurable_of_isStoppingTime_coe {𝓖 : Filtration ℝ≥0 mΩ} {s : Ω → ℝ≥0}
    (hs : IsStoppingTime 𝓖 fun ω => (s ω : WithTop ℝ≥0)) : Measurable s := by
  refine measurable_of_Iic fun r => ?_
  have e : s ⁻¹' Iic r = {ω | ((s ω : ℝ≥0) : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
  rw [e]
  exact 𝓖.le r _ (hs r)

/-! ### The hull clauses at a lifted stopping time -/

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Doob–Dynkin for the lifted driving filtration**: an almost surely finite stopping time of the driving filtration
of the killed driving read through `fst` is almost surely `s ∘ fst` for a finite stopping time `s` of the driving
filtration on `Ω`. -/
theorem exists_stop_factor (hμ : μ.map Prod.fst = P) (hX : IsMeasurableKilledDriving W VL VR ζ)
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
theorem hullClauses_fst [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
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
  refine ⟨isLocalSet_fst hμ hloc hhull, fun u hu φ => ?_⟩
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

/-- A path continuous before `ζ`, read on `[0, t]` through `toNNReal`, for `t < ζ`. -/
theorem continuousOn_Icc_of_lt {f : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < L}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < L) : ContinuousOn (fun r : ℝ => f r.toNNReal) (Icc 0 (t : ℝ)) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
  refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
  exact hr.2

/-- A path continuous on `[0, t]`, read through `toNNReal`. -/
theorem continuousOn_Icc_of_Iic {f : ℝ≥0 → ℝ} {t : ℝ≥0} (hf : ContinuousOn f (Iic t)) :
    ContinuousOn (fun r : ℝ => f r.toNNReal) (Icc 0 (t : ℝ)) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
  show r.toNNReal ≤ t
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
  exact hr.2

/-! ### Optional hull couplings -/

/-- **An optional hull coupling lifts along `fst`**: read through the first factor of any probability `μ` on `Ω × C`
whose first marginal is `P`, an optional hull coupling under `P` is one under `μ`, for the pulled-back filtration. -/
theorem isOptionalHullCoupling_fst [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
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
  obtain ⟨s, hs, hτs⟩ := exists_stop_factor hμ hX hτ hτfin
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
  exact hullClauses_fst hμ hhm hX hτ hs hτs hcont hloc hker

/-! ### Couplings through a stop -/

/-- **A filtered Brownian motion lifts along `fst`** (the Brownian part of `Coupling.IsIntegratedSLEEvolution.fst`). -/
theorem isFilteredBrownianReal_fst (hμ : μ.map Prod.fst = P) (hB : IsFilteredBrownianReal 𝓕 B P) :
    IsFilteredBrownianReal (Coupling.filtrationFst 𝓕 C) (fun t p => B t p.1) μ := by
  obtain ⟨hBB, hBa, hBi⟩ := hB
  have hlaw : HasLaw Prod.fst P μ := ⟨measurable_fst.aemeasurable, hμ⟩
  have hBm : ∀ t, Measurable (B t) := fun t => (hBa t).mono (𝓕.le t) le_rfl
  refine ⟨⟨⟨fun I => (hBB.hasLaw I).comp hlaw⟩, ?_⟩, fun t => ?_, fun s t hst => ?_⟩
  · rw [← hμ] at hBB
    exact ae_of_ae_map measurable_fst.aemeasurable hBB.cont
  · exact @Measurable.comp _ _ _ ((𝓕 t).comap Prod.fst) (𝓕 t) _ _ _ (hBa t) (comap_measurable Prod.fst)
  · rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht1
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht2
    have hS' : MeasurableSet ((fun ω => B t ω - B s ω) ⁻¹' S) := ((hBm t).sub (hBm s)) hS
    have hT' : MeasurableSet T := 𝓕.le s _ hT
    have hind := (Indep_iff _ _ _).1 (hBi s t hst) _ T (MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩) hT
    have e : (fun p : Ω × C => B t p.1 - B s p.1) ⁻¹' S = Prod.fst ⁻¹' ((fun ω => B t ω - B s ω) ⁻¹' S) := rfl
    rw [e, ← preimage_inter, ← Measure.map_apply measurable_fst (hS'.inter hT'),
      ← Measure.map_apply measurable_fst hS', ← Measure.map_apply measurable_fst hT', hμ]
    exact hind

/-- Adaptedness before a time lifts along `fst`. -/
theorem adaptedBefore_fst {X : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hX : AdaptedBefore 𝓕 L X) :
    AdaptedBefore (Coupling.filtrationFst 𝓕 C) (fun p => L p.1) fun t p => X t p.1 := fun t A hA =>
  MeasurableSpace.measurableSet_comap.2 ⟨_, hX t A hA, rfl⟩

/-- **A coupling through a stop lifts along `fst`** (`StoppedExtend.IsStoppedHullCoupling`, the same proof as
`isOptionalHullCoupling_fst`; at the stop itself the driver is continuous by the continuity clause). -/
theorem isStoppedHullCoupling_fst [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
    {V : Ω → ℝ≥0∞} (hC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h) :
    StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR μ (Coupling.filtrationFst 𝓕 C) (fun t p => W t p.1)
      (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun t p => B t p.1) (fun p => V p.1)
      (fun p => h p.1) := by
  obtain ⟨hE, hcV, hhm, hgff, hX, hcl⟩ := hC
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) μ := measurable_fst.aemeasurable
  refine ⟨⟨isFilteredBrownianReal_fst hμ hE.brownian, adaptedBefore_fst hE.adapted_W,
    fun i => adaptedBefore_fst (hE.adapted_VL i), fun j => adaptedBefore_fst (hE.adapted_VR j),
    ae_of_ae_map hfst (by rw [hμ]; exact hE.ae_path)⟩,
    ae_of_ae_map hfst (by rw [hμ]; exact hcV), hhm.comp measurable_fst, fun u₀ hu₀ => ?_,
    Exist.isMeasurableKilledDriving_comp hX measurable_fst, fun τ hτ hτV => ?_⟩
  · have h1 := hgff u₀ hu₀
    rw [← hμ] at h1
    exact isZBGFFProcess_comp measurable_fst h1
  obtain ⟨s, hs, hτs⟩ := exists_stop_factor hμ hX hτ (hτV.mono fun p hp => hp.2)
  have hsm : Measurable s := measurable_of_isStoppingTime_coe hs
  have hsV : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) ≤ V ω := by
    have hVm : Measurable V := measurable_lifetime hX
    have hmeas : MeasurableSet {ω | (s ω : ℝ≥0∞) ≤ V ω} :=
      measurableSet_le (measurable_coe_nnreal_ennreal.comp hsm) hVm
    rw [← hμ, ae_map_iff hfst hmeas]
    filter_upwards [hτV, hτs] with p hp hps
    rw [hps] at hp
    exact hp.1
  obtain ⟨hloc, hker⟩ := hcl _ hs (hsV.mono fun ω hω => ⟨hω, WithTop.coe_ne_top⟩)
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 (s ω : ℝ)) := by
    filter_upwards [hE.ae_path, hcV, hsV] with ω hω hcω hsω
    rcases lt_or_eq_of_le hsω with hlt | heq
    · exact continuousOn_Icc_of_lt hω.continuousOn_w hlt
    · exact continuousOn_Icc_of_Iic
        ((continuous_fst.comp_continuousOn (hcω (s ω) heq)) : ContinuousOn (fun t => W t ω) (Iic (s ω)))
  exact hullClauses_fst hμ hhm hX hτ hs hτs hcont hloc hker

/-! ### Flow lines -/

/-- **A flow line lifts along `fst`**: read through the first factor of any probability `μ` on `Ω × C` whose first
marginal is `P`, a flow line of `h` under `P` is a flow line of `h ∘ fst` under `μ`. -/
theorem isFlowLine_fst [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P) {b : ℝ → ℝ}
    {J : Finset ℝ} {y θ : ℝ} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hΓ : IsFlowLine κ b J y θ P h Γ U) :
    IsFlowLine κ b J y θ μ (fun p => h p.1) (fun p => Γ p.1) fun p => U p.1 := by
  obtain ⟨h', 𝓕', W', VL', VR', B', htr, hC, hgen⟩ := hΓ
  refine ⟨fun p => h' p.1, Coupling.filtrationFst 𝓕' C, fun t p => W' t p.1, fun i t p => VL' i t p.1,
    fun j t p => VR' j t p.1, fun t p => B' t p.1, fun p => htr p.1, isOptionalHullCoupling_fst hμ hC, ?_⟩
  exact ae_of_ae_map measurable_fst.aemeasurable (by rw [hμ]; exact hgen)

/-- **A stopped flow line with the lifetime clause lifts along `fst`** (`FlowStopIdentG.IsStoppedFlowLineL`). -/
theorem isStoppedFlowLineL_fst [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P)
    {b : ℝ → ℝ} {J : Finset ℝ} {y θ : ℝ} {V : Set ℂ} {Γ : Ω → ℝ≥0 → ℂ} {e : Ω → ℝ≥0∞}
    (hΓ : FlowStopIdentG.IsStoppedFlowLineL κ b J y θ V P h Γ e) :
    FlowStopIdentG.IsStoppedFlowLineL κ b J y θ V μ (fun p => h p.1) (fun p => Γ p.1) fun p => e p.1 := by
  obtain ⟨h', 𝓕', W', VL', VR', B', htr, hC, hgen, hlife⟩ := hΓ
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) μ := measurable_fst.aemeasurable
  refine ⟨fun p => h' p.1, Coupling.filtrationFst 𝓕' C, fun t p => W' t p.1, fun i t p => VL' i t p.1,
    fun j t p => VR' j t p.1, fun t p => B' t p.1, fun p => htr p.1, isStoppedHullCoupling_fst hμ hC,
    ae_of_ae_map hfst (by rw [hμ]; exact hgen), ae_of_ae_map hfst (by rw [hμ]; exact hlife)⟩

end FlowStopIdentLift

end Restart

end InteractingSLE
