/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocalGFF
import InteractingSLE.WangWu.Prop420Ext
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# The local-set mean of the hull of a full level-line coupling (B6–B7 obstruction 1(b))

Packet PROVE-WW-B8. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Definitions 1.4–1.5
and Corollary 3.9; the proof of Proposition 4.19 uses "local-set boundary compatibility" for the prefixes of a seed
line, whose conditional mean is the explicit `η_t` of Definition 1.4.

PROVE-WW-B7 left open (obstruction 1(b)): the stopped prefix as a local set **with mean `η_t`**, for the germ
σ-algebra of `IsLocalSetMean` (Definition 1.5 only gives the conditional law given the driving history `𝓕_τ`). It is
closed here through Corollary 3.9 (`PrefixLocalGFF.lean`) and the landed history-marked germ kernel of the frozen
coupling (`WholeField.ae_condExp_germSigma_hull_eq`, Aux. lemma 18): given the germ σ-algebra **and** `𝓕_τ`, the field
has the conditional mean `η_τ − u₀` off the hull; the local-set mean is the conditional mean given the germ alone,
which is the same (`IsLocalSetMean.ae_eq_condExp_germSigma_sup`: the germ-and-history conditional mean is
germ-measurable).

## Main results

* `ae_forall_apply_eq_of_forall_ae`: from "for every test function, almost surely" to "almost surely, for every test
  function supported off `A`", for a harmonic local-set mean and a harmonic candidate (rational radial bumps and the
  mean value property);
* `IsLocalSetMean.ae_eq_condExp_germSigma_sup`: `g(φ) = E[h(φ) | 𝒜 ∨ ℋ]` for history-marked local sets;
* **`IsFullLevelLineCoupling.ae_apply_eq_of_isLocalSetMean_hull`**: for a full level-line coupling (admissible seed,
  continuous trace through the lifetime), every stopping time `τ < ζ`, every hitting-measurable version `A` of `K_τ`
  and every local-set mean `g` of `A` for the centred field `F − u₀`: almost surely, for every test function `φ`
  supported in `ℍ \ A`, `g(φ) = ∫ (η_τ − u₀) φ`;
* `IsFullLevelLineCoupling.exists_isLocalSetMean_hull`: such `A` and `g` exist.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.WangWu

open LQGMetric LocalSets

/-! ### Swapping "for every test function" and "almost surely" -/

section Swap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The points `a + bi`, `a, b ∈ ℚ`, are dense in `ℂ`. -/
theorem denseRange_ratPt : DenseRange fun p : ℚ × ℚ => ratPt p.1 p.2 := by
  refine Metric.denseRange_iff.2 fun z ε hε => ?_
  obtain ⟨a, b, h⟩ := exists_ratPt_dist_lt z hε
  exact ⟨(a, b), by rwa [dist_comm]⟩

/-- **From "for every test function, almost surely" to "almost surely, for every test function"**. Let `g` be almost
surely harmonic on the open set `ℍ \ A` and `m` almost surely a harmonic function there. If for every test function
`φ`, almost surely, `g(φ) = ∫ m φ` whenever `φ` is supported in `ℍ \ A`, then almost surely this holds for every such
`φ` simultaneously. (Only the countably many rational radial bumps are used, with the mean value property.) -/
theorem ae_forall_apply_eq_of_forall_ae {g : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
    {m : Ω → ℂ → ℝ} (hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω))
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω))
    (hm : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A ω))
    (hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, m ω z * φ z) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, m ω z * φ z := by
  classical
  set bump : ℚ × ℚ × ℚ → TestOn upperHalfPlaneOpens := fun i =>
    if hi : 0 < (i.2.2 : ℝ) ∧ closedBall (ratPt i.1 i.2.1) i.2.2 ⊆ (upperHalfPlaneOpens : Set ℂ) then
      GFF.bumpTest (ratPt i.1 i.2.1) hi.1 hi.2 else 0 with hbump
  have hall : ∀ᵐ ω ∂P, ∀ i, tsupport (bump i) ⊆ H \ A ω → g ω (bump i) = ∫ z, m ω z * bump i z :=
    ae_all_iff.2 fun i => hφ (bump i)
  filter_upwards [hall, hharm, hopen, hm] with ω hω hgω hO hmω φ hsupp
  obtain ⟨v, hv, hvg⟩ := hgω
  have hcont : ∀ {f : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd f (H \ A ω) → ContinuousOn f (H \ A ω) :=
    fun hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hrat : ∀ a b : ℚ, ratPt a b ∈ H \ A ω → v (ratPt a b) = m ω (ratPt a b) := by
    intro a b hab
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO _ hab
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    have hB : closedBall (ratPt a b) r ⊆ H \ A ω :=
      (closedBall_subset_ball (by linarith)).trans hεO
    have hBH : closedBall (ratPt a b) r ⊆ (upperHalfPlaneOpens : Set ℂ) := hB.trans sdiff_subset
    have hbi : bump (a, b, r) = GFF.bumpTest (ratPt a b) hr0' hBH := by
      simp only [hbump, show 0 < (r : ℝ) ∧ closedBall (ratPt a b) r ⊆ (upperHalfPlaneOpens : Set ℂ) from
        ⟨hr0', hBH⟩, and_self, ↓reduceDIte]
    have hsupp' : tsupport (bump (a, b, r)) ⊆ H \ A ω := by
      rw [hbi, GFF.coe_bumpTest]
      exact (GFF.tsupport_bumpFun_subset hr0').trans hB
    have e1 := hω (a, b, r) hsupp'
    rw [hvg _ hsupp', hbi, GFF.coe_bumpTest, GFF.integral_mul_bumpFun_of_harmonic hO hv hr0' hB,
      GFF.integral_mul_bumpFun_of_harmonic hO hmω hr0' hB] at e1
    have hpos : 0 < (r : ℝ) ^ 2 * GFF.bumpMass := by
      have := GFF.bumpMass_pos; positivity
    exact mul_right_cancel₀ hpos.ne' e1
  have heq : EqOn v (m ω) (H \ A ω) := by
    refine Set.EqOn.of_subset_closure (s := (H \ A ω) ∩ range fun p : ℚ × ℚ => ratPt p.1 p.2) ?_
      (hcont hv) (hcont hmω) inter_subset_left (denseRange_ratPt.open_subset_closure_inter hO)
    rintro z ⟨hz, ⟨a, b⟩, rfl⟩
    exact hrat a b hz
  rw [hvg φ hsupp]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ H \ A ω
  · simp only [heq hz]
  · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hsupp h)
    simp [this]

end Swap

/-! ### The local-set mean is the germ-and-history conditional mean -/

section Germ

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
  {g : Ω → DistOn upperHalfPlaneOpens}

/-- **For a history-marked local set, the local-set mean is the conditional mean given the germs and the marks**:
`g(φ) = E[h(φ) | 𝒜 ∨ ℋ]` almost surely (the latter is germ-measurable by Aux. lemma 18). -/
theorem IsLocalSetMean.ae_eq_condExp_germSigma_sup
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A h P) (hℋ : ℋ ≤ mΩ) (hmark : WholeField.IsHistoryAvoidanceLocal ℋ A h P)
    (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => g ω φ) =ᵐ[P] P[fun ω => h ω φ | germSigma A h ⊔ ℋ] := by
  have hle := germSigma_le hA hh.measurable
  obtain ⟨M, hMm, hM1, -⟩ := WholeField.exists_condExp_germSigma_history hh hA hℋ hmark hloc.2.1 φ
  have hMi : Integrable M P := integrable_condExp.congr hM1.symm
  have e1 : P[P[fun ω => h ω φ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
      P[fun ω => h ω φ | germSigma A h] := condExp_condExp_of_le le_sup_left (sup_le hle hℋ)
  have e2 : P[P[fun ω => h ω φ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
      P[M | germSigma A h] := condExp_congr_ae hM1.symm
  rw [condExp_of_stronglyMeasurable hle hMm.stronglyMeasurable hMi] at e2
  have hMg : M =ᵐ[P] fun ω => g ω φ :=
    e2.symm.trans (e1.trans (Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc hg φ).symm)
  exact hMg.symm.trans hM1

end Germ

/-! ### The full level-line coupling -/

section Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → DistOn upperHalfPlaneOpens}

/-- Deterministic step: off the hull, the frozen `couplingMean 4` with any bounded harmonic extension of the data at
time `t` is `η_t`, so `∫ couplingMean φ − ∫ u₀ φ = ∫ (η_t − u₀) φ` for `φ` supported off the hull. -/
theorem integral_couplingMean_sub_eq {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ₀) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ₀) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR (fun i => vL i t - w t)
      (fun i => vR i t - w t)) (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) u)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {φ : TestOn upperHalfPlaneOpens}
    (hφ : tsupport φ ⊆ H \ fwdHull (Ito.rpath w) t) :
    (∫ z, couplingMean 4 (Ito.rpath w) t u z * φ z) - ∫ z, u₀ z * φ z =
      ∫ z, (meanAt ρL ρR w vL vR t z - u₀ z) * φ z := by
  have hO := isOpen_H_diff_fwdHull_of_lt hp ht
  have hharm := harmonicOnNhd_meanAt_of_lt hp ht
  have h1 : ∫ z, couplingMean 4 (Ito.rpath w) t u z * φ z = ∫ z, meanAt ρL ρR w vL vR t z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ H \ fwdHull (Ito.rpath w) t
    · simp only
      rw [couplingMean_eq_meanAt_of_path hp ht hz.1 (exists_isForwardSol_of_not_mem_hull hz.1 hz.2) hu]
    · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφ h)
      simp [this]
  have i1 : Integrable fun z => meanAt ρL ρR w vL vR t z * φ z :=
    integrable_mul_test hO (fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt) φ hφ
  have i2 : Integrable fun z => u₀ z * φ z :=
    integrable_mul_test isOpen_H (fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt) φ
      (hφ.trans sdiff_subset)
  rw [h1, ← integral_sub i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- **The local-set mean of the hull is `η_τ − u₀` off the hull** (B6–B7 obstruction 1(b), Wang–Wu Definition 1.4 with
Corollary 3.9). For a full level-line coupling with an admissible seed whose driver almost surely has a continuous
generating trace through its lifetime, a bounded harmonic extension `u₀` of the seed data, a stopping time `τ < ζ` of
the driving filtration, a hitting-measurable version `A` of the hull `K_τ`, and a local-set mean `g` of `A` for the
centred field `F − u₀`: almost surely, for every test function `φ` supported in `ℍ \ A`,
`g(φ) = ∫ (η_τ − u₀) φ`. -/
theorem IsFullLevelLineCoupling.ae_apply_eq_of_isLocalSetMean_hull [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField F u₀) P g) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = ∫ z, (meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) ((τ ω).untopD 0) z -
        u₀ z) * φ z := by
  have hE := hF.1
  have hC := hF.isOptionalHullCoupling htr hseed
  have hh0 := hF.isZeroBoundaryGFF_centredField htr hseed hu₀
  have hloc : IsLocalSet A (WholeField.centredField F u₀) P :=
    Coupling.IsLocalSet.congr_set (hF.isLocalSet_hull_centredField htr hu₀.1 hh0 hX hτ hτζ) hAK
  have hmark := WholeField.isHistoryAvoidanceLocal_hull hC (by norm_num) hu₀ hX hτ hτζ hA hAK
  choose u hu using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData 4 ρL ρR
    (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
    (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
  -- the candidate mean and its harmonicity
  set m : Ω → ℂ → ℝ := fun ω z =>
    meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) ((τ ω).untopD 0) z - u₀ z with hm
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  refine ae_forall_apply_eq_of_forall_ae (m := m) hg.2.1 (hloc.2.1.mono fun ω h => h.2) ?_ fun φ => ?_
  · filter_upwards [hE.2.2.2.2, hτζ', hAK] with ω hp hlt hAω
    rw [hAω]
    exact (harmonicOnNhd_meanAt_of_lt hp hlt).sub fun z hz => hu₀.1 z hz.1
  · have k1 := (WholeField.ae_condExp_germSigma_hull_eq hC (by norm_num) hu₀ hX hτ hτζ hA hAK hu φ).1
    have e := IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA hloc hτ.measurableSpace_le hmark hg φ
    filter_upwards [k1, e, hAK, hE.2.2.2.2, hτζ'] with ω k e hAω hp hlt hφ
    have hdisj : Disjoint (tsupport φ) (A ω) := Set.disjoint_left.2 fun z hz hzA => (hφ hz).2 hzA
    rw [e, k hdisj]
    rw [hAω] at hφ
    exact integral_couplingMean_sub_eq hp hlt (hu ω) hu₀.1 hφ

/-- **The hull of a full level-line coupling has a hitting-measurable version and a local-set mean** for the centred
field (admissible seed, continuous trace through the lifetime), at every stopping time `τ < ζ`. -/
theorem IsFullLevelLineCoupling.exists_isLocalSetMean_hull [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧
      (∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet A (WholeField.centredField F u₀) P ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField F u₀) P g := by
  have hh0 := hF.isZeroBoundaryGFF_centredField htr hseed hu₀
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hF.1.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨A, hAm, hAK, -⟩ := Coupling.exists_hittingVersion_hull hX hpath hτ hτζ
  have hloc : IsLocalSet A (WholeField.centredField F u₀) P :=
    Coupling.IsLocalSet.congr_set (hF.isLocalSet_hull_centredField htr hu₀.1 hh0 hX hτ hτζ) hAK
  exact ⟨A, hAm, hAK, hloc, IsLocalSet.exists_isLocalSetMean hh0 hAm hloc⟩

end Coupling

end InteractingSLE.WangWu
