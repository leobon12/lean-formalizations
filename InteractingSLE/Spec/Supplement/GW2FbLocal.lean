/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbMean

/-!
# GW2's marked union locality at a stopping time of the flow line

Packet PROVE-GW2-FABLE. GB9, p. 525 ("The two compact histories remain physically separated … Their own exposed
germs survive"). The explored curve of GW2 is a flow line that may reach a continuation threshold, so its hull is a
local set only at stopping times before its lifetime (GB6's explored counterflow, `Supp8.RelSafeS8`, is read at
deterministic times with an infinite lifetime).

* **`exists_flowHull_marks`**: for an optional hull coupling of any force word with field-determined histories and a
  finite stopping time `τ < ζ` of its driving filtration, a version `K` of the hull `K_τ` that is hitting-measurable
  for the stopped σ-algebra `𝓕_τ`, with `𝓕_τ` field-determined and `K` history-marked local for the marks `𝓕_τ`
  (`Sec7.SideHeight.isHistoryAvoidanceLocal_flowHull`, `Supp8.GB6LMean.measurable_stop_of_ae_eq_reflect_hull`,
  `Supp8.Q3Chain.stopping_measurableSpace_le_aeSigma`);
* **`exists_union_local_gw2`**: GW2's marked union locality from Theorems 1.2–1.3 — a hitting-measurable version `K`
  of the flow hull at `τ` such that `retSet s W ζ ∪ K` (the inverted counterflow hull at `s` with the flow hull at `τ`)
  is a local set of the centred coupling field (`Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det`).

* **`ae_eqOn_unionMean_gw2_of_thm12_thm13`**: with `ae_eqOn_unionMean_gw2`, GW2's finite-word mean identification
  from Theorems 1.2–1.3 alone (the counterflow's no-return to its base, a hypothesis here, is
  `Wire.counterflowNoReturnStatement_of_theorem13`).

R48: Theorems 1.2–1.3 enter as hypotheses; GW2 serves Theorem 1.4 only. Conditional helpers with distinct names;
they replace no source theorem. No `κ < 4` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open GW2JointKernel GW2TipSystem

/-! ### The explored hull at a stopping time -/

/-- **The hull of a coupling at a finite stopping time before its lifetime, with its stopped marks.** -/
theorem exists_flowHull_marks {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 Wα VL VR B ζα X)
    (hdet : LP.IsFieldDeterminedHistory P X Wα VL VR ζα) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P)
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) :
    ∃ K : Ω → Set ℂ, Measurable[hτ.measurableSpace, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω)) ∧
      hτ.measurableSpace ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace K (centredField X u₀) P := by
  classical
  have hE := hC.1
  -- the seed is admissible: otherwise the lifetime is `0`
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
    intro hseed
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B) (κ := κ)
    (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  -- a hitting-measurable version of the hull
  obtain ⟨hX', hker⟩ := hC.2.2.2
  have hK₀ := (hker τ hτ hτζ).1
  have hlK₀ : IsLocalSet (fun ω => fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (centredField X u₀) P :=
    WholeField.IsLocalSet.sub_dist hK₀ (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  obtain ⟨K, hKm, hKe, -⟩ := WholeField.IsLocalSet.exists_measurable_version hlK₀ hh0.measurable
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := by
    filter_upwards [hKe, hlK₀.2.1] with ω hω hgeom
    rw [hω]
    exact hgeom
  -- measurable for the stopped σ-algebra, through the reflected hull
  have hA'm : Measurable[mΩ, hittingSigma] fun ω => WangWu.negInv '' K ω :=
    WangWu.measurable_image_negInv.comp hKm
  have hA'e : ∀ᵐ ω ∂P, WangWu.negInv '' K ω =
      WangWu.negInv '' fwdHull (fun s : ℝ => Wα s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hKe] with ω hω
    rw [hω]
  have hA'τ := measurable_stop_of_ae_eq_reflect_hull hE hX hσ hτ hτζ hA'm hA'e
  have hKτ : Measurable[hτ.measurableSpace, hittingSigma] K := by
    have h1 := WangWu.measurable_image_negInv.comp hA'τ
    have e : ((fun S : Set ℂ => WangWu.negInv '' S) ∘ fun ω => WangWu.negInv '' K ω) = K :=
      funext fun ω => WangWu.image_negInv_image_negInv' (K ω)
    rwa [e] at h1
  -- the stopped marks are field-determined
  have hcomap : MeasurableSpace.comap X inferInstance ≤
      aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (X ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).symm)
  have h𝓕 : ∀ t, drivingFiltration P hX t ≤
      aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P := fun t =>
    (drivingFiltration_le_aeSigma hdet hX t).trans (aeSigma_le_of_le hcomap)
  have hτd := stopping_measurableSpace_le_aeSigma h𝓕 hτ hτt
  -- marked locality
  have htr : ∀ ω, IsTranslateAddConst 0 (0 * 0) (X ω) (X ω) := fun ω =>
    Sec7.StripSysField.isTranslateAddConst_zero_self (X ω) 0
  have hloc := Sec7.SideHeight.isHistoryAvoidanceLocal_flowHull hC hκ htr hh0 hu₀.1 hu₀ (fun z _ => by simp) hX hτ
    hτζ hKm (by
      filter_upwards [hKe] with ω hω
      simp only [hω, Complex.ofReal_zero, add_zero, image_id'])
  exact ⟨K, hKτ, hKe, hKc, hτd, hloc⟩

/-! ### The union -/

/-- **GW2's marked union locality from Theorems 1.2–1.3**: a hitting-measurable version `K` of the flow hull at a
finite stopping time `τ < ζα` such that the union of the inverted counterflow hull at `s` and `K` is a local set of
the centred coupling field of the flow line. -/
theorem exists_union_local_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ) (s : ℝ≥0)
    {X : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) P 𝓕 Wα VL VR B ζα X)
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P := by
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have huh' : IsBoundedHarmonicExtension (cfData κ b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := huh
  -- the two marked local sets
  obtain ⟨ℋ, hAℋ, hℋd, hlocA⟩ := exists_retained_marks_gw2 h12 h13 hκ hb hG hb' hT hcf htr huh' hu₀ hh0 s
  have hdetα := Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ
    (Theorem15.isOrderedForceWord_flowLine b J 0) P 𝓕 Wα VL VR B ζα X hC
  obtain ⟨K, hKτ, hKe, hKc, hτd, hlocK⟩ := exists_flowHull_marks hκ hC hdetα hu₀ hh0 hX hτ hτζ hτt
  have hAm : Measurable[mΩ, hittingSigma] (retSet s W ζ) := hAℋ.mono ℋ.2 le_rfl
  have hKm : Measurable[mΩ, hittingSigma] K := hKτ.mono hτ.measurableSpace_le le_rfl
  -- the union
  have hUloc := WalkLaw.isHistoryAvoidanceLocal_union_of_det hh0.measurable
    (fun U hUH => hAℋ (measurableSet_avoid U.isOpen hUH))
    (fun U hUH => hKτ (measurableSet_avoid U.isOpen hUH)) hℋd hτd hlocA hlocK
  have hUm : Measurable[mΩ, hittingSigma] (fun ω => retSet s W ζ ω ∪ K ω) := measurable_union_hitting hAm hKm
  have hUc : ∀ᵐ ω ∂P, retSet s W ζ ω ∪ K ω ⊆ H ∧ IsOpen (H \ (retSet s W ζ ω ∪ K ω)) := by
    filter_upwards [hKc] with ω hK
    refine ⟨union_subset (retSet_subset_H s W ζ ω) hK.1, ?_⟩
    have e : H \ (retSet s W ζ ω ∪ K ω) = (H \ retSet s W ζ ω) ∩ (H \ K ω) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [e]
    exact (isOpen_H_diff_retSet s W ζ ω).inter hK.2
  exact ⟨K, hKm, hKe, ((isLocalSet_tfae hh0 hUm hUc).out 4 1).2 hUloc.isAvoidanceLocal⟩

/-! ### The finite-word mean identification -/

/-- **GW2's finite-word mean identification from Theorems 1.2–1.3** (GB9, p. 525: "Before a new flow prefix first
meets the retained counterflow, the conditional exploration has its full canonical word in this joint chart"). For a
flow line of `h` at any angle `θ`, read at a finite stopping time `τ < ζα` of its driving filtration, and the
counterflow of the transported field stopped at `s` (infinite lifetime, no return to its base): there is a
hitting-measurable version `K` of the flow hull at `τ` such that `retSet s W ζ ∪ K` is a local set of the centred
coupling field and, for every local-set mean `g` of this union, almost surely on `{γ(s) ∈ ℍ, 0 < τ < T_c}` the
harmonic representative of `g` is the canonical coupling mean of the relative flow line in the joint chart, for the
angle-`θ` flow-line word of the joint word `jointWordOfRec (specOffset κ) κ c′ (cfRec s W ζ)` flowed by the relative
chain. No relative coupling, conditional kernel or mean identity is assumed. -/
theorem ae_eqOn_unionMean_gw2_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) (s : ℝ≥0)
    (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → v ≤ s → γ ω v ≠ 0)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {X : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) P 𝓕 Wα VL VR B ζα X)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P g →
        ∀ᵐ ω ∂P, γ ω s ∈ H → 0 < (τ ω).untopD 0 →
            (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
              ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 s) →
            ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
              IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
                (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                  (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
                (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                  (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
                (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                  (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
                (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                  (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
                (fun r : ℝ => W r.toNNReal ω) s (fun t => Wα t ω) ((τ ω).untopD 0) p ∧
              IsBoundedHarmonicExtension
                (flowedData κ
                  (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
                  (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
                  (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
                  (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0) p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0)))
                (flowedJumps
                  (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
                  (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
                    (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0) p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0))) G ∧
              ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (retSet s W ζ ω ∪ K ω)) →
                (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (retSet s W ζ ω ∪ K ω) →
                  g ω φ = ∫ z, wU z * φ z) →
                EqOn (fun z => wU z + u₀ z)
                  (fun z => G (fwdMap p.2.2.1
                      (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                        ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) s z)) -
                    chiC κ * ((logDerivFwd p.2.2.1
                      (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                        ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) s z)).im +
                      (relLog (fun r : ℝ => W r.toNNReal ω) s z).im))
                  (H \ (retSet s W ζ ω ∪ K ω)) := by
  obtain ⟨K, hKm, hKe, hlU⟩ :=
    exists_union_local_gw2 h12 h13 hκ hb hG hb' hT hcf s htr hC hX hτ hτζ hτt hu₀
  exact ⟨K, hKm, hKe, hlU, fun g hg =>
    ae_eqOn_unionMean_gw2 h12 h13 hκ hb hG hb' hT hcf hcomp s hNR hc'J hc'b htr hC hα hX hτ hτζ hu₀ hKm hKe hlU hg⟩

end InteractingSLE.Theorem14.GW2Fb
