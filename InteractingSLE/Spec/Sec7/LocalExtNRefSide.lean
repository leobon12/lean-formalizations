/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtNTransfer

/-!
# Aux. lemma 54, (Loc) after the stop: the reference side

Packet PROVE-LOCEXT-N. On the reference, the projection identity at a member `(U, s)` on every event of `𝓖_s` makes the
projection `G X̂` onto `H(U)` independent of `X̂ − G X̂` together with `𝓖_s` (`indep_markov_of_setIntegral_lapTest`). After
the capped local stop `Ŝ ≤ s`, the reference's record history (its stopped-σ-algebra version `refVer`) is an event of
`𝓖_s`; so every bounded function of the record of `X̂ − G X̂` on `D₀ = A₀ ∩ {Ŝ ≤ s}` is independent of `G X̂`
(`setIntegral_refRecord_gauss`):

  `∫_{D₀} e^{i G X̂(χ)} ã(1, rec(X̂ − G X̂, Ŷ)) = exp(−‖covVec_U χ‖²/2) ∫_{D₀} ã(1, rec(X̂ − G X̂, Ŷ))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets Ito QuantumZipper.K3 QuantumZipper.Thm11Asm

section RefSide

variable {κ rL rR r : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {Ωr : Type u} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr} [IsProbabilityMeasure Pr] {𝓕r : Filtration ℝ≥0 mΩr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
  {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

/-- The record of the complementary projection after the capped local stop, as a measurable function of the
complementary projection and `𝓖_s` (a fixed history off `D₀`). -/
def refRecordOn (D₀ : Set Ωr) (Y : Ωr → DistOn upperHalfPlaneOpens) (yv : Ωr → TwoSeedHist) (ω : Ωr) :
    ℝ × RecSp := by
  classical
  exact ((1 : ℝ), (if ω ∈ D₀ then yv ω else ((0 : WithTop ℝ≥0), fun _ => 0)),
    fun ψ => if ω ∈ D₀ ∧ Disjoint (tsupport ψ) (tsHull (yv ω)) then Y ω ψ else 0)

omit mΩr in
theorem refRecordOn_of_mem {D₀ : Set Ωr} {Y : Ωr → DistOn upperHalfPlaneOpens} {yv : Ωr → TwoSeedHist} {ω : Ωr}
    (hω : ω ∈ D₀) : refRecordOn D₀ Y yv ω = ((1 : ℝ), recOf (Y ω) (yv ω)) := by
  classical
  simp only [refRecordOn, hω, ↓reduceIte, true_and, recOf]
  rfl

omit mΩr in
theorem measurable_refRecordOn {𝓜 𝓐 : MeasurableSpace Ωr} {D₀ : Set Ωr} {Y : Ωr → DistOn upperHalfPlaneOpens}
    {yv : Ωr → TwoSeedHist} (hY : Measurable[𝓐] Y) (h𝓐 : 𝓐 ≤ 𝓜) (hD₀ : MeasurableSet[𝓜] D₀)
    (hyv : ∀ M : Set TwoSeedHist, MeasurableSet M → MeasurableSet[𝓜] (D₀ ∩ yv ⁻¹' M)) :
    Measurable[𝓜] (refRecordOn D₀ Y yv) := by
  classical
  refine Measurable.prodMk (m := 𝓜) measurable_const (Measurable.prodMk (m := 𝓜) ?_ ?_)
  · intro M hM
    have e : (fun ω => if ω ∈ D₀ then yv ω else (((0 : WithTop ℝ≥0), fun _ => 0) : TwoSeedHist)) ⁻¹' M =
        (D₀ ∩ yv ⁻¹' M) ∪ (D₀ᶜ ∩ {_ω | (((0 : WithTop ℝ≥0), fun _ => 0) : TwoSeedHist) ∈ M}) := by
      ext ω
      by_cases hω : ω ∈ D₀ <;> simp [hω]
    rw [e]
    refine (hyv M hM).union (hD₀.compl.inter ?_)
    by_cases h0 : (((0 : WithTop ℝ≥0), fun _ => 0) : TwoSeedHist) ∈ M
    · simp only [h0, ofPred_true, MeasurableSet.univ]
    · simp only [h0, ofPred_false, MeasurableSet.empty]
  · refine (@measurable_pi_iff _ _ _ 𝓜 _ _).2 fun ψ => ?_
    have hset : MeasurableSet[𝓜] {ω | ω ∈ D₀ ∧ Disjoint (tsupport ψ) (tsHull (yv ω))} :=
      hyv _ (measurableSet_disjoint_tsHull ψ.hasCompactSupport.isCompact)
    exact Measurable.ite hset (((measurable_distOn_apply ψ).comp hY).mono h𝓐 le_rfl) measurable_const

/-- **The reference side**: on `D₀ = A₀ ∩ {Ŝ ≤ s}` (`A₀ ∈ 𝓖_s`), the projection `G X̂` is independent of every bounded
function of the record of `X̂ − G X̂`. -/
theorem setIntegral_refRecord_gauss
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    {X : Ωr → DistOn upperHalfPlaneOpens} (hXm : Measurable X) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) Pr)
    {s : Ωr → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕r Pr) fun ω => (s ω : WithTop ℝ≥0))
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ωr),
      MeasurableSet[hs.measurableSpace] D →
        ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂Pr =
          Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂Pr)
    {A₀ : Set Ωr} (hA₀ : MeasurableSet[hs.measurableSpace] A₀) {ã : ℝ × RecSp → ℂ} (hã : Measurable ã)
    (χ : TestOn upperHalfPlaneOpens) :
    ∫ ω in A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)},
        Complex.exp (Complex.I * (G (X ω) χ : ℂ)) *
          ã ((1 : ℝ), recOf (markovCompl G (X ω)) (refVer xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr =
      gaussFactor U χ * ∫ ω in A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)},
          ã ((1 : ℝ), recOf (markovCompl G (X ω)) (refVer xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr := by
  classical
  obtain ⟨hXr, -⟩ := hC.2.2.2
  set D₀ : Set Ωr := A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)} with hD₀def
  -- the capped local stop and the history version
  have hŜd := isStoppingTime_capStop hXr hGm hG0 hG r
  have hle := Ito.drivingFiltration_le_usualAugmentation hC.1 hXr
  have hŜ := Ito.isStoppingTime_usualAugmentation_of_drivingFiltration hC.1 hXr hŜd
  have hdl : killedDrivingFiltration hXr ≤ drivingFiltration Pr hXr := Ito.le_usualAugmentation _ Pr
  have hSle : ∀ t : ℝ≥0, MeasurableSet[drivingFiltration Pr hXr t]
      {ω | ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} := fun t => hŜd t
  have hSζ : ∀ ω, ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ζr ω := fun ω => capStop_le r ω
  have hWa := (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_W hXr)).of_le hSle hSζ
  have hVLa := fun i => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VL hXr i)).of_le hSle hSζ
  have hVRa := fun j => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VR hXr j)).of_le hSle hSζ
  have hrefm : Measurable[hŜd.measurableSpace] (refVer xL xR r Gr Wr VLr VRr ζr) :=
    (measurable_seedProj xL xR).comp (measurable_histVersion hŜd hWa hVLa hVRa)
  have hrefm' : Measurable[hŜ.measurableSpace] (refVer xL xR r Gr Wr VLr VRr ζr) :=
    hrefm.mono (Ito.measurableSpace_le_of_filtration_le hle hŜd hŜ) le_rfl
  have hD₀ : MeasurableSet[hs.measurableSpace] D₀ := by
    have h1 := hŜ.measurableSet_inter_le hs _ (@MeasurableSet.univ _ hŜ.measurableSpace)
    have h2 := (hŜ.min hs).measurableSpace_mono hs (fun ω => min_le_right _ _) _ h1
    rw [univ_inter] at h2
    exact hA₀.inter h2
  have hyv : ∀ M : Set TwoSeedHist, MeasurableSet M →
      MeasurableSet[hs.measurableSpace] (D₀ ∩ refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' M) := by
    intro M hM
    have h1 := hŜ.measurableSet_inter_le hs _ (hrefm' hM)
    have h2 := (hŜ.min hs).measurableSpace_mono hs (fun ω => min_le_right _ _) _ h1
    have e : D₀ ∩ refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' M =
        A₀ ∩ (refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' M ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)}) := by
      ext ω
      simp only [hD₀def, mem_inter_iff, mem_preimage, mem_ofPred_eq]
      tauto
    rw [e]
    exact hA₀.inter h2
  -- independence
  have hind := indep_markov_of_setIntegral_lapTest hXm hUH hGG hd hs.measurableSpace_le hid
  have h𝓜l : MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ hs.measurableSpace := le_sup_left
  have h𝓜r : hs.measurableSpace ≤
      MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ hs.measurableSpace := le_sup_right
  set ρ := refRecordOn D₀ (fun ω => markovCompl G (X ω)) (refVer xL xR r Gr Wr VLr VRr ζr) with hρdef
  have hρ : Measurable[MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ hs.measurableSpace] ρ :=
    measurable_refRecordOn (comap_measurable _) h𝓜l (h𝓜r _ hD₀) fun M hM => h𝓜r _ (hyv M hM)
  set B : Ωr → ℂ := D₀.indicator fun ω => ã (ρ ω) with hBdef
  have hB : Measurable[MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ hs.measurableSpace] B :=
    (hã.comp hρ).indicator (h𝓜r _ hD₀)
  have hind' : IndepFun (fun ω => G (X ω)) B Pr :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right hind hB.comap_le)
  have hBm : Measurable B := hB.mono (sup_le ((measurable_markovCompl hGG).comp hXm).comap_le hs.measurableSpace_le)
    le_rfl
  have hprod := hind'.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (T χ : ℂ))) (g := id) (hGG.comp hXm).aemeasurable hBm.aemeasurable
    (GFF.measurable_exp_I_mul (measurable_distOn_apply χ)).aestronglyMeasurable
    measurable_id.aestronglyMeasurable
  have hDm : MeasurableSet D₀ := hs.measurableSpace_le _ hD₀
  have e1 : ∫ ω in D₀, Complex.exp (Complex.I * (G (X ω) χ : ℂ)) *
      ã ((1 : ℝ), recOf (markovCompl G (X ω)) (refVer xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr =
      ∫ ω, Complex.exp (Complex.I * (G (X ω) χ : ℂ)) * B ω ∂Pr := by
    rw [← integral_indicator hDm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ D₀
    · simp only [indicator_of_mem hω, hBdef, hρdef, refRecordOn_of_mem hω]
    · simp only [indicator_of_notMem hω, hBdef, mul_zero]
  have e2 : ∫ ω in D₀, ã ((1 : ℝ), recOf (markovCompl G (X ω)) (refVer xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr =
      ∫ ω, B ω ∂Pr := by
    rw [← integral_indicator hDm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ D₀
    · simp only [indicator_of_mem hω, hBdef, hρdef, refRecordOn_of_mem hω]
    · simp only [indicator_of_notMem hω, hBdef]
  rw [e1, e2]
  simp only [id] at hprod
  rw [hprod, integral_cexp_markov_eq_gauss hXm hUH hGG hd]

end RefSide

end LocalExt

end InteractingSLE
