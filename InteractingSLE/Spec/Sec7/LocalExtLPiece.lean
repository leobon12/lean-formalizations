/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLTrunc
import InteractingSLE.Spec.Sec7.LocalExtHMain

/-!
# Aux. lemma 54, (K-pre): the identity on one truncated history event

Packet PROVE-LOCEXT-L. On a record extension `E` of a stopped seed coupling `(Q, h)` by a two-seed reference
`(P̂, ĥ)`, for a rational time `t` and a Borel set `D` of histories whose hulls avoid `supp ψ`, the event
`Â = {t < Ŝ, truncH t Ŷ ∈ D}` of the reference (read through `Prod.snd`) carries the same integral of `e^{i h(ψ)}` (original
field) and of `e^{i ĥ(ψ)}` (reference field):

`∫_{snd⁻¹ Â} e^{i h(p.1)(ψ)} dE = ∫_{snd⁻¹ Â} e^{i ĥ(p.2)(ψ)} dE`.

Proof: on `E` the two histories agree, so `snd⁻¹ Â` is `fst⁻¹ A` for the same event `A` of the stopped coupling; there the
kernel at `t ∧ S` (`IsStoppedSeedCoupling.setIntegral_cexp_trunc`) gives `∫_A kerFun ψ (truncH t Y) dQ`, a functional of the
history; the two histories have the same law (`IsRecordExtension.map_stRecHist_eq`); on the reference side the kernel at
`t ∧ Ŝ` (`setIntegral_cexp_trunc_ref`) returns `∫_{Â} e^{i ĥ(ψ)} dP̂`.

## Main results

* `IsRecordExtension.map_stRecHist_eq`: the two record histories have the same law;
* **`setIntegral_trunc_eq`**: the identity above.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

section Piece

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ωr : Type u} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
  {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

/-- The measurable version of the reference history is measurable. -/
theorem measurable_refVer (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω) :
    Measurable (refVer xL xR r Gr Wr VLr VRr ζr) := by
  obtain ⟨hXr, -⟩ := hC.2.2.2
  have hŜ := isStoppingTime_capStop hXr hGm hG0 hG r
  have hdl : killedDrivingFiltration hXr ≤ drivingFiltration Pr hXr := Ito.le_usualAugmentation _ Pr
  have hSle : ∀ s : ℝ≥0, MeasurableSet[drivingFiltration Pr hXr s]
      {ω | ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := fun s => hŜ s
  have hSζ : ∀ ω, ((capStop r Gr ζr Wr ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ζr ω := fun ω => capStop_le r ω
  have hWa := (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_W hXr)).of_le hSle hSζ
  have hVLa := fun i => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VL hXr i)).of_le hSle hSζ
  have hVRa := fun j => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VR hXr j)).of_le hSle hSζ
  exact ((measurable_seedProj xL xR).comp (measurable_histVersion hŜ hWa hVLa hVRa)).mono
    hŜ.measurableSpace_le le_rfl

/-- **The two record histories of a record extension have the same law** (through the measurable versions). -/
theorem IsRecordExtension.map_stRecHist_eq {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    (hRm : Measurable (stRecHist xL xR W VL VR S)) (hVm : Measurable (refVer xL xR r Gr Wr VLr VRr ζr))
    (hVe : ∀ᵐ ω ∂Pr, refVer xL xR r Gr Wr VLr VRr ζr ω = refRecHist xL xR r Gr Wr VLr VRr ζr ω) :
    Q.map (stRecHist xL xR W VL VR S) = Pr.map (refVer xL xR r Gr Wr VLr VRr ζr) := by
  obtain ⟨hfst, hsnd, hhist, -, -⟩ := hE
  have hVeE : ∀ᵐ p ∂E, refVer xL xR r Gr Wr VLr VRr ζr p.2 = refRecHist xL xR r Gr Wr VLr VRr ζr p.2 := by
    rw [← hsnd] at hVe
    exact ae_of_ae_map measurable_snd.aemeasurable hVe
  rw [← hfst, ← hsnd, Measure.map_map hRm measurable_fst, Measure.map_map hVm measurable_snd]
  refine Measure.map_congr ?_
  filter_upwards [hhist, hVeE] with p h1 h2
  simp only [Function.comp_apply, h1, h2]

/-- **(K-pre) on one truncated history event.** -/
theorem setIntegral_trunc_eq [IsProbabilityMeasure Q] [IsProbabilityMeasure Pr]
    (hr : 0 < r) (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    (t : ℚ≥0) {D : Set TwoSeedHist} (hD : MeasurableSet D) (ψ : TestOn upperHalfPlaneOpens)
    (hDψ : ∀ y ∈ D, Disjoint (tsupport ψ) (tsHull y)) :
    ∫ p in Prod.snd ⁻¹' {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
        truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D}, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
      ∫ p in Prod.snd ⁻¹' {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
        truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D}, Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) ∂E := by
  classical
  have hRm := hc.measurable_stRecHist
  have hVm := measurable_refVer (r := r) hC hGm hG0 hG
  have hVe := ae_refVer_eq xL xR hL hR hr hG0 hG
  have hlaw := hE.map_stRecHist_eq hRm hVm hVe
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  obtain ⟨hfst, hsnd, hhist, -, -⟩ := hE
  set D' : Set TwoSeedHist := {y | ((t : ℝ≥0) : WithTop ℝ≥0) < y.1 ∧ truncH t y ∈ D} with hD'def
  have hD' : MeasurableSet D' :=
    (measurableSet_lt measurable_const measurable_fst).inter ((measurable_truncH t) hD)
  -- the events on the two sides
  set Ar : Set Ωr := {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
    truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D} with hArdef
  set AQ : Set Ω := {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D} with hAQdef
  obtain ⟨hAQm, hQker⟩ := hc.setIntegral_cexp_trunc t hD ψ hDψ
  obtain ⟨hArm, hrker⟩ := setIntegral_cexp_trunc_ref (r := r) xL xR hL hR hr hC hGm hG0 hG
    (fun h' => seedSumL_eq_zero h') (fun h' => seedSumR_eq_zero h') t hD ψ hDψ
  have hArD : Ar = refRecHist xL xR r Gr Wr VLr VRr ζr ⁻¹' D' := rfl
  have hAQD : AQ = stRaw xL xR W VL VR S ⁻¹' D' := rfl
  -- the histories agree on `E`
  have hrawQ : ∀ᵐ ω ∂Q, stRecHist xL xR W VL VR S ω = stRaw xL xR W VL VR S ω := hc.ae_stRecHist_eq hr
  have hrawE : ∀ᵐ p ∂E, stRaw xL xR W VL VR S p.1 = refRecHist xL xR r Gr Wr VLr VRr ζr p.2 := by
    have h1 : ∀ᵐ p ∂E, stRecHist xL xR W VL VR S p.1 = stRaw xL xR W VL VR S p.1 := by
      rw [← hfst] at hrawQ
      exact ae_of_ae_map measurable_fst.aemeasurable hrawQ
    filter_upwards [h1, hhist] with p h1 h2
    rw [← h1, h2]
  have hset : (Prod.snd ⁻¹' Ar : Set (Ω × Ωr)) =ᵐ[E] (Prod.fst ⁻¹' AQ : Set (Ω × Ωr)) := by
    filter_upwards [hrawE] with p hp
    simp only [hArD, hAQD, mem_preimage, hp]
  have hcexp : ∀ g : Ω → DistOn upperHalfPlaneOpens, Measurable g →
      Measurable fun ω => Complex.exp (Complex.I * (g ω ψ : ℂ)) := fun g hg =>
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hg)))
  have hcexpr : Measurable fun ω => Complex.exp (Complex.I * (hr' ω ψ : ℂ)) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hC.2.1)))
  -- the left side is an integral under `Q`
  have hL1 : ∫ p in Prod.snd ⁻¹' Ar, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
      ∫ ω in AQ, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂Q := by
    rw [setIntegral_congr_set hset]
    rw [← hfst]
    exact (setIntegral_map hAQm (hcexp h hhm).aestronglyMeasurable measurable_fst.aemeasurable).symm
  -- the right side is an integral under `P̂`
  have hR1 : ∫ p in Prod.snd ⁻¹' Ar, Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) ∂E =
      ∫ ω in Ar, Complex.exp (Complex.I * (hr' ω ψ : ℂ)) ∂Pr := by
    rw [← hsnd]
    exact (setIntegral_map hArm hcexpr.aestronglyMeasurable measurable_snd.aemeasurable).symm
  rw [hL1, hR1, hQker, hrker]
  -- both kernel integrals are one functional of the history, under the common law
  set Φ : TwoSeedHist → ℂ := D'.indicator fun y => kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ (truncH t y)
    with hΦdef
  have hΦm : Measurable Φ := ((measurable_kerFun _ _ _ ψ).comp (measurable_truncH t)).indicator hD'
  have hQΦ : ∫ ω in AQ, kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ (truncH t (stRaw xL xR W VL VR S ω)) ∂Q =
      ∫ ω, Φ (stRecHist xL xR W VL VR S ω) ∂Q := by
    rw [← integral_indicator hAQm]
    refine integral_congr_ae ?_
    filter_upwards [hrawQ] with ω hω
    rw [hω]
    exact Set.indicator_comp_right (s := D') (g := fun y => kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ
      (truncH t y)) (stRaw xL xR W VL VR S)
  have hrΦ : ∫ ω in Ar, kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ
      (truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr =
      ∫ ω, Φ (refVer xL xR r Gr Wr VLr VRr ζr ω) ∂Pr := by
    rw [← integral_indicator hArm]
    refine integral_congr_ae ?_
    filter_upwards [hVe] with ω hω
    rw [hω]
    exact Set.indicator_comp_right (s := D') (g := fun y => kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ
      (truncH t y)) (refRecHist xL xR r Gr Wr VLr VRr ζr)
  rw [hQΦ, hrΦ, ← integral_map hRm.aemeasurable hΦm.aestronglyMeasurable,
    ← integral_map hVm.aemeasurable hΦm.aestronglyMeasurable, hlaw]

end Piece

end LocalExt

end InteractingSLE
