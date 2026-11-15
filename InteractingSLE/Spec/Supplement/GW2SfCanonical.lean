/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfThreshold

/-!
# Transferring a GW2 threshold bound to the conditioned canonical law

Packet PROVE-GW2-SAFE. This adapter only changes probability coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.PocketTraversal Restart.FCDet
  Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd

/-- A physical-space bound for the typed geometric threshold transfers to
the conditioned joint law of the record, field, driver and stop. -/
theorem ae_canonStp_le_thr_gw2_of_driver_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {h' Hc : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {J' : Finset ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (s : ℝ≥0) (hHcm : Measurable Hc) (c' : BoundaryWord)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous (R · ω)) (hR0 : ∀ ω, R 0 ω = 0)
    (hVm : Measurable V) (w : WordType)
    (hbound : ∀ᵐ ω ∂P, γ ω s ∈ H → wordType κ (gw2Word κ θ c' (gb6Rec s W ζ ω)) = w →
      V ω ≤ thr (typedRhoL w) (typedRhoR w) R
        (fun ω => typedXL κ w (gw2Word κ θ c' (gb6Rec s W ζ ω)))
        (fun ω => typedXR κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) ω) :
    ∀ᵐ y ∂((P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|
          typeEvent κ w (gw2Word κ θ c') (gb6TS s)]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv
        (fun y => typedXL κ w (gw2Word κ θ c' y.1))
        (fun y => typedXR κ w (gw2Word κ θ c' y.1)) y := by
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hraised : Measurable fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) :=
    (Exist.measurable_flowField 0 _).comp hHcm
  have hΦ := hrec.prodMk (measurable_relVar hraised hRm hVm)
  have hβ := measurable_gw2Word κ θ c'
  have hxL : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXL κ w (gw2Word κ θ c' y.1) :=
    (((measurable_typedXL κ w).comp hβ).comp measurable_fst_canonRec).mono
      (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXR κ w (gw2Word κ θ c' y.1) :=
    (((measurable_typedXR κ w).comp hβ).comp measurable_fst_canonRec).mono
      (canonRec_le_canonFilt 0) le_rfl
  refine ae_cond_of_ae_comp hΦ (measurableSet_typeEvent hβ (measurableSet_gb6TS s))
    (measurableSet_le measurable_canonStp
      (measurable_thr continuous_canonDrv stronglyAdapted_canonDrv hxL hxR)) ?_
  filter_upwards [hbound, ae_gb6RecGood hcf hγ s] with ω hb hr hm
  have hsH := ((mem_gb6TS_iff hr).2 hm.1).2
  have hd : ∀ t, canonDrv t (gb6Rec s W ζ ω,
      relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω) = R t ω :=
    fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  rw [thr_congr (W := R)
    (xL := fun ω => typedXL κ w (gw2Word κ θ c' (gb6Rec s W ζ ω)))
    (xR := fun ω => typedXR κ w (gw2Word κ θ c' (gb6Rec s W ζ ω))) hd rfl rfl]
  exact hb hsH hm.2

end InteractingSLE.Theorem14.GW2Sf
