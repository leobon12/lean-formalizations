/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstMean
import InteractingSLE.Spec.Sec5.Aux61MeanIdChart
import InteractingSLE.Spec.Sec7.PhaseSelAdapt
import InteractingSLE.GFF.LocalSets.BoundaryVanishing

/-!
# A measurable correction read from the time-zero harmonic distribution

Packet PROVE-AUX61-GLUEINST. Reuse the existing jointly measurable harmonic
version, subtract the explicit initial reference mean, and set the correction
to zero off its measurable conull set. The result is harmonic for every
history, jointly measurable, and gives the required initial-mean identity
almost surely. Boundary cancellation on the chosen real window is separate.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GInst

open Aux61Fib (FibData)

/-- The initial reference mean is measurable on the whole carrier. -/
theorem measurable_refMean0 (d : FibData) : Measurable (Aux61GlueK.refMean0 d) :=
  Sec7.PhaseSelAdapt.measurable_meanExt _ _ _ measurable_const measurable_const measurable_const measurable_id

/-- The time-zero harmonic distribution has a jointly measurable correction
relative to `refMean0`. The correction is harmonic at every history, and
almost surely `refMean0 + Q` equals every harmonic representative on H. -/
theorem exists_measurable_initialCorrection {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (d : FibData) {T : β → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    (hh : ∀ᵐ z ∂μ, IsHarmonicDistOn (T z) H) :
    ∃ Q : β → ℂ → ℝ, Measurable (fun p : β × ℂ => Q p.1 p.2) ∧
      (∀ z, InnerProductSpace.HarmonicOnNhd (Q z) H) ∧
      ∀ᵐ z ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
        (∀ ψ : TestOn upperHalfPlaneOpens, T z ψ = ∫ w, v w * ψ w) →
        EqOn (fun w => Aux61GlueK.refMean0 d w + Q z w) v H := by
  have hr : ∀ A : DistOn upperHalfPlaneOpens, GFF.restrictDist upperHalfPlaneOpens A = A := by
    intro A
    ext ψ
    rw [GFF.restrictDist_apply]
    congr 1
    ext w
    exact congrFun (GFF.coe_testIncl le_rfl ψ) w
  have hh' : ∀ᵐ z ∂μ, ∃ v, GFF.IsHarmRep upperHalfPlaneOpens
      (GFF.restrictDist upperHalfPlaneOpens (T z)) v := by
    filter_upwards [hh] with z hz
    obtain ⟨v, hv, hrep⟩ := hz
    refine ⟨v, hv, fun ψ => ?_⟩
    rw [hr]
    exact hrep ψ ψ.tsupport_subset
  obtain ⟨S, G, hSm, hSμ, hGm, hSrep, hGrep⟩ :=
    GFF.exists_measurable_harmonic_version le_rfl hT hh'
  classical
  let Q : β → ℂ → ℝ := fun z w => if z ∈ S then G (z, w) - Aux61GlueK.refMean0 d w else 0
  have heq : ∀ z ∈ S, ∀ v, GFF.IsHarmRep upperHalfPlaneOpens
      (GFF.restrictDist upperHalfPlaneOpens (T z)) v →
      EqOn (Q z) (fun w => v w - Aux61GlueK.refMean0 d w) H := by
    intro z hz v hv w hw
    simp only [Q, hz, ↓reduceIte, hGrep z hz v hv w hw]
  refine ⟨Q, Measurable.ite (measurable_fst hSm)
    (hGm.sub ((measurable_refMean0 d).comp measurable_snd)) measurable_const, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ S
    · obtain ⟨v, hv⟩ := hSrep z hz
      exact Aux61MeanId.harmonicOnNhd_of_eqOn QuantumZipper.isOpen_H
        (hv.1.sub (Aux61GlueK.refMean0_ext d).1) (heq z hz v hv)
    · have hQ0 : Q z = fun _ => 0 := funext fun w => by simp only [Q, hz, ↓reduceIte]
      rw [hQ0]
      exact InnerProductSpace.harmonicOnNhd_const 0
  · filter_upwards [show ∀ᵐ z ∂μ, z ∈ S from mem_ae_iff.2 hSμ] with z hz
    intro v hv hrep w hw
    have hv' : GFF.IsHarmRep upperHalfPlaneOpens (GFF.restrictDist upperHalfPlaneOpens (T z)) v := by
      rw [hr]
      exact ⟨hv, hrep⟩
    dsimp only
    rw [heq z hz v hv' hw]
    ring

end InteractingSLE.Sec5.Aux61GInst
