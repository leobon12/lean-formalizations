import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFamSigmaBdd
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalityNormalizedSB

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private theorem jointlyLocal_of_open_factors
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : Measurable h)
    (E : Ω → LSCMetric)
    (hLoc : ∀ U : TopologicalSpace.Opens ℂ,
      LQGMetric.Blueprint.famSigma (B2.PfeLocal.lscInternalFam E) U ≤
        LQGMetric.GM.Bilip.aeClosure P
          (LQGMetric.Blueprint.fieldSigma h U)) :
    LQGMetric.Blueprint.IsJointlyLocalFam P h
      (B2.PfeLocal.lscInternalFam E) (B2.PfeLocal.lscInternalFam E) := by
  intro V
  let I := B2.PfeLocal.lscInternalFam E
  have hVm : LQGMetric.Blueprint.fieldSigma h V ≤ mΩ :=
    LQGMetric.GM.Bilip.fieldSigma_le hh V
  have hOutside : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  let W : TopologicalSpace.Opens ℂ := ⟨(closure (V : Set ℂ))ᶜ, hOutside⟩
  have hWm : LQGMetric.Blueprint.fieldSigma h W ≤ mΩ :=
    LQGMetric.GM.Bilip.fieldSigma_le hh W
  have hfieldOut : LQGMetric.Blueprint.fieldSigmaClosed h (V : Set ℂ)ᶜ ≤ mΩ :=
    (LQGMetric.DFGPS.L219.fieldSigmaClosed_le_comap h (V : Set ℂ)ᶜ).trans
      hh.comap_le
  have hmetricOut : LQGMetric.Blueprint.famSigma I W ≤
      LQGMetric.GM.Bilip.aeClosure P mΩ :=
    (hLoc W).trans (LQGMetric.GM.Bilip.aeClosure_mono hWm)
  have hB : LQGMetric.Blueprint.fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
      LQGMetric.Blueprint.famSigma I W ⊔
      LQGMetric.Blueprint.famSigma I W ≤
      LQGMetric.GM.Bilip.aeClosure P mΩ :=
    sup_le (sup_le (hfieldOut.trans (LQGMetric.GM.Bilip.le_aeClosure _))
      hmetricOut) hmetricOut
  simpa [I, W] using
    (LQGMetric.GM.Bilip.condIndepEv_of_le_aeClosure hVm
      (by simpa only [sup_idem] using hLoc V) hB)

theorem jointlyLocal_internal_bdd_of_geometry_annulus
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hGeom : ∀ᵐ ω ∂P,
      ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    LQGMetric.Blueprint.IsJointlyLocalFam P h
      (B2.PfeLocal.lscInternalFam (fun ω => D (h ω)))
      (B2.PfeLocal.lscInternalFam (fun ω => D (h ω))) := by
  exact jointlyLocal_of_open_factors P h hh.1
    (fun ω => D (h ω))
    (famSigma_internal_bdd_le_aeClosure_fieldSigma
      ξ m ε hε D hD P h hh X hX hGeom hAnn)

end SupercriticalLQGUniqueness.B2.PfeAxioms
