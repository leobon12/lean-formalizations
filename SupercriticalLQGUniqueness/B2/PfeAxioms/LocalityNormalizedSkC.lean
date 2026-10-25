import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalityNormalizedSB
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableOpenJointLawSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFamSigmaSkC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem jointlyLocal_internal_of_dg20LimitSkC
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    LQGMetric.Blueprint.IsJointlyLocalFam P h
      (B2.PfeLocal.lscInternalFam (fun ω => D (h ω)))
      (B2.PfeLocal.lscInternalFam (fun ω => D (h ω))) := by
  intro V
  let I := B2.PfeLocal.lscInternalFam (fun ω => D (h ω))
  have hloc (U : TopologicalSpace.Opens ℂ) :
      LQGMetric.Blueprint.famSigma I U ≤
        LQGMetric.GM.Bilip.aeClosure P
          (LQGMetric.Blueprint.fieldSigma h U) :=
    famSigma_internal_le_aeClosure_fieldSigma_of_smallAnnulusCosts_skC
      hSkSB ξ Q hQ m hm ε hε D hD P h hh X hX hAnn U
  have hVm : LQGMetric.Blueprint.fieldSigma h V ≤
      mΩ :=
    LQGMetric.GM.Bilip.fieldSigma_le hh.1.measurable V
  have hOutside : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  let W : TopologicalSpace.Opens ℂ := ⟨(closure (V : Set ℂ))ᶜ, hOutside⟩
  have hWm : LQGMetric.Blueprint.fieldSigma h W ≤
      mΩ :=
    LQGMetric.GM.Bilip.fieldSigma_le hh.1.measurable W
  have hfieldOut : LQGMetric.Blueprint.fieldSigmaClosed h (V : Set ℂ)ᶜ ≤
      mΩ := by
    exact LQGMetric.DFGPS.L219.fieldSigmaClosed_le_comap h (V : Set ℂ)ᶜ |>.trans
      hh.1.measurable.comap_le
  have hmetricOut : LQGMetric.Blueprint.famSigma I W ≤
      LQGMetric.GM.Bilip.aeClosure P mΩ :=
    (hloc W).trans (LQGMetric.GM.Bilip.aeClosure_mono hWm)
  have hB : LQGMetric.Blueprint.fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
      LQGMetric.Blueprint.famSigma I W ⊔
      LQGMetric.Blueprint.famSigma I W ≤
      LQGMetric.GM.Bilip.aeClosure P mΩ := by
    exact sup_le (sup_le (hfieldOut.trans (LQGMetric.GM.Bilip.le_aeClosure _))
      hmetricOut) hmetricOut
  simpa [I, W] using
    (LQGMetric.GM.Bilip.condIndepEv_of_le_aeClosure hVm
      (by simpa only [sup_idem] using hloc V) hB)

end SupercriticalLQGUniqueness.B2.PfeAxioms
