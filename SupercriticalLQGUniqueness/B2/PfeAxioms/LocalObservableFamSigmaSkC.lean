import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFamSigmaSB
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableOpenJointLawSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableOpenFactorSkC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem famSigma_internal_le_aeClosure_fieldSigma_of_smallAnnulusCosts_skC
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
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V)
    (U : TopologicalSpace.Opens ℂ) :
    LQGMetric.Blueprint.famSigma
      (B2.PfeLocal.lscInternalFam (fun ω => D (h ω))) U ≤
        LQGMetric.GM.Bilip.aeClosure P
          (LQGMetric.Blueprint.fieldSigma h U) := by
  let hFactors (x y : U) :=
    ae_internal_local_factor_of_smallAnnulusCosts_skC
      hSkSB ξ Q hQ m hm ε hε D hD P h hh X hX hAnn U x y
  have hcoord (u v : ℂ) :
      Measurable[LQGMetric.GM.Bilip.aeClosure P
        (LQGMetric.Blueprint.fieldSigma h U)]
        (fun ω => B2.PfeLocal.lscInternalFam
          (fun ω => D (h ω)) ω U u v) := by
    by_cases hu : u ∈ (U : Set ℂ)
    · by_cases hv : v ∈ (U : Set ℂ)
      · obtain ⟨F, _, hFE, hFσ⟩ := hFactors ⟨u, hu⟩ ⟨v, hv⟩
        have hFm : Measurable[LQGMetric.Blueprint.fieldSigma h U]
            (fun ω => F (h ω)) :=
          (comap_measurable _).mono hFσ le_rfl
        have hEq : (fun ω => B2.PfeLocal.lscInternalFam
            (fun ω => D (h ω)) ω U u v) =ᵐ[P]
            (fun ω => F (h ω)) := by
          filter_upwards [hFE] with ω hω
          simpa only [B2.PfeLocal.lscInternalFam,
            Uniqueness.TwoScale.S36.internal_eq_intExt] using hω
        exact (comap_measurable _).mono
          (LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq hFm hEq)
          le_rfl
      · have hEq : (fun ω => B2.PfeLocal.lscInternalFam
          (fun ω => D (h ω)) ω U u v) = fun _ => (∞ : ℝ≥0∞) := by
          funext ω
          exact Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_right
            (D := D (h ω)) (Y := (U : Set ℂ)) u hv
        rw [hEq]
        exact measurable_const
    · have hEq : (fun ω => B2.PfeLocal.lscInternalFam
        (fun ω => D (h ω)) ω U u v) = fun _ => (∞ : ℝ≥0∞) := by
        funext ω
        exact Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_left
          (D := D (h ω)) (Y := (U : Set ℂ)) v hu
      rw [hEq]
      exact measurable_const
  have hFam : Measurable[LQGMetric.GM.Bilip.aeClosure P
      (LQGMetric.Blueprint.fieldSigma h U)]
      (fun ω => B2.PfeLocal.lscInternalFam
        (fun ω => D (h ω)) ω (U : Set ℂ)) := by
    rw [measurable_iff_comap_le]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    exact iSup_le fun u => iSup_le fun v => (hcoord u v).comap_le
  exact hFam.comap_le

end SupercriticalLQGUniqueness.B2.PfeAxioms
