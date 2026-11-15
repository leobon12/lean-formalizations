/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysSign
import InteractingSLE.Spec.Sec5.CfResumeMemberLaw
import InteractingSLE.Spec.Sec5.CfConvRecord

/-!
# Raw projection members pass from the glued law to the given space

Packet PROVE-CFCHART2. The coarse raw generators are the same observations as
the full raw generators. Their ambient measurable spaces differ; the pullback
inclusion and the landed equal-law member adapter handle precisely that change.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Coupling CfChart
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart.DomainMarkov Restart.DomainMarkov.K2

/-- Coarsening the original sample σ-algebra does not add raw observations. -/
theorem qRaw_comap_coarse_le {Ω : Type u} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {nL nR mL mR : ℕ} (xL : Fin mL → ℝ) (xR : Fin mR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (E : Set (Coarse m × HistorySpace 0 0)) :
    filtrationComap (qRaw (Ω := Coarse m) xL xR W VL VR ζ s E)
      (((measurable_toCoarse hm).comp measurable_fst).prodMk measurable_snd) ≤
        qRaw (Ω := Ω) xL xR W VL VR ζ s E := by
  intro t A hA
  obtain ⟨D, hD, rfl⟩ := hA
  refine ⟨?_, (((measurable_toCoarse hm).comp measurable_fst).prodMk measurable_snd)
    ((qRaw (Ω := Coarse m) xL xR W VL VR ζ s E).le t D hD)⟩
  exact hD.1

/-- Equal-law transfer for the actual raw chart field. The sole data premise
is the already established raw members on the full glued space. -/
theorem hasSafeMembers_coarse_of_glue {Ω : Type u} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {μ : Measure (Ω × HistorySpace 0 0)}
    {nL nR mL mR : ℕ} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Coarse m × HistorySpace 0 0)}
    {Y : Ω → HistorySpace 0 0} (hY : Measurable Y) (hm : m ≤ mΩ)
    (hX : @IsMeasurableKilledDriving Ω m nL nR W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hlaw : μ.map (fun p => (toCoarse m p.1, p.2)) = P.map (fun ω => (toCoarse m ω, Y ω)))
    {X : Coarse m × HistorySpace 0 0 → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hmem : HasSafeMembers μ (qRaw (Ω := Ω) xL xR W VL VR ζ s E) univ
      (fun p => qT W VL VR ζ s E p) (qW W VL VR ζ s E) X) :
    HasSafeMembers P (filtrationComap (qRaw (Ω := Coarse m) xL xR W VL VR ζ s E)
      ((measurable_toCoarse hm).prodMk hY)) univ
      (fun ω => qT W VL VR ζ s E (toCoarse m ω, Y ω))
      (fun t ω => qW W VL VR ζ s E t (toCoarse m ω, Y ω))
      (fun ω => X (toCoarse m ω, Y ω)) := by
  have hg₁ : Measurable (fun p : Ω × HistorySpace 0 0 => (toCoarse m p.1, p.2)) :=
    ((measurable_toCoarse hm).comp measurable_fst).prodMk
    (measurable_snd (β := HistorySpace 0 0))
  have hg₂ : Measurable (fun ω => (toCoarse m ω, Y ω)) := (measurable_toCoarse hm).prodMk hY
  have hmem' : HasSafeMembers μ
      (filtrationComap (qRaw (Ω := Coarse m) xL xR W VL VR ζ s E) hg₁) univ
      (fun p => qT W VL VR ζ s E p) (qW W VL VR ζ s E) X := by
    intro r Fb hFb D hD hDs f Ξ
    exact hmem r Fb hFb D (qRaw_comap_coarse_le hm xL xR W VL VR ζ s E r D hD) hDs f Ξ
  have hg : HasSafeMembers μ
      (filtrationComap (qRaw (Ω := Coarse m) xL xR W VL VR ζ s E) hg₁)
      ((fun p => (toCoarse m p.1, p.2)) ⁻¹' univ)
      ((fun p : Coarse m × HistorySpace 0 0 => (qT W VL VR ζ s E p : ℝ≥0∞)) ∘
        fun p => (toCoarse m p.1, p.2))
      (fun t p => qW W VL VR ζ s E t (toCoarse m p.1, p.2))
      (X ∘ fun p => (toCoarse m p.1, p.2)) := by
    intro r Fb hFb D hD hDs f Ξ
    exact hmem' r Fb hFb D hD hDs f Ξ
  have key := CfResume.hasSafeMembers_of_map_eq_of_adaptedBefore hg₁ hg₂ hlaw MeasurableSet.univ hXm
    (adaptedBefore_qW_raw hX hE hEg)
    (fun p => (isKilledCurve_qgCurve hEg p).continuousOn_kcW)
    (fun p => (isKilledCurve_qgCurve hEg p).kcW_zero) hg
  intro r Fb hFb D hD hDs f Ξ
  exact key r Fb hFb D hD hDs f Ξ

end InteractingSLE.Sec5.CfPhys
