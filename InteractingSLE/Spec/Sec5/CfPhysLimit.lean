/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysSafe

/-!
# Eventual compact avoidance along strict upper physical lines

Packet PROVE-CFCHART2. At an alive image time, inverse capacity is a pre-contact
physical time. The capacity of its strict upper dyadic approximations converges
to the image time; compact avoidance persists by the landed Loewner hull lemma.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyF tendsto_dyF)

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
  {p : Ω × HistorySpace 0 0} {r : ℝ≥0}

/-- Alive inverse-capacity times remain pre-contact along sufficiently fine
strict upper dyadic physical lines, and their capacities converge to `r`. -/
theorem capClock_dyF_limit (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) :
    (∀ᶠ n in atTop, (dyF n (qTheta W VL VR ζ s E r p) : ℝ) ∈ qgPre W VL VR ζ s E p) ∧
      Tendsto (fun n => (capClock (qgCurve W s E p)
        (dyF n (qTheta W VL VR ζ s E r p))).toNNReal) atTop (𝓝 r) := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hθP, hθc⟩ := qTheta_spec hEg hr
  obtain ⟨S, hSP, hθS⟩ := hγ.exists_gt _ hθP
  have ht : Tendsto (fun n => (dyF n (qTheta W VL VR ζ s E r p) : ℝ)) atTop
      (𝓝 (qTheta W VL VR ζ s E r p : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_dyF _)
  have hpre : ∀ᶠ n in atTop,
      (dyF n (qTheta W VL VR ζ s E r p) : ℝ) ∈ qgPre W VL VR ζ s E p := by
    filter_upwards [ht.eventually (gt_mem_nhds hθS)] with n hn
    exact hγ.icc S hSP ⟨NNReal.coe_nonneg _, hn.le⟩
  refine ⟨hpre, ?_⟩
  have hin := tendsto_nhdsWithin_iff.2 ⟨ht, hpre⟩
  have hcap := (hγ.continuousOn_capClock _ hθP).tendsto.comp hin
  rw [hθc] at hcap
  simpa only [Function.comp_def, Real.toNNReal_coe] using (continuous_real_toNNReal.tendsto _).comp hcap

/-- A compact set avoiding the image hull at an alive time eventually avoids
its hull at the strict upper dyadic physical lines. -/
theorem eventually_imageLineSafe (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H)
    (hdis : Disjoint C (fwdHull (Ito.rpath fun q => qW W VL VR ζ s E q p) r)) :
    ∀ᶠ n in atTop, p ∈ imageLineSafe W VL VR ζ s E C (dyF n (qTheta W VL VR ζ s E r p)) := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hpre, hlim⟩ := capClock_dyF_limit hEg hr
  obtain ⟨δ, hδ, -, hsafe⟩ := Restart.DomainMarkov.exists_pos_disjoint_fwdHull_rpath'
    (show ContinuousOn (fun q => qW W VL VR ζ s E q p)
      {q | (q : ℝ≥0∞) < (qT W VL VR ζ s E p : ℝ≥0∞)} from hγ.continuousOn_kcW)
    hr hC hCH hdis
  have hb : ∀ᶠ n in atTop, (capClock (qgCurve W s E p)
      (dyF n (qTheta W VL VR ζ s E r p))).toNNReal ≤ r + δ :=
    (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right r hδ))).mono fun _ hn => hn.le
  filter_upwards [hpre, hb] with n hn hb'
  refine ⟨hn, ?_⟩
  have h0 := hγ.capClock_nonneg hn
  rw [← Real.coe_toNNReal _ h0]
  exact hsafe _ hb'

end InteractingSLE.Sec5.CfPhys
