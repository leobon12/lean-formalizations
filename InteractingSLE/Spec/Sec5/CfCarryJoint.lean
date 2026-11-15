/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfCarryExplicit

/-!
# Joint chart, reduction and member data from the raw physical members

Packet PROVE-CFCHART2. The explicit filtration adapter avoids choosing a chart
from a predicate that discards its reduction or its physical member identities.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfCarry

open CfConv LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart Restart.DomainMarkov.K2 Sec7.PocketTraversal

section Convert

variable {Z Ω : Type*} [MeasurableSpace Z] [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR mL mR : ℕ} {κ θ : ℝ} {ρL : Fin (mL + 2) → ℝ}
  {ρR : Fin (mR + 2) → ℝ} {xL : Fin (mL + 1) → ℝ} {xR : Fin (mR + 1) → ℝ}
  {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ}
  {ζ : Z → ℝ≥0∞} {s : ℝ≥0} {E : Set (Z × HistorySpace 0 0)} {ι : Ω → Z × HistorySpace 0 0}
  {h h' : Ω → DistOn upperHalfPlaneOpens} {R : Ω → RecData}

/-- Keep the explicit chart, its word reduction and physical members together.
Only `hmem` is the additional physical locality input; all conversions are proved. -/
theorem exists_chartBase_reduction_members_of_raw (hι : Measurable ι) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hEtop : ∀ p ∈ E, qT W VL VR ζ s E p = ⊤) (hEae : ∀ᵐ ω ∂P, ι ω ∈ E)
    (hs : 0 < s) (hR : Measurable R)
    (hReq : ∀ ω, R ω = recOf (s : ℝ≥0∞) ((fun t => W t (ι ω).1), ζ (ι ω).1))
    (hreg : ∀ ω, IsRegularDriver ((fun t => W t (ι ω).1), ζ (ι ω).1))
    (hh' : Measurable h') (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω))
    (hcan : IsChartCanon (16 / κ) ρL ρR P (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι)
      (fun t ω => qW W VL VR ζ s E t (ι ω))
      (fun i t ω => qVL xL W VL VR ζ s E i t (ι ω))
      (fun j t ω => qVR xR W VL VR ζ s E j t (ι ω))
      (fun ω => (qT W VL VR ζ s E (ι ω) : ℝ≥0∞)) (fun ω => fChart W VL VR ζ s (ι ω))
      (-((π - θ) * chiC κ)) (-chiC κ) (fun ω => -h' ω))
    (hκ : 0 < κ) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hsL : StrictAnti xL) (hsR : StrictMono xR) (hL0 : xL 0 = 0) (hR0 : xR 0 = 0)
    (hpL : ∀ m : ℕ, 1 ≤ m → m ≤ mL + 2 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (mL + 2) => i.val < m), ρL i)
    (hpR : ∀ m : ℕ, 1 ≤ m → m ≤ mR + 2 →
      16 / κ / 2 - 2 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (mR + 2) => j.val < m), ρR j)
    (hmem : HasSafeMembers P (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι)
      univ (fun ω => qT W VL VR ζ s E (ι ω))
      (fun t ω => qW W VL VR ζ s E t (ι ω)) (fun ω => imgField κ (R ω) (h ω))) :
    ∃ d : Wire.Night.ChartData Ω,
      Wire.Night.ChartBase κ P h R (fun ω t => WangWu.histLine (ι ω).2 t) d ∧
      Wire.Night.ChartReduction κ P d ∧
      HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver (fun ω => imgField κ (R ω) (h ω)) := by
  let 𝓐 := Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι
  let A := ι ⁻¹' E
  let V := eventDriver A (fun t ω => qW W VL VR ζ s E t (ι ω))
  let 𝓑 := recordFiltration (eventFiltration 𝓐 A (hι hE)) R hR
  let XL := fun ω => recordXL s xL (R ω)
  let XR := fun ω => recordXR s xR (R ω)
  obtain ⟨h𝒢, hV0, hVc, hVa, _, hchart, hpath⟩ :=
    converted_chart_explicit hι hX hE hEg hEtop hEae hs hR hReq hreg hh' htr hcan
  have hm := CfResume.hasSafeMembers_record_image hι hX hE hEg hEtop hEae hR hReq hmem
  have hsep : ∀ᵐ ω ∂P, StrictAnti (XL ω) ∧ StrictMono (XR ω) := by
    filter_upwards [hEae] with ω hω
    dsimp only [XL, XR]
    rw [hReq]
    exact CfNext.record_strict_of_good hxL hxR hsL hsR (hEg (ι ω) hω) (hreg ω) hs
  obtain ⟨kL, kR, eL, eR, _, _, heL, heR, htype⟩ :=
    CfFinish.exists_erasure_record_flowType_ae (show 0 < 16 / κ from div_pos (by norm_num) hκ)
      hL0 hR0 ρL ρR s R hsep
  have hLa : ∀ ω, Antitone (XL ω) := fun ω => antitone_recordXL hxL hsL.antitone s (R ω)
  have hRm : ∀ ω, Monotone (XR ω) := fun ω => monotone_recordXR hxR hsR.monotone s (R ω)
  have hc : -2 < 16 / κ / 2 - 2 := by
    have hp : 0 < 16 / κ / 2 := by positivity
    linarith only [hp]
  refine ⟨⟨𝓑, mL + 2, mR + 2, ρL, ρR, XL, XR, V, qTr W VL VR ζ s E ∘ ι⟩,
    ?_, ?_, hm⟩
  · exact ⟨h𝒢, (measurable_recordXL s xL).comp (comap_measurable R),
      (measurable_recordXR s xR).comp (comap_measurable R),
      (fun ω => recordXL_nonpos hxL s (R ω)), (fun ω => recordXR_nonneg hxR s (R ω)),
      hLa, hRm, hV0, hVc, hVa,
      ae_of_all _ (thr_eq_top_of_prefix hVc hLa hRm hc hc hpL hpR), hchart, hpath⟩
  · exact ⟨kL + 1, kR + 1, eL.toEmbedding, eR.toEmbedding,
      eL.strictMono, eR.strictMono, heL, heR, htype⟩

end Convert

end InteractingSLE.Sec5.CfCarry
