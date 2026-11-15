/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaProtect
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaWord
import InteractingSLE.Spec.Supplement.GW4SafeREtaMean
import InteractingSLE.Spec.Sec5.CfStepGeom

/-! # GW4: exposed reference heights, including physical wall contacts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField MartChar.RealFlow Sec7.PocketStopSide
open Sec7.Aux119Heights

/-- On one event, all actual GW4 components and their exposed accesses
have a protected rational reference whose ambient corrected union mean
tends to the canonical height on the current side. Real wall landings are
included; no boundary-limit or cover assumption is imposed. -/
theorem ae_exposed_reference_heights
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {K : ℚ → Ω → Set ℂ} (hKm : ∀ s, Measurable[mΩ, hittingSigma] (K s))
    (hKeq : ∀ s : ℚ, ∀ᵐ ω ∂P,
      K s ω = fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ).toNNReal)
    {g : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ s, IsLocalSetMean (fun ω => E ω ∪ K s ω) (centredField h u₀) P (g s)) :
    ∀ᵐ ω ∂P, ∀ F : Frame, F.IsOk → F.IsPathOk (fun r => W r ω) →
      Disjoint (GW4Traverse.relDom F.C) (E ω) →
      ∀ R : ℝ≥0 → ℝ, Continuous R → R 0 = 0 → ∀ V : ℝ≥0∞,
      (∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
        ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt (fun r => W r ω) t) →
      ∀ t q : ℝ≥0, F.ent (fun r => W r ω) ≤ t →
        (t : ℝ≥0∞) < F.exit (fun r => W r ω) → 0 < q → (q : ℝ≥0∞) < V →
        (q : ℝ) = F.rcap (fun r => W r ω) t →
      ∃ S : Set ℂ, S.Finite ∧ ∀ ξ ∈ Ioo
        (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
        (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q), ξ ≠ 0 → ∀ p : ℂ,
        Tendsto (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1
          (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ∉ S →
        ∃ s : ℚ, (F.ent (fun r => W r ω) : ℝ) < s ∧ (s : ℝ) < t ∧
          0 < F.rcap (fun r => W r ω) (s : ℝ).toNNReal ∧
          F.rcap (fun r => W r ω) (s : ℝ).toNNReal < F.rcap (fun r => W r ω) t ∧
          ∃ x r : ℝ, x ∈ Ioo
            (-rightImg (fun u : ℝ => -R u.toNNReal) 0
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal) -
              R (F.rcap (fun u => W u ω) (s : ℝ).toNNReal).toNNReal)
            (rightImg (fun u : ℝ => R u.toNNReal) 0
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal) -
              R (F.rcap (fun u => W u ω) (s : ℝ).toNNReal).toNNReal) ∧ 0 < r ∧
          (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
            (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).2.1 '' (H ∩ Metric.ball (x : ℂ) r) ⊆
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).dom : Set ℂ) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
            (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).1
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y) -
            (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
          Tendsto (fun y => harmRep (g s ω) (H \ (E ω ∪ K s ω))
              ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) +
            u₀ ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) + chiC κ *
              (logDerivFwd (fun r : ℝ => W r.toNNReal ω) (s : ℝ).toNNReal
                ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y)).im)
            (𝓝[H] (ξ : ℂ))
            (𝓝 (if ξ < 0 then -(Real.pi / Real.sqrt κ) else Real.pi / Real.sqrt κ)) := by
  have hsζ : ∀ s : ℚ, ∀ᵐ ω ∂P, ((s : ℝ).toNNReal : ℝ≥0∞) < ζ ω :=
    fun s => hζ.mono fun ω hω => hω ▸ ENNReal.coe_lt_top
  have hall := ae_all_iff.2 fun s : ℚ => ae_tendsto_ambientWord_freeNear hC hκ hu₀ hX
    (s : ℝ).toNNReal (hsζ s) (hKm s) (hKeq s) hEm hEd hEl (hg s)
  filter_upwards [hall, ae_all_iff.2 hKeq, hζ, hC.1.2.2.2.2]
    with ω hMean hKω hζω hPath F hF hw hDE R hR hR0 V hVer t q htEnt htExit hq hqV hqt
  obtain ⟨S, hS, hCover⟩ := Frame.exists_protected_seed_reference_cover hF hw hR hR0 hVer
    htEnt htExit hq hqV hqt
  refine ⟨S, hS, fun ξ hξ hξ0 p hland hp => ?_⟩
  obtain ⟨s, hsEnt, hst, -, -, hsCap0, hsCapLt, hpTrace, hpTip, x, r, ρ, hx, hr, hρ,
    hCol, hTr, hLift, hFree⟩ := hCover ξ hξ hξ0 p hland hp
  have hsNonneg : 0 ≤ (s : ℝ) := (F.ent (fun r => W r ω)).coe_nonneg.trans hsEnt.le
  have hsEntN : F.ent (fun r => W r ω) ≤ (s : ℝ).toNNReal :=
    (Real.le_toNNReal_iff_coe_le hsNonneg).2 hsEnt.le
  have hsExit : ((s : ℝ).toNNReal : ℝ≥0∞) < F.exit (fun r => W r ω) :=
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hst.le)).trans_lt htExit
  have hv : 0 < (F.rcap (fun r => W r ω) (s : ℝ).toNNReal).toNNReal := Real.toNNReal_pos.2 hsCap0
  have hvq : (F.rcap (fun r => W r ω) (s : ℝ).toNNReal).toNNReal ≤ q := by
    apply NNReal.coe_le_coe.1
    rw [Real.coe_toNNReal _ hsCap0.le, hqt]
    exact hsCapLt.le
  obtain ⟨x', hx'0, hx'Seed, hx'Old, hx'Cur, hSide⟩ :=
    Frame.ambient_access_of_seed_reference (ξ := ξ) (x := x) hF hw hR hR0 hVer hsEntN hsExit htEnt htExit
      hv hvq hqV (Real.coe_toNNReal _ hsCap0.le) hqt hξ
      (by simpa only [Real.coe_toNNReal _ hsCap0.le] using hx) hr
      (by simpa only [Real.coe_toNNReal _ hsCap0.le] using hCol)
      (by simpa only [Real.coe_toNNReal _ hsCap0.le] using hTr) hland hpTip
  obtain ⟨hL, hR'⟩ := Sec5.CfStep.force_eq_geom_of_path_top hPath hζω hw.1 (fun _ => rfl)
  have hWW : Continuous (fun r : ℝ => W r.toNNReal ω) := hw.1.comp continuous_real_toNNReal
  have hWord := ambient_exposed_word (κ := κ) hWW
    (s : ℝ).toNNReal.coe_nonneg hxL hxR
    (fun i => (show VL i (s : ℝ).toNNReal ω = _ from hL i (s : ℝ).toNNReal))
    (fun j => (show VR j (s : ℝ).toNNReal ω = _ from hR' j (s : ℝ).toNNReal)) hx'0
    (by simpa only [Real.toNNReal_coe] using hx'Seed) hSide ρL ρR
  simp only [Real.toNNReal_coe] at hWord
  have hpK : p ∈ K s ω ∪ {z : ℂ | z.im = 0} := by
    rw [hKω s]
    by_cases hpH : p ∈ H
    · left
      rw [Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling
        (isCompact_Icc.image (Frame.continuous_trc hw))
        (hw.2.2.1.2.2 (s : ℝ).toNNReal ENNReal.coe_lt_top)]
      exact ⟨hpH, Or.inl (subset_closure hpTrace)⟩
    · right
      obtain ⟨v, -, hvp⟩ := hpTrace
      have hbar := GW2aPiece.trace_mem_Hbar hw.2.2.1 hw.1 hw.2.1 v
      rw [hvp] at hbar
      exact le_antisymm (not_lt.1 hpH) hbar
  have hlim := hMean s p hpK _ (ξ : ℂ) x' hWord.1 hland ⟨ρ, hρ, ?_⟩ hx'Cur
  · exact ⟨s, hsEnt, hst, hsCap0, hsCapLt, x, r, hx, hr, hCol, hTr, hLift, hWord.2 ▸ hlim⟩
  · rw [hKω s]
    simpa only [Real.coe_toNNReal _ hsNonneg] using hFree (E ω) hDE

end InteractingSLE.Theorem14.GW4Fix
