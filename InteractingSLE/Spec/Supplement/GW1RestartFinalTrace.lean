/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartFinalBoundary

/-!
# A completed ordinary piece preserves the marked boundary range

The finite endpoint is included. Filling is used only to locate the frontier;
the new physical boundary values belong to the raw generating trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW1RestartFinal

/-- A finite real boundary value of a Loewner inverse, when it lies in `ℍ`,
belongs to the closed generating set rather than merely to its filling. -/
theorem inverse_boundary_mem_generating_set {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv W T)) {A : Set ℂ} (hAc : IsClosed A)
    (hAb : Bornology.IsBounded A) (hfill : fwdHull W T = fillH A)
    {p : ℂ} (hp : p ∈ Hbar) (hpH : p ∉ H)
    (hfH : extendFrom H (fwdMapInv W T) p ∈ H) :
    extendFrom H (fwdMapInv W T) p ∈ A := by
  have hc := Chart.isConformal_id.loewner hW hW0 hT
  have hdom : ((Chart.id.loewner W T).dom : Set ℂ) = H \ fwdHull W T := by
    rw [hc.coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 hT
  have hfr := boundary_limit_mem_frontier hc hp hpH (hB.tendsto hp)
  rw [hdom, hfill] at hfr
  rcases frontier_H_diff_fillH_subset hAb hfr with hreal | hA
  · exact (ne_of_gt (show 0 < (extendFrom H (fwdMapInv W T) p).im from hfH) hreal).elim
  · rwa [hAc.closure_eq] at hA

/-- The boundary range is preserved at a finite stop, including a finite
continuation threshold of the ordinary piece. -/
theorem HasBoundaryRange.loewner_stopped {c : Chart} {A : Set ℂ}
    (hc : HasBoundaryRange c A) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hr : GW1P.PieceRegular W S) (hS : S ≠ ⊤)
    (hA : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ⊆ A) :
    HasBoundaryRange (c.loewner
      (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
      ((S.toNNReal : ℝ≥0) : ℝ)) A := by
  obtain ⟨f, hf, hboundary⟩ := hc
  obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
  let U : ℝ → ℝ := fun r => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal
  let T : ℝ≥0 := S.toNNReal
  let Fb : ℂ → ℂ := extendFrom H (fwdMapInv U T)
  have hB := hr.hasBdryLimits hS
  have hFH : ∀ p ∈ Hbar, Fb p ∈ Hbar := fun p hp =>
    GW1P.mem_Hbar_of_tendsto hp
      (fun z hz => QuantumZipper.RS.fwdMapInv_mem_H hU hU0 T.coe_nonneg hz) (hB.tendsto hp)
  refine ⟨fun p => f (Fb p), ?_, ?_⟩
  · intro p hp
    exact CounterflowRange.tendsto_loewner_inv hU hU0 T.coe_nonneg
      (hB.tendsto hp) (hf _ (hFH p hp))
  · intro p hp hpH
    by_cases hFb : Fb p ∈ H
    · left
      have hST : (T : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
      by_cases hT : T = 0
      · have hid : Fb p = p := by
          refine extendFrom_eq (by rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar]) ?_
          refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with z hz
          rw [show (T : ℝ) = 0 from NNReal.coe_eq_zero.2 hT]
          exact (InteractingSLE.fwdMapInv_zero_time hU hU0 hz).symm
        exact (hpH (hid ▸ hFb)).elim
      · obtain ⟨hw0, hwc, α, hα, -⟩ := hr
        have hα' : IsGeneratingTrace
            (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) (T : ℝ≥0∞) α := by
          rw [hST]
          exact CounterflowRange.isGeneratingTrace_stopped hα
        have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hα'
        have hηc : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 (T : ℝ)) :=
          hα'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
            ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
        have hfill := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hη hU hU0
          (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hT)) hηc
        have hcompact := isCompact_Icc.image_of_continuousOn hηc
        obtain ⟨s, hs, hsp⟩ := inverse_boundary_mem_generating_set hU hU0 T.coe_nonneg hB
          hcompact.isClosed hcompact.isBounded hfill hp hpH hFb
        apply hA
        have hwlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
          hwc.mono fun _ (hs : (_ : ℝ≥0∞) < S) => (le_of_lt hs : (_ : ℝ≥0∞) ≤ S)
        rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hwc hw0 fun t ht =>
          hf _ (Sec7.IsGeneratingTrace.mem_Hbar hα hwlt hw0 ht)]
        refine ⟨α s.toNNReal, ⟨s.toNNReal, ?_, rfl⟩, congrArg f hsp⟩
        rw [← hST]
        exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    · exact hboundary _ (hFH p hp) hFb

end InteractingSLE.Theorem14.GW1RestartFinal
