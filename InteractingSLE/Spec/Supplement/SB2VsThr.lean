/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsGauge

/-!
# A driver whose trace avoids the bad set has no threshold before (D19's `V_le_thr`)

Packet PROVE-AUX61-NOJUMP (decision D19). **`le_thr_of_avoid`** (deterministic): if a continuous driver from `0` has a
generating trace on `[0, V]` that avoids the bad set of a word before `V`, the continuation threshold of the driver
with the geometric images of the word is at least `V`. A threshold `T < V` is attained
(`FCDet.thr_mem_thresholdSet`). At `T = 0` the colliding seed group puts `0 = Γ 0` in the bad set. At `T > 0` the
collision core (`Vq.right_bad_of_collision`, reflected on the left) puts the tip `Γ T` in the bad set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Sec7.PocketTraversal MartChar.RealFlow

variable {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A driver whose trace avoids the bad set before `V` has its threshold at or after `V`.** -/
theorem le_thr_of_avoid {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω} (hxL0 : ∀ i, xL ω i ≤ 0) (hxR0 : ∀ j, 0 ≤ xR ω j)
    {V : ℝ≥0} {Γ : ℝ≥0 → ℂ} (hgen : IsGeneratingTrace (fun t => W t ω) V Γ)
    (havoid : ∀ t : ℝ≥0, t < V → Γ t ∉ badSet (xL ω) (xR ω) ρL ρR) :
    (V : ℝ≥0∞) ≤ Restart.FCDet.thr ρL ρR W xL xR ω := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨T, hTe⟩ : ∃ T : ℝ≥0, Restart.FCDet.thr ρL ρR W xL xR ω = T :=
    ⟨_, (ENNReal.coe_toNNReal (ne_top_of_lt hlt)).symm⟩
  have hTV : T < V := by rw [hTe] at hlt; exact_mod_cast hlt
  have hmem := Restart.FCDet.thr_mem_thresholdSet hWc xL xR hTe
  set U : ℝ → ℝ := fun s => W s.toNNReal ω with hUdef
  have hU : Continuous U := (hWc ω).comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [hUdef, hW0]
  have hwT : W T ω = U T := by simp [hUdef]
  have hR : ∀ j, geomRW W xR j T ω = rightImg U (xR ω j) T := fun j => rfl
  have hL : ∀ i, geomLW W xL i T ω = -rightImg (-U) (-xL ω i) T := fun i => rfl
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
  · -- a threshold at time `0`: the seed group is bad and `Γ 0 = 0`
    subst hT0
    apply havoid 0 hTV
    rw [hgen.1]
    refine ⟨by simp, ?_⟩
    rcases hmem with hl | hr
    · right
      refine ⟨by simp, ?_⟩
      have e : univ.filter (fun i => geomLW W xL i 0 ω = W 0 ω) = univ.filter (fun i => (0 : ℂ).re ≤ xL ω i) := by
        refine Finset.filter_congr fun i _ => ?_
        rw [hL, hW0, show ((0 : ℝ≥0) : ℝ) = 0 from rfl, rightImg_zero hU.neg (by simp [hU0])
          (neg_nonneg.2 (hxL0 i))]
        simp only [neg_neg, Complex.zero_re]
        exact ⟨fun h => h.ge, fun h => le_antisymm (hxL0 i) h⟩
      unfold wL
      rw [← e]
      exact hl
    · left
      refine ⟨by simp, ?_⟩
      have e : univ.filter (fun j => geomRW W xR j 0 ω = W 0 ω) = univ.filter (fun j => xR ω j ≤ (0 : ℂ).re) := by
        refine Finset.filter_congr fun j _ => ?_
        rw [hR, hW0, show ((0 : ℝ≥0) : ℝ) = 0 from rfl, rightImg_zero hU hU0 (hxR0 j)]
        simp only [Complex.zero_re]
        exact ⟨fun h => h.le, fun h => le_antisymm h (hxR0 j)⟩
      unfold wR
      rw [← e]
      exact hr
  · -- a threshold at a positive time: the tip is at a bad point
    have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen
    have hTV' : (T : ℝ) ≤ V := by exact_mod_cast hTV.le
    have hηT : IsLoewnerTraceLT U T (fun s : ℝ => Γ s.toNNReal) := Vo.isLoewnerTraceLT_mono hη hTV'
    have hc : ContinuousOn (fun s : ℝ => Γ s.toNNReal) (Icc 0 (T : ℝ)) :=
      hgen.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
        ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hTV.le)
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT0
    have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hηT hU hU0 hTr hc
    have htip : extendFrom H (fwdMapInv U T) 0 = Γ T := by
      rw [TraceClose.extendFrom_zero_eq hηT hU hU0 hTr hc, Real.toNNReal_coe]
    apply havoid T hTV
    rcases hmem with hl | hr
    · -- a left threshold, by reflection
      have hηr := Vo.isLoewnerTraceLT_reflect hηT
      have hc' : ContinuousOn (fun s : ℝ => LP.reflectC (Γ s.toNNReal)) (Icc 0 (T : ℝ)) :=
        LP.continuous_reflectC.comp_continuousOn hc
      have hnU : Continuous (-U) := hU.neg
      have hnU0 : (-U) 0 = 0 := by simp [hU0]
      have hB' := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hηr hnU hnU0 hTr hc'
      have htip' : extendFrom H (fwdMapInv (-U) T) 0 = LP.reflectC (Γ T) := by
        rw [TraceClose.extendFrom_zero_eq hηr hnU hnU0 hTr hc', Real.toNNReal_coe]
      have hfilt : univ.filter (fun i => geomLW W xL i T ω = W T ω) =
          univ.filter (fun i => rightImg (-U) (-xL ω i) T = (-U) T) := by
        refine Finset.filter_congr fun i _ => ?_
        rw [hL, hwT, Pi.neg_apply]
        constructor <;> intro h <;> linarith
      rw [hfilt] at hl
      obtain ⟨him, hre, hw'⟩ := right_bad_of_collision (xR := fun i => -xL ω i) hnU hnU0 T.2 hB' htip'
        (fun i => neg_nonneg.2 (hxL0 i)) hl
      have hre' : (LP.reflectC (Γ T)).re = -(Γ T).re := by simp [LP.reflectC]
      have him' : (LP.reflectC (Γ T)).im = (Γ T).im := by simp [LP.reflectC]
      refine ⟨him' ▸ him, Or.inr ⟨by linarith [hre' ▸ hre], ?_⟩⟩
      have hwL : wR (fun i => -xL ω i) ρL (LP.reflectC (Γ T)).re = wL (xL ω) ρL (Γ T).re := by
        unfold wR wL
        rw [hre']
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_le_neg_iff]
      rw [← hwL]
      exact hw'
    · have hfilt : univ.filter (fun j => geomRW W xR j T ω = W T ω) =
          univ.filter (fun j => rightImg U (xR ω j) T = U T) := by
        refine Finset.filter_congr fun j _ => ?_
        rw [hR, hwT]
      rw [hfilt] at hr
      obtain ⟨him, hre, hw'⟩ := right_bad_of_collision hU hU0 T.2 hB htip hxR0 hr
      exact ⟨him, Or.inl ⟨hre, hw'⟩⟩

end InteractingSLE.Theorem14.SB.Vs
