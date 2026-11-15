/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdOriginal
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly

/-!
# The rectangle-wise Eight records are the actual first seeded view

Packet PROVE-ZHAN-GT4-A22. Replace the frozen path stopped at its current
height by the single path stopped at the rectangle's second exit. The chart,
hull and tip at that height are unchanged, including the exit height itself.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- The first-view clock chosen by the landed rectangle-wise source record. -/
def seedSrcClock (W : ℝ → ℝ) (S : ℝ) (Wf : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  (A1EightSeed.imgChain W (fwdHull Wf t) (frzChart Wf t) S).1

/-- The first-view image driver chosen by the landed source record. -/
def seedSrcDriver (W : ℝ → ℝ) (S : ℝ) (Wf : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  (A1EightSeed.imgChain W (fwdHull Wf t) (frzChart Wf t) S).2

/-- Freezing the same path at its current height or at the rectangle exit
gives literally the same chosen source record at that height. -/
theorem srcRec_stopped_frozen_eq {n : ℕ} (W w : ℝ → ℝ) (S κ p : ℝ)
    (rr : Fin n → ℝ) (V : Fin n → ℝ → ℝ) {t T : ℝ}
    (hc : ContinuousOn w (Icc 0 T)) (ht : 0 ≤ t) (htT : t ≤ T) :
    A1EightSeed.srcRec W S (fun u => A1Ref.stopDrv w t u + p) t κ rr p V =
      A1EightSeed.srcRec W S (fun u => A1Ref.stopDrv w T u + p) t κ rr p V := by
  have he : EqOn (fun u => A1Ref.stopDrv w t u + p)
      (fun u => A1Ref.stopDrv w T u + p) (Icc 0 t) := by
    intro u hu
    change A1Ref.stopDrv w t u + p = A1Ref.stopDrv w T u + p
    rw [A1Ref.stopDrv_eqOn w t hu, A1Ref.stopDrv_eqOn w T ⟨hu.1, hu.2.trans htT⟩]
  have htip := he ⟨ht, le_rfl⟩
  have hchart : frzChart (fun u => A1Ref.stopDrv w t u + p) t =
      frzChart (fun u => A1Ref.stopDrv w T u + p) t := by
    funext z
    unfold frzChart
    rw [fwdMap_eq_of_eqOn_Icc he le_rfl, htip]
  have hK : fwdHull (fun u => A1Ref.stopDrv w t u + p) t =
      fwdHull (fun u => A1Ref.stopDrv w T u + p) t := by
    rcases htT.eq_or_lt with rfl | hlt
    · rfl
    · exact LocalExt.fwdHull_congr_of_continuousOn
        ((A1Ref.continuous_stopDrv (hc.mono (Icc_subset_Icc_right htT)) ht).add continuous_const).continuousOn
        ((A1Ref.continuous_stopDrv hc (ht.trans htT)).add continuous_const).continuousOn ht hlt he
  unfold A1EightSeed.srcRec
  rw [hK, hchart, htip]

/-- The actual Eight record on a rectangle is the first seeded view of the
single full stopped second driver. This is equality of records, not a density
compatibility assumption. -/
theorem eightRec_eq_seedSView {X Y : Type*} (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ)
    (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (W₂ : ℝ≥0 → Y → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) (y : Y)
    {t T : ℝ} (hc : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T))
    (h0 : W₂ 0 y = 0) (ht : 0 ≤ t) (htT : t ≤ T) :
    A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y) =
      seedSView (A2X.kh κ) (A1EightSeed.eightRR κ) (A1EightSeed.eightDrv W₁ S₁ m x)
        (A1EightSeed.frzPath W₂ p T y)
        (seedSrcClock (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p T y))
        (seedSrcDriver (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p T y))
        (A1EightSeed.eightMarks VL₁ VR₁ x) t := by
  unfold A1EightSeed.eightRec
  rw [show A1EightSeed.frzPath W₂ p t y = fun u => A1Ref.stopDrv (Strip.extPath (W₂ · y)) t u + p
    from rfl, srcRec_stopped_frozen_eq _ _ _ _ _ _ _ hc ht htT]
  unfold seedSView A1EightSeed.srcRec seedSrcClock seedSrcDriver
  rw [A1EightSeed.frzPath_zero h0 (ht.trans htT)]
  rfl

end InteractingSLE.ZhanGT4
