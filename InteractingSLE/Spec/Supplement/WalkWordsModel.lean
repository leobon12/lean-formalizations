/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsDom
import InteractingSLE.Spec.Supplement.WalkIntBridgePair

/-!
# Recorded pieces read through a global Loewner model of their driver

Packet PROVE-WALK-WORDS. A recorded piece `pc` (launch chart, stopped driver, stop) whose driver is continuous on
`[0, T']` and agrees there with a continuous driver `W` (`W 0 = 0`) generating a Loewner trace `η`:

* `prefixChart_inv_eq_loewner`: the inverse of the prefix chart at `τ < T'` is that of `pc.1.loewner W τ`;
* `SideIdentification.congrInv`: incident-side identifications only see the inverse maps;
* `mem_tipSet_of_model`, `mem_wsetOf_of_model`: an interior trace point `η(t)`, `t < T'`, `t` before the stop, has
  the physical point `pc.1⁻¹(η(t))` on the piece, hence on the walk.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry

section Model

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {pc : Piece} {T' : ℝ}

/-- The inverse of a prefix chart is the inverse of the Loewner stage of the model driver. -/
theorem prefixChart_inv_eq_loewner (hW : Continuous W) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T'))
    (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) {τ : ℝ≥0} (hτ : (τ : ℝ) < T') (z : ℂ) :
    (prefixChart pc τ).2.1 z = (pc.1.loewner W τ).2.1 z := by
  change pc.1.2.1 (fwdMapInv (pieceDrv pc) τ z) = pc.1.2.1 (fwdMapInv W τ z)
  rw [LocalExt.fwdMapInv_congr_of_continuousOn hpc hW.continuousOn τ.coe_nonneg hτ
    (hagree.mono (Icc_subset_Icc_right hτ.le)) z]

/-- Incident-side identifications only see the inverse maps. -/
def SideIdentification.congrInv {cR cL cR' cL' : Chart} {yR yL : ℝ}
    (G : WalkIntBridge.SideIdentification cR' cL' yR yL) (hR : ∀ z, cR.2.1 z = cR'.2.1 z)
    (hL : ∀ z, cL.2.1 z = cL'.2.1 z) : WalkIntBridge.SideIdentification cR cL yR yL :=
  ⟨G.radius, G.radius_pos, G.map, G.continuous, G.real, G.at_base, fun z hz => by
    rw [hR, hL]; exact G.inv_agree z hz⟩

/-- **An interior trace point of the model is a physical point of the piece.** -/
theorem mem_tipSet_of_model (hc : pc.1.IsConformal) (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T')) (hagree : EqOn (pieceDrv pc) W (Icc 0 T'))
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T') (htS : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2) (hH : η t ∈ H) :
    pc.1.2.1 (η t) ∈ pc.1.tipSet pc.2.1 pc.2.2 := by
  refine ⟨t.toNNReal, htS, ?_⟩
  have htt : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  have hinv : ∀ z, fwdMapInv (fun r : ℝ => pc.2.1 r.toNNReal) (t.toNNReal : ℝ) z = fwdMapInv W t z := by
    intro z
    rw [htt]
    exact LocalExt.fwdMapInv_congr_of_continuousOn hpc hW.continuousOn ht htT
      (hagree.mono (Icc_subset_Icc_right htT.le)) z
  have hlim : Tendsto (fwdMapInv W t) (𝓝[H] 0) (𝓝 (η t)) := hη.tendsto_fwdMapInv_tip hW hW0 ht
  have hI : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun y : ℝ => (y : ℂ) * I) := by fun_prop
      have h := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show 0 < ((y : ℂ) * I).im
      simpa using hy
  have hcq : ContinuousAt pc.1.2.1 (η t) := (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hH)).continuousAt
  refine (hcq.tendsto.comp (hlim.comp hI)).congr fun y => ?_
  simp only [Function.comp_apply]
  rw [hinv]

/-- **An interior trace point of the model is a point of the walk.** -/
theorem mem_wsetOf_of_model {s : ExplState} {pre post : List Piece} (hs : s.1 = pre ++ pc :: post)
    (hc : pc.1.IsConformal) (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T')) (hagree : EqOn (pieceDrv pc) W (Icc 0 T'))
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T') (htS : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2) (hH : η t ∈ H) :
    pc.1.2.1 (η t) ∈ wsetOf s := by
  refine ⟨?_, hc.2.1 hH⟩
  simp only [ordOf, mem_iUnion, exists_prop]
  exact ⟨pc, by rw [hs]; exact List.mem_append_right _ List.mem_cons_self,
    mem_tipSet_of_model hc hη hW hW0 hpc hagree ht htT htS hH⟩

end Model

end InteractingSLE.Theorem14.WalkWords
