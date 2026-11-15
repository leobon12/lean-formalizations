/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6ReadDTrace

/-!
# Physical trace read-back from relative hull coordinates

The inverse readout is independent of the construction of the relative
driver. Local continuity and the full clock/hull identities imply agreement
with the canonical prefix driver, by the existing driver uniqueness theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.GB6.ReadD

open Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section Coordinates

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
  {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
  {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
  (hd : Disjoint (closure (fwdHull U s))
    (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))
  {D : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hDc : ContinuousOn D {u | (u : ℝ≥0∞) < L}) (hD0 : D 0 = 0)

include hU hU0 hs htip hw hw0 hγ hT hd hDc hD0

omit hT hDc hD0 in
/-- The intrinsic relative clock is monotone on a separated compact prefix. -/
theorem monotoneOn_relClock : MonotoneOn (relClock U s (Ito.rpath w)) (Icc (0 : ℝ) T) := by
  have hwr : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal
  have hwz : Ito.rpath w 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  have hfill : ∀ t ∈ Icc (0 : ℝ) T,
      IsFilling (fwdHull (Ito.rpath w) t) ((fun r : ℝ => γ r.toNNReal) '' Icc 0 t) := by
    intro t ht
    have h := hγ.2.2 t.toNNReal ENNReal.coe_lt_top
    rw [← image_Icc_toNNReal, Real.coe_toNNReal _ ht.1] at h
    exact h
  obtain ⟨_, _, _, _, hm, _, _⟩ := exists_relChain_Icc hwr hwz hU hU0 hs htip T.coe_nonneg hd hfill
  exact hm.monotoneOn

/-- Any continuous relative driver with the correct hulls agrees with the
canonical local driver through each smaller compact physical prefix. -/
theorem localDriver_eq_of_relHulls {S : ℝ≥0} (hS : 0 < S) (hST : S < T)
    (hclock : ENNReal.ofReal (relClock U s (Ito.rpath w) S) < L)
    (hD : ∀ q ∈ Icc (0 : ℝ) S,
      fwdHull (Ito.rpath D) (relClock U s (Ito.rpath w) q) = relMap U s '' fwdHull (Ito.rpath w) q)
    {v : ℝ≥0} (hv : (v : ℝ) ≤ relClock U s (Ito.rpath w) S) :
    CoordB.drivenDriver (fun _ : Unit => CoordB.localCurve U s γ T) v () = D v := by
  obtain ⟨b, hab, hbL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hclock
  obtain ⟨W, hW, hW0, hK⟩ := CoordB.exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd
  have hnnS := (hK S ⟨S.coe_nonneg, by exact_mod_cast hST.le⟩).1
  have habR : relClock U s (Ito.rpath w) S < b := by
    simpa only [ENNReal.coe_toReal] using (ENNReal.ofReal_lt_iff_lt_toReal hnnS ENNReal.coe_ne_top).1 hab
  let V : ℝ → ℝ := fun r => LP.freezeAt b D r.toNNReal
  have hb : ContinuousOn D (Iic b) := hDc.mono fun u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hbL
  have hV : Continuous V := (LP.continuous_freezeAt hb).comp continuous_real_toNNReal
  have hV0 : V 0 = 0 := by simp [V, LP.freezeAt, hD0]
  have hVhull : ∀ q ∈ Icc (0 : ℝ) S, fwdHull V (relClock U s (Ito.rpath w) q) =
      fillH ((fun r : ℝ => CoordB.relBdry U s (γ r.toNNReal)) '' Icc 0 q) := by
    intro q hq
    have hqT : q ∈ Icc (0 : ℝ) T := ⟨hq.1, hq.2.trans (by exact_mod_cast hST.le)⟩
    have haq : relClock U s (Ito.rpath w) q ≤ relClock U s (Ito.rpath w) S :=
      monotoneOn_relClock hU hU0 hs htip hw hw0 hγ hd hqT
        ⟨S.coe_nonneg, by exact_mod_cast hST.le⟩ hq.2
    have he : fwdHull V (relClock U s (Ito.rpath w) q) = fwdHull (Ito.rpath D) (relClock U s (Ito.rpath w) q) :=
      fwdHull_eq_of_eqOn (hK q hqT).1 (haq.trans_lt habR) fun r hr => by
        change D (min r.toNNReal b) = D r.toNNReal
        rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
    rw [he, hD q hq, ← (hK q hqT).2.2]
    exact (hK q hqT).2.1
  have he := CoordB.localDriver_eq_fixed hU hU0 hs htip hw hw0 hγ hT hS hST hd hV hV0 hVhull hv
  rw [he]
  change D (min (v : ℝ).toNNReal b) = D v
  rw [Real.toNNReal_coe, min_eq_left (show v ≤ b from by exact_mod_cast hv.trans habR.le)]

/-- The Borel trace selector agrees for every relative driver having the
same clock and hulls through a later physical prefix. -/
theorem traceAt_of_relHulls {S : ℝ≥0} (hS : 0 < S) (hST : S < T)
    (hclock : ENNReal.ofReal (relClock U s (Ito.rpath w) S) < L)
    (hD : ∀ q ∈ Icc (0 : ℝ) S,
      fwdHull (Ito.rpath D) (relClock U s (Ito.rpath w) q) = relMap U s '' fwdHull (Ito.rpath w) q)
    {t : ℝ≥0} (ht : t ≤ S) :
    LP.traceAt (relClock U s (Ito.rpath w) t).toNNReal D = CoordB.relBdry U s (γ t) := by
  obtain ⟨_, _, _, hK⟩ := CoordB.exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd
  have htT : t < T := ht.trans_lt hST
  have hnn := (hK t ⟨t.coe_nonneg, by exact_mod_cast htT.le⟩).1
  have ham : relClock U s (Ito.rpath w) t ≤ relClock U s (Ito.rpath w) S :=
    monotoneOn_relClock hU hU0 hs htip hw hw0 hγ hd
      ⟨t.coe_nonneg, by exact_mod_cast htT.le⟩
      ⟨S.coe_nonneg, by exact_mod_cast hST.le⟩ (by exact_mod_cast ht)
  have he : ∀ v ≤ (relClock U s (Ito.rpath w) t).toNNReal,
      D v = CoordB.drivenDriver (fun _ : Unit => CoordB.localCurve U s γ T) v () := by
    intro v hv
    apply (localDriver_eq_of_relHulls hU hU0 hs htip hw hw0 hγ hT hd hDc hD0 hS hST hclock hD _).symm
    have hv' : (v : ℝ) ≤ relClock U s (Ito.rpath w) t := by
      simpa only [Real.coe_toNNReal _ hnn] using NNReal.coe_le_coe.2 hv
    exact hv'.trans ham
  rw [LP.traceAt_congr he]
  exact traceAt_localDriver hU hU0 hs htip hw hw0 hγ hT hd htT

end Coordinates

/-- Physical trace read-back is determined by the full relative hulls and
local driver regularity. The choice used to construct that driver is irrelevant. -/
theorem physicalTrace_of_relHulls (s : ℝ≥0) {r : RecData} (hs : 0 < s)
    (hΨ : Q3Rel.IsRetainedChartOff (Q3Rel.invHull (rdrv r) s) (relMap (rdrv r) s)
      (relInv (rdrv r) s) (Q3Rel.relLog (rdrv r) s) (Q3Rel.relBad (rdrv r) s))
    {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv (rdrv r) s) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T S : ℝ≥0} (hT : 0 < T) (hS : 0 < S) (hST : S < T)
    (hd : Disjoint (closure (fwdHull (rdrv r) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))
    {D : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hDc : ContinuousOn D {u | (u : ℝ≥0∞) < L}) (hD0 : D 0 = 0)
    (hclock : ENNReal.ofReal (relClock (rdrv r) s (Ito.rpath w) S) < L)
    (hD : ∀ q ∈ Icc (0 : ℝ) S, fwdHull (Ito.rpath D) (relClock (rdrv r) s (Ito.rpath w) q) =
      relMap (rdrv r) s '' fwdHull (Ito.rpath w) q)
    {t : ℝ≥0} (ht : t ≤ S) :
    physicalTrace s (relClock (rdrv r) s (Ito.rpath w) t).toNNReal (r, D) = γ t := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hcan := traceAt_localDriver hU hU0 hs' htip hw hw0 hγ hT hd (ht.trans_lt hST)
  have hactual := traceAt_of_relHulls hU hU0 hs' htip hw hw0 hγ hT hd hDc hD0 hS hST hclock hD ht
  have he : LP.traceAt (relClock (rdrv r) s (Ito.rpath w) t).toNNReal D =
      LP.traceAt (relClock (rdrv r) s (Ito.rpath w) t).toNNReal
        (fun v => CoordB.drivenDriver (fun _ : Unit => CoordB.localCurve (rdrv r) s γ T) v ()) :=
    hactual.trans hcan.symm
  unfold physicalTrace
  rw [he]
  exact physicalTrace_localDriver s hs hΨ htip hw hw0 hγ hT hd (ht.trans_lt hST)

end InteractingSLE.Supp8.GB6.ReadD
