/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF14Extension

/-!
# Joint-chart carriers on a protected finite lifetime window

Packet PROVE-T14-GW2ROOT2. Extend both traces using their existing finite
prefix models, transfer the relative hull identities by driver locality,
and apply E13. The complete traces are constructed, not assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF14

open Supp8.GB6

/-- The exact relative upper carrier before a protected physical cutoff,
with only finite-lifetime traces and pre-lifetime driver continuity. -/
theorem relMap_upper_prefix_eq_of_finite
    {Wc Wrel : ℝ≥0 → ℝ} {Tγ TΓ : ℝ≥0∞} {γ Γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace Wc Tγ γ)
    (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < Tγ}) (hWc0 : Wc 0 = 0)
    (hΓ : IsGeneratingTrace Wrel TΓ Γ)
    (hWrel : ContinuousOn Wrel {t | (t : ℝ≥0∞) < TΓ}) (hWrel0 : Wrel 0 = 0)
    {U : ℝ → ℝ} {σ : ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
    {B : ℝ≥0} (hBT : (B : ℝ≥0∞) < Tγ)
    (hcapT : ((relClock U σ (fun q : ℝ => Wc q.toNNReal) B).toNNReal : ℝ≥0∞) < TΓ)
    (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t) (Icc 0 B))
    (hac : ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t) (Icc 0 B))
    (ha0 : relClock U σ (fun q : ℝ => Wc q.toNNReal) 0 = 0)
    (hK : ∀ t ∈ Icc 0 B,
      QuantumZipper.fwdHull (fun q : ℝ => Wrel q.toNNReal)
        (relClock U σ (fun q : ℝ => Wc q.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t)
    (hdom : ∀ t ∈ Icc 0 B, ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t,
      -z⁻¹ ∉ QuantumZipper.fwdHull U σ)
    (hγdom : ∀ t ∈ Icc 0 B, γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ)
    {v : ℝ≥0} (hv : v < B) :
    relMap U σ '' (γ '' Icc 0 v ∩ H) =
      Γ '' Icc 0 (relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal ∩ H := by
  let a : ℝ≥0 → ℝ := fun r => relClock U σ (fun q : ℝ => Wc q.toNNReal) r
  have hB : B ∈ Icc 0 B := ⟨zero_le, le_rfl⟩
  have hn : ∀ r ∈ Icc 0 B, 0 ≤ a r := by
    intro r hr
    have hm := hsm.monotoneOn (show (0 : ℝ≥0) ∈ Icc 0 B from ⟨le_rfl, zero_le⟩) hr zero_le
    simpa only [NNReal.coe_zero, ha0] using hm
  obtain ⟨wc, γc, bc, hBbc, hwc, hwc0, hγc, hewc, heγc⟩ :=
    exists_complete_prefix_model hγ hWc hWc0 hBT
  obtain ⟨wr, Γr, br, hBbr, hwr, hwr0, hΓr, hewr, heΓr⟩ :=
    exists_complete_prefix_model hΓ hWrel hWrel0 hcapT
  have hphys : ∀ r ∈ Icc 0 B,
      QuantumZipper.fwdHull (fun q : ℝ => wc q.toNNReal) r =
        QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) r := by
    intro r hr
    exact fwdHull_eq_of_prefix_eq hewc (hr.2.trans_lt hBbc)
  have heqa : ∀ r ∈ Icc 0 B, relClock U σ (fun q : ℝ => wc q.toNNReal) r = a r := by
    intro r hr
    change ConformalImage.hcapSet (relMap U σ '' _) / 2 = ConformalImage.hcapSet (relMap U σ '' _) / 2
    rw [hphys r hr]
  have hsub : {r : ℝ≥0 | (r : ℝ≥0∞) < (B : ℝ≥0∞)} ⊆ Icc 0 B :=
    fun r hr => ⟨zero_le, (ENNReal.coe_lt_coe.mp hr).le⟩
  have hmono : ∀ r ∈ Icc 0 B, (a r).toNNReal ≤ (a B).toNNReal :=
    fun r hr => Real.toNNReal_mono (hsm.monotoneOn hr hB hr.2)
  have hrel : ∀ r ∈ Icc 0 B,
      QuantumZipper.fwdHull (fun q : ℝ => wr q.toNNReal) (a r) =
        QuantumZipper.fwdHull (fun q : ℝ => Wrel q.toNNReal) (a r) := by
    intro r hr
    have hh := fwdHull_eq_of_prefix_eq hewr ((hmono r hr).trans_lt hBbr)
    simpa only [Real.coe_toNNReal _ (hn r hr)] using hh
  have hsmc : StrictMonoOn (fun r : ℝ≥0 => relClock U σ (fun q : ℝ => wc q.toNNReal) r)
      {r | (r : ℝ≥0∞) < (B : ℝ≥0∞)} := by
    intro r hr r' hr' hrr'
    change relClock U σ (fun q : ℝ => wc q.toNNReal) r <
      relClock U σ (fun q : ℝ => wc q.toNNReal) r'
    rw [heqa r (hsub hr), heqa r' (hsub hr')]
    exact hsm (hsub hr) (hsub hr') hrr'
  have hacc : ContinuousOn (fun r : ℝ≥0 => relClock U σ (fun q : ℝ => wc q.toNNReal) r)
      {r | (r : ℝ≥0∞) < (B : ℝ≥0∞)} := (hac.congr heqa).mono hsub
  have hnnc : ∀ r : ℝ≥0, (r : ℝ≥0∞) < (B : ℝ≥0∞) →
      0 ≤ relClock U σ (fun q : ℝ => wc q.toNNReal) r := by
    intro r hr
    rw [heqa r (hsub hr)]
    exact hn r (hsub hr)
  have hKc : ∀ r : ℝ≥0, (r : ℝ≥0∞) < (B : ℝ≥0∞) →
      QuantumZipper.fwdHull (fun q : ℝ => wr q.toNNReal)
        (relClock U σ (fun q : ℝ => wc q.toNNReal) r) =
          relMap U σ '' QuantumZipper.fwdHull (fun q : ℝ => wc q.toNNReal) r := by
    intro r hr
    rw [heqa r (hsub hr), hrel r (hsub hr), hphys r (hsub hr)]
    exact hK r (hsub hr)
  have hdomc : ∀ r : ℝ≥0, (r : ℝ≥0∞) < (B : ℝ≥0∞) →
      ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => wc q.toNNReal) r,
        -z⁻¹ ∉ QuantumZipper.fwdHull U σ := by
    intro r hr z hz
    rw [hphys r (hsub hr)] at hz
    exact hdom r (hsub hr) z hz
  have hγdomc : ∀ r : ℝ≥0, (r : ℝ≥0∞) < (B : ℝ≥0∞) → γc r ∈ H →
      -(γc r)⁻¹ ∉ QuantumZipper.fwdHull U σ := by
    intro r hr
    rw [heγc ⟨zero_le, (hsub hr).2.trans hBbc.le⟩]
    exact hγdom r (hsub hr)
  have ha0c : relClock U σ (fun q : ℝ => wc q.toNNReal) 0 = 0 := by
    have he := heqa 0 (show (0 : ℝ≥0) ∈ Icc 0 B from ⟨le_rfl, zero_le⟩)
    exact he.trans (by simpa only [a, NNReal.coe_zero] using ha0)
  have hvB : v ∈ Icc 0 B := ⟨zero_le, hv.le⟩
  have hresult := RootE13.relMap_upper_prefix_eq hwc hwc0 hU hU0 hσ hγc hwr hwr0 hΓr
    hsmc hacc hnnc hKc hdomc hγdomc ha0c (ENNReal.coe_lt_coe.mpr hv)
  rw [heqa v hvB] at hresult
  have hγimage : γc '' Icc 0 v = γ '' Icc 0 v :=
    (heγc.mono (Icc_subset_Icc_right (hv.le.trans hBbc.le))).image_eq
  have hΓimage : Γr '' Icc 0 (a v).toNNReal = Γ '' Icc 0 (a v).toNNReal :=
    (heΓr.mono (Icc_subset_Icc_right ((hmono v hvB).trans hBbr.le))).image_eq
  rw [hγimage, hΓimage] at hresult
  exact hresult

end InteractingSLE.Theorem14.GW2TipSystem.RootF14
