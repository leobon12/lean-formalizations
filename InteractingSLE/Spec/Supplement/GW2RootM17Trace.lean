/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootM17Model
import InteractingSLE.Spec.Supplement.GW2RootJ16Clock

/-!
# The relative generating trace from the two actual finite traces

Packet PROVE-T14-GW2ROOT2. Derive all separation and chart data from the
original generating traces. A global relative trace exists through a
buffer beyond every strictly pre-contact cutoff. No relative trace,
clock regularity or hull-transport conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootM17

open Supp8.GB6

/-- Every live pre-contact cutoff of the actual regularized chart has a
protected complete relative generating trace, with exact clock and hulls. -/
theorem exists_regW_relative_trace_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) α)
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T) :
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let U : ℝ → ℝ := fun q => regW s W ζ q.toNNReal ω
    let a : ℝ≥0 → ℝ := fun t => relClock U s (Ito.rpath w) t
    ∃ (B : ℝ≥0) (V : ℝ≥0 → ℝ) (Γ : ℝ≥0 → ℂ),
      v < B ∧ (B : ℝ≥0∞) < S ∧ Continuous V ∧ V 0 = 0 ∧
      IsGeneratingTrace V ⊤ Γ ∧ a 0 = 0 ∧
      StrictMonoOn a (Icc 0 B) ∧ ContinuousOn a (Icc 0 B) ∧
      ∀ t ∈ Icc 0 B, QuantumZipper.fwdHull (Ito.rpath V) (a t) =
        relMap U s '' QuantumZipper.fwdHull (Ito.rpath w) t := by
  let S := min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
  let U : ℝ → ℝ := fun q => regW s W ζ q.toNNReal ω
  let a : ℝ≥0 → ℝ := fun t => relClock U s (Ito.rpath w) t
  change ∃ B V Γ, v < B ∧ (B : ℝ≥0∞) < S ∧ Continuous V ∧ V 0 = 0 ∧
    IsGeneratingTrace V ⊤ Γ ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 B) ∧ ContinuousOn a (Icc 0 B) ∧
    ∀ t ∈ Icc 0 B, QuantumZipper.fwdHull (Ito.rpath V) (a t) =
      relMap U s '' QuantumZipper.fwdHull (Ito.rpath w) t
  obtain ⟨B, hvB, hBS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hv
  obtain ⟨D, hBD, hDS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hBS
  have hvB' : v < B := ENNReal.coe_lt_coe.mp hvB
  have hBD' : B < D := ENNReal.coe_lt_coe.mp hBD
  have hD : 0 < D := lt_of_le_of_lt zero_le (hvB'.trans hBD')
  obtain ⟨wa, αa, ba, hsba, hwa, hwa0, hαa, hewa, heαa⟩ :=
    RootF14.exists_complete_prefix_model hα hW hW0 hs
  obtain ⟨wc, γc, bc, hDbc, hwc, hwc0, hγc, hewc, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 (lt_min_iff.mp hDS).2
  have hUa : Continuous (Ito.rpath wa) := hwa.comp continuous_real_toNNReal
  have hUa0 : Ito.rpath wa 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hwa0
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hz | hp
    · exact False.elim (ne_zero_of_mem_H hsH (by rw [← hz]; exact hα.1))
    · exact hp
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hαa hwa.continuousOn hwa0
    (show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hchart : QuantumZipper.fwdHull (Ito.rpath wa) s =
      QuantumZipper.fwdHull (Ito.rpath (fun t => W t ω)) s :=
    RootF14.fwdHull_eq_of_prefix_eq hewa hsba
  have hphys : ∀ t ∈ Icc 0 D, QuantumZipper.fwdHull (Ito.rpath wc) t =
      QuantumZipper.fwdHull (Ito.rpath w) t := fun t ht =>
    RootF14.fwdHull_eq_of_prefix_eq hewc (ht.2.trans_lt hDbc)
  have hd : Disjoint (closure (QuantumZipper.fwdHull (Ito.rpath wa) s))
      (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (Ito.rpath wc) D)) := by
    rw [hchart, hphys D ⟨zero_le, le_rfl⟩]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hα hW hW0 hγ hw hw0 hs
      (lt_min_iff.mp hDS).2 (lt_min_iff.mp hDS).1
  obtain ⟨V, Γ, hV, hV0, hΓ, ha0, hm, hc, hK⟩ :=
    exists_complete_relative_prefix hUa hUa0 (by exact_mod_cast hs0) htip hwc hwc0 hγc hD hd hBD'
  have he : ∀ q ∈ Icc (0 : ℝ) s, wa q.toNNReal = U q := by
    intro q hq
    rw [hewa ⟨zero_le, (Real.toNNReal_le_iff_le_coe.mpr hq.2).trans hsba.le⟩]
    exact (cfE_fst_of_lt s hW0 hW
      ((ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hs)).symm
  have hM : relMap (Ito.rpath wa) s = relMap U s := relMap_eq_of_eqOn s.coe_nonneg he
  have heclock : EqOn (fun t : ℝ≥0 => relClock (Ito.rpath wa) s (Ito.rpath wc) t) a (Icc 0 D) := by
    intro t ht
    change ConformalImage.hcapSet (relMap (Ito.rpath wa) s '' QuantumZipper.fwdHull (Ito.rpath wc) t) / 2 =
      ConformalImage.hcapSet (relMap U s '' QuantumZipper.fwdHull (Ito.rpath w) t) / 2
    rw [hM, hphys t ht]
  have hsub : Icc 0 B ⊆ Icc 0 D := Icc_subset_Icc_right hBD'.le
  refine ⟨B, V, Γ, hvB', hBS, hV, hV0, hΓ, ?_, ?_, ?_, ?_⟩
  · exact (heclock ⟨zero_le, zero_le⟩).symm.trans ha0
  · exact hm.congr (heclock.mono hsub)
  · exact hc.congr (heclock.mono hsub).symm
  · intro t ht
    rw [← heclock (hsub ht), hK t ht, hM, hphys t (hsub ht)]

end InteractingSLE.Theorem14.GW2TipSystem.RootM17
