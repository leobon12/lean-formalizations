/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ16Contact
import InteractingSLE.Spec.Supplement.GW2RootG15Avoid
import InteractingSLE.Spec.Sec5.CrossCondGenFinalGeometry

/-!
# Constructing the actual regularized relative chain before contact

Packet PROVE-T14-GW2ROOT2. Reuse the landed finite-lifetime relative-image
theorem with the actual first-contact horizon. The source trace data prove
positivity and separation; prefix agreement identifies the regularized
chart. No clock, hull identity or separation conclusion is a premise.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ16

open Supp8.GB6

/-- The actual regularized relative chain exists before first contact and
the original physical lifetime. Its clock and hull identities are proved
from the two finite generating traces on the interior chart-tip event. -/
theorem exists_regW_relative_chain_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) α)
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hT : 0 < T) :
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let a : ℝ≥0 → ℝ := fun t =>
      relClock (fun q : ℝ => regW s W ζ q.toNNReal ω) s (fun q : ℝ => w q.toNNReal) t
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧ a 0 = 0 ∧
      StrictMonoOn a {t | (t : ℝ≥0∞) < S} ∧ ContinuousOn a {t | (t : ℝ≥0∞) < S} ∧
      ContinuousOn V {u | (u : ℝ≥0∞) <
        ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        QuantumZipper.fwdHull (fun q : ℝ => V q.toNNReal) (a t) =
          relMap (fun q : ℝ => regW s W ζ q.toNNReal ω) s ''
            QuantumZipper.fwdHull (fun q : ℝ => w q.toNNReal) t ∧
        IsFilling (QuantumZipper.fwdHull (fun q : ℝ => V q.toNNReal) (a t))
          (relMap (fun q : ℝ => regW s W ζ q.toNNReal ω) s '' (γ '' Icc 0 t ∩ H)) := by
  dsimp only
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hz | hp
    · exact False.elim (ne_zero_of_mem_H hsH (by rw [← hz]; exact hα.1))
    · exact hp
  obtain ⟨V, hV⟩ := Sec5.CrossCond.Gen.exists_relativeImage_of_traces
    hγ hw hw0 hα hW hW0 hs0 hs (precontact_horizon_pos hα hs hγ hT)
    (min_le_right _ _) (min_le_left _ _)
  have he : ∀ q ∈ Icc (0 : ℝ) s, W q.toNNReal ω = regW s W ζ q.toNNReal ω := by
    intro q hq
    exact (cfE_fst_of_lt s hW0 hW
      ((ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hs)).symm
  have hA : relClock (Ito.rpath (fun t => W t ω)) s (Ito.rpath w) =
      relClock (fun q : ℝ => regW s W ζ q.toNNReal ω) s (Ito.rpath w) :=
    relClock_eq_of_eqOn s.coe_nonneg he (Ito.rpath w)
  have hM : relMap (Ito.rpath (fun t => W t ω)) s =
      relMap (fun q : ℝ => regW s W ζ q.toNNReal ω) s :=
    relMap_eq_of_eqOn s.coe_nonneg he
  rw [hA, hM] at hV
  let S := min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
  let a : ℝ≥0 → ℝ := fun t =>
    relClock (fun q : ℝ => regW s W ζ q.toNNReal ω) s (fun q : ℝ => w q.toNNReal) t
  obtain ⟨hV0, ha0, hm, hc, hVc, hK⟩ := hV
  change a 0 = 0 at ha0
  change StrictMonoOn a {t | (t : ℝ≥0∞) < S} at hm
  refine ⟨V, hV0, ha0, hm, hc, ?_, hK⟩
  apply hVc.mono
  intro u hu
  change (u : ℝ≥0∞) < ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S),
    ((a t).toNNReal : ℝ≥0∞) at hu
  obtain ⟨t, hu⟩ := lt_iSup_iff.mp hu
  obtain ⟨ht, hu⟩ := lt_iSup_iff.mp hu
  refine ⟨t, ht, ?_⟩
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < S :=
    lt_of_le_of_lt bot_le ht
  have hn : 0 ≤ a t := by
    have h := hm.monotoneOn h0 ht (zero_le : (0 : ℝ≥0) ≤ t)
    rwa [ha0] at h
  have h : (u : ℝ) < ((a t).toNNReal : ℝ) :=
    NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp hu)
  rwa [Real.coe_toNNReal _ hn] at h

end InteractingSLE.Theorem14.GW2TipSystem.RootJ16
