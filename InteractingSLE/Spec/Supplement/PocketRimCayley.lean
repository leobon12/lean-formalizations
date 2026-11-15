/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketSectorAssembly

/-!
# Finite and infinite endpoints of a compactified pocket

PROVE-POCKETSHAPE continuation. Reuse the existing Cayley map and its boundary
topology to reflect closure points and distinguish bounded pockets from pockets
whose compactified frontier contains the point at infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Theorem14.PocketRim

open GW4Reg WangWu Sec7.Lemma71I

/-- The Cayley image reflects closure membership at each finite half-plane point. -/
theorem mem_closure_of_cayley_mem_closure {C : Set ℂ} (hCH : C ⊆ H) {z : ℂ} (hz : z ∈ Hbar)
    (hcl : cayley z ∈ closure (cayley '' C)) : z ∈ closure C := by
  have h := (continuousAt_cayleyInv (cayley_ne_one_of_Hbar hz)).continuousWithinAt.mem_closure_image hcl
  rw [cayleyInv_cayley_of_mem_Hbar hz, image_image] at h
  have heq : (fun w : ℂ => cayleyInv (cayley w)) '' C = C := by
    calc
      _ = (id : ℂ → ℂ) '' C := image_congr fun w hw =>
        cayleyInv_cayley_of_mem_Hbar (show 0 < w.im from hCH hw).le
      _ = C := image_id C
  rwa [heq] at h

/-- A bounded half-plane set has no point at infinity in the closure of its Cayley image. -/
theorem one_not_mem_closure_cayley_of_isBounded {C : Set ℂ} (hCH : C ⊆ H) (hCb : IsBounded C) :
    (1 : ℂ) ∉ closure (cayley '' C) := by
  have hHb : closure C ⊆ Hbar := closure_minimal
    (fun z hz => (show 0 < z.im from hCH hz).le) QuantumZipper.isClosed_Hbar
  have hcompact : IsCompact (cayley '' closure C) := hCb.isCompact_closure.image_of_continuousOn
    (fun z hz => (continuousAt_cayley_of_mem_Hbar (hHb hz)).continuousWithinAt)
  have hsub : closure (cayley '' C) ⊆ cayley '' closure C :=
    closure_minimal (image_mono subset_closure) hcompact.isClosed
  intro h1
  obtain ⟨z, hz, he⟩ := hsub h1
  exact cayley_ne_one_of_Hbar (hHb hz) he

/-- Boundedness is exactly exclusion of infinity from the compactified frontier. -/
theorem isBounded_iff_one_not_mem_frontier_cayley {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) :
    IsBounded C ↔ (1 : ℂ) ∉ frontier (cayley '' C) := by
  refine ⟨fun hb h1 => one_not_mem_closure_cayley_of_isBounded hCH hb (frontier_subset_closure h1), ?_⟩
  intro h1
  by_contra hu
  exact h1 (Sec7.Lemma71F.one_mem_frontier_cayley_image hCo hCH hu)

/-- A compactified contact with finite first parameter has a finite second parameter. -/
theorem finite_contact_of_disc_contact {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {a t : ℝ} (ha : a < 1) (ht : t ≤ 1)
    (he : toDisc (realPath αR) a = toDisc (realPath αL) t) :
    t < 1 ∧ αR (arcTime a).toNNReal = αL (arcTime t).toNNReal := by
  have ha1 : toDisc (realPath αR) a ≠ 1 := by
    rw [toDisc_of_lt ha]
    exact cayley_ne_one_of_Hbar (hR.2.2.2.1 _)
  have ht1 : t < 1 := lt_of_le_of_ne ht fun he1 => ha1 (by rw [he, he1, toDisc_one])
  refine ⟨ht1, ?_⟩
  rw [toDisc_of_lt ha, toDisc_of_lt ht1] at he
  exact cayley_injOn_Hbar (hR.2.2.2.1 _) (hL.2.2.2.1 _) he

/-- Reflect a compactified wall interval at a finite half-plane point.
The upper bound is needed only when the disc endpoint is finite. -/
theorem mem_wall_interval_of_cayley_mem {α : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α)
    {z : ℂ} (hz : z ∈ Hbar) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hm : cayley z ∈ toDisc (realPath α) '' Icc a b) :
    ∃ r : ℝ≥0, (arcTime a).toNNReal ≤ r ∧ (b < 1 → r ≤ (arcTime b).toNNReal) ∧ α r = z := by
  obtain ⟨q, hq, he⟩ := hm
  have hq1 : q < 1 := lt_of_le_of_ne (hq.2.trans hb) fun hq1 =>
    cayley_ne_one_of_Hbar hz (by rw [hq1, toDisc_one] at he; exact he.symm)
  have he' : α (arcTime q).toNNReal = z := by
    rw [toDisc_of_lt hq1] at he
    exact cayley_injOn_Hbar (hα.2.2.2.1 _) hz he
  refine ⟨(arcTime q).toNNReal, ?_, ?_, he'⟩
  · apply Real.toNNReal_mono
    exact strictMonoOn_arcTime.monotoneOn ⟨ha, hq.1.trans_lt hq1⟩
      ⟨ha.trans hq.1, hq1⟩ hq.1
  · intro hb1
    apply Real.toNNReal_mono
    exact strictMonoOn_arcTime.monotoneOn ⟨ha.trans hq.1, hq1⟩
      ⟨(ha.trans hq.1).trans hq.2, hb1⟩ hq.2

end InteractingSLE.Theorem14.PocketRim
