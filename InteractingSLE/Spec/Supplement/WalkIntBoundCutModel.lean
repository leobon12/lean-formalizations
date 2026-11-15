/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutRaw

/-!
# A finite recorded list realizes every full-walk raw cutoff

Cut each piece by the continuous full-walk clock. The recorded prefixes
are totally ordered, so finitely many cuts have an actual maximum prefix.
Real connector gaps contribute no points to the raw set in H.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkWords WalkIntOrient WalkIntClosed

/-- Finitely many ordinary portions are contained in one actual prefix
that remains inside the specified target. -/
theorem exists_closedPrefix_finite_cover {s : ExplState} {T : Set ℂ}
    (hEmpty : ∃ R : ClosedPrefix s, R.raw = ∅)
    (hCover : ∀ pc ∈ s.1, ∃ R : ClosedPrefix s,
      R.raw ⊆ T ∧ pc.1.tipSet pc.2.1 pc.2.2 ∩ T ⊆ R.raw) :
    ∃ R : ClosedPrefix s, R.raw ⊆ T ∧ ∀ pc ∈ s.1,
      pc.1.tipSet pc.2.1 pc.2.2 ∩ T ⊆ R.raw := by
  have hf : ∀ L : List Piece, L ⊆ s.1 → ∃ R : ClosedPrefix s,
      R.raw ⊆ T ∧ ∀ pc ∈ L, pc.1.tipSet pc.2.1 pc.2.2 ∩ T ⊆ R.raw := by
    intro L
    induction L with
    | nil =>
      intro _
      obtain ⟨R, hR⟩ := hEmpty
      exact ⟨R, hR ▸ empty_subset T, fun _ hp => False.elim (List.not_mem_nil hp)⟩
    | cons pc L ih =>
      intro hL
      obtain ⟨P, hPT, hpc⟩ := hCover pc (hL List.mem_cons_self)
      obtain ⟨Q, hQT, hQ⟩ := ih (fun _ hp => hL (List.mem_cons_of_mem _ hp))
      rcases closed_raw_total P Q with hPQ | hQP
      · refine ⟨Q, hQT, fun q hq => ?_⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hpc.trans hPQ
        · exact hQ q hq
      · refine ⟨P, hPT, fun q hq => ?_⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hpc
        · exact (hQ q hq).trans hQP
  exact hf s.1 (fun _ hp => hp)

/-- Actual prefix models and chronological piece data realize every
finite full-walk raw initial segment, including real connector gaps. -/
theorem exists_closedPrefix_at_parameter {s : ExplState} {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hRange : range α ∩ H = wsetOf s)
    (hEmpty : ∃ R : ClosedPrefix s, R.raw = ∅)
    (hData : ∀ (pre post : List Piece) (pc : Piece), s.1 = pre ++ pc :: post →
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ),
        PieceData pc A f W η ∧ pc.1.tipSet pc.2.1 pc.2.2 ⊆ range α ∧
        StrictMonoOn (fun t => curveTime α (f (η t))) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2} ∧
        ∀ z ∈ (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2),
          z ∈ range α ∧ curveTime α z ≤ curveTime α (f (η 0)))
    (hModel : ∀ (pre post : List Piece) (pc : Piece), s.1 = pre ++ pc :: post →
      ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ pc.2.2 →
        ∃ R : ClosedPrefix s, R.raw = prefixSet pre pc τ)
    (a : ℝ≥0) : ∃ R : ClosedPrefix s, R.raw = (α '' Icc 0 a) ∩ H := by
  have hCover : ∀ pc ∈ s.1, ∃ R : ClosedPrefix s,
      R.raw ⊆ (α '' Icc 0 a) ∩ H ∧
      pc.1.tipSet pc.2.1 pc.2.2 ∩ ((α '' Icc 0 a) ∩ H) ⊆ R.raw := by
    intro pc hpc
    obtain ⟨pre, post, hs⟩ := List.append_of_mem hpc
    obtain ⟨A, f, W, η, d, hrange, hm, hpre⟩ := hData pre post pc hs
    by_cases hstart : curveTime α (f (η 0)) ≤ a
    · obtain ⟨τ, hτ, hsub, hpcsub⟩ := exists_raw_piece_cut hα d hrange hm hpre hstart
      obtain ⟨R, hR⟩ := hModel pre post pc hs τ hτ
      exact ⟨R, hR ▸ hsub, hR ▸ hpcsub⟩
    · obtain ⟨R, hR⟩ := hEmpty
      refine ⟨R, hR ▸ empty_subset _, ?_⟩
      rintro z ⟨hz, ⟨u, hu, heq⟩, _⟩
      rw [d.tipSet_eq] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      change α u = f (η t) at heq
      have hclock : curveTime α (f (η t)) ≤ a := by
        rw [← heq, curveTime_apply hα.2.1]
        exact hu.2
      exact False.elim (hstart ((hm.monotoneOn (by simp) ht zero_le).trans hclock))
  obtain ⟨R, hsub, hcover⟩ := exists_closedPrefix_finite_cover hEmpty hCover
  refine ⟨R, Subset.antisymm hsub ?_⟩
  intro z hz
  have hzfull : z ∈ wsetOf s := by
    rw [← hRange]
    exact ⟨image_subset_range α _ hz.1, hz.2⟩
  obtain ⟨pc, hpc, hzpc⟩ := mem_iUnion₂.1 hzfull.1
  exact hcover pc hpc ⟨hzpc, hz⟩

end InteractingSLE.Theorem14.WalkIntBoundCut
