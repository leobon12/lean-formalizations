/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideSpec

/-!
# Theorem 1.4's walk leaves: the lower union of an explored set is connected

Packet PROVE-T14-WALKSIDE. Proposition 3.8 (the comparison of two local-set means, landed as
`Sec7.PocketStopSide.ae_tendsto_sub_of_marked_union`) needs every component of `A ∪ {Im ≤ 0}` to be unbounded for both
compared sets. For the explored set of a run whose launched pieces are regular this holds because the set, together
with the closed lower half-plane, is **preconnected**: every launched piece is the image of its continuous trace under
the boundary extension of the launch chart (`CounterflowRange.tipSet_stopped_eq_of_tendsto`), which starts at the
boundary value of the chart at the seed, a point of the earlier explored set or of `ℝ`
(`GW1RestartFinal.chart_boundaryRange_run`).

* **`isPreconnected_ordinary_union_lower`** (by induction on the run);
* **`not_isBounded_lowerUnion_stageSet`**: every component of `stageSet k ∪ {Im ≤ 0}` is unbounded.

Deterministic. R48: serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged

section Lower

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The times before an extended time form a preconnected set. -/
theorem isPreconnected_le_ennreal (S : ℝ≥0∞) : IsPreconnected {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
  refine OrdConnected.isPreconnected ⟨fun a _ c hc x hx => ?_⟩
  exact le_trans (ENNReal.coe_le_coe.2 hx.2) hc

/-- The closed lower half-plane is not bounded. -/
theorem not_isBounded_of_lower_subset {S : Set ℂ} (hS : {w : ℂ | w.im ≤ 0} ⊆ S) : ¬ IsBounded S := by
  intro hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hmem : (-((|R| + 1 : ℝ) : ℂ) * Complex.I) ∈ S := hS (by
    simp only [mem_ofPred_eq, neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, neg_nonpos]
    positivity)
  have h := hR _ hmem
  rw [neg_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < |R| + 1)] at h
  linarith [le_abs_self R]

/-- **The ordinary part of a regular run, together with the closed lower half-plane, is preconnected.** -/
theorem isPreconnected_ordinary_union_lower (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    ∀ n : ℕ, IsPreconnected ((⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) ∪
      {w : ℂ | w.im ≤ 0})
  | 0 => by
    have h0 : (ExplState.run κ b jumps spec D 0).1 = [] := rfl
    rw [h0]
    simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union]
    exact (convex_halfSpace_le (f := Complex.imLm) Complex.imLm.isLinear 0).isPreconnected
  | n + 1 => by
    have ih := isPreconnected_ordinary_union_lower spec D hreg n
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · rw [GW1P.pieces_run_succ_of_noLaunch spec D hl]
      exact ih
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hl
      set S := min (instrTime spec n) (D n).2 with hS
      obtain ⟨hW0, hWc, α, hα, -⟩ := hreg n c θ hl
      obtain ⟨hconf, f, hf, hfr⟩ := GW1RestartFinal.chart_boundaryRange_run spec D hreg n
      have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
        Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
      have hT := CounterflowRange.tipSet_stopped_eq_of_tendsto (c := stChart (ExplState.run κ b jumps spec D n))
        hα hWc hW0 fun t ht => hf _ (hαH t ht)
      rw [he, CounterflowRange.pieces_launch]
      have hsplit : (⋃ p ∈ (ExplState.run κ b jumps spec D n).1 ++
            [((ExplState.run κ b jumps spec D n).2.2.2.2.1,
              fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal, S)], p.1.tipSet p.2.1 p.2.2) ∪
          {w : ℂ | w.im ≤ 0} =
          ((⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) ∪ {w : ℂ | w.im ≤ 0}) ∪
            f '' (α '' {t | (t : ℝ≥0∞) ≤ S}) := by
        rw [← hT]
        ext z
        simp only [mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨p, hp | rfl, hz⟩ | hz)
          · exact Or.inl (Or.inl ⟨p, hp, hz⟩)
          · exact Or.inr hz
          · exact Or.inl (Or.inr hz)
        · rintro ((⟨p, hp, hz⟩ | hz) | hz)
          · exact Or.inl ⟨p, Or.inl hp, hz⟩
          · exact Or.inr hz
          · exact Or.inl ⟨_, Or.inr rfl, hz⟩
      rw [hsplit]
      -- the new piece is preconnected and starts on the old set
      have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
      have hpc : IsPreconnected (f '' (α '' {t | (t : ℝ≥0∞) ≤ S})) :=
        ((isPreconnected_le_ennreal S).image α hα.2.1).image f
          (hfc.mono (by rintro _ ⟨t, ht, rfl⟩; exact hαH t ht))
      have h0mem : f 0 ∈ f '' (α '' {t | (t : ℝ≥0∞) ≤ S}) := ⟨α 0, ⟨0, by simp, rfl⟩, by rw [hα.1]⟩
      have h0Hb : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
      have h0H : (0 : ℂ) ∉ H := by simp [QuantumZipper.H]
      have hf0 : f 0 ∈ (⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) ∪
          {w : ℂ | w.im ≤ 0} := by
        rcases hfr 0 h0Hb h0H with hA | hA
        · rcases hA with (hA | hA) | hA
          · rw [mem_singleton_iff] at hA
            exact Or.inr (by rw [hA]; simp)
          · exact Or.inl hA
          · obtain ⟨a, -, x, -, hx⟩ := mem_iUnion₂.1 hA
            exact Or.inr (by rw [← hx]; simp)
        · refine Or.inr ?_
          have hcl : f 0 ∈ closure H := by
            have := GW1P.neBot_nhdsWithin_H h0Hb
            refine mem_closure_of_tendsto (hf 0 h0Hb) ?_
            exact eventually_nhdsWithin_of_forall fun w hw => hconf.2.1 hw
          rw [QuantumZipper.CA.Car.closure_H_eq_Hbar] at hcl
          change (0 : ℝ) ≤ (f 0).im at hcl
          have : ¬ (0 : ℝ) < (f 0).im := hA
          change (f 0).im ≤ 0
          linarith [not_lt.1 this]
      exact ih.union (f 0) hf0 h0mem hpc

/-- **Every component of the lower union of an explored set is unbounded** (launched pieces regular). -/
theorem not_isBounded_lowerUnion_stageSet {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c, θ) → GW1P.PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2)) (n : ℕ) :
    ∀ z ∈ LocalSets.lowerUnion (WalkLaw.stageSet κ b jumps spec E n ω),
      ¬ IsBounded (connectedComponentIn (LocalSets.lowerUnion (WalkLaw.stageSet κ b jumps spec E n ω)) z) := by
  intro z hz
  have e : LocalSets.lowerUnion (WalkLaw.stageSet κ b jumps spec E n ω) =
      (⋃ p ∈ (ExplState.run κ b jumps spec (fun j => E j ω) n).1, p.1.tipSet p.2.1 p.2.2) ∪ {w : ℂ | w.im ≤ 0} := by
    rw [WalkLaw.stageSet, WangWu.lowerUnion_inter_H]
    rfl
  have hpc := isPreconnected_ordinary_union_lower spec (fun j => E j ω) hreg n
  rw [← e] at hpc
  rw [hpc.connectedComponentIn hz]
  exact not_isBounded_of_lower_subset (by rw [e]; exact subset_union_right)

end Lower

end InteractingSLE.Theorem14.WalkSide
