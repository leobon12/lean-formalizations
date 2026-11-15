/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MbFill
import InteractingSLE.Spec.Supplement.SB2HEntry

/-!
# (L1): lifetimes of corresponding pieces are infinite together and zero together

Packet PROVE-T14-SB2LIFT (round 16; (L1), item 5 of handoff §R14.2). `stCorr_run_of_inputs` and SB2LIFTSET's
`RunInputs.L1` ask, at every pair of corresponding launches, that the lifetimes be infinite together and zero together.

* **Infinite together** is deterministic from the lift relation of the pieces (`LiftRel`, the piece datum of
  `RunInputs`):
  - a regular piece read in a chart with a proper boundary extension has a bounded tip set iff its lifetime is finite
    (`Lx.isCompact_tipSet`; **`not_isBounded_tipSet_top`**: an infinite piece's trace tends to `∞`);
  - the lift image of a bounded set is bounded (**`isBounded_liftImage`**, `β₀` proper), and the lift image of an
    unbounded part of the tail is unbounded (**`not_isBounded_liftImage`**, `γ` proper);
  - **`top_iff_of_liftRel`**.
* **Zero together** holds because neither lifetime is zero at a later launch: `Lk.sb2LowerWalkInputs` for the actual
  walk, and `WalkMarkSeed.ae_noZeroLaterLaunchData` for the relative walk once it is a staged walk.
  **`l1_of_liftRel`** combines both halves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W

/-- **An infinite regular piece read in a chart with a proper boundary extension has an unbounded tip set.** -/
theorem not_isBounded_tipSet_top {c : Chart} (hc : GW1P.HasProperBdryExt c) {W : ℝ≥0 → ℝ}
    (h : GW1P.PieceRegular W ⊤) :
    ¬ Bornology.IsBounded (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  obtain ⟨hW0, hWc, α, hα, hinf⟩ := h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ⊤ → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top) hW0 ht
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨t, ht⟩ := ((hinf rfl).eventually_gt_atTop (M + C)).exists
  have h1 := hM (f (α t)) ⟨α t, ⟨t, show (t : ℝ≥0∞) ≤ ⊤ from le_top, rfl⟩, rfl⟩
  have h2 := hC (α t) (hαH t le_top)
  have h3 := norm_sub_norm_le (α t) (f (α t))
  rw [norm_sub_rev] at h3
  linarith

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The lift image of a bounded set is bounded.** -/
theorem isBounded_liftImage (hβ : Supp9B.IsProperCurve β₀) (hγc : Continuous γ) {S : Set ℂ}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded (liftImage β₀ tL γ S) := by
  obtain ⟨M, hM⟩ := hS.exists_norm_le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hβ.2.2.2.eventually_gt_atTop M)
  have hsub : {s | β₀ (tL + s) ∈ S} ⊆ Icc 0 T := fun s hs => by
    refine ⟨zero_le, ?_⟩
    by_contra h
    have h1 := hT (tL + s) (le_add_left (not_le.1 h).le)
    have h2 := hM _ hs
    linarith
  exact (isCompact_Icc.image hγc).isBounded.subset (image_mono hsub)

/-- **The lift image of an unbounded part of the tail is unbounded.** -/
theorem not_isBounded_liftImage (hβc : Continuous β₀) (hγ : Supp9B.IsProperCurve γ) {S : Set ℂ}
    (hS : ¬ Bornology.IsBounded S) (hSt : S ⊆ β₀ '' Ici tL) : ¬ Bornology.IsBounded (liftImage β₀ tL γ S) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hγ.2.2.2.eventually_gt_atTop M)
  apply hS
  refine ((isCompact_Icc (a := tL) (b := tL + T)).image hβc).isBounded.subset fun z hz => ?_
  obtain ⟨t, ht, rfl⟩ := hSt hz
  obtain ⟨u, rfl⟩ : ∃ u, t = tL + u := ⟨t - tL, (add_tsub_cancel_of_le ht).symm⟩
  refine ⟨tL + u, ⟨le_self_add, (add_le_add_iff_left tL).2 ?_⟩, rfl⟩
  by_contra h
  have h1 := hT u (not_le.1 h).le
  have h2 := hM (γ u) ⟨u, hz, rfl⟩
  linarith

/-- **Lifted pieces are infinite together**: if the relative piece is the lift image of the actual one (which lies on
the tail), both pieces are regular and both charts have proper boundary extensions, then the lifetimes are infinite
together. -/
theorem top_iff_of_liftRel {s₁ s₂ : ExplState} {d₁ d₂ : (ℝ≥0 → ℝ) × ℝ≥0∞} (hβ : Supp9B.IsProperCurve β₀)
    (hγ : Supp9B.IsProperCurve γ) (hc₁ : GW1P.HasProperBdryExt (stChart s₁))
    (hc₂ : GW1P.HasProperBdryExt (stChart s₂)) (hr₁ : GW1P.PieceRegular d₁.1 (min ⊤ d₁.2))
    (hr₂ : GW1P.PieceRegular d₂.1 (min ⊤ d₂.2))
    (htail : (newPc s₁ d₁).1.tipSet (newPc s₁ d₁).2.1 (newPc s₁ d₁).2.2 ⊆ β₀ '' Ici tL)
    (hL : LiftRel β₀ tL γ (newPc s₁ d₁) (newPc s₂ d₂)) : d₂.2 = ⊤ ↔ d₁.2 = ⊤ := by
  have hT₂ : (newPc s₂ d₂).1.tipSet (newPc s₂ d₂).2.1 (newPc s₂ d₂).2.2 =
      liftImage β₀ tL γ ((newPc s₁ d₁).1.tipSet (newPc s₁ d₁).2.1 (newPc s₁ d₁).2.2) := hL
  -- a finite piece has a bounded tip set
  have hfin : ∀ (s : ExplState) (d : (ℝ≥0 → ℝ) × ℝ≥0∞), GW1P.HasProperBdryExt (stChart s) →
      GW1P.PieceRegular d.1 (min ⊤ d.2) → d.2 ≠ ⊤ →
      Bornology.IsBounded ((newPc s d).1.tipSet (newPc s d).2.1 (newPc s d).2.2) := fun s d hc hr hd =>
    (Lx.isCompact_tipSet hc hr (by rw [min_eq_right le_top]; exact hd)).isBounded
  -- an infinite piece has an unbounded tip set
  have hinf : ∀ (s : ExplState) (d : (ℝ≥0 → ℝ) × ℝ≥0∞), GW1P.HasProperBdryExt (stChart s) →
      GW1P.PieceRegular d.1 (min ⊤ d.2) → d.2 = ⊤ →
      ¬ Bornology.IsBounded ((newPc s d).1.tipSet (newPc s d).2.1 (newPc s d).2.2) := fun s d hc hr hd => by
    have hS : min (⊤ : ℝ≥0∞) d.2 = ⊤ := by rw [hd, min_self]
    change ¬ Bornology.IsBounded ((stChart s).tipSet (fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min ⊤ d.2)).toNNReal)
      (min ⊤ d.2))
    rw [hS] at hr ⊢
    exact not_isBounded_tipSet_top hc hr
  constructor
  · intro h₂
    by_contra h₁
    apply hinf s₂ d₂ hc₂ hr₂ h₂
    rw [hT₂]
    exact isBounded_liftImage hβ hγ.1 (hfin s₁ d₁ hc₁ hr₁ h₁)
  · intro h₁
    by_contra h₂
    have hb := hfin s₂ d₂ hc₂ hr₂ h₂
    rw [hT₂] at hb
    exact not_isBounded_liftImage hβ.1 hγ (hinf s₁ d₁ hc₁ hr₁ h₁) htail hb

/-- **(L1) at a pair of lifted pieces**: infinite together by `top_iff_of_liftRel`, zero together since neither
lifetime is zero. -/
theorem l1_of_liftRel {s₁ s₂ : ExplState} {d₁ d₂ : (ℝ≥0 → ℝ) × ℝ≥0∞} (hβ : Supp9B.IsProperCurve β₀)
    (hγ : Supp9B.IsProperCurve γ) (hc₁ : GW1P.HasProperBdryExt (stChart s₁))
    (hc₂ : GW1P.HasProperBdryExt (stChart s₂)) (hr₁ : GW1P.PieceRegular d₁.1 (min ⊤ d₁.2))
    (hr₂ : GW1P.PieceRegular d₂.1 (min ⊤ d₂.2))
    (htail : (newPc s₁ d₁).1.tipSet (newPc s₁ d₁).2.1 (newPc s₁ d₁).2.2 ⊆ β₀ '' Ici tL)
    (hL : LiftRel β₀ tL γ (newPc s₁ d₁) (newPc s₂ d₂)) (hz₁ : d₁.2 ≠ 0) (hz₂ : d₂.2 ≠ 0) :
    (d₂.2 = ⊤ ↔ d₁.2 = ⊤) ∧ (d₂.2 = 0 ↔ d₁.2 = 0) :=
  ⟨top_iff_of_liftRel hβ hγ hc₁ hc₂ hr₁ hr₂ htail hL, iff_of_false hz₂ hz₁⟩

end InteractingSLE.Theorem14.SB.Lk
