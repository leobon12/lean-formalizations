/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsNext

/-!
# Proposition BW1: the conditional word at the terminal tip is admissible for the counterflow

Packet PROVE-BW1-LIFE. Supplement §25, proof of Proposition BW1 (`source/spec/p577-624.md` L837–L845, p. 614):
"An active flow-side interval has one of the terminal counterflow sums (BW1.2) […] All surviving original-real
intervals retain the original admissible counterflow partials […] Consequently the whole conditional word is
admissible".

In the staged-law form: the conditional word after a piece of angle `θ ∈ [−π/2, π/2]` launched with the word `c` is
the stop word `stopWord κ (c, θ, r)` of its record `r`. Every value of the stop word is either a flow-side value
(`−λ − θχ` left of the tip, `λ − θχ` right of it) or a value of the launch word `c` (the force-word value with `m ≥ 1`
marks between the point and the tip is the launch data at a point of the corresponding original interval). Hence, if
`c` satisfies the two ambient height bounds of the counterflow (`c − (π/2)χ < λ` left of `0`,
`−λ < c + (π/2)χ` right of `0`), so does the stop word, **for every record** (`isCfGoodWord_stopWord`). These are the
bounds of `GW1Laws.ae_cfDrvOf_snd_eq_top`: the canonical counterflow of the conditional field lives forever.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.BW1Life

open Exist Exist.StagedLaw Exist.Staged Restart GW1W GW1Conn

variable {κ : ℝ}

/-- **The left side of the stop word satisfies the counterflow's left height bound** at every record, for an angle
`θ ≥ −π/2`, if the launch word does. -/
theorem stopWord_fn_neg_bound (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} {θ : ℝ}
    (hθ : -(Real.pi / 2) ≤ θ)
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ) (r : RecData) {y : ℝ}
    (hy : y < 0) : (stopWord κ (c, θ, r)).fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_neg (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ) hy
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  change (forceWord κ _ _ _ _ _ _ _).fn y + _ < _
  rw [he]
  change -sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.1 i) - θ * chiC κ +
    -(Real.pi / 2) * chiC κ < sleLambda κ
  rcases m with _ | j
  · simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
    nlinarith
  · have hj : j < flowLineNL c.fn c.jumps 0 := by omega
    rw [sum_range_padFL_left κ θ c hj]
    have hsum : ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNL c.fn c.jumps 0))),
          flowLineRhoL κ c.fn c.jumps 0 θ l =
        ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNL c.fn c.jumps 0))),
          flowLineRhoL κ c.fn c.jumps 0 0 l - θ * chiC κ / sleLambda κ := by
      rw [Finset.sum_congr rfl (fun l _ => flowLineRhoL_theta κ c.fn c.jumps θ l), Finset.sum_add_distrib,
        sum_filter_le_ite_val_eq_zero _ ⟨j, hj⟩ ⟨0, by unfold flowLineNL; omega⟩ rfl]
      ring
    rw [hsum, GW3Word.filter_le_eq_filter_le_flowLineXL]
    obtain ⟨y', -, hy', hy'J, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hκ
      c.isPiecewiseConstantBoundaryData (lo := flowLineXL c.fn c.jumps 0 ⟨j, hj⟩ - 1) (by linarith)
      (GW3Word.flowLineXL_nonpos c.fn c.jumps ⟨j, hj⟩)
    rw [hS, Sec4.cumWeightLeft]
    have h1 := hL y' (lt_of_lt_of_le hy' (GW3Word.flowLineXL_nonpos c.fn c.jumps ⟨j, hj⟩)) hy'J
    have e : -sleLambda κ * (1 + (-c.fn y' / sleLambda κ - 1 - θ * chiC κ / sleLambda κ)) - θ * chiC κ =
        c.fn y' := by
      field_simp
      ring
    rw [e]
    exact h1

/-- **The right side of the stop word satisfies the counterflow's right height bound** at every record, for an angle
`θ ≤ π/2`, if the launch word does. -/
theorem stopWord_fn_pos_bound (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} {θ : ℝ}
    (hθ : θ ≤ Real.pi / 2)
    (hR : ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + Real.pi / 2 * chiC κ) (r : RecData) {y : ℝ}
    (hy : 0 < y) : -sleLambda κ < (stopWord κ (c, θ, r)).fn y + Real.pi / 2 * chiC κ := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_pos (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ)
    (isMarkOrder_stopWord c r).2.1 hy
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  change _ < (forceWord κ _ _ _ _ _ _ _).fn y + _
  rw [he]
  change -sleLambda κ < sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.2 i) - θ * chiC κ +
    Real.pi / 2 * chiC κ
  rcases m with _ | j
  · simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
    nlinarith
  · have hj : j < flowLineNR c.fn c.jumps 0 := by omega
    rw [sum_range_padFL_right κ θ c hj]
    have hsum : ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNR c.fn c.jumps 0))),
          flowLineRhoR κ c.fn c.jumps 0 θ l =
        ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNR c.fn c.jumps 0))),
          flowLineRhoR κ c.fn c.jumps 0 0 l + θ * chiC κ / sleLambda κ := by
      rw [Finset.sum_congr rfl (fun l _ => flowLineRhoR_theta κ c.fn c.jumps θ l), Finset.sum_add_distrib,
        sum_filter_le_ite_val_eq_zero _ ⟨j, hj⟩ ⟨0, by unfold flowLineNR; omega⟩ rfl]
    rw [hsum, GW3Word.filter_le_eq_filter_flowLineXR_le]
    obtain ⟨y', hy', hy'J, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hκ
      c.isPiecewiseConstantBoundaryData (GW3Word.flowLineXR_nonneg c.fn c.jumps ⟨j, hj⟩)
    rw [hS, Sec4.cumWeightRight]
    have h1 := hR y' (lt_of_le_of_lt (GW3Word.flowLineXR_nonneg c.fn c.jumps ⟨j, hj⟩) hy') hy'J
    have e : sleLambda κ * (1 + (c.fn y' / sleLambda κ - 1 + θ * chiC κ / sleLambda κ)) - θ * chiC κ =
        c.fn y' := by
      field_simp
      ring
    rw [e]
    exact h1

/-- **BW1's conditional word is admissible** (p. 614, "the whole conditional word is admissible"): for
`0 < κ < 4` and `θ ∈ [−π/2, π/2]`, if the launch word satisfies the two ambient height bounds of the counterflow,
the stop word of every record satisfies them (`GW1Laws.IsCfGoodWord`). -/
theorem isCfGoodWord_stopWord (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} {θ : ℝ}
    (hθ : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + Real.pi / 2 * chiC κ) (r : RecData) :
    GW1Laws.IsCfGoodWord κ (stopWord κ (c, θ, r)) :=
  ⟨isSorted_stopWord κ _, fun _ hy _ => stopWord_fn_neg_bound hκ hκ4 hθ.1 hL r hy,
    fun _ hy _ => stopWord_fn_pos_bound hκ hκ4 hθ.2 hR r hy⟩

end InteractingSLE.Theorem14.BW1Life
