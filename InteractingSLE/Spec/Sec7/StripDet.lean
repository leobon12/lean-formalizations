/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.AdmissibleFlowCodeDrv
import InteractingSLE.Spec.Sec7.Lemma71GFlow

/-!
# (4.4) from boundary heights, for flow-line words

Packet PROVE-STRIPSYS21, item (i). The admissible-word determination (`AdmCode.ae_admDrv_eq_of_ae_condExpKernel`)
needs the flow-line word of the conditional field to satisfy (4.4). (4.4) is a statement about index partial sums of
the weights; for a word with strictly ordered positions the partial sums are the cumulative weights read off the force
boundary data between consecutive marks (`Sec4.cumWeightLeft_forceBoundaryData`). Hence:

* **`cond44_of_forall_not_mem`**: a word with strictly ordered positions satisfies (4.4) as soon as its force boundary
  data is at most `−λ + πχ` left of `0` and at least `λ` right of `0`, off a finite set (Remark 4.1's form of (4.4));
* **`strictAnti_flowLineXL`**, **`strictMono_flowLineXR`**: the positions of a flow-line word from `0` are strictly
  ordered;
* **`cond44_flowLine_of_heights`**: the angle-`θ` flow-line word from `0` of piecewise-constant data `b` satisfies (4.4)
  when `b + θχ ≤ −λ + πχ` left of `0` and `b + θχ ≥ λ` right of `0` (off the jumps) — the general form of
  `Lemma71H.cond44_flowLine_prop74Data`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripDet

open Sec4 QuantumZipper

/-! ### (4.4) from the force boundary data -/

section Cond44

variable {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **(4.4) from heights.** A word whose left positions are strictly decreasing and nonpositive and whose right
positions are strictly increasing and nonnegative satisfies (4.4) when its force boundary data is at most `−λ + πχ`
at negative points and at least `λ` at positive points, off a finite set `E`. -/
theorem cond44_of_forall_not_mem (hk : 0 < k) (hxL : StrictAnti xL) (hxL0 : ∀ i, xL i ≤ 0)
    (hxR : StrictMono xR) (hxR0 : ∀ i, 0 ≤ xR i) (E : Finset ℝ)
    (hL : ∀ x : ℝ, x < 0 → x ∉ E → forceBoundaryData k ρL ρR xL xR x ≤ -sleLambda k + Real.pi * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ E → sleLambda k ≤ forceBoundaryData k ρL ρR xL xR x) :
    Cond44 k ρL ρR := by
  refine ⟨fun j hj1 hjn => ?_, fun j hj1 hjn => ?_⟩
  · set i₀ : Fin nL := ⟨j - 1, by omega⟩ with hi₀
    obtain ⟨a, hau, ha⟩ : ∃ a, a < xL i₀ ∧ ∀ i : Fin nL, j ≤ i.val → xL i ≤ a := by
      by_cases hj : j < nL
      · refine ⟨xL ⟨j, hj⟩, hxL (Fin.mk_lt_mk.2 (by omega)), fun i hi => hxL.antitone ?_⟩
        exact Fin.mk_le_mk.2 hi
      · exact ⟨xL i₀ - 1, by linarith, fun i hi => absurd i.isLt (by omega)⟩
    obtain ⟨x, hax, hxu, hxE⟩ := exists_mem_Ioo_not_mem E hau
    have hx0 : x < 0 := hxu.trans_le (hxL0 i₀)
    have hS : univ.filter (fun i => x < xL i) = univ.filter (fun i : Fin nL => i.val < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hc
        exact absurd (ha i (not_lt.1 hc)) (not_le.2 (hax.trans h))
      · intro h
        exact hxu.trans_le (hxL.antitone (Fin.mk_le_mk.2 (by omega)))
    have := (le_cumWeightLeft_iff hk).2 (hL x hx0 hxE)
    rwa [cumWeightLeft_forceBoundaryData hk ρL ρR xL xR hx0, hS] at this
  · set i₀ : Fin nR := ⟨j - 1, by omega⟩ with hi₀
    obtain ⟨u, hlu, hu⟩ : ∃ u, xR i₀ < u ∧ ∀ i : Fin nR, j ≤ i.val → u ≤ xR i := by
      by_cases hj : j < nR
      · refine ⟨xR ⟨j, hj⟩, hxR (Fin.mk_lt_mk.2 (by omega)), fun i hi => hxR.monotone ?_⟩
        exact Fin.mk_le_mk.2 hi
      · exact ⟨xR i₀ + 1, by linarith, fun i hi => absurd i.isLt (by omega)⟩
    obtain ⟨x, hlx, hxu, hxE⟩ := exists_mem_Ioo_not_mem E hlu
    have hx0 : 0 < x := (hxR0 i₀).trans_lt hlx
    have hS : univ.filter (fun i => xR i ≤ x) = univ.filter (fun i : Fin nR => i.val < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hc
        exact absurd (hu i (not_lt.1 hc)) (not_le.2 (h.trans_lt hxu))
      · intro h
        exact (hxR.monotone (Fin.mk_le_mk.2 (by omega) : i ≤ i₀)).trans hlx.le
    have h1 := hR x hx0 hxE
    rw [forceBoundaryData_of_nonneg ρL ρR xL xR hx0.le, hS] at h1
    have hl := sleLambda_pos hk
    nlinarith

end Cond44

/-! ### The positions of a flow-line word are strictly ordered -/

theorem strictAnti_flowLineXL (b : ℝ → ℝ) (J : Finset ℝ) : StrictAnti (flowLineXL b J 0) := by
  set s := (PiecewiseConstantBoundaryData.jumpSet b J).filter (· < (0 : ℝ)) with hs
  change StrictAnti (Fin.cons (0 : ℝ) (fun i => s.orderEmbOfFin rfl (Fin.rev i) - 0) : Fin (s.card + 1) → ℝ)
  intro i i' hii'
  revert i
  refine Fin.cases (fun i h => absurd h (Fin.not_lt_zero i)) (fun m' => ?_) i'
  intro i
  refine Fin.cases (fun _ => ?_) (fun m h => ?_) i
  · rw [Fin.cons_succ, Fin.cons_zero, sub_zero]
    exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem s rfl (Fin.rev m'))).2
  · rw [Fin.cons_succ, Fin.cons_succ, sub_zero, sub_zero]
    exact (s.orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.2 (Fin.succ_lt_succ_iff.1 h))

theorem strictMono_flowLineXR (b : ℝ → ℝ) (J : Finset ℝ) : StrictMono (flowLineXR b J 0) := by
  set s := (PiecewiseConstantBoundaryData.jumpSet b J).filter ((0 : ℝ) < ·) with hs
  change StrictMono (Fin.cons (0 : ℝ) (fun i => s.orderEmbOfFin rfl i - 0) : Fin (s.card + 1) → ℝ)
  intro i i' hii'
  revert i
  refine Fin.cases (fun i h => absurd h (Fin.not_lt_zero i)) (fun m' => ?_) i'
  intro i
  refine Fin.cases (fun _ => ?_) (fun m h => ?_) i
  · rw [Fin.cons_succ, Fin.cons_zero, sub_zero]
    exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem s rfl m')).2
  · rw [Fin.cons_succ, Fin.cons_succ, sub_zero, sub_zero]
    exact (s.orderEmbOfFin rfl).strictMono (Fin.succ_lt_succ_iff.1 h)

/-- **(4.4) for the angle-`θ` flow-line word from `0`, from the boundary heights**: `b + θχ ≤ −λ + πχ` left of `0`
and `b + θχ ≥ λ` right of `0`, off the jump candidates. -/
theorem cond44_flowLine_of_heights {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ * chiC κ) :
    Cond44 κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) := by
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  refine cond44_of_forall_not_mem hκ (strictAnti_flowLineXL b J) hF.2.1 (strictMono_flowLineXR b J) hF.2.2.2
    (insert 0 J) (fun x hx hxE => ?_) (fun x hx hxE => ?_)
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hx.ne (by rwa [add_zero]), add_zero]
    exact hL x hx hxJ
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hx.ne' (by rwa [add_zero]), add_zero]
    exact hR x hx hxJ

end StripDet

end Sec7

end InteractingSLE
