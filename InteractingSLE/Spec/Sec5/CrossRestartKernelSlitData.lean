/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma57
import InteractingSLE.Spec.Sec5.CrossCondThetaImg

/-!
# Figure 5.5 in the counterflow restart chart

The frame cancels from the parameter-field data. The two exposed flow sides have
heights `−λ + (θ − π)χ` and `λ + (θ + π)χ`. Their junction weights reuse the general
angle cross-conditioning weights at the dual parameter, with left and right exchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Sec5.CrossRestart

open Sec4 Restart

/-- The Figure 5.5 parameter-field data in the normalized counterflow chart. -/
def fig55Data (κ θ Q pL pR a b a' b' : ℝ) : ℝ → ℝ :=
  stripCounterflowData κ 0 Q (fig55Lower κ θ pL pR a b)
    (fig51Upper (Real.log Q / π) a' b')

/-- The field frame cancels exactly, including the fixed branch terms. -/
theorem stripCounterflowData_fig55Frame (κ α θ Q pL pR a b a' b' x : ℝ) :
    stripCounterflowData κ α Q (fig55LowerFrame κ α θ pL pR a b)
        (fig51UpperFrame κ α (Real.log Q / π) a' b') x =
      fig55Data κ θ Q pL pR a b a' b' x := by
  unfold fig55Data stripCounterflowData stripHData fig55LowerFrame fig51UpperFrame
  split_ifs <;> ring

/-- On the lower right, the exposed right flow side precedes the original height `b`. -/
theorem fig55Data_lower_right {κ θ Q pL pR a b a' b' x : ℝ}
    (hQ : 0 < Q) (hpL : pL ≤ 0) (hx : x < -1) :
    fig55Data κ θ Q pL pR a b a' b' x =
      if Real.log ((x - Q) / (x + 1)) / π < pR
      then -sleLambda κ + (θ - π) * chiC κ else -b - π * chiC κ := by
  have hv : 0 < Real.log ((x - Q) / (x + 1)) / π := by
    apply div_pos _ Real.pi_pos
    apply Real.log_pos
    rw [lt_div_iff_of_neg (by linarith : x + 1 < 0)]
    linarith only [hQ]
  rw [fig55Data, stripCounterflowData_of_lt_neg_one hQ hx]
  unfold fig55Lower
  rw [ite_eq_right (not_lt.2 (hpL.trans hv.le)), ite_eq_right (not_lt.2 hv.le)]
  split_ifs <;> ring

/-- On the lower left, the original height `−a` precedes the exposed left flow side. -/
theorem fig55Data_lower_left {κ θ Q pL pR a b a' b' x : ℝ}
    (hQ : 0 < Q) (hx : Q < x) :
    fig55Data κ θ Q pL pR a b a' b' x =
      if Real.log ((x - Q) / (x + 1)) / π < pL
      then a + π * chiC κ else sleLambda κ + (θ + π) * chiC κ := by
  have hv : Real.log ((x - Q) / (x + 1)) / π < 0 := by
    apply div_neg_of_neg_of_pos _ Real.pi_pos
    apply Real.log_neg
    · exact div_pos (sub_pos.2 hx) (by linarith)
    · rw [div_lt_one (by linarith : 0 < x + 1)]
      linarith only [hQ]
  rw [fig55Data, stripCounterflowData_of_lt hQ hx]
  unfold fig55Lower
  split_ifs with hp
  · ring
  · ring

/-- The untouched upper-right boundary has parameter-field height `−b'`. -/
theorem fig55Data_upper_right {κ θ Q pL pR a b a' b' x : ℝ}
    (hQ : 0 < Q) (hx : x ∈ Ioo (-1 : ℝ) 0) :
    fig55Data κ θ Q pL pR a b a' b' x = -b' := by
  have hv : Q < (Q - x) / (x + 1) := by
    rw [lt_div_iff₀ (by linarith [hx.1] : 0 < x + 1)]
    nlinarith only [hQ, hx.2]
  have hl := div_lt_div_of_pos_right (Real.log_lt_log hQ hv) Real.pi_pos
  rw [fig55Data, stripCounterflowData_of_mem_Ioo_neg_one_zero hQ hx,
    fig51Upper, ite_eq_right (not_lt.2 hl.le)]
  ring

/-- The untouched upper-left boundary has parameter-field height `a'`. -/
theorem fig55Data_upper_left {κ θ Q pL pR a b a' b' x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) Q) :
    fig55Data κ θ Q pL pR a b a' b' x = a' := by
  have hv0 : 0 < (Q - x) / (x + 1) := div_pos (sub_pos.2 hx.2) (by linarith [hx.1])
  have hv : (Q - x) / (x + 1) < Q := by
    rw [div_lt_iff₀ (by linarith [hx.1] : 0 < x + 1)]
    have hQ : 0 < Q := hx.1.trans hx.2
    nlinarith only [hQ, hx.1]
  have hl := div_lt_div_of_pos_right (Real.log_lt_log hv0 hv) Real.pi_pos
  rw [fig55Data, stripCounterflowData_of_mem_Ioo_zero hx,
    fig51Upper, ite_eq_left hl]
  ring

/-- The left junction weight: the old counterflow total is subtracted. -/
abbrev slitJunctionL (κ θ S : ℝ) : ℝ := CrossCond.Theta.cRT θ (16 / κ) S

/-- The right junction weight, with the same normalization. -/
abbrev slitJunctionR (κ θ S : ℝ) : ℝ := CrossCond.Theta.cLT θ (16 / κ) S

/-- Explicit left junction weight. -/
theorem slitJunctionL_eq (κ θ S : ℝ) :
    slitJunctionL κ θ S = (3 / 2 - θ / π) * (16 / κ / 2 - 2) - S := rfl

/-- Explicit right junction weight. -/
theorem slitJunctionR_eq (κ θ S : ℝ) :
    slitJunctionR κ θ S = (3 / 2 + θ / π) * (16 / κ / 2 - 2) - S := rfl

/-- The left junction matches the exposed right side of the original flow slit. -/
theorem slitJunctionL_height {κ : ℝ} (hκ : 0 < κ) (θ S : ℝ) :
    -sleLambda (16 / κ) * (1 + S + slitJunctionL κ θ S) =
      -sleLambda κ + (θ - π) * chiC κ := by
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have he : CrossCond.Theta.cLT (-θ) (16 / κ) S = slitJunctionL κ θ S := by
    unfold slitJunctionL CrossCond.Theta.cLT CrossCond.Theta.cRT
    ring
  have hd : 16 / (16 / κ) = κ := by field_simp
  have hh := CrossCond.Theta.junction_height_leftT hκ' (-θ) S
  rw [he, hd, chiC_sixteen_div hκ] at hh
  change -sleLambda (16 / κ) * (1 + S + slitJunctionL κ θ S) = _ at hh
  calc
    _ = -sleLambda κ + π * -chiC κ + -θ * -chiC κ := hh
    _ = _ := by ring

/-- The right junction matches the exposed left side of the original flow slit. -/
theorem slitJunctionR_height {κ : ℝ} (hκ : 0 < κ) (θ S : ℝ) :
    sleLambda (16 / κ) * (1 + S + slitJunctionR κ θ S) =
      sleLambda κ + (θ + π) * chiC κ := by
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have he : CrossCond.Theta.cRT (-θ) (16 / κ) S = slitJunctionR κ θ S := by
    unfold slitJunctionR CrossCond.Theta.cLT CrossCond.Theta.cRT
    ring
  have hd : 16 / (16 / κ) = κ := by field_simp
  have hh := CrossCond.Theta.junction_height_rightT hκ' (-θ) S
  rw [he, hd, chiC_sixteen_div hκ] at hh
  change sleLambda (16 / κ) * (1 + S + slitJunctionR κ θ S) = _ at hh
  calc
    _ = sleLambda κ - π * -chiC κ + -θ * -chiC κ := hh
    _ = _ := by ring

/-- Equality with the explicit data gives exactly the existing Figure 5.5 datum predicate. -/
theorem isFig55RestartDatum_of_eq_fig55Data {κ α θ Q pL pR a b a' b' : ℝ}
    (hQ : 0 < Q) (hpL : pL ≤ 0) (hpR : 0 ≤ pR) {c : BoundaryWord}
    (h1 : -1 ∈ c.jumps) (hQJ : Q ∈ c.jumps)
    (hc : ∀ x ∉ c.jumps, c.fn x = fig55Data κ θ Q pL pR a b a' b' x) :
    IsFig55RestartDatum κ α θ a b a' b' (Q, c) := by
  refine ⟨hQ, h1, hQJ, pL, pR, hpL, hpR, ?_⟩
  intro x hx
  rw [stripCounterflowData_fig55Frame]
  exact hc x hx

end InteractingSLE.Sec5.CrossRestart
