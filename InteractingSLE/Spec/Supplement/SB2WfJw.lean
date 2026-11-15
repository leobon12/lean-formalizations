/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfCls
import InteractingSLE.Spec.Supplement.SB2WeStep
import InteractingSLE.Spec.Supplement.SB2VnTr

/-!
# The junction invariant of the lower walk: definition, root and moves

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). `JW κ θ ψ u b β s`: for every continuous boundary
extension `g` of the inverse chart of the state `s`, every chart point `r` right of the image of the whole untouched
left ray at which the word `β` continues with the old lower-side height `−λ − θχ`, and every real `p = g r`: `p` is at
or right of the left record, and right of the upper seed `u` it is not a bad point of the upper flow at angle `ψ`.

* `cumWeightRight_gt_of_lowSide`: a right limit equal to the lower-side height is never upper-bad (`θ < ψ`);
* `jw_root`, `jw_moveAlong`: the invariant at the root (only coincidence junctions) and through rightward moves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- **The junction invariant** of a state of the lower walk (angle `θ`), for the upper flow from `u` at angle `ψ`. -/
def JW (κ θ ψ u : ℝ) (b : ℝ → ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  ∀ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} → EqOn g (stChart s).2.1 H →
  ∀ r : ℝ, (∀ x, x < stRecL s → rProf (stChart s) x < r) →
  (∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ β.jumps → β.fn y = -sleLambda κ - θ * chiC κ) →
  ∀ p : ℝ, g (r : ℂ) = p → stRecL s ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ))

/-- **A lower-side right limit is not upper-bad.** -/
theorem cumWeightRight_gt_of_lowSide {κ θ ψ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {b : ℝ → ℝ}
    {p : ℝ} (hp : rightLim b p = -sleLambda κ - θ * chiC κ) :
    -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [hp]
  unfold Sec4.cumWeightRight
  have h1 : 0 < (ψ - θ) * chiC κ := mul_pos (by linarith) hχ
  have h2 : (-sleLambda κ - θ * chiC κ + ψ * chiC κ) / sleLambda κ = -1 + (ψ - θ) * chiC κ / sleLambda κ := by
    field_simp
    ring
  rw [h2]
  have : 0 < (ψ - θ) * chiC κ / sleLambda κ := div_pos h1 hl
  linarith

/-- **The junction invariant at the root**: the chart is the identity, so a junction is a real point with the original
data right of it equal to the lower-side height. -/
theorem jw_root {κ θ ψ u : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {c₀ : BoundaryWord} (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    JW κ θ ψ u b (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hci : (stChart (ExplState.init 0)).2.1 = fun z => z + ((0 : ℝ) : ℂ) := by
    funext z
    simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hL0 : stRecL (ExplState.init 0) = 0 := rfl
  intro g hgc hgi r hr hlow p hp
  -- the boundary map is the identity
  have hgid : EqOn g (fun z => z) {z | 0 ≤ z.im} :=
    Vn.eqOn_closedH_of_eqOn_H hgc continuous_id.continuousOn fun z hz => by
      rw [hgi hz, hci]; simp
  have hrp : r = p := by
    have h1 := hgid (show (0 : ℝ) ≤ ((r : ℂ)).im by simp)
    rw [hp] at h1
    have h2 : ((r : ℂ)) = (p : ℂ) := h1.symm
    exact_mod_cast h2
  subst hrp
  rw [hL0]
  rw [hL0, hprof] at hr
  have hr0 : 0 ≤ r := by
    by_contra hneg
    push Not at hneg
    exact absurd (hr r hneg) (by simp)
  refine ⟨hr0, fun _ => cumWeightRight_gt_of_lowSide hκ hκ4 hθψ ?_⟩
  obtain ⟨ε, hε, hεl⟩ := hlow
  refine Sec4.rightLim_eq_of_forall_notMem (jumps ∪ (BoundaryWord.shiftW 0 c₀).jumps) (a := r + ε)
    (by linarith) fun t ht htJ => ?_
  have h1 : t ∉ jumps := fun h => htJ (Finset.mem_union_left _ h)
  have h2 : t ∉ (BoundaryWord.shiftW 0 c₀).jumps := fun h => htJ (Finset.mem_union_right _ h)
  have := hεl t ht h2
  rw [BoundaryWord.fn_shiftW, add_zero, hc₀ t h1] at this
  exact this

/-- **The junction invariant survives a rightward move** (chart and word recentred by the image `a` of the new point;
the left record does not change). -/
theorem jw_moveAlong {κ θ ψ u : ℝ} {b : ℝ → ℝ} {γ : BoundaryWord} {s₁ : ExplState} (hI : JW κ θ ψ u b γ s₁)
    (w : ℝ) :
    JW κ θ ψ u b (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ true w true) := by
  set a := rProf (stChart s₁) w with hadef
  have hprof : ∀ x, rProf (stChart (ExplState.moveAlong s₁ true w true)) x = rProf (stChart s₁) x - a := by
    intro x
    rw [stChart_moveAlong, rProf_recenter]
    rfl
  have hL : stRecL (ExplState.moveAlong s₁ true w true) = stRecL s₁ := stRecL_moveAlong_true' _ _ _
  intro g hgc hgi r hr hlow p hp
  -- the boundary map of the old chart
  set g₁ : ℂ → ℂ := fun z => g (z - (a : ℂ)) with hg₁
  have hg₁c : ContinuousOn g₁ {z | 0 ≤ z.im} :=
    hgc.comp (continuous_id.sub continuous_const).continuousOn fun z hz => by
      show 0 ≤ (z - (a : ℂ)).im
      simpa using hz
  have hg₁i : EqOn g₁ (stChart s₁).2.1 H := by
    intro z hz
    have hz' : z - (a : ℂ) ∈ H := by
      have h0 : (0 : ℝ) < z.im := hz
      show 0 < (z - (a : ℂ)).im
      simpa using h0
    show g (z - (a : ℂ)) = (stChart s₁).2.1 z
    rw [hgi hz', stChart_moveAlong]
    simp [InteractingSLE.Chart.recenter, hadef, rProf]
  have hr₁ : ∀ x, x < stRecL s₁ → rProf (stChart s₁) x < r + a := by
    intro x hx
    have := hr x (by rw [hL]; exact hx)
    rw [hprof] at this
    linarith
  have hlow₁ : ∃ ε > 0, ∀ y ∈ Ioo (r + a) (r + a + ε), y ∉ γ.jumps → γ.fn y = -sleLambda κ - θ * chiC κ := by
    obtain ⟨ε, hε, hεl⟩ := hlow
    refine ⟨ε, hε, fun y hy hyJ => ?_⟩
    have hyJ' : y - a ∉ (BoundaryWord.shiftW a γ).jumps := by
      rw [BoundaryWord.jumps_shiftW]
      intro h
      obtain ⟨z, hz, hze⟩ := Finset.mem_image.1 h
      have : z = y := by linarith
      exact hyJ (this ▸ hz)
    have := hεl (y - a) ⟨by linarith [hy.1], by linarith [hy.2]⟩ hyJ'
    rwa [BoundaryWord.fn_shiftW, sub_add_cancel] at this
  have hp₁ : g₁ ((r + a : ℝ) : ℂ) = p := by
    show g (((r + a : ℝ) : ℂ) - (a : ℂ)) = p
    rw [show ((r + a : ℝ) : ℂ) - (a : ℂ) = (r : ℂ) by push_cast; ring]
    exact hp
  rw [hL]
  exact hI g₁ hg₁c hg₁i (r + a) hr₁ hlow₁ p hp₁

end InteractingSLE.Theorem14.SB.Wf
