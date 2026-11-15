/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnFootprint
import InteractingSLE.Spec.Sec7.R6TnChart

/-!
# The left force-mark landing in the initial physical boundary

PROVE-R6-TWO. This transports the curve-generated hull statement to any
initial Jordan coordinate. In particular, the landing is on the
initial pocket's frontier and cannot equal an interior physical tip.
Its membership in the required inner shared subarc remains geometric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec7.R6Tn

open WangWu (chartAL chartAR)
open R6Fc

/-- Identify the initial coordinate of the canonical physical force-mark
landing with the boundary extension of the inverse Loewner map. -/
theorem initial_coord_left_force {O : Chart} {ψ E₀ : ℂ → ℂ}
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar) :
    ψ (extendFrom H O.2.1 (chartAL W q : ℂ)) =
      extendFrom H (fwdMapInv W q) (chartAL W q : ℂ) := by
  have hp : extendFrom H O.2.1 (chartAL W q : ℂ) =
      E₀ (extendFrom H (fwdMapInv W q) (chartAL W q : ℂ)) :=
    extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar _)
      (tendsto_of_extension hE hEc _)
  rw [hp]
  exact hcomp _ ((extendFrom_props hη hW hW0 hq).2.2 (real_mem_Hbar _))

/-- The canonical physical left force mark lands on the original
pocket frontier, independently of trace simplicity or reverse visits. -/
theorem left_force_mem_initial_frontier {C : Set ℂ} {O : Chart} {ψ E₀ : ℂ → ℂ}
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hψH : MapsTo ψ C H) (hE₀m : MapsTo E₀ Hbar (closure C))
    (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar) :
    extendFrom H O.2.1 (chartAL W q : ℂ) ∈ frontier C := by
  have hp : extendFrom H O.2.1 (chartAL W q : ℂ) =
      E₀ (extendFrom H (fwdMapInv W q) (chartAL W q : ℂ)) :=
    extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar _)
      (tendsto_of_extension hE hEc _)
  have hpC : extendFrom H O.2.1 (chartAL W q : ℂ) ∈ closure C := by
    rw [hp]
    exact hE₀m ((extendFrom_props hη hW hW0 hq).2.2 (real_mem_Hbar _))
  have hpnot : extendFrom H O.2.1 (chartAL W q : ℂ) ∉ C := by
    intro h
    have hH := hψH h
    rw [initial_coord_left_force hη hW hW0 hq hcomp hE hEc] at hH
    have hreal := (left_boundary_real_nonpos hη hW hW0 hq (le_refl (chartAL W q))).1
    change 0 < (extendFrom H (fwdMapInv W q) (chartAL W q : ℂ)).im at hH
    exact (lt_irrefl (0 : ℝ)) (hreal ▸ hH)
  exact ⟨hpC, fun h => hpnot (interior_subset h)⟩

/-- In the initial coordinate, the physical left force-mark landing is
the least real point of the closed curve-generated hull. -/
theorem physical_left_force_isLeast {O : Chart} {ψ E₀ : ℂ → ℂ}
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 < q)
    (hgap : chartAL W q < chartAR W q) (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar) :
    IsLeast {y : ℝ | (y : ℂ) ∈ closure (fwdHull W q)}
      (ψ (extendFrom H O.2.1 (chartAL W q : ℂ))).re := by
  rw [initial_coord_left_force hη hW hW0 hq.le hcomp hE hEc]
  exact left_force_landing_isLeast hη hW hW0 hq hgap

end InteractingSLE.Sec7.R6Tn
