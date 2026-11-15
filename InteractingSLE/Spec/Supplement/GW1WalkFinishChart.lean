/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinish

/-!
# GW1: identifying a boundary record through its exterior ray

A continuous boundary map is calibrated at the record by its inverse correspondence on
the untouched exterior ray. Only monotonicity and arbitrarily small positive chart
coordinates are needed. The final lemmas pass these boundary values to physical radial tips.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain

/-- Exterior inverse correspondence determines the boundary value at its record. -/
theorem record_value_of_profile {m : ℝ → ℝ} {a : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousAt f 0) (hmono : StrictMonoOn m (Ioi a))
    (hpos : ∀ x, a < x → 0 < m x)
    (hsmall : ∀ ε > 0, ∃ x, a < x ∧ m x < ε)
    (hinv : ∀ x, a < x → f (m x) = (x : ℂ)) : f 0 = (a : ℂ) := by
  have hm : Tendsto m (𝓝[>] a) (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro l hl
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hl.trans (hpos x hx)
    · intro u hu
      obtain ⟨x₀, hx₀, hmx₀⟩ := hsmall u hu
      have hev : ∀ᶠ x in 𝓝[>] a, x < x₀ :=
        (eventually_lt_nhds hx₀).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hev] with x hx hxx₀
      exact (hmono hx hx₀ hxx₀).trans hmx₀
  have hleft := hf.tendsto.comp hm
  have hright : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] a) (𝓝 (a : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hinv x hx).symm

theorem right_record_value {s : ExplState} (hs : GW1W.RProf s) {f : ℝ → ℂ}
    (hf : ContinuousAt f 0)
    (hinv : ∀ x, stRecR s < x → f (rProf (stChart s) x) = (x : ℂ)) :
    f 0 = (stRecR s : ℂ) :=
  record_value_of_profile hf hs.2.1.1 hs.2.2.1 hs.2.2.2 hinv

/-- Reflection changes both the input and the physical output coordinates. -/
theorem left_record_value {s : ExplState} (hs : GW1W.LProf s) {f : ℝ → ℂ}
    (hf : ContinuousAt f 0)
    (hinv : ∀ x, x < stRecL s → f (rProf (stChart s) x) = (x : ℂ)) :
    f 0 = (stRecL s : ℂ) := by
  have hg : ContinuousAt (fun y : ℝ => -f (-y)) 0 := by
    have hn : ContinuousAt (fun y : ℝ => -y) 0 := continuous_neg.continuousAt
    exact ((show ContinuousAt f (-0) by simpa only [neg_zero] using hf).comp hn).neg
  have he := record_value_of_profile hg hs.2.1.1 hs.2.2.1 hs.2.2.2 (fun x hx => by
    have h := hinv (-x) (by linarith only [hx])
    change -f (-lProf (stChart s) x) = (x : ℂ)
    rw [GW1W.lProf_eq, neg_neg, h, Complex.ofReal_neg, neg_neg])
  simpa only [neg_zero, Complex.ofReal_neg, neg_inj] using he

/-- A whole-half-plane boundary limit at zero supplies the radial limit in `tipAt`. -/
theorem tipAt_zero_of_boundary_limit {c : Chart} {q : ℂ} {W : ℝ≥0 → ℝ}
    (hW : Continuous (fun r : ℝ => W r.toNNReal)) (hW0 : W 0 = 0)
    (hc : Tendsto c.2.1 (𝓝[H] 0) (𝓝 q)) : c.tipAt W 0 q := by
  have h := hc.comp tendsto_ofReal_mul_I_nhdsWithin_H
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  change c.2.1 ((y : ℂ) * Complex.I) = _
  simp only [NNReal.coe_zero]
  rw [fwdMapInv_zero_time hW (by simpa only [Real.toNNReal_zero] using hW0)
    (show (y : ℂ) * Complex.I ∈ H from
      show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)]

/-- At a finite launch the stored chart is exactly the inverse map defining its endpoint tip. -/
theorem tipAt_stop_of_boundary_limit {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {k : ℕ} {θ : ℝ} {q : ℂ} (hfin : D.2 ≠ ⊤)
    (hc : Tendsto (stChart (ExplState.launch s k D θ ⊤)).2.1 (𝓝[H] 0) (𝓝 q)) :
    (stChart s).tipAt (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2.toNNReal q := by
  change Tendsto (ExplState.launch s k D θ ⊤).2.2.2.2.1.2.1 _ _ at hc
  rw [chart_launch _ _ _ _ _ (GW1W.min_top_ne_top hfin)] at hc
  have h := hc.comp tendsto_ofReal_mul_I_nhdsWithin_H
  unfold Chart.tipAt
  convert h using 1
  funext y
  simp only [Chart.loewner, Function.comp_apply, min_eq_right (le_top : D.2 ≤ ⊤), stChart]

end InteractingSLE.Theorem14.GW1WalkFinish
