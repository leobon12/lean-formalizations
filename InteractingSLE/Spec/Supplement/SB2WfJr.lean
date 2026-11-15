/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJw

/-!
# Junctions on the untouched right ray

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). Right of the tip a state's chart is the untouched right
ray (`RProf`), free and continuous there, with the original data (`ROrig`). So a chart point `r ≥ 0` at which the word
continues with the lower-side height reads back to a real point `p ≥ stRecR` with the original data equal to that
height just right of `p`; it is not upper-bad (`jw_rightRay`). This is the hypothesis `hRay` of `jw_launch`, and for
`r = 0` it gives the base of the next launch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

variable {κ θ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The read-back of the right ray**: `g (rProf c x) = x` beyond the right record, and `g 0 = stRecR`. -/
theorem rightRay_readback {s : ExplState} (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal)
    (hR : RProf s) (hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) :
    (∀ x, stRecR s < x → g (rProf (stChart s) x : ℂ) = x) ∧ g 0 = stRecR s := by
  have h1 : ∀ x, stRecR s < x → g (rProf (stChart s) x : ℂ) = x := by
    intro x hx
    have h := bdry_eq_of_chartFree hcc hgc hgi (hfree x hx).1 (hfree x hx).2 (hc x)
    rwa [hc.eq_ofReal x] at h
  refine ⟨h1, ?_⟩
  -- `rProf c x → 0` as `x ↓ recR`
  have hlim0 : Tendsto (fun x => rProf (stChart s) x) (𝓝[>] (stRecR s)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨x₁, hx₁, hx₁ε⟩ := hR.2.2.2 ε hε
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    have hpos := hR.2.2.1 x hx.1
    have hlt : rProf (stChart s) x < rProf (stChart s) x₁ := hR.2.1.1 hx.1 hx₁ hx.2
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have hgc0 : Tendsto g (𝓝[{z | 0 ≤ z.im}] (0 : ℂ)) (𝓝 (g 0)) := hgc 0 (by simp)
  have hcomp : Tendsto (fun x => g (rProf (stChart s) x : ℂ)) (𝓝[>] (stRecR s)) (𝓝 (g 0)) := by
    refine hgc0.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun x => by simp⟩)
    rw [← Complex.ofReal_zero]
    exact (Complex.continuous_ofReal.tendsto 0).comp hlim0
  have hid : Tendsto (fun x => g (rProf (stChart s) x : ℂ)) (𝓝[>] (stRecR s)) (𝓝 ((stRecR s : ℝ) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (h1 x hx).symm
  exact tendsto_nhds_unique hcomp hid

/-- **Junctions on the right ray are not upper-bad** (`θ < ψ`), and they lie at or right of the right record. -/
theorem jw_rightRay (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) {β : BoundaryWord} {s : ExplState}
    (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal)
    (hR : RProf s) (hO : ROrig b jumps β s)
    (hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) {r : ℝ} (hr : 0 ≤ r)
    (hlow : ∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ β.jumps → β.fn y = -sleLambda κ - θ * chiC κ) {p : ℝ}
    (hp : g (r : ℂ) = p) :
    stRecR s ≤ p ∧ -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ) := by
  classical
  obtain ⟨hrb, hg0⟩ := rightRay_readback hc hcc hR hfree hgc hgi
  set c := stChart s with hcdef
  set R := stRecR s with hRdef
  obtain ⟨ε, hε, hεl⟩ := hlow
  -- the physical point and a right neighbourhood of it mapping into `(r, r + ε)`
  obtain ⟨x₀, hx₀R, hx₀p, hnb⟩ : ∃ x₀, R ≤ x₀ ∧ x₀ = p ∧ ∃ x₁, x₀ < x₁ ∧
      ∀ x ∈ Ioo x₀ x₁, R < x ∧ rProf c x ∈ Ioo r (r + ε) := by
    rcases hr.lt_or_eq with hrpos | hr0
    · obtain ⟨x₀, hx₀, hx₀e⟩ := RProf.exists_eq hR hrpos
      have hcont : ContinuousAt (rProf c) x₀ :=
        hR.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont ε hε
      refine ⟨x₀, hx₀.le, ?_, x₀ + min δ (x₀ - R) / 2, by
        have : 0 < min δ (x₀ - R) := lt_min hδ (by linarith)
        linarith, fun x hx => ?_⟩
      · have h := hrb x₀ hx₀
        rw [hx₀e, hp] at h
        exact_mod_cast h.symm
      · have hm : min δ (x₀ - R) ≤ δ := min_le_left _ _
        have hxR : R < x := lt_trans hx₀ hx.1
        refine ⟨hxR, ?_, ?_⟩
        · rw [← hx₀e]; exact hR.2.1.1 hx₀ hxR hx.1
        · have h1 : dist x x₀ < δ := by
            rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
            have := hx.2
            have : 0 < min δ (x₀ - R) := lt_min hδ (by linarith)
            linarith
          have h2 := hδc h1
          rw [Real.dist_eq, hx₀e] at h2
          linarith [(abs_lt.1 h2).2]
    · subst hr0
      obtain ⟨x₁, hx₁, hx₁ε⟩ := hR.2.2.2 ε hε
      refine ⟨R, le_rfl, ?_, x₁, hx₁, fun x hx => ⟨hx.1, hR.2.2.1 x hx.1, ?_⟩⟩
      · have h := hp
        rw [Complex.ofReal_zero, hg0] at h
        exact_mod_cast h
      · have := hR.2.1.1 hx.1 hx₁ hx.2
        linarith
  obtain ⟨x₁, hx₀₁, hx₁⟩ := hnb
  refine ⟨by rw [← hx₀p]; exact hx₀R, ?_⟩
  rw [← hx₀p]
  refine cumWeightRight_gt_of_lowSide hκ hκ4 hθψ ?_
  -- the exceptional points: data jumps and preimages of word jumps
  set Ex : Set ℝ := {x | R < x ∧ rProf c x ∈ (β.jumps : Set ℝ)} with hEx
  have hExf : Ex.Finite :=
    Set.Finite.of_finite_image (f := rProf c) (β.jumps.finite_toSet.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
      (hR.2.1.1.injOn.mono fun x hx => hx.1)
  refine Sec4.rightLim_eq_of_forall_notMem (jumps ∪ hExf.toFinset) (a := x₁) hx₀₁ fun t ht htJ => ?_
  have htj : t ∉ jumps := fun h => htJ (Finset.mem_union_left _ h)
  obtain ⟨htR, hty⟩ := hx₁ t ht
  have htβ : rProf c t ∉ β.jumps := fun h =>
    htJ (Finset.mem_union_right _ (hExf.mem_toFinset.2 ⟨htR, h⟩))
  rw [← hO t htR htj htβ]
  exact hεl _ hty htβ

end InteractingSLE.Theorem14.SB.Wf
