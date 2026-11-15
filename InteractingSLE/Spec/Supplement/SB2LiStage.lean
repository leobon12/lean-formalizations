/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LhRec
import InteractingSLE.Spec.Supplement.SB2LpLift

/-!
# SB2(2): the lift relation at one relative stage, from the stage trace

Packet PROVE-SB2-LIFTSET (round 11). The data clause of the stage rule asks, at every launch, that the relative piece be
the lift of the actual one (`LiftRel`). For a relative driver `e` generating a trace `α` (as `EL` does for its stage
curves, `exists_EL_rec`):

* **`tipSet_newPc_eq`**: the launched relative piece's physical set is the boundary image `f '' (α '' [0, e.2])` of
  the trace through the relative chart (`CounterflowRange.tipSet_stopped_eq_of_tendsto`);
* **`image_eq_closure_of_dense`**: the image of a compact parameter set under a map continuous on it is the closure of
  the values at dense good parameters;
* **`liftRel_of_stage`**: hence, at finite lifetime, if the relative trace's boundary values at dense good times are
  exactly the intrinsic lifts `c.1 · + m` of the actual piece's points in `D = c⁻¹ '' ℍ` on the tail, the relative
  piece is the lift of the actual one (`liftRel_of_closure`).

For the concrete rule (stage curve = the relative chart applied to the intrinsic lift of the actual piece at its good
times) the hypothesis `hval` is `f ∘ (stChart …).1 = id` on the relative domain, and `hv` is the bookkeeping of the good
times; see the handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw

/-- **The physical set of a launched piece is the boundary image of its generating trace**: for a launch from `s` with
driver `e` generating `α` up to its lifetime, and `f` the boundary map of the chart along `α`, the piece recorded by
the launch (`newPc s e`) has physical set `f '' (α '' [0, e.2])` (`CounterflowRange.tipSet_stopped_eq_of_tendsto`). -/
theorem tipSet_newPc_eq {s : ExplState} {e : Drv} {α : ℝ≥0 → ℂ} {f : ℂ → ℂ}
    (hα : IsGeneratingTrace e.1 e.2 α) (hW : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ e.2}) (hW0 : e.1 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → Tendsto (stChart s).2.1 (𝓝[H] (α t)) (𝓝 (f (α t)))) :
    (newPc s e).1.tipSet (newPc s e).2.1 (newPc s e).2.2 = f '' (α '' {t | (t : ℝ≥0∞) ≤ e.2}) := by
  show (stChart s).tipSet (fun r : ℝ≥0 => e.1 (min (r : ℝ≥0∞) (min ⊤ e.2)).toNNReal) (min ⊤ e.2) = _
  rw [min_top_left]
  exact CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0 hc

/-- **The image of a compact parameter set is the closure of the values at dense good parameters**: for `g`
continuous on a compact `K` and good parameters `Gd ⊆ K` dense in `K`, `g '' K = closure (g '' Gd)`. With `g` the
relative chart's boundary map along the stage trace and the good parameters those where it is the intrinsic lift of
the actual piece, this is the target of `liftRel_of_closure`. -/
theorem image_eq_closure_of_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {g : X → Y} {K Gd : Set X} (hK : IsCompact K) (hg : ContinuousOn g K) (hGd : Gd ⊆ K)
    (hdense : K ⊆ closure Gd) : g '' K = closure (g '' Gd) := by
  refine Subset.antisymm ?_ ((hK.image_of_continuousOn hg).isClosed.closure_subset_iff.2 (image_mono hGd))
  rintro _ ⟨x, hx, rfl⟩
  have hcl : x ∈ closure Gd := hdense hx
  have hcw : ContinuousWithinAt g K x := hg x hx
  rw [mem_closure_iff_nhdsWithin_neBot] at hcl
  have hlim : Tendsto g (𝓝[Gd] x) (𝓝 (g x)) := hcw.mono_left (nhdsWithin_mono x hGd)
  exact mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => mem_image_of_mem g hy)

/-- **The lift relation at one stage** (finite lifetime): if the relative trace's boundary values at dense good times
are exactly the intrinsic lifts of the actual piece's points in `D = c⁻¹ '' ℍ` on the tail, the relative piece is the
lift of the actual one (`tipSet_newPc_eq`, `image_eq_closure_of_dense`, `liftRel_of_closure`). -/
theorem liftRel_of_stage {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hγ : IsTailLiftCurve c R m β₀ tL γ)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q₁ : Pc}
    (hTc : IsCompact {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    {s : ExplState} {e : Drv} {α : ℝ≥0 → ℂ} {f : ℂ → ℂ} (hα : IsGeneratingTrace e.1 e.2 α)
    (hW : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ e.2}) (hW0 : e.1 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → Tendsto (stChart s).2.1 (𝓝[H] (α t)) (𝓝 (f (α t))))
    (hfin : e.2 ≠ ⊤) (hgc : ContinuousOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ e.2})
    {Gd : Set ℝ≥0} {v : ℝ≥0 → ℂ} (hGd : Gd ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2})
    (hdense₂ : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} ⊆ closure Gd) (hval : ∀ t ∈ Gd, f (α t) = v t)
    (hv : v '' Gd = liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL)) :
    LiftRel β₀ tL γ q₁ (newPc s e) := by
  have hK : IsCompact {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} := by
    have e' : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} = Iic e.2.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Iic]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    rw [e', ← Icc_bot]
    exact isCompact_Icc
  refine liftRel_of_closure hγ hcH hc1 hoff hTc hdense₁ ?_
  rw [tipSet_newPc_eq hα hW hW0 hc, image_image, image_eq_closure_of_dense hK hgc hGd hdense₂, ← hv]
  congr 1
  exact image_congr hval

end InteractingSLE.Theorem14.SB.Lk
