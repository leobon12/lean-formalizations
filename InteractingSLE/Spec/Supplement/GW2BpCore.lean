/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnBridge
import InteractingSLE.Spec.Supplement.DS3ProofReach

/-!
# nearImg, the per-sample core: the near stop at an exit before the lower cap (clauses (i)–(ii))

Packet PROVE-GW2-BUF (round 13). The near stop of `GW2BoPkg` is the minimum of a lower cap and the exit rule
`shapeStop` of the record's shape cell. At one sample, suppose the stage record's shape and padded positions are those
of the near family `f` (D16's decoder, `GW2BnBridge.withNearS_decoder`). Then:

* **`exit_spec_family`**: the exit `τ` of the comparison path satisfies `0 < τ`, `τ ≤ c`, and if `τ < c` the image
  state with `f`'s labels at comparison time `a τ` is outside `nearBuffer f n`. This needs the initial state inside
  the buffer.
* `isOpen_bufOfShape`, `compl_bufOfShape_nonempty`: the hypotheses of `exitRule_spec`.
* `imgState_mem_bufOfShape_transport`: the image state's membership does not depend on how the labels are typed. The
  shape equality `famShapeB f = shape y` is only propositional, so the statement is transported.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

/-- The shape buffers are open. -/
theorem isOpen_bufOfShape (K : NearShape) (n : ℕ) : IsOpen (bufOfShape K n) := by
  unfold bufOfShape
  split_ifs
  · exact isOpen_setOf_inBuffer _ _ _ _
  · exact isOpen_setOf_inBuffer _ _ _ _

/-- The shape buffers have nonempty complement (a driver coordinate beyond the box). -/
theorem compl_bufOfShape_nonempty (K : NearShape) (n : ℕ) : (bufOfShape K n)ᶜ.Nonempty := by
  refine ⟨(((n : ℝ) + 1), fun _ => 0, fun _ => 0), fun h => ?_⟩
  have hbox : |((n : ℝ) + 1)| < (n : ℝ) := by
    unfold bufOfShape at h
    split_ifs at h
    · exact h.1.1
    · exact h.1.1
  rw [abs_of_pos (by positivity)] at hbox
  linarith

/-- **Transport across a shape equality**: the image state with labels typed by either shape. -/
theorem imgState_mem_bufOfShape_transport {K K' : NearShape} (h : K = K') (n : ℕ) (L : Fin K.1 → ℝ)
    (R : Fin K.2.1 → ℝ) (L' : Fin K'.1 → ℝ) (R' : Fin K'.2.1 → ℝ)
    (hL : ∀ i : Fin K.1, L i = L' (Fin.cast (congrArg (fun K : NearShape => K.1) h) i))
    (hR : ∀ j : Fin K.2.1, R j = R' (Fin.cast (congrArg (fun K : NearShape => K.2.1) h) j))
    (w : ℝ≥0 → ℝ) (t : ℝ≥0) :
    GW2Sdg.imgState L R w t ∈ bufOfShape K n ↔ GW2Sdg.imgState L' R' w t ∈ bufOfShape K' n := by
  subst h
  have e1 : L = L' := funext fun i => by rw [hL i]; rfl
  have e2 : R = R' := funext fun j => by rw [hR j]; rfl
  rw [e1, e2]

/-- **The exit of the near family's comparison path.** If the shape and padded positions of the record `y` are those
of the near family `f`, and the initial comparison state lies in `f`'s buffer, then the exit `τ` of the record's cell
satisfies `0 < τ ≤ c`, and before the horizon `c` the image state with `f`'s labels at comparison time `a τ` is
outside `nearBuffer f n`. -/
theorem exit_spec_family {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) (shape : RecData → NearShape)
    (posL posR : RecData → ℕ → ℝ) (y : RecData) (hsh : famShapeB f = shape y)
    (hL : ∀ i : Fin f.nL, f.xL i = posL y i) (hR : ∀ j : Fin f.nR, f.xR j = posR y j) (a : ℝ≥0) (b : ℝ)
    {c : ℝ≥0} (hc : 0 < c) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ nearBuffer f n) :
    ∃ τ : ℝ≥0, shapeStop (fun K => bufOfShape K n) shape posL posR a b c (y, w) = τ ∧ 0 < τ ∧ τ ≤ c ∧
      (τ < c → GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * τ) ∉ nearBuffer f n) := by
  set K := shape y with hK
  have htr : ∀ t : ℝ≥0, (GW2Sdg.imgState (fun i : Fin K.1 => posL y i) (fun j : Fin K.2.1 => posR y j)
      (scaledPath a b w) t ∈ bufOfShape K n ↔ GW2Sdg.imgState f.xL f.xR (scaledPath a b w) t ∈ nearBuffer f n) :=
    fun t => by
      rw [nearBuffer_eq_bufOfShape]
      refine imgState_mem_bufOfShape_transport hsh.symm n _ _ f.xL f.xR (fun i => ?_) (fun j => ?_) _ t
      · have hn : f.nL = K.1 := congrArg (fun K : NearShape => K.1) hsh
        exact (hL ⟨(i : ℕ), by rw [hn]; exact i.2⟩).symm
      · have hn : f.nR = K.2.1 := congrArg (fun K : NearShape => K.2.1) hsh
        exact (hR ⟨(j : ℕ), by rw [hn]; exact j.2⟩).symm
  obtain ⟨τ, hτ, hτ0, hτc, hout⟩ := exitRule_spec (fun i : Fin K.1 => posL y i) (fun j : Fin K.2.1 => posR y j)
    (isOpen_bufOfShape K n) (compl_bufOfShape_nonempty K n) a b hc y hw ((htr 0).2 h0)
  refine ⟨τ, ?_, hτ0, hτc, fun hlt hin => hout hlt ((htr _).2 hin)⟩
  rw [shapeStop_eq]
  exact hτ

end InteractingSLE.Theorem14.GW2Bh
