/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Avoid
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Noncolliding marks keep the trace off the boundary beyond them (§4.1)

Packet PROVE-SEC4-A3. Specification §4.1 (`source/spec/p097-144.md`, pp. 105–115). The proofs of Lemma 4.3
(first case), Lemma 4.5 and Aux. lemma 22 exclude boundary contacts beyond a strip end with dense passive
zero-weight marks: "A boundary contact in one of these open arcs would swallow a passive mark strictly between
that contact and the adjacent strip end … This contradicts noncollision." Here the same conclusion is proved
directly from the noncollision of the *actual* marks (Aux. lemma 6, `aux6Statement`) and the deterministic
avoidance lemma `ne_ofReal_of_isGeneratingTrace`:

* `IsIntegratedSLEPath.trace_ne_of_left` / `trace_ne_of_right` (pathwise): on an integrated path with infinite
  lifetime, if the left mark `i` never meets the driver at positive times, a generating trace never visits a real
  point `x < 0` with `x ≤ x^{i,L}`; symmetrically on the right.
* `IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissiblePartialSums`: for an ordered force word whose side partial
  sums are at least `k/2 − 2` (the hypothesis of Aux. lemmas 6–7 and Remark 4.1), almost surely the lifetime is
  infinite and every generating trace avoids `(−∞, x^{i,L}] ∩ (−∞, 0)` and `[x^{j,R}, ∞) ∩ (0, ∞)` for every
  mark. With seed marks at `0⁻` and `0⁺` (as for every flow line) the trace never touches `ℝ \ {0}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

universe u

namespace InteractingSLE

namespace Sec4

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- On an integrated path with infinite lifetime the driver is continuous in real time. -/
theorem continuous_toNNReal_of_isIntegratedSLEPath {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ⊤) :
    Continuous fun s : ℝ => w s.toNNReal := by
  have hwc : Continuous w :=
    continuousOn_univ.1 (hp.2.2.2.1.mono fun t _ => (ENNReal.coe_lt_top : (t : ℝ≥0∞) < ⊤))
  exact hwc.comp continuous_real_toNNReal

/-- **Pathwise avoidance, left side.** On an integrated path with infinite lifetime, if the left mark `i`
stays strictly left of the driver at positive times, a generating trace never visits a real point `x < 0`
with `x ≤ x^{i,L}`. -/
theorem IsIntegratedSLEPath.trace_ne_of_left {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ⊤) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (i : Fin nL) (hsep : ∀ t : ℝ≥0, 0 < t → vL i t < w t)
    (t : ℝ≥0) {x : ℝ} (hx : x < 0) (hxi : x ≤ xL i) : η t ≠ x := by
  have hW := continuous_toNNReal_of_isIntegratedSLEPath hp
  obtain ⟨hw0, hvL0, -, -, hvLc, -, -, -, -, -, hgL, -, -, hvLeq, -⟩ := hp
  have hu : Continuous (vL i) :=
    continuousOn_univ.1 ((hvLc i).mono fun t _ => (ENNReal.coe_lt_top : (t : ℝ≥0∞) < ⊤))
  have hueq : ∀ t : ℝ≥0, vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal) :=
    fun t => hvLeq t ENNReal.coe_lt_top i
  have huint : ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 t := by
    intro t
    have h := (hgL t ENNReal.coe_lt_top i).const_mul (-2)
    refine h.congr ?_
    intro s _
    show -2 * (w s.toNNReal - vL i s.toNNReal)⁻¹ = 2 / (vL i s.toNNReal - w s.toNNReal)
    rw [← neg_sub (vL i s.toNNReal) (w s.toNNReal), inv_neg, div_eq_mul_inv]
    ring
  refine ne_ofReal_of_isGeneratingTrace hW hw0 hη (C := Iic x) isClosed_Iic
    (fun h0 => absurd (show (0 : ℝ) ≤ x from h0) (not_le.2 hx))
    (fun y hy T hT => exists_isForwardSol_of_forceEq_left hW hw0 hu hueq huint hsep
      (lt_of_le_of_lt hy hx) (le_trans hy hxi) hT) t x (mem_Iic.2 le_rfl)

/-- **Pathwise avoidance, right side.** On an integrated path with infinite lifetime, if the right mark `i`
stays strictly right of the driver at positive times, a generating trace never visits a real point `x > 0`
with `x ≥ x^{i,R}`. -/
theorem IsIntegratedSLEPath.trace_ne_of_right {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ⊤) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (i : Fin nR) (hsep : ∀ t : ℝ≥0, 0 < t → w t < vR i t)
    (t : ℝ≥0) {x : ℝ} (hx : 0 < x) (hxi : xR i ≤ x) : η t ≠ x := by
  have hW := continuous_toNNReal_of_isIntegratedSLEPath hp
  obtain ⟨hw0, -, hvR0, -, -, hvRc, -, -, -, -, -, hgR, -, -, hvReq, -⟩ := hp
  have hu : Continuous (vR i) :=
    continuousOn_univ.1 ((hvRc i).mono fun t _ => (ENNReal.coe_lt_top : (t : ℝ≥0∞) < ⊤))
  have hueq : ∀ t : ℝ≥0, vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal) :=
    fun t => hvReq t ENNReal.coe_lt_top i
  have huint : ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t := by
    intro t
    have h := (hgR t ENNReal.coe_lt_top i).const_mul (-2)
    refine h.congr ?_
    intro s _
    show -2 * (w s.toNNReal - vR i s.toNNReal)⁻¹ = 2 / (vR i s.toNNReal - w s.toNNReal)
    rw [← neg_sub (vR i s.toNNReal) (w s.toNNReal), inv_neg, div_eq_mul_inv]
    ring
  refine ne_ofReal_of_isGeneratingTrace hW hw0 hη (C := Ici x) isClosed_Ici
    (fun h0 => absurd (show x ≤ (0 : ℝ) from h0) (not_le.2 hx))
    (fun y hy T hT => exists_isForwardSol_of_forceEq_right hW hw0 hu hueq huint hsep
      (lt_of_lt_of_le hx hy) (le_trans hxi hy) hT) t x (mem_Ici.2 le_rfl)

/-- **Avoidance of the boundary beyond the marks** (the passive-mark step of Lemmas 4.3, 4.5 and Aux. lemma
22, from Aux. lemma 6). For an ordered force word whose side partial sums are at least `k/2 − 2`, almost surely
the lifetime is infinite and every generating trace on `[0, ζ]` avoids every real point `x < 0` at or beyond a
left mark and every real point `x > 0` at or beyond a right mark. -/
theorem IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissiblePartialSums (hk : 0 < k)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hword : IsOrderedForceWord xL xR) (hadm : HasAdmissiblePartialSums k ρL ρR xL xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0,
      (∀ i, ∀ x : ℝ, x < 0 → x ≤ xL i → η ω t ≠ x) ∧
        ∀ i, ∀ x : ℝ, 0 < x → xR i ≤ x → η ω t ≠ x := by
  filter_upwards [aux6Statement hk xL xR ρL ρR P 𝓕 W VL VR B ζ hword hadm h, h.2.2.2.2, hη]
    with ω h6 hp hηω
  obtain ⟨hζ, hsep⟩ := h6
  rw [hζ] at hp hηω
  refine ⟨hζ, fun t => ⟨fun i x hx hxi => ?_, fun i x hx hxi => ?_⟩⟩
  · exact IsIntegratedSLEPath.trace_ne_of_left hp hηω i (fun s hs => (hsep s hs).1 i) t hx hxi
  · exact IsIntegratedSLEPath.trace_ne_of_right hp hηω i (fun s hs => (hsep s hs).2 i) t hx hxi

end Sec4

end InteractingSLE
