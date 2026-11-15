/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Strip
import InteractingSLE.Spec.Sec4.SpecialHeights

/-!
# Aux. lemma 22, the hitting case: exact statement and its pathwise consequences

Packet PROVE-SEC4-B5 (specification §4.1, Aux. lemma 22, `source/spec/p097-144.md#aux-22`, p. 113):

> *Use the signed notation `k > 0`, `Λ = π/√k`, and `X = 2/√k − √k/2`. In the strip of height one, assume the lower
> data are either the basic constants `−Λ, Λ`, or are piecewise constant with finitely many changes, at most
> `−Λ + πX` left of zero and at least `Λ − πX` right of zero. Let `−∞ ≤ u < v ≤ +∞`. Suppose the upper data have
> finitely many pieces, every height on `I = {x + i : u < x < v}` lies strictly between `−Λ` and `Λ`, every height
> left of `I` is at most `−Λ`, and every height right of `I` is at least `Λ`. Then the trace has an actual first upper
> endpoint at a finite point of `I`.*

The end alternatives (every upper height `≥ Λ`, resp. `≤ −Λ`) are PROVE-SEC4-A3's/A4's (`lemma43_left_of_aux7`,
`lemma43_right_of_aux7` and the `ZeroMarksCharts` versions). This file fixes the **hitting case** in the carriers of
§4.2 (chart `E(z) = e^{πz} − 1`, `Sec4.IsStripFlowLine`, upper line `upperLineH = (−∞, −1)`):

* `IsAux22SpanData k u v bL bU JL JU`: the hypotheses on the data, with `u v : EReal`;
* `HasFirstUpperEndpointIn u v η ζ`: "the trace has an actual first upper endpoint at a finite point of `I`" — at some
  finite time `t ≤ ζ` (so the trace is continuous up to `t`, `IsFlowLine`), `η` avoids the upper line before `t`, and
  `η(t) = E(x + i)` with `u < x < v`;
* `Aux22HitStatement k`: the hitting case for every such flow line. **Not proved here** (see
  `planning/handoffs/PROVE-SEC4-B5.md`): its proof is Aux. lemma 21 through the maps (UC11)–(UC12), which needs the
  strip endpoint theorem's clause (3) (`Strip.StripEndpointStatement`, packet PROVE-ZHAN-A4), the whole-tail Girsanov
  deletions of the lower groups and of the drift error (UC10), the recurrence argument after (UC9), and the change of
  target between the half-plane chart of `E` and the strip chart of (UC11) at the level of the driving process (only
  its algebra is landed, `Zhan.TargetChange`).

Proved here (pathwise and almost surely, from the statement): the consequences used by Remark 4.8 (a) and Lemma 4.7 —
`T_top = firstUpperContact η` is the endpoint time, `0 < T_top < ∞`, `T_top ≤ ζ`, and `η` is continuous on
`[0, T_top]` (`firstUpperContact_eq_of_first`, `ae_remark48a_top_of_aux22Hit`); and the data of Figure
4.6(a) (`κ ∈ (0, 4)`) form a semi-infinite left span `u = −∞`, `v = x₀` (`isAux22SpanData_fig46`; Lemma 4.7 proof,
p. 118: "Aux. lemma 22, with a semi-infinite left span, therefore gives an actual finite first upper endpoint strictly
left of `z₀`").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec4

/-- The hypotheses of Aux. lemma 22's hitting case on the strip data (signed notation: `k > 0` is `κ` or `κ′`,
`Λ = sleLambda k`, `X = chiC k`). Lower data `bL`: piecewise constant off `JL`, and either the basic constants `−Λ`,
`Λ`, or at most `−Λ + πX` left of `0` and at least `Λ − πX` right of `0`. Upper data `bU` (read along `x + i`):
piecewise constant off `JU`, strictly between `−Λ` and `Λ` on `I = (u, v)`, at most `−Λ` left of `I`, at least `Λ`
right of `I` (values at the finitely many jumps are not constrained). -/
def IsAux22SpanData (k : ℝ) (u v : EReal) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) : Prop :=
  IsPiecewiseConstantBoundaryData bL JL ∧ IsPiecewiseConstantBoundaryData bU JU ∧
    (((∀ x : ℝ, x < 0 → bL x = -sleLambda k) ∧ ∀ x : ℝ, 0 < x → bL x = sleLambda k) ∨
      ((∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k) ∧
        ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)) ∧
    (∀ x : ℝ, x ∉ JU → u < (x : EReal) → (x : EReal) < v → -sleLambda k < bU x ∧ bU x < sleLambda k) ∧
    (∀ x : ℝ, x ∉ JU → (x : EReal) < u → bU x ≤ -sleLambda k) ∧
    ∀ x : ℝ, x ∉ JU → v < (x : EReal) → sleLambda k ≤ bU x

/-- "The trace has an actual first upper endpoint at a finite point of `I`", in the chart `E`: at a finite time
`t ≤ ζ` (inside the closed lifetime, where a generating trace is continuous) the path `η` is at the image
`E(x + i) = −e^{πx} − 1` of a point `x + i ∈ I`, and it is off the upper line `E(ℝ + i) = (−∞, −1)` before `t`. -/
def HasFirstUpperEndpointIn (u v : EReal) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Prop :=
  ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ (∀ s : ℝ≥0, s < t → η s ∉ upperLineH) ∧
    ∃ x : ℝ, u < (x : EReal) ∧ (x : EReal) < v ∧ η t = ((-Real.exp (π * x) - 1 : ℝ) : ℂ)

/-- **Aux. lemma 22, the hitting case** (named statement; not proved — see the module docstring). For every flow line
from `0` (parameter `k`, in the chart `E`) of a strip field whose data satisfy `IsAux22SpanData k u v`, almost surely
the trace has an actual first upper endpoint at a finite point of `I = (u, v) + i`. -/
def Aux22HitStatement (k : ℝ) : Prop :=
  ∀ (u v : EReal) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    u < v → IsAux22SpanData k u v bL bU JL JU → IsStripFlowLine k bL bU JL JU P h η ζ →
      ∀ᵐ ω ∂P, HasFirstUpperEndpointIn u v (η ω) (ζ ω)

/-! ### Pathwise consequences -/

theorem ofReal_neg_exp_sub_one_mem_upperLineH (x : ℝ) :
    (((-Real.exp (π * x) - 1 : ℝ)) : ℂ) ∈ upperLineH :=
  ⟨_, show -Real.exp (π * x) - 1 < -1 by linarith [Real.exp_pos (π * x)], rfl⟩

/-- The endpoint time is the first upper contact `T_top`. -/
theorem firstUpperContact_eq_of_first {η : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hlt : ∀ s : ℝ≥0, s < t → η s ∉ upperLineH) (ht : η t ∈ upperLineH) :
    firstUpperContact η = t := by
  refine le_antisymm (firstUpperContact_le ht) (le_iInf₂ fun s hs => ?_)
  by_contra hst
  exact hlt s (ENNReal.coe_lt_coe.1 (not_le.1 hst)) hs

/-- **Remark 4.8 (a) at `T_top`, one path.** If `η` starts at `0`, is continuous on `[0, ζ]` (a generating trace)
and has an actual first upper endpoint, then `T_top = firstUpperContact η` is finite, positive, at most `ζ`, and `η`
is continuous on `[0, T_top]` (read as a path on `ℝ`). -/
theorem remark48a_top_of_hasFirstUpperEndpointIn {u v : EReal} {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    (hη : IsGeneratingTrace w ζ η) (hE : HasFirstUpperEndpointIn u v η ζ) :
    firstUpperContact η ≠ ⊤ ∧ firstUpperContact η ≤ ζ ∧ 0 < (firstUpperContact η).toReal ∧
      ContinuousOn (fun s : ℝ => η s.toNNReal) (Icc 0 (firstUpperContact η).toReal) := by
  obtain ⟨t, htζ, hlt, x, -, -, hx⟩ := hE
  have hmem : η t ∈ upperLineH := hx ▸ ofReal_neg_exp_sub_one_mem_upperLineH x
  have hT : firstUpperContact η = t := firstUpperContact_eq_of_first hlt hmem
  obtain ⟨h0, hc, -⟩ := hη
  have hcont0 : ContinuousAt η 0 := by
    rcases eq_or_ne ζ 0 with hζ0 | hζ0
    · -- `ζ = 0` forces `t = 0`, but `η 0 = 0 ∉ upperLineH`
      exfalso
      have ht0 : t = 0 := by
        rw [hζ0] at htζ
        exact_mod_cast le_zero_iff.1 htζ
      rw [ht0, h0] at hmem
      obtain ⟨y, hy, hy0⟩ := hmem
      have : y = 0 := by exact_mod_cast hy0
      rw [this] at hy
      exact absurd hy (by norm_num)
    · refine (hc 0 (by simp)).continuousAt ?_
      obtain ⟨r, hr0, hrζ⟩ : ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ ζ := by
        induction ζ using ENNReal.recTopCoe with
        | top => exact ⟨1, one_pos, le_top⟩
        | coe z => exact ⟨z, pos_iff_ne_zero.2 (by exact_mod_cast hζ0), le_rfl⟩
      exact Filter.mem_of_superset (Iio_mem_nhds hr0) fun s hs =>
        (ENNReal.coe_le_coe.2 (le_of_lt hs)).trans hrζ
  have hpos : 0 < firstUpperContact η := firstUpperContact_pos h0 hcont0
  refine ⟨by rw [hT]; exact ENNReal.coe_ne_top, by rw [hT]; exact htζ, ?_, ?_⟩
  · rw [hT] at hpos ⊢
    exact ENNReal.toReal_pos (ne_of_gt hpos) ENNReal.coe_ne_top
  · rw [hT, ENNReal.coe_toReal]
    have hcomp : ContinuousOn (fun s : ℝ => s.toNNReal) (Icc 0 (t : ℝ)) :=
      continuous_real_toNNReal.continuousOn
    refine hc.comp hcomp fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    refine le_trans (ENNReal.coe_le_coe.2 ?_) htζ
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2

/-- **Remark 4.8 (a) at `T_top`, from Aux. lemma 22's hitting case** (conditional helper). For a strip flow line whose
data satisfy `IsAux22SpanData k u v`, almost surely `T_top` is finite, positive, at most the lifetime, and the trace
is continuous on `[0, T_top]` (including `T_top`): the part of Remark 4.8 (a) that is not simplicity before `T_top`. -/
theorem ae_remark48a_top_of_aux22Hit {k : ℝ} (h22 : Aux22HitStatement.{u} k) {u v : EReal} (huv : u < v)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} (hdat : IsAux22SpanData k u v bL bU JL JU) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, firstUpperContact (η ω) ≠ ⊤ ∧ firstUpperContact (η ω) ≤ ζ ω ∧
      0 < (firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (firstUpperContact (η ω)).toReal) := by
  have h22' := h22 u v bL bU JL JU P h η ζ huv hdat hfl
  obtain ⟨-, -, W, -, -, -, -, -, htr⟩ := hfl
  filter_upwards [h22', htr] with ω hω hη
  have hη' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hη
  exact remark48a_top_of_hasFirstUpperEndpointIn hη' hω

/-! ### Figure 4.6(a): a semi-infinite left span -/

/-- **The data of Figure 4.6(a) form a semi-infinite left span** (`0 < κ < 4`; Lemma 4.7 proof, p. 118: "the two
upper heights for the flow line are `−λ′ + π/2 χ = λ − 2λ′ ∈ (−λ, λ)` and `λ′ + π/2 χ = λ`. Aux. lemma 22, with a
semi-infinite left span, therefore gives an actual finite first upper endpoint strictly left of `z₀`"): with
`u = −∞`, `v = x₀`, the lower data are the basic constants and the upper data are `−λ + πχ ∈ (−λ, λ)` on `I` and
`λ` right of `I`. -/
theorem isAux22SpanData_fig46 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (x₀ : ℝ) :
    IsAux22SpanData κ ⊥ (x₀ : EReal) (fig46Lower κ) (fig46Upper κ x₀) {0} {x₀} := by
  have hI : -sleLambda κ + π * chiC κ ∈ Ioo (-sleLambda κ) (sleLambda κ) := by
    have h1 := fig46_upper_left_mem_Ioo hκ hκ4
    rw [show π / 2 * chiC κ = π * chiC κ / 2 by ring, rem410_upper_left_eq hκ] at h1
    exact h1
  refine ⟨isPiecewiseConstantBoundaryData_fig46Lower κ, isPiecewiseConstantBoundaryData_fig46Upper κ x₀,
    Or.inl ⟨fun x hx => by simp [fig46Lower, hx], fun x hx => by simp [fig46Lower, not_lt.2 hx.le]⟩,
    fun x _ _ hxv => ?_, fun x _ hx => absurd hx (not_lt.2 bot_le), fun x hx hxv => ?_⟩
  · have hxv' : x < x₀ := by exact_mod_cast hxv
    simp only [fig46Upper, hxv', ↓reduceIte]
    exact ⟨hI.1, hI.2⟩
  · have hxv' : x₀ < x := by exact_mod_cast hxv
    simp only [fig46Upper, not_lt.2 hxv'.le, ↓reduceIte, le_refl]

end Sec4

end InteractingSLE
