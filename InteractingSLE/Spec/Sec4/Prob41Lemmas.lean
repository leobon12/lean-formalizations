/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Trace
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec4.Strip
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Lemmas 4.3 and 4.5 and the end alternatives of Aux. lemma 22: boundary avoidance and limits at the target

Packet PROVE-SEC4-A3. Specification §4.1 (`source/spec/p097-144.md`, pp. 103–115).

**The flow line of a field with Remark 4.1's boundary data** (`IsFlowLine.ae_trace_ne_real`): if the boundary
data `b` of a field on `ℍ` is at most `−Λ + πX` left of `0` and at least `Λ − πX` right of `0` (off its jump
candidates), then almost surely the flow line from `0` has infinite lifetime and never touches `ℝ \ {0}`. This is
the passive-mark step of the proofs of Lemmas 4.3 and 4.5 and Aux. lemma 22, proved here from the noncollision of
the seed marks (Aux. lemma 6) and the deterministic avoidance lemma `ne_ofReal_of_isGeneratingTrace`. Every
statement is for a general parameter `k > 0` with `Λ = sleLambda k`, `X = chiC k`; the two applications are
`k = κ` and `k = κ′ = 16/κ` (`chiC (16/κ) = −chiC κ`, Remark 4.2).

**Limits at the target** use Aux. lemma 7 (§2.2, p. 33), not yet in Lean; it is the named input `Aux7Statement`
(exact source statement below), and the theorems using it carry `_of_aux7` in their names.

**Charts.** In the chart `E(z) = e^{πz} − 1` (target the right strip end, SEC4-B2's `IsStripFlowLine`): Lemma 4.3
for `a ≤ −Λ` and the all-upper-negative alternative of Aux. lemma 22 (`lemma43_right_of_aux7`,
`ae_notMem_upperLineH_of_isStripFlowLine`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec4

/-! ### The named input: Aux. lemma 7 -/

/-- **Named input: Aux. lemma 7** (Transience in the noncolliding force regime; Specification §2.2, p. 33,
`source/spec/p001-048.md#aux-7`): "Let `κ > 0`, put `c = κ/2 − 2`, and consider finitely many ordered boundary
force groups, with coincident groups on each side amalgamated. Suppose that every side partial sum of their
weights is at least `c`. Either side may be empty, and force groups may start at `0⁻` or `0⁺`. Then the integrated
driving evolution has infinite lifetime, its trace is continuous, and `lim_{t→∞} η(t) = ∞`." Its proof rests on
[Zha10, Theorems 4.2 and 7.7] (with the external mathematician) and is not formalized. "Its trace" is the
continuous generating trace (`IsGeneratingTrace`), stated existentially and, for the limit, for every such trace
(a continuous generating trace of a driving function is unique, so this is the source's assertion). The same form
is used by SEC4-B's `prop412_of_aux7`. -/
def Aux7Statement (k : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → HasAdmissiblePartialSums k ρL ρR xL xR →
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
            Tendsto (fun t => ‖η t‖) atTop atTop

/-! ### The flow line of a field with Remark 4.1's boundary data -/

/-- The seed marks of a flow-line word sit at `0`. -/
theorem flowLineXL_zero (b : ℝ → ℝ) (J : Finset ℝ) :
    flowLineXL b J 0 ⟨0, by unfold flowLineNL; omega⟩ = 0 := rfl

theorem flowLineXR_zero (b : ℝ → ℝ) (J : Finset ℝ) :
    flowLineXR b J 0 ⟨0, by unfold flowLineNR; omega⟩ = 0 := rfl

variable {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- Unpacking a flow line from `0` (angle `0`): its coupling's driving evolution and its generating trace. -/
theorem IsFlowLine.exists_evolution {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsIntegratedSLEEvolution k (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL k b J 0 0)
        (flowLineRhoR k b J 0 0) P 𝓕 W VL VR B ζ ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
  obtain ⟨_, 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hfl
  refine ⟨𝓕, W, VL, VR, B, hcpl.1, ?_⟩
  filter_upwards [htr] with ω hω
  have he : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
    funext t
    simp
  rwa [he] at hω

/-- **Boundary avoidance for flow lines** (the passive-mark step of Lemmas 4.3, 4.5 and Aux. lemma 22). If the
boundary data `b` is at most `−Λ + πX` left of `0` and at least `Λ − πX` right of `0` off its jump candidates
(Remark 4.1), then almost surely the flow line from `0` has infinite lifetime and never touches `ℝ \ {0}`. -/
theorem IsFlowLine.ae_trace_ne_real (hk : 0 < k) (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := hasAdmissiblePartialSums_flowLine hk hb hL hR
  filter_upwards [IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissiblePartialSums hk hword hadm
    hev htr] with ω hω
  obtain ⟨hζ, hne⟩ := hω
  refine ⟨hζ, fun t x hx => ?_⟩
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact (hne t).1 _ x hx (by rw [flowLineXL_zero]; exact hx.le)
  · exact (hne t).2 _ x hx (by rw [flowLineXR_zero]; exact hx.le)

/-- **Boundary avoidance and the limit at the target for flow lines, from Aux. lemma 7.** Under Remark 4.1's
boundary condition, almost surely the flow line from `0` has infinite lifetime, never touches `ℝ \ {0}`, and
tends to `∞` (the target). -/
theorem IsFlowLine.ae_tendsto_of_aux7 (h7 : Aux7Statement.{u} k) (hk : 0 < k)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := hasAdmissiblePartialSums_flowLine hk hb hL hR
  filter_upwards [IsFlowLine.ae_trace_ne_real hk hb hL hR hfl, h7 _ _ _ _ P 𝓕 W VL VR B ζ hword hadm hev, htr]
    with ω h1 h2 h3
  obtain ⟨hζ, hne⟩ := h1
  rw [hζ] at h3
  exact ⟨hζ, hne, h2.2.2 _ h3⟩

/-! ### The chart `E(z) = e^{πz} − 1`: Lemma 4.3 for `a ≤ −Λ`, Aux. lemma 22 with all upper heights `≤ −Λ` -/

/-- Remark 4.1's bounds for the `E`-transported data when every upper height is at most `−Λ` (left side). -/
theorem stripHData_le_of_neg {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0)
    (hyJ : y ∉ stripHJumps JL JU) : stripHData k bL bU y ≤ -sleLambda k + π * chiC k := by
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨hy1, hyL, hyU⟩ := hyJ
  have hπ := Real.pi_pos
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [stripHData_of_lt_neg_one hlt]
    set x := Real.log (-y - 1) / π with hx
    have hxy : -Real.exp (π * x) - 1 = y := by
      rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring
    have := hU x fun h => hyU ⟨x, h, hxy⟩
    linarith
  · rw [stripHData_of_lt hgt]
    set x := Real.log (y + 1) / π with hx
    have hxy : Real.exp (π * x) - 1 = y := by
      rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring
    have hx0 : x < 0 := div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) hπ
    exact hlowL x hx0 fun h => hyL ⟨x, h, hxy⟩

/-- Remark 4.1's bounds for the `E`-transported data (right side: only the lower line). -/
theorem le_stripHData_of_pos {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y)
    (hyJ : y ∉ stripHJumps JL JU) : sleLambda k - π * chiC k ≤ stripHData k bL bU y := by
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hyL, -⟩ := hyJ
  have hπ := Real.pi_pos
  rw [stripHData_of_lt (by linarith)]
  set x := Real.log (y + 1) / π with hx
  have hxy : Real.exp (π * x) - 1 = y := by
    rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring
  have hx0 : 0 < x := div_pos (Real.log_pos (by linarith)) hπ
  exact hlowR x hx0 fun h => hyL ⟨x, h, hxy⟩

/-- `‖w‖ → ∞` in the chart `E` is `Re E⁻¹(w) → +∞`: the strip point tends to the right strip end. -/
theorem tendsto_re_stripInv {f : ℝ≥0 → ℂ} (hf : Tendsto (fun t => ‖f t‖) atTop atTop) :
    Tendsto (fun t => (stripInv (f t)).re) atTop atTop := by
  have hre : ∀ w : ℂ, (stripInv w).re = Real.log ‖w + 1‖ / π := fun w => by
    rw [stripInv, Complex.div_ofReal_re, Complex.log_re]
  simp only [hre]
  refine Tendsto.atTop_div_const Real.pi_pos (Real.tendsto_log_atTop.comp ?_)
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) hf)
  have := norm_sub_norm_le (f t) (-1)
  rw [norm_neg, norm_one, sub_neg_eq_add] at this
  linarith

/-- **Lemma 4.3, `a ≤ −Λ`, boundary part; Aux. lemma 22, all upper heights `≤ −Λ`, boundary part.** For the flow
line from `0` towards the right strip end (chart `E`), with lower data as in Remark 4.1 and every upper height at
most `−Λ` (equality included): almost surely the lifetime is infinite and the flow line never hits `∂_U𝒮`
(`upperLineH`) — indeed it never touches `∂𝒮` away from its seed. -/
theorem ae_notMem_upperLineH_of_isStripFlowLine (hk : 0 < k) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hbL : IsPiecewiseConstantBoundaryData bL JL) (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, η ω t ∉ upperLineH ∧ ∀ x : ℝ, x ≠ 0 → η ω t ≠ x := by
  filter_upwards [IsFlowLine.ae_trace_ne_real hk (isPiecewiseConstantBoundaryData_stripHData k hbL hbU)
    (fun y hy hyJ => stripHData_le_of_neg hU hlowL hy hyJ)
    (fun y hy hyJ => le_stripHData_of_pos hlowR hy hyJ) hfl] with ω hω
  refine ⟨hω.1, fun t => ⟨?_, hω.2 t⟩⟩
  rintro ⟨y, hy, hyt⟩
  exact hω.2 t y (ne_of_lt (lt_trans (mem_Iio.1 hy) (by norm_num))) hyt.symm

/-- **Lemma 4.3, `a ≤ −Λ`; Aux. lemma 22, all upper heights `≤ −Λ`** (from Aux. lemma 7). For the flow line from
`0` towards the right strip end (chart `E`), with lower data as in Remark 4.1 and every upper height at most `−Λ`:
almost surely the lifetime is infinite, the flow line never hits `∂_U𝒮`, and it accumulates at `+∞` (in the chart,
`‖η(t)‖ → ∞`; in the strip, `Re E⁻¹(η(t)) → +∞`). -/
theorem lemma43_right_of_aux7 (h7 : Aux7Statement.{u} k) (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ upperLineH) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (stripInv (η ω t)).re) atTop atTop := by
  filter_upwards [ae_notMem_upperLineH_of_isStripFlowLine hk hbL hbU hU hlowL hlowR hfl,
    IsFlowLine.ae_tendsto_of_aux7 h7 hk (isPiecewiseConstantBoundaryData_stripHData k hbL hbU)
      (fun y hy hyJ => stripHData_le_of_neg hU hlowL hy hyJ)
      (fun y hy hyJ => le_stripHData_of_pos hlowR hy hyJ) hfl] with ω h1 h2
  exact ⟨h1.1, fun t => (h1.2 t).1, h2.2.2, tendsto_re_stripInv h2.2.2⟩

end Sec4

end InteractingSLE
