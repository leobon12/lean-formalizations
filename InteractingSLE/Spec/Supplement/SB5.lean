/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBFrontier
import InteractingSLE.Spec.Supplement.GW2ConeArc

/-!
# Corollary SB5 from Theorem SB4 and the ambient counterflow admissibility

Packet PROVE-T14-SB2. Corollary SB5 (supplement p. 635, `source/spec/p625-671.md` L192–L196):

> "In GW2 let `v > 0` be a prescribed root on the initial forced lower boundary arc, and let every prescribed schedule
> angle lie in `(−π/2, π/2)`. The schedule lies to the left of the completed lower walk and to the right of the
> completed upper walk, including every finite available endpoint."
>
> *Proof.* "The same-connector assertion of SB4 supplies the lower barrier. For the upper barrier apply its reflected
> distinct-seed version to the interval `[0, v]`. On each of its finitely many original height intervals, ambient
> counterflow admissibility and the low arc rule give `−λ − πχ/2 < H ≤ −λ + πχ/2 = −Λ` (SB5.1). [...] Thus the
> whole initial middle word is doubly admissible for every schedule angle."

Main results:

* **`neg_sleLambda_sub_lt_of_counterflow`** (the lower half of (SB5.1), "ambient counterflow admissibility"): in the
  setting of Theorem 1.4 and under Lemma GW0's forward implication, `−λ − πχ/2 < b(x)` at every positive real `x` off
  `jumps`. The centred counterflow is the angle-`0` flow line at `16/κ` of the word of `counterflowData κ b`
  (`GW2Cone.isFlowLineDriver_counterflowData`); GW0 makes its left partial sums `> −2`
  (`GW0.counterflow_admissible`); at `y = −1/x` the forced data is `−λ'(1 + S)` with `S` a left partial sum, and
  `counterflowData κ b y = −b(x) − πχ`, `λ' = λ − πχ/2`;
* `le_of_low_arc` (the upper half of (SB5.1), "the low arc rule"): `b(x) − πχ/2 ≤ −λ` on `(0, v]` off `jumps`;
* `SB4InitialArcStatement` (**named input**): SB4's same-connector assertion for a connector seed `v` on the initial
  forced lower arc, where the retained lower prefix is the real interval `[0, v]` (no field reveal);
* **`sb5Statement_of_inputs`**: `SB5Statement` from `GW0ForwardStatement`, `SB4InitialArcStatement` and the reflected
  half of `SB4DistinctSeedStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

open Sec4 Sec7.StripSysField
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The two halves of (SB5.1) -/

/-- **The left marks to the right of a point form an initial segment.** For a flow-line word (left marks strictly
decreasing in the index), the left weights of the marks strictly to the right of `y` sum to a left partial sum
`∑_{l ≤ i} ρL l`, or to `0` if there is none. -/
theorem exists_sum_filter_lt_flowLineXL (b : ℝ → ℝ) (J : Finset ℝ) (ρ : Fin (flowLineNL b J 0) → ℝ) (y : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => y < flowLineXL b J 0 i), ρ i) = 0 ∨
      ∃ i₀ : Fin (flowLineNL b J 0), (∑ i ∈ Finset.univ.filter (fun i => y < flowLineXL b J 0 i), ρ i) =
        ∑ l ∈ Finset.univ.filter (fun l => l ≤ i₀), ρ l := by
  set S := Finset.univ.filter (fun i : Fin (flowLineNL b J 0) => y < flowLineXL b J 0 i) with hS
  by_cases hne : S.Nonempty
  · refine Or.inr ⟨S.max' hne, ?_⟩
    congr 1
    ext i
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact S.le_max' i (by simpa [hS] using hi)
    · intro hi
      have hm : y < flowLineXL b J 0 (S.max' hne) := by
        have := S.max'_mem hne
        simpa [hS] using this
      rcases hi.lt_or_eq with hlt | heq
      · exact hm.trans (GW0.flowLineXL_lt b J 0 hlt)
      · rw [heq]
        exact hm
  · left
    rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]

/-- **Ambient counterflow admissibility** (the lower half of (SB5.1), supplement p. 635): in the setting of
Theorem 1.4 (a centred counterflow of the GFF `h` with data `b`, with almost surely infinite lifetime), under
Lemma GW0's forward implication, every positive real point `x` off `jumps` has `−λ − πχ/2 < b(x)`. -/
theorem neg_sleLambda_sub_lt_of_counterflow (hGW0 : GW0.GW0ForwardStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {x : ℝ} (hx0 : 0 < x)
    (hxJ : x ∉ jumps) :
    -sleLambda κ - Real.pi / 2 * chiC κ < b x := by
  obtain ⟨h', -, hfl⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨hadmL, -⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfl hζ'
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  have hk : 0 < 16 / κ := by positivity
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  set y : ℝ := -x⁻¹ with hy
  have hy0 : y < 0 := by rw [hy]; exact neg_neg_of_pos (inv_pos.2 hx0)
  have hyx : -y⁻¹ = x := by rw [hy, inv_neg, inv_inv, neg_neg]
  have hyJ : y ∉ J' := by
    intro hmem
    rcases Finset.mem_insert.1 hmem with h0 | himg
    · exact hy0.ne h0
    · obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 himg
      have : w = x := by
        have e : w⁻¹ = x⁻¹ := by linarith
        exact inv_injective e
      exact hxJ (this ▸ hw)
  -- the forced data of the counterflow word at `y`
  have hfb := Sec4.forceBoundaryData_flowLine hk hb' (x := y) hy0.ne hyJ
  unfold forceBoundaryData at hfb
  simp only [hy0, ↓reduceIte] at hfb
  have hcd : b' y = -b x - Real.pi * chiC κ := by
    rw [hb'def, GW2Cone.counterflowData_of_neg κ b hy0, hyx]
  rw [hcd] at hfb
  -- the left partial sum is `> −2`
  set S := ∑ i ∈ Finset.univ.filter (fun i => y < flowLineXL b' J' 0 i), flowLineRhoL (16 / κ) b' J' 0 0 i
    with hS
  have hS2 : -2 < S := by
    rcases exists_sum_filter_lt_flowLineXL b' J' (flowLineRhoL (16 / κ) b' J' 0 0) y with h0 | ⟨i₀, hi₀⟩
    · rw [hS, h0]
      norm_num
    · rw [hS, hi₀]
      exact hadmL i₀
  have hL : Real.pi / Real.sqrt (16 / κ) = sleLambda (16 / κ) := rfl
  rw [hL] at hfb
  have hlam := GW2Cone.sleLambda_sixteen_div_eq hκ
  have hpos : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  -- `−b(x) − πχ = −λ'(1 + S) < λ'`, and `λ' = λ − πχ/2`
  have hlt : -b x - Real.pi * chiC κ < sleLambda (16 / κ) := by
    rw [← hfb]
    nlinarith
  rw [hlam] at hlt
  linarith

/-- **The low arc rule** (the upper half of (SB5.1)): if the right seed at `0` and every genuine jump in `(0, v]`
keep the outward height low (`b(·⁺) − πχ/2 ≤ −λ`), then `b(x) − πχ/2 ≤ −λ` at every `x ∈ (0, v]` off `jumps` (`b(x)`
is the right limit at the last genuine jump below `x`, or at `0`). -/
theorem le_of_low_arc {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {v : ℝ} (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {x : ℝ} (hx0 : 0 < x) (hxv : x ≤ v) (hxJ : x ∉ jumps) :
    b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
  set G := (jumpSet b jumps).filter (fun z => 0 < z ∧ z < x) with hG
  -- the last genuine jump below `x`, or `0`
  set e : ℝ := if hne : G.Nonempty then G.max' hne else 0 with he
  have he0 : 0 ≤ e := by
    rw [he]
    split_ifs with hne
    · exact (Finset.mem_filter.1 (G.max'_mem hne)).2.1.le
    · exact le_rfl
  have hex : e < x := by
    rw [he]
    split_ifs with hne
    · exact (Finset.mem_filter.1 (G.max'_mem hne)).2.2
    · exact hx0
  have hlowe : rightLim b e - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    rw [he]
    split_ifs with hne
    · have hm := Finset.mem_filter.1 (G.max'_mem hne)
      exact hlow _ hm.1 hm.2.1 (hm.2.2.le.trans hxv)
    · exact hlow0
  have hsum := Exist.eq_rightLim_add_sum_seed hb hex hxJ
  have hzero : ∑ z ∈ jumps.filter (fun z => e < z ∧ z < x), (rightLim b z - leftLim b z) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨hzJ, hez, hzx⟩ := Finset.mem_filter.1 hz
    by_contra hne
    have hzG : z ∈ G := Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨hzJ, fun h => hne (by rw [h, sub_self])⟩, he0.trans_lt hez, hzx⟩
    have hle : z ≤ e := by
      rw [he]
      split_ifs with hne'
      · exact G.le_max' z hzG
      · exact absurd ⟨z, hzG⟩ hne'
    linarith
  rw [hsum, hzero, add_zero]
  exact hlowe

/-- **(SB5.1): the initial middle word is doubly admissible** for every schedule angle `θ ≤ π/2`: on `(0, v)` off
`jumps`, the upper walk (angle `π/2`) has right cumulative weight `> −2` and the angle-`θ` schedule has left cumulative
weight `> −2`. -/
theorem sb51_of_counterflow (hGW0 : GW0.GW0ForwardStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ}
    (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {x : ℝ} (hx : x ∈ Ioo 0 v) (hxJ : x ∉ jumps) {θ : ℝ} (hθ : θ ≤ Real.pi / 2) :
    -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ) ∧ -2 < cumWeightLeft κ (b x + θ * chiC κ) := by
  have hlo := neg_sleLambda_sub_lt_of_counterflow hGW0 hκ hκ4 hb hh hcf hζ' hx.1 hxJ
  have hhi := le_neg_bigLambda_of_low (le_of_low_arc hb hlow0 hlow hx.1 hx.2.le hxJ)
  exact ⟨sb51_upper_right hκ hlo, sb51_left hκ hκ4 hhi hθ⟩

/-! ### SB4's same-connector assertion on the initial forced arc (named input) -/

/-- **Theorem SB4, the same-connector assertion, at a seed of the initial forced lower arc** (supplement p. 634:
"The same holds for a schedule launched from a point of a recorded lower real connector in the retained conditional
field, after adjoining the corresponding lower-walk prefix"; p. 635: "For a connector seed `v`, retain the lower
prefix through `v`. The remaining lower walk, in its current domain, starts with the remaining low interval up to the
next available mark."), in the setting of Theorem 1.4, for the connector seeds `v > 0` of the initial forced lower arc
(the lower walk's right seed group at `0` is bad and every genuine jump in `(0, v]` keeps the outward height low, as in
`SB5Statement`): the retained lower prefix through `v` is the real interval `[0, v]`, which reveals no field, so the
retained conditional field is the original one and the schedule is the original-field schedule from `v`. For a
prescribed schedule `l` (switch times increasing) with angles in `(−π/2, π/2]` and (SB4.1), almost surely its whole
history misses the open right side of the completed lower walk `R`. This is a special case of SB4's assertion. -/
def SB4InitialArcStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ᵐ ω ∂P,
        ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅

/-! ### Corollary SB5 -/

/-- **Corollary SB5** (supplement p. 635) from SB4's same-connector assertion on the initial arc (the lower barrier),
the reflected distinct-seed version of SB4 on `[0, v]` (the upper barrier) and Lemma GW0's forward implication (the
ambient counterflow admissibility in (SB5.1)). -/
theorem sb5Statement_of_inputs (hGW0 : GW0.GW0ForwardStatement.{u}) (hIA : SB4InitialArcStatement.{u})
    (hDS : SB4DistinctSeedStatement.{u}) : SB5Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE v hv hlow0 hlow l hl hθ
  have h41 : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ := fun p hp q hq =>
    sb41_of_mem_Ioo hκ hκ4 (hθ p hp) (hθ q hq)
  have hlower := hIA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE v hv hlow0 hlow l hl h41
    fun p hp => ⟨(hθ p hp).1, (hθ p hp).2.le⟩
  have hupper := (hDS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE l hl h41).2 v hv.le
    (fun p hp => ⟨(hθ p hp).1.le, (hθ p hp).2⟩)
    (fun x hx hxJ => (sb51_of_counterflow hGW0 hκ hκ4 hb hh hcf hζ' hlow0 hlow hx hxJ le_rfl).1)
    (fun p hp x hx hxJ => Or.inl
      (sb51_of_counterflow hGW0 hκ hκ4 hb hh hcf hζ' hlow0 hlow hx hxJ (hθ p hp).2.le).2)
  filter_upwards [hlower, hupper] with ω h1 h2
  exact ⟨h1, h2⟩

end SB

end Theorem14

end InteractingSLE
