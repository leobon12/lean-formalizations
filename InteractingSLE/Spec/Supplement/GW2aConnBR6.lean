/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ConeArc
import InteractingSLE.Spec.Supplement.BR6ProofArc

/-!
# GW2a's connectors: Theorem BR6 for data that are low next to the seed

Packet PROVE-GW2A-CONN. GW2a (supplement p. 624): "For a right threshold the proposed connector has
`H + θχ ≤ −λ ⟹ H ≤ −λ − θχ ≤ −Λ`. Its outward conditional counterflow sums are consequently at most `d` by the BW2
calculation, while the whole conditional word is admissible. BR6 forces the entire connector". This file proves the
BR6 step for any GFF `h` with piecewise-constant data `b` (in the application: the conditional field read in the state
chart, under the regular conditional law given the retained past) and any centred counterflow of `h` with infinite
lifetime:

* **`ae_trace_eq_of_low_right`**: if `b − πχ/2 ≤ −λ` on `(0, v)` (off the jumps), the counterflow trace visits the
  inverted point `−1/v` (BR6 sufficiency for the reflected counterflow word at `1/v`, as in GW2's forced arcs;
  `GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`, whose hypothesis `v ∈ lowerArcRoots` is replaced by the
  low data on `(0, v)` alone);
* **`ae_trace_eq_of_low_left`**: the mirror: if `b + πχ/2 ≥ λ` on `(v, 0)`, `v < 0`, the trace visits `−1/v > 0`
  (BR6 sufficiency for the counterflow word itself, no reflection: the right intervals of the counterflow word beyond
  `−1/v` are the physical intervals of `(v, 0)`, where the counterflow data are `−b − πχ − 2πχ(16/κ) ≤ λ'(k/2 − 3)`).

Conditions 1–2 of BR6 are the admissibility of the counterflow word (Lemma GW0's forward implication, from the infinite
lifetime); the visit is turned into a time `t` with `γ(t) = −1/v` for the chosen continuous trace `γ` (Theorem 1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Sec7.StripSysField GW2Cone
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Condition 3 for the reflected counterflow word (right connectors) -/

/-- **The reflected counterflow word is low beyond `1/v`** when the data are low on `(0, v)`: the proof of
`GW2Cone.rightLowBeyond_counterflow`, with the low data on `(0, v)` in place of `v ∈ lowerArcRoots`. -/
theorem rightLowBeyond_counterflow_of_low {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {v : ℝ} (hv0 : 0 < v)
    (hlow : ∀ x, 0 < x → x < v → x ∉ jumps → b x - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ) :
    BR6.RightLowBeyond (16 / κ) (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0)
      (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0) v⁻¹ := by
  intro p hp hgap
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  set xL := flowLineXL b' J' 0 with hxL
  have hk : 0 < 16 / κ := by positivity
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  have hxL0 : ∀ i, xL i ≤ 0 := (Theorem15.isOrderedForceWord_flowLine b' J' 0).2.1
  have hp0 : 0 ≤ p := by
    rcases hp with rfl | ⟨i, rfl⟩
    · exact le_rfl
    · simp only [Pi.neg_apply, neg_nonneg]
      exact hxL0 i
  have hz0 : 0 < v⁻¹ := inv_pos.2 hv0
  set F := (Finset.univ.image fun i => -xL i).filter (p < ·) with hF
  set m := max p v⁻¹ with hm
  set q : ℝ := if hne : F.Nonempty then F.min' hne else m + 1 with hq
  have hmq : m < q := by
    rw [hq]
    split_ifs with hne
    · obtain ⟨hmem, hpq⟩ := Finset.mem_filter.1 (F.min'_mem hne)
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
      have hzq : v⁻¹ < F.min' hne := by
        rcases hgap i with h | h
        · simp only [Pi.neg_apply] at h
          rw [← hi] at hpq
          linarith
        · simpa only [Pi.neg_apply, hi] using h
      exact max_lt hpq hzq
    · linarith
  obtain ⟨s, ⟨hms, hsq⟩, hsT⟩ := (Set.Ioo_infinite hmq).exists_notMem_finset
    (J'.image (fun y => -y) ∪ jumps.image (fun x => x⁻¹))
  have hs0 : 0 < s := lt_of_lt_of_le hz0 (le_max_right _ _) |>.trans hms
  have hzs : v⁻¹ < s := lt_of_le_of_lt (le_max_right _ _) hms
  have hyJ : -s ∉ J' := fun h => hsT (Finset.mem_union_left _ (Finset.mem_image.2 ⟨-s, h, neg_neg s⟩))
  have hxJ : s⁻¹ ∉ jumps := fun h => hsT (Finset.mem_union_right _ (Finset.mem_image.2 ⟨s⁻¹, h, inv_inv s⟩))
  have hfilt : Finset.univ.filter (fun i => (-xL) i ≤ p) = Finset.univ.filter (fun i => -s < xL i) := by
    refine Finset.filter_congr fun i _ => ?_
    simp only [Pi.neg_apply]
    constructor
    · intro h
      linarith [lt_of_le_of_lt (le_max_left p v⁻¹) hms]
    · intro h
      by_contra hpi
      push Not at hpi
      have hmemF : -xL i ∈ F := Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hpi⟩
      have hqle : q ≤ -xL i := by
        rw [hq]
        split_ifs with hne
        · exact F.min'_le _ hmemF
        · exact absurd ⟨_, hmemF⟩ hne
      linarith
  have hfb := Sec4.forceBoundaryData_flowLine hk hb' (x := -s) (by linarith) hyJ
  have hneg : -s < 0 := by linarith
  unfold forceBoundaryData at hfb
  have hcd : b' (-s) = -b (-(-s)⁻¹) - Real.pi * QuantumZipper.chiC κ := counterflowData_of_neg κ b hneg
  simp only [hneg, ↓reduceIte] at hfb
  rw [hcd] at hfb
  have hinv : -(-s)⁻¹ = s⁻¹ := by rw [inv_neg, neg_neg]
  rw [hinv] at hfb
  have hsv : s⁻¹ < v := by
    rw [inv_lt_comm₀ hs0 hv0]
    exact hzs
  have hlow' := hlow s⁻¹ (inv_pos.2 hs0) hsv hxJ
  have hlam := sleLambda_sixteen_div_eq hκ
  have hπ := Sec7.pi_mul_chiC_div_sleLambda_sixteen_div hκ
  have hpos : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  have hL : Real.pi / Real.sqrt (16 / κ) = sleLambda (16 / κ) := rfl
  rw [hL] at hfb
  rw [div_eq_iff hpos.ne'] at hπ
  rw [hfilt]
  set S := ∑ i ∈ Finset.univ.filter (fun i => -s < xL i), flowLineRhoL (16 / κ) b' J' 0 0 i with hS
  have key : sleLambda (16 / κ) * (1 + S) ≤ sleLambda (16 / κ) * (16 / κ / 2 - 3) := by
    nlinarith
  have := le_of_mul_le_mul_left key hpos
  linarith

/-! ### Condition 3 for the counterflow word (left connectors) -/

/-- The counterflow data on the chart's right side: `counterflowData κ b y = −b(−1/y) − πχ − 2πχ(16/κ)` for
`y > 0`. -/
theorem counterflowData_of_pos (κ : ℝ) (b : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    counterflowData κ b y = -b (-y⁻¹) - Real.pi * QuantumZipper.chiC κ -
      2 * Real.pi * QuantumZipper.chiC (16 / κ) := by
  have hy' : ¬ y < 0 := not_lt.2 hy.le
  simp only [counterflowData, inverseData, returnData, liftBoundary, hy', ↓reduceIte, cfOffset, cfCoeff]
  ring

/-- **The counterflow word is low beyond `−1/v`** (BR6's condition 3 for the counterflow word itself) when the data
are high on `(v, 0)`, `v < 0`: every right interval `(p, p⁺)` of the counterflow word meeting `(−1/v, ∞)` corresponds
to physical points of `(v, 0)`, where `b + πχ/2 ≥ λ`, and its cumulative weight is `(−b − πχ − 2πχ')/λ' − 1 ≤ k/2 − 4`
(`χ' = χ(16/κ) = −χ`, `λ' = λ − πχ/2`, `πχ = (k/2 − 2)λ'`). -/
theorem rightLowBeyond_counterflow_of_high {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {v : ℝ} (hv0 : v < 0)
    (hhigh : ∀ x, v < x → x < 0 → x ∉ jumps → sleLambda κ ≤ b x + Real.pi / 2 * QuantumZipper.chiC κ) :
    BR6.RightLowBeyond (16 / κ) (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0)
      (flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0) (-v⁻¹) := by
  intro p hp hgap
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  set xR := flowLineXR b' J' 0 with hxR
  have hk : 0 < 16 / κ := by positivity
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  have hz0 : 0 < -v⁻¹ := neg_pos.2 (inv_lt_zero.2 hv0)
  set F := (Finset.univ.image fun i => xR i).filter (p < ·) with hF
  set m := max p (-v⁻¹) with hm
  set q : ℝ := if hne : F.Nonempty then F.min' hne else m + 1 with hq
  have hmq : m < q := by
    rw [hq]
    split_ifs with hne
    · obtain ⟨hmem, hpq⟩ := Finset.mem_filter.1 (F.min'_mem hne)
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
      have hzq : -v⁻¹ < F.min' hne := by
        rcases hgap i with h | h
        · rw [← hi] at hpq
          linarith
        · rw [← hi]; exact h
      exact max_lt hpq hzq
    · linarith
  obtain ⟨s, ⟨hms, hsq⟩, hsT⟩ := (Set.Ioo_infinite hmq).exists_notMem_finset
    (J' ∪ jumps.image (fun x => -x⁻¹))
  have hs0 : 0 < s := lt_of_lt_of_le hz0 (le_max_right _ _) |>.trans hms
  have hzs : -v⁻¹ < s := lt_of_le_of_lt (le_max_right _ _) hms
  have hps : p < s := lt_of_le_of_lt (le_max_left _ _) hms
  have hyJ : s ∉ J' := fun h => hsT (Finset.mem_union_left _ h)
  have hxJ : -s⁻¹ ∉ jumps := fun h => hsT (Finset.mem_union_right _ (Finset.mem_image.2 ⟨-s⁻¹, h, by
    rw [inv_neg, inv_inv, neg_neg]⟩))
  have hfilt : Finset.univ.filter (fun i => xR i ≤ p) = Finset.univ.filter (fun i => xR i ≤ s) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h
      linarith
    · intro h
      by_contra hpi
      push Not at hpi
      have hmemF : xR i ∈ F := Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hpi⟩
      have hqle : q ≤ xR i := by
        rw [hq]
        split_ifs with hne
        · exact F.min'_le _ hmemF
        · exact absurd ⟨_, hmemF⟩ hne
      linarith
  have hfb := Sec4.forceBoundaryData_flowLine hk hb' (x := s) hs0.ne' hyJ
  unfold forceBoundaryData at hfb
  have hcd := counterflowData_of_pos κ b hs0
  simp only [not_lt.2 hs0.le, ↓reduceIte] at hfb
  rw [show b' s = counterflowData κ b s from rfl, hcd] at hfb
  -- the physical point `−1/s` lies in `(v, 0)`
  have hxv : v < -s⁻¹ := by
    have h1 : s⁻¹ < -v := by
      rw [inv_lt_comm₀ hs0 (neg_pos.2 hv0), inv_neg]
      exact hzs
    linarith
  have hx0 : -s⁻¹ < 0 := neg_lt_zero.2 (inv_pos.2 hs0)
  have hhigh' := hhigh _ hxv hx0 hxJ
  have hlam := sleLambda_sixteen_div_eq hκ
  have hπ := Sec7.pi_mul_chiC_eq_mul_sleLambda_sixteen_div hκ
  have hχ := Sec4.chiC_sixteen_div hκ
  have hpos : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  have hL : Real.pi / Real.sqrt (16 / κ) = sleLambda (16 / κ) := rfl
  rw [hL, hχ] at hfb
  rw [hfilt]
  change ∑ i ∈ Finset.univ.filter (fun i => flowLineXR b' J' 0 i ≤ s), flowLineRhoR (16 / κ) b' J' 0 0 i ≤ _
  set S := ∑ i ∈ Finset.univ.filter (fun i => flowLineXR b' J' 0 i ≤ s), flowLineRhoR (16 / κ) b' J' 0 0 i
    with hS
  have key : sleLambda (16 / κ) * (1 + S) ≤ sleLambda (16 / κ) * (16 / κ / 2 - 3) := by
    nlinarith
  have := le_of_mul_le_mul_left key hpos
  linarith

/-! ### The visits -/

/-- **BR6 at a point of a low right interval next to the seed** (GW2a, p. 624; BW2): for a GFF `h` with data `b`
that are low (`b − πχ/2 ≤ −λ`) on `(0, v)`, and a centred counterflow of `h` with infinite lifetime, almost surely
the chosen continuous counterflow trace (Theorem 1.3) visits `−1/v`, i.e. `v` is a physical point of the counterflow. -/
theorem ae_trace_eq_of_low_right (hT13 : Exist.Theorem13Statement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ} (hv0 : 0 < v)
    (hlow : ∀ x, 0 < x → x < v → x ∉ jumps → b x - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, GW2aSingle.chosenTrace W' ζ' ω t = -((v : ℂ))⁻¹ := by
  obtain ⟨h', -, hfl⟩ := isFlowLineDriver_counterflowData hκ hb hh hcf
  have hk : 0 < 16 / κ := by positivity
  have hk4 : 4 < 16 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfl hζ'
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hE := hC.1.reflect
  have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) (ζ' ω)
      (fun t => LP.reflectC (GW2aSingle.chosenTrace W' ζ' ω t)) := by
    filter_upwards [hγ] with ω hω
    exact LP.isGeneratingTrace_reflect hω.1
  have hword := Supp7.G12.isOrderedForceWord_reflect
    (Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps jumps) 0)
  have hseed : (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0) ⟨0, Nat.succ_pos _⟩ < v⁻¹ := by
    change -(0 : ℝ) < v⁻¹
    rw [neg_zero]
    exact inv_pos.2 hv0
  have hvis := BR6Proof.ae_visit_of_conditions hT13 hk4 (inv_pos.2 hv0) hword (Nat.succ_pos _) ⟨_, hseed⟩ hE hη
    (fun j _ => hadmR j) (fun m _ _ => hadmL m) (rightLowBeyond_counterflow_of_low hκ hb hv0 hlow)
  filter_upwards [hvis] with ω hω
  obtain ⟨t, -, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [eq_neg_of_reflectC_eq ht, Complex.ofReal_inv]

/-- **BR6 at a point of a high left interval next to the seed** (the reflected rule of GW2a, p. 624): for data with
`b + πχ/2 ≥ λ` on `(v, 0)`, `v < 0`, almost surely the chosen counterflow trace visits `−1/v`. -/
theorem ae_trace_eq_of_low_left (hT13 : Exist.Theorem13Statement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ} (hv0 : v < 0)
    (hhigh : ∀ x, v < x → x < 0 → x ∉ jumps → sleLambda κ ≤ b x + Real.pi / 2 * QuantumZipper.chiC κ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, GW2aSingle.chosenTrace W' ζ' ω t = -((v : ℂ))⁻¹ := by
  obtain ⟨h', -, hfl⟩ := isFlowLineDriver_counterflowData hκ hb hh hcf
  have hk : 0 < 16 / κ := by positivity
  have hk4 : 4 < 16 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfl hζ'
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (GW2aSingle.chosenTrace W' ζ' ω) := by
    filter_upwards [hγ] with ω hω
    exact hω.1
  have hword := Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps jumps) 0
  have hz0 : 0 < -v⁻¹ := neg_pos.2 (inv_lt_zero.2 hv0)
  have hseed : flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0 ⟨0, Nat.succ_pos _⟩ < -v⁻¹ := by
    change (0 : ℝ) < -v⁻¹
    exact hz0
  have hvis := BR6Proof.ae_visit_of_conditions hT13 hk4 hz0 hword (Nat.succ_pos _) ⟨_, hseed⟩ hC.1 hη
    (fun j _ => hadmL j) (fun m _ _ => hadmR m) (rightLowBeyond_counterflow_of_high hκ hb hv0 hhigh)
  filter_upwards [hvis] with ω hω
  obtain ⟨t, -, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [ht, Complex.ofReal_neg, Complex.ofReal_inv]

end GW2aConn

end Theorem14

end InteractingSLE
