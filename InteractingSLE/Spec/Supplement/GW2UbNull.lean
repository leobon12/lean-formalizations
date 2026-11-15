/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbVis
import InteractingSLE.Spec.Supplement.GB6RelDetGood
import InteractingSLE.Spec.Supplement.GB6RelDrvLift
import InteractingSLE.Spec.Supplement.GW2BjImg
import InteractingSLE.Spec.Supplement.CS3

/-!
# The tip-exclusion event is null for the canonical flow line of every GFF with a far right height

Packet PROVE-GW2-RELDET (round 38, decision D73 route (ii)). In the relative stage chart the counterflow tip is the
flow line's target `∞`, and beyond the far right junction the boundary carries the counterflow side's height
`λ' − πχ + θχ` (`λ' = λ(16/κ)`, `θ` the angle; NEARIMG2's `GW2Ni.FarRAt` at `GW2Ni.farJunctionX`), of right
cumulative weight `3κ/4 − 3 + θχ/λ`, in `(κ/2 − 4, κ/2 − 2)` for `θ ∈ (−π/2, π/2)` (`lt_cumWeightRight_far`, NEARIMG2's
`flowSwallow_premises_schedWordMapX`). A first contact at the tip is a flow line that reaches `∞` without touching
that far ray. It is read on the word and the canonical driver code, at rational points (`BadCode`):

* the code's lifetime is `⊤` and the code is good;
* there is a rational `r > 0` beyond which the word's height is one constant at the rational non-jump points, of right
  cumulative weight in `(κ/2 − 4, κ/2 − 2)`;
* every rational `q > r` is alive for the decoded driver at every integer time (`GW2Bh.aliveRead`).

`BadCode` is a measurable event (`measurableSet_badCode`). It is null under the GFF of every sorted word
(`ae_not_badCode_of_isGFF`): on the flow line of Theorem 1.1's coupling, `r` is swallowed (`FlowSwallowStatement`, the
total right weight is `< κ/2 − 2`), never visited (Lemma G12, the cumulative weight through `r` is `> κ/2 − 4`), so a
rational `q > r` is swallowed (`exists_rat_not_alive_of_collide`); the code is the flow
line's driver (the determination clause), and the law of the code depends only on the law of the field.

* **`BadCode`**, **`measurableSet_badCode`**;
* **`ae_not_badCode_of_flowLine`**, **`ae_not_badCode_of_isGFF`** (inputs: Theorem 1.3 and `FlowSwallowStatement`, in
  `Type`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Rd

open MartChar.RealFlow Restart Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv Sec4

/-! ### The far right height and its weight -/

/-- **The far right height at angle `θ` has right cumulative weight above `κ/2 − 4`** for `θ > −π/2`: it is
`3κ/4 − 3 + θχ/λ` (`CS3.cs3_rR_eq` at `S = 0`). -/
theorem lt_cumWeightRight_far {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : -(Real.pi / 2) < θ) :
    κ / 2 - 4 < cumWeightRight κ (sleLambda (16 / κ) - Real.pi * chiC κ + θ * chiC κ) := by
  have h := CS3.cs3_rR_eq hκ 0 θ
  simp only [add_zero, mul_one] at h
  rw [h]
  have h1 : κ / 4 * (0 - (16 / κ / 2 - 4)) = κ - 2 := by
    have := CS3.quarter_mul_d hκ
    linarith
  have h2 : 0 < (Real.pi / 2 + θ) * chiC κ / sleLambda κ :=
    div_pos (mul_pos (by linarith) (chiC_pos hκ hκ4)) (sleLambda_pos hκ)
  linarith

/-! ### Right limits from rational heights -/

/-- Right of every point there is an interval without jumps. -/
theorem exists_noJump_right (c : BoundaryWord) (y : ℝ) : ∃ a, y < a ∧ ∀ t ∈ Ioo y a, t ∉ c.jumps := by
  classical
  set S := c.jumps.filter (fun j => y < j) with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.min' hne, (Finset.mem_filter.1 (S.min'_mem hne)).2, fun t ht hj => ?_⟩
    have hmin := S.min'_le t (Finset.mem_filter.2 ⟨hj, ht.1⟩)
    exact absurd ht.2 (not_lt.2 hmin)
  · refine ⟨y + 1, by linarith, fun t ht hj => hne ⟨t, Finset.mem_filter.2 ⟨hj, ht.1⟩⟩⟩

/-- **A height read at the rational points beyond `r` is the right limit at every point at or beyond `r`.** -/
theorem rightLim_eq_of_rat {c : BoundaryWord} {r : ℚ} {v : ℝ}
    (hfar : ∀ x : ℚ, r < x → (x : ℝ) ∉ c.jumps → c.fn x = v) {y : ℝ} (hy : (r : ℝ) ≤ y) :
    PiecewiseConstantBoundaryData.rightLim c.fn y = v := by
  obtain ⟨a, hya, hna⟩ := exists_noJump_right c y
  refine Sec4.rightLim_eq_of_forall hya fun t ht => ?_
  obtain ⟨q, hq1, hq2, hqj, hq⟩ := exists_rat_fn_eq c (hna t ht) ht.1 ht.2
  rw [← hq]
  exact hfar q (by exact_mod_cast lt_of_le_of_lt hy hq1) hqj

/-- **A constant height at the rational non-jump points beyond `r`**: some rational point beyond `r` is not a jump, and
every such point carries its height. -/
theorem exists_far_height {c : BoundaryWord} {r : ℚ}
    (hc : ∀ x x' : ℚ, r < x → r < x' → (x : ℝ) ∉ c.jumps → (x' : ℝ) ∉ c.jumps → c.fn x = c.fn x') :
    ∃ x₀ : ℚ, r < x₀ ∧ (x₀ : ℝ) ∉ c.jumps ∧ ∀ x : ℚ, r < x → (x : ℝ) ∉ c.jumps → c.fn x = c.fn x₀ := by
  obtain ⟨a, hra, hna⟩ := exists_noJump_right c r
  obtain ⟨x₀, h1, h2⟩ := exists_rat_btwn hra
  have hx₀ : r < x₀ := by exact_mod_cast h1
  exact ⟨x₀, hx₀, hna x₀ ⟨h1, h2⟩, fun x hx hxj => hc x x₀ hx hx₀ hxj (hna x₀ ⟨h1, h2⟩)⟩

/-! ### The event -/

/-- **The tip-exclusion event of a word and a driver code**: infinite lifetime, a good code, and a rational `r > 0`
such that the word's height is one constant at the rational non-jump points beyond `r`, of right cumulative weight in
`(κ/2 − 4, κ/2 − 2)`, and every rational `q > r` is alive for the decoded driver at every integer time. -/
def BadCode (κ : ℝ) (b : BoundaryWord) (p : PCode × ℝ≥0∞) : Prop :=
  p.2 = ⊤ ∧ IsGoodDrvCode p ∧ ∃ r : ℚ, 0 < r ∧
    (∀ x x' : ℚ, r < x → r < x' → (x : ℝ) ∉ b.jumps → (x' : ℝ) ∉ b.jumps → b.fn x = b.fn x') ∧
    (∀ x : ℚ, r < x → (x : ℝ) ∉ b.jumps →
      κ / 2 - 4 < cumWeightRight κ (b.fn x) ∧ cumWeightRight κ (b.fn x) < κ / 2 - 2) ∧
    ∀ q : ℚ, r < q → ∀ n : ℕ, GW2Bh.aliveRead n q (drvDec p)

/-- `BadCode` is a measurable event of the word and the code. -/
theorem measurableSet_badCode (κ : ℝ) :
    MeasurableSet {x : BoundaryWord × (PCode × ℝ≥0∞) | BadCode κ x.1 x.2} := by
  have hdec : Measurable fun x : BoundaryWord × (PCode × ℝ≥0∞) => drvDec x.2 :=
    measurable_pi_iff.2 fun t => (measurable_drvDec t).comp measurable_snd
  have hfnm : ∀ x : ℚ, Measurable fun y : BoundaryWord × (PCode × ℝ≥0∞) => y.1.fn (x : ℝ) := fun x =>
    (measurable_fn (x : ℝ)).comp measurable_fst
  have hjm : ∀ x : ℚ, MeasurableSet {y : BoundaryWord × (PCode × ℝ≥0∞) | (x : ℝ) ∈ y.1.jumps} := fun x =>
    measurable_fst (measurableSet_mem_jumps (x : ℝ))
  have e : {x : BoundaryWord × (PCode × ℝ≥0∞) | BadCode κ x.1 x.2} =
      {x | x.2.2 = ⊤} ∩ (Prod.snd ⁻¹' {p | IsGoodDrvCode p}) ∩ ⋃ r : ℚ, ⋃ (_ : 0 < r),
        (⋂ x : ℚ, ⋂ x' : ℚ, ⋂ (_ : r < x), ⋂ (_ : r < x'),
          ({y : BoundaryWord × (PCode × ℝ≥0∞) | (x : ℝ) ∈ y.1.jumps} ∪ {y | (x' : ℝ) ∈ y.1.jumps} ∪
            {y | y.1.fn x = y.1.fn x'})) ∩
        (⋂ x : ℚ, ⋂ (_ : r < x), ({y : BoundaryWord × (PCode × ℝ≥0∞) | (x : ℝ) ∈ y.1.jumps} ∪
          ({y | κ / 2 - 4 < cumWeightRight κ (y.1.fn x)} ∩ {y | cumWeightRight κ (y.1.fn x) < κ / 2 - 2}))) ∩
        ⋂ q : ℚ, ⋂ (_ : r < q), ⋂ n : ℕ,
          (fun y : BoundaryWord × (PCode × ℝ≥0∞) => drvDec y.2) ⁻¹' {w | GW2Bh.aliveRead n q w} := by
    ext x
    simp only [BadCode, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iUnion, mem_iInter, mem_union,
      exists_prop]
    constructor
    · rintro ⟨h1, h2, r, hr, hc, hb, ha⟩
      refine ⟨⟨h1, h2⟩, r, hr, ⟨fun a a' ha ha' => ?_, fun a ha => ?_⟩, ha⟩
      · by_cases j1 : (a : ℝ) ∈ x.1.jumps
        · exact Or.inl (Or.inl j1)
        · by_cases j2 : (a' : ℝ) ∈ x.1.jumps
          · exact Or.inl (Or.inr j2)
          · exact Or.inr (hc a a' ha ha' j1 j2)
      · by_cases j1 : (a : ℝ) ∈ x.1.jumps
        · exact Or.inl j1
        · exact Or.inr (hb a ha j1)
    · rintro ⟨⟨h1, h2⟩, r, hr, ⟨hc, hb⟩, ha⟩
      refine ⟨h1, h2, r, hr, fun a a' ha ha' j1 j2 => ?_, fun a ha j1 => ?_, ha⟩
      · rcases hc a a' ha ha' with (h | h) | h
        · exact absurd h j1
        · exact absurd h j2
        · exact h
      · rcases hb a ha with h | h
        · exact absurd h j1
        · exact h
  have hcw : ∀ x : ℚ, Measurable fun y : BoundaryWord × (PCode × ℝ≥0∞) => cumWeightRight κ (y.1.fn x) := fun x =>
    ((hfnm x).div_const _).sub_const _
  rw [e]
  refine (((measurable_snd.comp measurable_snd) (measurableSet_singleton ⊤)).inter
    (measurable_snd measurableSet_isGoodDrvCode)).inter (MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
      ((MeasurableSet.iInter fun x => MeasurableSet.iInter fun x' => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ => ((hjm x).union (hjm x')).union (measurableSet_eq_fun (hfnm x) (hfnm x'))).inter
      (MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ => (hjm x).union
        ((measurableSet_lt measurable_const (hcw x)).inter (measurableSet_lt (hcw x) measurable_const)))).inter
        (MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun n =>
          hdec (GW2Bh.measurableSet_aliveRead n q)))

/-! ### The event is null on a flow line -/

open Classical in
/-- **`BadCode` is null for the canonical code of a flow line's field** (Theorem 1.3 and `FlowSwallowStatement` in
`Type`). For a flow-line driver at angle `0` of a field with the data of a word `c`, almost surely the canonical code
of `(c, field)` is not bad: for a rational `r > 0` beyond which the height is the far right height, `r` is swallowed on
an infinite lifetime and never visited (Lemma G12), so a rational `q > r` is swallowed. -/
theorem ae_not_badCode_of_flowLine (h13₀ : Exist.Theorem13Statement.{0}) (hsw : FlowSwallowStatement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ c.fn c.jumps 0 P X W ζ) :
    ∀ᵐ ω ∂P, ¬ BadCode κ c (F (c, X ω)) := by
  have hb := c.isPiecewiseConstantBoundaryData
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hfl' := hfl
  obtain ⟨X', 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hE := hC.1
  -- the trace (Theorem 1.3)
  have h13E := h13₀ hκ hord hE
  set ηr : Ω → ℝ≥0 → ℂ := fun ω => if h : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) then h.choose else fun _ => 0 with hηrdef
  have hηr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (ηr ω) := by
    filter_upwards [h13E] with ω hp
    have hex := hp.2
    simp only [hηrdef, hex, ↓reduceDIte]
    exact hex.choose_spec.1
  -- the weights through the points beyond `r`
  set good : ℚ → Prop := fun r => 0 < r ∧
    (∀ x x' : ℚ, r < x → r < x' → (x : ℝ) ∉ c.jumps → (x' : ℝ) ∉ c.jumps → c.fn x = c.fn x') ∧
    (∀ x : ℚ, r < x → (x : ℝ) ∉ c.jumps →
      κ / 2 - 4 < cumWeightRight κ (c.fn x) ∧ cumWeightRight κ (c.fn x) < κ / 2 - 2) with hgooddef
  have hcum : ∀ r : ℚ, good r → ∃ v : ℝ, κ / 2 - 4 < cumWeightRight κ v ∧ cumWeightRight κ v < κ / 2 - 2 ∧
      ∀ y : ℝ, (r : ℝ) ≤ y → ∑ i ∈ Finset.univ.filter (fun i => flowLineXR c.fn c.jumps 0 i ≤ y - 0),
        flowLineRhoR κ c.fn c.jumps 0 0 i = cumWeightRight κ v := by
    intro r hr
    obtain ⟨x₀, hx₀, hx₀j, hfar⟩ := exists_far_height hr.2.1
    refine ⟨c.fn x₀, (hr.2.2 x₀ hx₀ hx₀j).1, (hr.2.2 x₀ hx₀ hx₀j).2, fun y hy => ?_⟩
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by exact_mod_cast hr.1) hy
    rw [Supp7.sum_filter_flowLineXR_le hκ hb 0 hy0, rightLim_eq_of_rat hfar hy, zero_mul, add_zero]
  have htot : ∀ r : ℚ, good r → ∑ i, flowLineRhoR κ c.fn c.jumps 0 0 i < κ / 2 - 2 := by
    intro r hr
    obtain ⟨v, -, hv2, hv⟩ := hcum r hr
    set Y : ℝ := r + ∑ i, |flowLineXR c.fn c.jumps 0 i| with hY
    have hsum0 : 0 ≤ ∑ i, |flowLineXR c.fn c.jumps 0 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hrY : (r : ℝ) ≤ Y := le_add_of_nonneg_right hsum0
    have hall : Finset.univ.filter (fun i => flowLineXR c.fn c.jumps 0 i ≤ Y - 0) = Finset.univ := by
      refine Finset.filter_true_of_mem fun i _ => ?_
      rw [sub_zero]
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr.1.le
      calc flowLineXR c.fn c.jumps 0 i ≤ |flowLineXR c.fn c.jumps 0 i| := le_abs_self _
        _ ≤ ∑ j, |flowLineXR c.fn c.jumps 0 j| :=
          Finset.single_le_sum (fun j _ => abs_nonneg (flowLineXR c.fn c.jumps 0 j)) (Finset.mem_univ i)
        _ ≤ Y := le_add_of_nonneg_left hr0
    have h := hv Y hrY
    rw [hall] at h
    rw [h]
    exact hv2
  -- Lemma G12 at every such `r`
  have hG12 : ∀ᵐ ω ∂P, ∀ r : ℚ, good r → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ηr ω t ≠ ((r : ℝ) : ℂ) := by
    rw [ae_all_iff]
    intro r
    by_cases hr : good r
    · have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.1
      have hex : ∃ j, flowLineXR c.fn c.jumps 0 j < (r : ℝ) := ⟨⟨0, Nat.succ_pos _⟩, by
        have h0 : flowLineXR c.fn c.jumps 0 ⟨0, Nat.succ_pos _⟩ = 0 := Fin.cons_zero _ _
        rw [h0]
        exact hr0⟩
      have hS : κ / 2 - 4 < ∑ i ∈ Finset.univ.filter (fun i => flowLineXR c.fn c.jumps 0 i ≤ (r : ℝ)),
          flowLineRhoR κ c.fn c.jumps 0 0 i := by
        obtain ⟨v, hv1, -, hv⟩ := hcum r hr
        have h := hv r le_rfl
        rw [sub_zero] at h
        rw [h]
        exact hv1
      filter_upwards [Supp7.G12Low.ae_trace_ne_right_of_exists hκ hκ4 hord hE hηr hr0 hex hS] with ω hω _ t ht
      exact hω t ht
    · exact Eventually.of_forall fun ω h => absurd h hr
  -- the swallow of every such `r`
  have hswr : ∀ᵐ ω ∂P, ∀ r : ℚ, good r → ζ ω = ⊤ →
      ∃ t : ℝ≥0, rightImg (fun s : ℝ => W s.toNNReal ω) r t ≤ W t ω := by
    rw [ae_all_iff]
    intro r
    by_cases hr : good r
    · have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.1
      have ht := htot r hr
      filter_upwards [hsw hκ hκ4 c.fn c.jumps r hr0 ht P X W ζ hfl] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hr
  -- the code is the flow line's driver
  have hm := hF.2.2 c P X W ζ hfl
  have hcont := ae_driver_zero_continuousOn hfl
  filter_upwards [hm, hcont, hηr, hG12, hswr] with ω hmω hcω hηω hG12ω hswω
  rintro ⟨hL, hgood, r, hr0, hconst, hbd, halive⟩
  have hr : good r := ⟨hr0, hconst, hbd⟩
  have hζ : ζ ω = ⊤ := by rw [hmω.1]; exact hL
  have hcW : Continuous fun t => W t ω := by
    refine continuousOn_univ.1 (hcω.2.mono fun t _ => ?_)
    show (t : ℝ≥0∞) < ζ ω
    rw [hζ]
    exact ENNReal.coe_lt_top
  have hdec : drvDec (F (c, X ω)) = fun t => W t ω := funext fun t =>
    eqOn_drvDec_of_isStopDrvMatch hgood hcω.2 ⟨hmω.1.le, hmω.2.2⟩ t (by rw [hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨t₀, ht₀⟩ := hswω r hr hζ
  have hηtop : IsGeneratingTrace (fun t => W t ω) ⊤ (ηr ω) := hζ ▸ hηω
  obtain ⟨q, hq, hnal⟩ := exists_rat_not_alive_of_collide hcW hcω.1 hηtop (by exact_mod_cast hr0)
    (fun t => hG12ω r hr t (by rw [hζ]; exact le_top)) ht₀
  obtain ⟨n, hn⟩ := exists_nat_ge (t₀ : ℝ)
  have hal := halive q (by exact_mod_cast hq) n
  rw [hdec] at hal
  have hal2 := (GW2Bh.aliveRead_iff (q : ℝ) hcW.continuousOn).1 hal
  have hal3 : Alive (fun s : ℝ => W s.toNNReal ω) q ((n : ℝ≥0) : ℝ) := by
    refine (Supp8.GB6.alive_congr fun s hs => ?_).1 hal2
    simp only [frozenDrive, min_eq_left hs.2]
  refine hnal (hal3.mono ?_)
  simpa using hn

/-- **`BadCode` is null under every GFF with the data of a sorted word** (Theorem 1.3 and `FlowSwallowStatement` in
`Type`): Theorem 1.1's coupling carries a flow line whose field is a GFF with the data of `c`
(`ae_not_badCode_of_flowLine`), and the law of the code depends only on the law of the field. -/
theorem ae_not_badCode_of_isGFF (h13₀ : Exist.Theorem13Statement.{0}) (hsw : FlowSwallowStatement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData Q X c.fn c.jumps) :
    ∀ᵐ ω ∂Q, ¬ BadCode κ c (F (c, X ω)) := by
  obtain ⟨Ω₀, mΩ₀, -, P₀, hP₀, 𝓕, W, VL, VR, B, ζ, X₀, hC⟩ :=
    Sec7.StripSysBorel.exists_isOptionalHullCoupling_standardBorel.{0} hκ
      (ρL := flowLineRhoL κ c.fn c.jumps 0 0) (ρR := flowLineRhoR κ c.fn c.jumps 0 0)
      (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  have hfld : IsFlowLineDriver κ c.fn c.jumps 0 P₀ X₀ W ζ :=
    ⟨X₀, 𝓕, VL, VR, B, fun ω => Sec7.StripSysField.isTranslateAddConst_zero_self (X₀ ω) (chiC κ), hC⟩
  have hX₀ : IsGFFWithBoundaryData P₀ X₀ c.fn c.jumps :=
    Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ c.isPiecewiseConstantBoundaryData ⟨hC.2.1, hC.2.2.1⟩
  have h0 := ae_not_badCode_of_flowLine h13₀ hsw hκ hκ4 hF hfld
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hmap₀ : P₀.map X₀ = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX₀ (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hmap : Q.map X = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | ¬ BadCode κ c (F (c, g))} :=
    ((measurable_const.prodMk (hF.1.comp (measurable_const.prodMk measurable_id))) (measurableSet_badCode κ)).compl
  have hlaw : ∀ᵐ g ∂c.gffLaw, ¬ BadCode κ c (F (c, g)) := by
    rw [← hmap₀, ae_map_iff hX₀.1.aemeasurable hmeas]
    exact h0
  rw [← hmap, ae_map_iff hX.1.aemeasurable hmeas] at hlaw
  exact hlaw

/-! ### A finite lifetime with an unbounded driver -/

/-- **The finite-lifetime tip event of a driver code**: a finite lifetime before which the decoded driver is unbounded
at the rational times (a relative curve reaching the tip at a finite relative capacity has an unbounded driver
there). -/
def BadFin (p : PCode × ℝ≥0∞) : Prop :=
  p.2 ≠ ⊤ ∧ ∀ M : ℕ, ∃ q : ℚ, ((q : ℝ).toNNReal : ℝ≥0∞) < p.2 ∧ (M : ℝ) < |drvDec p (q : ℝ).toNNReal|

/-- `BadFin` is a measurable event of the code. -/
theorem measurableSet_badFin : MeasurableSet {p : PCode × ℝ≥0∞ | BadFin p} := by
  have e : {p : PCode × ℝ≥0∞ | BadFin p} = {p | p.2 ≠ ⊤} ∩ ⋂ M : ℕ, ⋃ q : ℚ,
      ({p : PCode × ℝ≥0∞ | ((q : ℝ).toNNReal : ℝ≥0∞) < p.2} ∩ {p | (M : ℝ) < |drvDec p (q : ℝ).toNNReal|}) := by
    ext p
    simp only [BadFin, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [e]
  exact ((measurable_snd (measurableSet_singleton ⊤)).compl).inter (MeasurableSet.iInter fun M =>
    MeasurableSet.iUnion fun q => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_const (measurable_drvDec _).abs))

/-- **`BadFin` is null for the canonical code of a flow line's field**: the code is good and its decoded driver is the
flow line's driver before the lifetime (the determination clause), which has a left limit at a finite positive lifetime
(Aux. lemma 3, `IsIntegratedSLEEvolution.ae_tendsto_threshold`), so it is bounded before it. -/
theorem ae_not_badFin_of_flowLine {κ : ℝ} (hκ : 0 < κ) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ c.fn c.jumps 0 P X W ζ) :
    ∀ᵐ ω ∂P, ¬ BadFin (F (c, X ω)) := by
  have hfl' := hfl
  obtain ⟨X', 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hm := hF.2.2 c P X W ζ hfl
  have hcont := ae_driver_zero_continuousOn hfl
  filter_upwards [hm, hcont, hC.1.ae_tendsto_threshold hκ] with ω hmω hcω hlimω
  rintro ⟨hfin, hunb⟩
  have hζ : ζ ω ≠ ⊤ := by rw [hmω.1]; exact hfin
  have hgood := isGoodDrvCode_of_driverCodeMatch hmω hcω.2
  have hdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → drvDec (F (c, X ω)) t = W t ω :=
    eqOn_drvDec_of_isStopDrvMatch hgood hcω.2 ⟨hmω.1.le, hmω.2.2⟩
  have hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ w₀ : ℝ, Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) :=
    fun T hT hTζ => by
      obtain ⟨w₀, vL₀, vR₀, hl, -⟩ := hlimω T hT hTζ
      exact ⟨w₀, (continuous_fst.tendsto _).comp hl⟩
  obtain ⟨M, hM⟩ := Sec7.exists_bound_before hcω.2 le_rfl hζ hlim
  obtain ⟨N, hN⟩ := exists_nat_gt M
  obtain ⟨q, hq, hk⟩ := hunb N
  have hqζ : ((q : ℝ).toNNReal : ℝ≥0∞) < ζ ω := by rw [hmω.1]; exact hq
  rw [hdec _ hqζ] at hk
  linarith [hM _ hqζ]

/-- `BadFin` is null under every GFF with the data of a sorted word (the transfer of `ae_not_badFin_of_flowLine`
through Theorem 1.1's coupling, as in `ae_not_badCode_of_isGFF`). -/
theorem ae_not_badFin_of_isGFF {κ : ℝ} (hκ : 0 < κ) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData Q X c.fn c.jumps) :
    ∀ᵐ ω ∂Q, ¬ BadFin (F (c, X ω)) := by
  obtain ⟨Ω₀, mΩ₀, -, P₀, hP₀, 𝓕, W, VL, VR, B, ζ, X₀, hC⟩ :=
    Sec7.StripSysBorel.exists_isOptionalHullCoupling_standardBorel.{0} hκ
      (ρL := flowLineRhoL κ c.fn c.jumps 0 0) (ρR := flowLineRhoR κ c.fn c.jumps 0 0)
      (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  have hfld : IsFlowLineDriver κ c.fn c.jumps 0 P₀ X₀ W ζ :=
    ⟨X₀, 𝓕, VL, VR, B, fun ω => Sec7.StripSysField.isTranslateAddConst_zero_self (X₀ ω) (chiC κ), hC⟩
  have hX₀ : IsGFFWithBoundaryData P₀ X₀ c.fn c.jumps :=
    Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ c.isPiecewiseConstantBoundaryData ⟨hC.2.1, hC.2.2.1⟩
  have h0 := ae_not_badFin_of_flowLine hκ hF hfld
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hmap₀ : P₀.map X₀ = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX₀ (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hmap : Q.map X = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | ¬ BadFin (F (c, g))} :=
    ((hF.1.comp (measurable_const.prodMk measurable_id)) measurableSet_badFin).compl
  have hlaw : ∀ᵐ g ∂c.gffLaw, ¬ BadFin (F (c, g)) := by
    rw [← hmap₀, ae_map_iff hX₀.1.aemeasurable hmeas]
    exact h0
  rw [← hmap, ae_map_iff hX.1.aemeasurable hmeas] at hlaw
  exact hlaw

/-! ### The combined tip event -/

/-- **The tip event of a word and a driver code**: a bad code, `BadCode` (infinite lifetime, the far right points
never swallowed) or `BadFin` (finite lifetime, unbounded driver). -/
def TipCode (κ : ℝ) (b : BoundaryWord) (p : PCode × ℝ≥0∞) : Prop := ¬ IsGoodDrvCode p ∨ BadCode κ b p ∨ BadFin p

theorem measurableSet_tipCode (κ : ℝ) :
    MeasurableSet {x : BoundaryWord × (PCode × ℝ≥0∞) | TipCode κ x.1 x.2} := by
  have e : {x : BoundaryWord × (PCode × ℝ≥0∞) | TipCode κ x.1 x.2} =
      (Prod.snd ⁻¹' {p | IsGoodDrvCode p})ᶜ ∪ ({x | BadCode κ x.1 x.2} ∪ Prod.snd ⁻¹' {p | BadFin p}) := rfl
  rw [e]
  exact (measurable_snd measurableSet_isGoodDrvCode).compl.union
    ((measurableSet_badCode κ).union (measurable_snd measurableSet_badFin))

/-- **The tip event is null under every GFF with the data of a sorted word** (inputs: Theorem 1.3 and
`FlowSwallowStatement` in `Type`). -/
theorem ae_not_tipCode_of_isGFF (h13₀ : Exist.Theorem13Statement.{0}) (hsw : FlowSwallowStatement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData Q X c.fn c.jumps) :
    ∀ᵐ ω ∂Q, ¬ TipCode κ c (F (c, X ω)) := by
  filter_upwards [ae_isGoodDrvCode_of_isGFF hκ hF hc hX, ae_not_badCode_of_isGFF h13₀ hsw hκ hκ4 hF hc hX,
    ae_not_badFin_of_isGFF hκ hF hc hX] with ω h1 h2 h3
  rintro (h | h | h)
  · exact h h1
  · exact h2 h
  · exact h3 h


end InteractingSLE.Theorem14.GW2Rd
