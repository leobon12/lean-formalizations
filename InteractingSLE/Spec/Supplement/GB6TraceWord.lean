/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Trace
import InteractingSLE.Spec.Supplement.GB6Meas
import InteractingSLE.Spec.ZhanGT4.WordsRef

/-!
# Proposition GB6: the conditional counterflow word — lifetime and protected tails from its data

Packet PROVE-GB6D. The conditional counterflow of GB6 is the flow line from `0` (angle `0`) at `k = 16/κ` of a field
with boundary word `c`. Its force word's cumulative weights are read off the data of `c`
(`Sec4.forceBoundaryData_flowLine`: `Λ(1 + S)` on the right, `−Λ(1 + S)` on the left), at a nearby non-jump point
(`exists_sumR_eq`, `exists_sumL_eq`). Hence:

* **`ae_lifetime_eq_top_of_admData`**: an admissible word (`IsGB6AdmData`, every cumulative weight `> −2`) has infinite
  lifetime (the continuation threshold never occurs:
  `ZhanGT4.IsIntegratedSLEEvolution.ae_lifetime_eq_top_of_groupEndSums`
  with the least group-end sum, `exists_hasGroupEndSums`);
* **`ae_trace_ne_of_ge_word`**, **`ae_trace_ne_of_le_word`**: beyond a point where the data is at least `Λ(1 + c)`
  (resp. at most `−Λ(1 + c)`), `c = k/2 − 2`, the trace never visits the closed tail (GB5, `GB6Trace.lean`);
* `ae_forall_of_upClosed`: almost surely simultaneously for every threshold of an upward closed set of thresholds
  (rationals and the infimum).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec4

variable {κ : ℝ}

/-! ### Cumulative weights of the counterflow word from its data -/

/-- The right cumulative weight of the counterflow word of `c` at `x ≥ 0` is `c(x′)/Λ − 1` at a non-jump `x′ > x`. -/
theorem exists_sumR_eq (hκ : 0 < κ) (c : BoundaryWord) {x : ℝ} (hx : 0 ≤ x) :
    ∃ x', x < x' ∧ x' ∉ c.jumps ∧
      ∑ i ∈ univ.filter (fun i => flowLineXR c.fn c.jumps 0 i ≤ x), flowLineRhoR (16 / κ) c.fn c.jumps 0 0 i =
        c.fn x' / bigLambda κ - 1 := by
  have hk : 0 < 16 / κ := by positivity
  obtain ⟨x', h1, hE, hS⟩ := exists_right_prefix_eq (flowLineXR c.fn c.jumps 0) (insert 0 c.jumps) x
  have hx'0 : x' ≠ 0 := (hx.trans_lt h1).ne'
  have hx'J : x' ∉ c.jumps := fun h => hE (Finset.mem_insert_of_mem h)
  refine ⟨x', h1, hx'J, ?_⟩
  rw [← hS, ← cumWeightRight_forceBoundaryData hk _ _ _ _ (hx.trans h1.le),
    forceBoundaryData_flowLine hk c.isPiecewiseConstantBoundaryData hx'0 hx'J]
  rfl

/-- The left cumulative weight `Σ_{x ≤ x_L} ρ_L` of the counterflow word of `c` at `x ≤ 0` is `−c(x′)/Λ − 1` at a
non-jump `x′ < x`. -/
theorem exists_sumL_eq (hκ : 0 < κ) (c : BoundaryWord) {x : ℝ} (hx : x ≤ 0) :
    ∃ x', x' < x ∧ x' ∉ c.jumps ∧
      ∑ i ∈ univ.filter (fun i => x ≤ flowLineXL c.fn c.jumps 0 i), flowLineRhoL (16 / κ) c.fn c.jumps 0 0 i =
        -c.fn x' / bigLambda κ - 1 := by
  have hk : 0 < 16 / κ := by positivity
  set xL := flowLineXL c.fn c.jumps 0 with hxLdef
  set E : Finset ℝ := (insert 0 c.jumps).image (fun z => -z) ∪ univ.image (fun i => -xL i) with hEdef
  obtain ⟨y, h1, hE, hS⟩ := exists_right_prefix_eq (fun i => -xL i) E (-x)
  have hy0 : -y < 0 := by linarith
  have hyJ : -y ∉ c.jumps := fun h => hE (Finset.mem_union_left _ (Finset.mem_image.2
    ⟨-y, Finset.mem_insert_of_mem h, by ring⟩))
  have hymark : ∀ i, xL i ≠ -y := fun i h => hE (Finset.mem_union_right _ (Finset.mem_image.2
    ⟨i, Finset.mem_univ _, by rw [h]; ring⟩))
  refine ⟨-y, by linarith, hyJ, ?_⟩
  have hf : univ.filter (fun i => x ≤ xL i) = univ.filter (fun i => -y < xL i) := by
    have e1 : univ.filter (fun i => x ≤ xL i) = univ.filter (fun i => -xL i ≤ -x) :=
      Finset.filter_congr fun i _ => by constructor <;> intro h <;> linarith
    have e2 : univ.filter (fun i => -xL i ≤ y) = univ.filter (fun i => -y < xL i) :=
      Finset.filter_congr fun i _ => ⟨fun h => lt_of_le_of_ne (by linarith) (hymark i).symm, fun h => by linarith⟩
    rw [e1, ← hS, e2]
  rw [hf, ← cumWeightLeft_forceBoundaryData hk _ _ _ _ hy0,
    forceBoundaryData_flowLine hk c.isPiecewiseConstantBoundaryData hy0.ne hyJ]
  rfl

/-! ### Admissible words have infinite lifetime -/

/-- A least group-end sum: if every group-end sum exceeds `−2`, some `m > −2` bounds all of them below. -/
theorem exists_hasGroupEndSums {n : ℕ} {ρ x : Fin n → ℝ}
    (h : ∀ j : Fin n, (∀ i, j < i → x j < x i) → -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i) :
    ∃ m, -2 < m ∧ HasGroupEndSums m ρ x := by
  classical
  set f : Fin n → ℝ := fun j => if (∀ i, j < i → x j < x i) then ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i else -1
  set T : Finset ℝ := insert (-1) (univ.image f)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, ?_, fun j hj => ?_⟩
  · obtain ⟨v, hv, hvm⟩ := T.exists_min_image id hT
    have : T.min' hT = v := le_antisymm (T.min'_le v hv) (T.le_min' hT v fun q hq => hvm q hq)
    rw [this]
    rcases Finset.mem_insert.1 hv with rfl | hv
    · norm_num
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      simp only [f]
      split_ifs with hj
      · exact h j hj
      · norm_num
  · have hfj : f j = ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i := ite_eq_left_of_eq_true _ _ (eq_true hj)
    rw [← hfj]
    exact T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ j)))

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {c : BoundaryWord}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **An admissible conditional word has infinite lifetime.** -/
theorem ae_lifetime_eq_top_of_admData (hκ : 0 < κ) (hadm : IsGB6AdmData κ c)
    (hE : IsIntegratedSLEEvolution (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hΛ : 0 < bigLambda κ := bigLambda_pos hκ
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  obtain ⟨mR, hmR, hR⟩ := exists_hasGroupEndSums (ρ := flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
    (x := flowLineXR c.fn c.jumps 0) fun j hend => by
      rw [filter_le_eq_filter_xR_le hF.2.2.1 hend]
      obtain ⟨x', h1, hJ, hS⟩ := exists_sumR_eq hκ c (hF.2.2.2 j)
      rw [hS]
      have := hadm.1 x' (lt_of_le_of_lt (hF.2.2.2 j) h1) hJ
      have h2 : -1 < c.fn x' / bigLambda κ := by rw [lt_div_iff₀ hΛ]; linarith
      linarith
  have hmonoL : Monotone fun i => -flowLineXL c.fn c.jumps 0 i := fun i j hij => neg_le_neg (hF.1 hij)
  obtain ⟨mL, hmL, hL⟩ := exists_hasGroupEndSums (ρ := flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
    (x := fun i => -flowLineXL c.fn c.jumps 0 i) fun j hend => by
      rw [filter_le_eq_filter_xR_le hmonoL hend]
      have e : univ.filter (fun l => -flowLineXL c.fn c.jumps 0 l ≤ -flowLineXL c.fn c.jumps 0 j) =
          univ.filter (fun l => flowLineXL c.fn c.jumps 0 j ≤ flowLineXL c.fn c.jumps 0 l) :=
        Finset.filter_congr fun l _ => neg_le_neg_iff
      rw [e]
      obtain ⟨x', h1, hJ, hS⟩ := exists_sumL_eq hκ c (hF.2.1 j)
      rw [hS]
      have := hadm.2 x' (lt_of_lt_of_le h1 (hF.2.1 j)) hJ
      have h2 : -1 < -c.fn x' / bigLambda κ := by rw [lt_div_iff₀ hΛ]; linarith
      linarith
  obtain ⟨m, hm, hmL', hmR'⟩ : ∃ m, -2 < m ∧ m ≤ mL ∧ m ≤ mR := ⟨min mL mR, lt_min hmL hmR, min_le_left _ _,
    min_le_right _ _⟩
  exact ZhanGT4.IsIntegratedSLEEvolution.ae_lifetime_eq_top_of_groupEndSums hm hF
    (fun j hj => hmL'.trans (hL j hj)) (fun j hj => hmR'.trans (hR j hj)) hE

/-- **The right protected tail of the conditional word is never visited** (word form of `ae_trace_ne_of_ge`). -/
theorem ae_trace_ne_of_ge_word [IsProbabilityMeasure P] (hκ : 0 < κ) (hadm : IsGB6AdmData κ c) {p : ℝ}
    (hp : 0 < p) (htail : ∀ y, p < y → y ∉ c.jumps → tailLevel κ ≤ c.fn y)
    (hE : IsIntegratedSLEEvolution (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ y : ℝ, p ≤ y → η ω t ≠ y := by
  have hk : 0 < 16 / κ := by positivity
  have hΛ : 0 < bigLambda κ := bigLambda_pos hκ
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  refine ae_trace_ne_of_ge hk hF hE hζ hη hp ⟨_, by rw [flowLineXR_zero]; exact hp⟩ (fun x hx => ?_)
    (fun x hx => ?_)
  · rcases lt_or_ge x 0 with hx0 | hx0
    · have e : univ.filter (fun i => flowLineXR c.fn c.jumps 0 i ≤ x) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun i _ => not_le.2 (hx0.trans_le (hF.2.2.2 i))
      rw [e, Finset.sum_empty]; norm_num
    · obtain ⟨x', h1, hJ, hS⟩ := exists_sumR_eq hκ c hx0
      rw [hS]
      have := hadm.1 x' (lt_of_le_of_lt hx0 h1) hJ
      have h2 : -1 < c.fn x' / bigLambda κ := by rw [lt_div_iff₀ hΛ]; linarith
      linarith
  · obtain ⟨x', h1, hJ, hS⟩ := exists_sumR_eq hκ c (hp.le.trans hx)
    rw [hS]
    have h3 := htail x' (lt_of_le_of_lt hx h1) hJ
    have h4 : protLevel κ + 1 ≤ c.fn x' / bigLambda κ := by
      rw [le_div_iff₀ hΛ]; unfold tailLevel at h3; linarith
    have e : protLevel κ = 16 / κ / 2 - 2 := rfl
    linarith

/-- **The left protected tail of the conditional word is never visited** (word form of `ae_trace_ne_of_le`). -/
theorem ae_trace_ne_of_le_word [IsProbabilityMeasure P] (hκ : 0 < κ) (hadm : IsGB6AdmData κ c) {p : ℝ}
    (hp : p < 0) (htail : ∀ y, y < p → y ∉ c.jumps → c.fn y ≤ -tailLevel κ)
    (hE : IsIntegratedSLEEvolution (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ y : ℝ, y ≤ p → η ω t ≠ y := by
  have hk : 0 < 16 / κ := by positivity
  have hΛ : 0 < bigLambda κ := bigLambda_pos hκ
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  refine ae_trace_ne_of_le hk hF hE hζ hη hp ⟨_, by rw [flowLineXL_zero]; exact hp⟩ (fun x hx => ?_)
    (fun x hx => ?_)
  · rcases lt_or_ge 0 x with hx0 | hx0
    · have e : univ.filter (fun i => x ≤ flowLineXL c.fn c.jumps 0 i) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun i _ => not_le.2 ((hF.2.1 i).trans_lt hx0)
      rw [e, Finset.sum_empty]; norm_num
    · obtain ⟨x', h1, hJ, hS⟩ := exists_sumL_eq hκ c hx0
      rw [hS]
      have := hadm.2 x' (lt_of_lt_of_le h1 hx0) hJ
      have h2 : -1 < -c.fn x' / bigLambda κ := by rw [lt_div_iff₀ hΛ]; linarith
      linarith
  · obtain ⟨x', h1, hJ, hS⟩ := exists_sumL_eq hκ c (hx.trans hp.le)
    rw [hS]
    have h3 := htail x' (lt_of_lt_of_le h1 hx) hJ
    have h4 : protLevel κ + 1 ≤ -c.fn x' / bigLambda κ := by
      rw [le_div_iff₀ hΛ]; unfold tailLevel at h3; linarith
    have e : protLevel κ = 16 / κ / 2 - 2 := rfl
    linarith

end Evolution

/-! ### Simultaneously for all thresholds -/

/-- **Almost surely for every threshold of an upward closed set of positive thresholds**, from almost surely for each:
the rational thresholds and the infimum are countably many, and every other threshold lies above one of them. -/
theorem ae_forall_of_upClosed {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {U : Set ℝ}
    (hU0 : ∀ p ∈ U, 0 < p) (hUup : ∀ p ∈ U, ∀ p', p ≤ p' → p' ∈ U) {A : ℝ → Ω → Prop}
    (hA : ∀ p ∈ U, ∀ᵐ ω ∂Q, A p ω) (hmono : ∀ p p' ω, p ≤ p' → A p ω → A p' ω) :
    ∀ᵐ ω ∂Q, ∀ p ∈ U, A p ω := by
  classical
  have hq : ∀ᵐ ω ∂Q, ∀ q : ℚ, (q : ℝ) ∈ U → A q ω := by
    rw [ae_all_iff]
    intro q
    by_cases hqU : (q : ℝ) ∈ U
    · filter_upwards [hA q hqU] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hqU
  have hm : ∀ᵐ ω ∂Q, sInf U ∈ U → A (sInf U) ω := by
    by_cases hmU : sInf U ∈ U
    · filter_upwards [hA _ hmU] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hmU
  filter_upwards [hq, hm] with ω hqω hmω p hp
  have hbdd : BddBelow U := ⟨0, fun p hp => (hU0 p hp).le⟩
  rcases (csInf_le hbdd hp).lt_or_eq with hlt | heq
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt ⟨p, hp⟩ hq1
    exact hmono q p ω hq2.le (hqω q (hUup u huU q hu.le))
  · rw [heq] at hmω
    exact hmω hp

end GB6

end Supp8

end InteractingSLE
