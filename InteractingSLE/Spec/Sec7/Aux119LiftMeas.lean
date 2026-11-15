/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Lift
import InteractingSLE.Spec.Sec7.Lemma71OMeas

/-!
# Aux. lemma 119: the measurable lift

Packet PROVE-STRIPSYS22. Specification §7.4, the end of the proof of Aux. lemma 119 (`source/spec/p385-432.md` L52,
p. 387):

> Finally, the component, its endpoints, the geometric prefixes, and their normalized maps are measurable from the
> incoming labels. Choose the first admissible rational prefixes and a rationally labelled interior normalization point.
> Analytic derivative logarithms are determined by their value at one interior point; the integer needed to make the
> reflected boundary argument zero is obtained as a boundary limit on a countable sequence in its untouched collar.
> These choices give a measurable lift.

For random two-arc frames (`Aux119Lift.IsTwoArcFrame`, no global order of the walls) whose chart values, chart lifts
and pocket memberships are measurable at every fixed point, and whose left wall has measurable coordinates, the
integer of the common lift (`IsTwoArcFrame.exists_isPocketBranch`) is a measurable function
(`exists_measurable_isPocketBranch`). As in PROVE-LEMMA71O's `Lemma71O.pocketBranchStatement`, the integer is read off,
for the chart points `ξ_j = −1/(j + 1)` and the integer own times `j`, from the canonical logarithm `Im log g′` of the
left wall's prefix hull `fill β([0, j])` at measurably selected pocket points approaching `ξ_j` in the chart
(`Lemma71O.exists_measurable_chart_approach`): the pins `Im log g′ − lift` tend to `2πn` (a double `limsup`, then the
nearest integer). The countable sequence and the integer times replace the source's "first admissible rational
prefixes".

## Main results

* **`exists_measurable_isPocketBranch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux119Lift

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open Lemma71O (land)
open Lemma71N (IsPocketBranch)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Aux. lemma 119's measurable lift**: on a family of two-arc frames over a measurable set `G` of realizations,
with measurable pocket memberships, chart values and chart lifts at every fixed point, a left wall with measurable
coordinates, and a logarithm of the chart derivative whose imaginary part is the lift, the integer of the common lift
is a measurable function of the realization. -/
theorem exists_measurable_isPocketBranch {β α : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hconf : ∀ ω, (c ω).IsConformal) (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω)
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω})
    (hfm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hlm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) {G : Set Ω}
    (hG : ∀ ω ∈ G, (∃ sa ta q₁ q₂ : ℝ≥0, IsTwoArcFrame (β ω) (α ω) (C ω) (c ω) sa ta q₁ q₂) ∧
      ∃ ℓ : ℂ → ℂ, IsDerivLog (c ω).1 ℓ (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (ℓ z).im) :
    ∃ n : Ω → ℤ, Measurable n ∧ ∀ ω ∈ G, IsPocketBranch (β ω) (α ω) (c ω) (n ω) := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set ξ : ℕ → ℝ := fun j => -(1 / ((j : ℝ) + 1)) with hξdef
  have hN := fun j => Lemma71O.exists_measurable_chart_approach hconf hdom hCm hfm he (ξ j)
  choose N hNm hNC hNt using hN
  set K : ℕ → Ω → Set ℂ := fun j ω => β ω '' Icc 0 (j : ℝ≥0) with hKdef
  have hKm : ∀ j, Restart.IsDyadicHitMeasurable (K j) := fun j =>
    Lemma71O.isDyadicHitMeasurable_image_Icc hβc hβm j
  have hKc : ∀ j ω, IsCompact (K j ω) := fun j ω => isCompact_Icc.image (hβc ω)
  have hKp : ∀ j ω, IsPreconnected (K j ω ∪ Restart.lowerHalf) := fun j ω =>
    Restart.isPreconnected_image_union_lowerHalf (hβc ω).continuousOn (by rw [hβ0 ω]; simp)
  set F : ℕ → ℕ → Ω → ℂ := fun j i => {ω | e i ∈ H \ fillH (K j ω)}.indicator fun ω =>
    Restart.canonDerivLog (fillH (K j ω)) (e i) with hFdef
  have hFm : ∀ j i, Measurable (F j i) := fun j i =>
    Restart.measurable_indicator_canonDerivLog (hKm j) (hKc j) (hKp j) (e i)
  set X : ℕ → ℕ → Ω → ℝ := fun j k ω => (F j (N j k ω) ω).im - (c ω).2.2 (e (N j k ω)) with hXdef
  have hXm : ∀ j k, Measurable (X j k) := by
    intro j k
    have h1 := Lemma71O.measurable_comp_index (hFm j) (hNm j k)
    have h2 := Lemma71E.measurable_at_seq (C := fun ω => ((c ω).dom : Set ℂ)) (f := fun ω z => (c ω).2.2 z) (e := e)
      (hNm j k) (fun ω => by rw [hdom]; exact hNC j k ω) hlm
    exact (Complex.measurable_im.comp h1).sub h2
  set Y : ℕ → Ω → ℝ := fun j ω => limsup (fun k => X j k ω) atTop with hYdef
  set Z : Ω → ℝ := fun ω => limsup (fun j => Y j ω) atTop with hZdef
  refine ⟨fun ω => ⌊Z ω / (2 * π) + 1 / 2⌋, Lemma71O.measurable_floor_limsup_limsup hXm (2 * π), ?_⟩
  intro ω hω
  obtain ⟨⟨sa, ta, q₁, q₂, hF⟩, ℓ, hℓd, hℓl⟩ := hG ω hω
  obtain ⟨n₀, hn₀⟩ := hF.exists_isPocketBranch hℓd hℓl
  by_cases hex : ∃ Wβ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ (β ω) ∧ IsGeneratingTrace Wα ⊤ (α ω)
  swap
  · exact fun Wβ Wα h₁ h₂ => absurd ⟨Wβ, Wα, h₁, h₂⟩ hex
  obtain ⟨Wβ, Wα, htrβ, htrα⟩ := hex
  have hWβ := Lemma71O.continuous_of_isGeneratingTrace_top htrβ
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  set Q₀ : ℕ := ⌈(sa : ℝ)⌉₊ + 1 with hQ₀
  have hsaQ₀ : sa < (Q₀ : ℝ≥0) := by
    have h1 : (sa : ℝ) ≤ ⌈(sa : ℝ)⌉₊ := Nat.le_ceil _
    have h2 : (sa : ℝ) < (Q₀ : ℝ) := by rw [hQ₀]; push_cast; linarith
    exact_mod_cast h2
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hF.left hsaQ₀
  have hξt : Tendsto ξ atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) atTop (𝓝 (-(0 : ℝ))) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    rw [neg_zero] at this
    exact this
  have hlt : Tendsto (fun j => land (c ω) (ξ j)) atTop (𝓝 (land (c ω) 0)) := by
    have := ((hF.continuous_land_ofReal).tendsto 0).comp hξt
    rw [Complex.ofReal_zero] at this
    exact this
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlt (ball_mem_nhds _ hρ))
  have hY : ∀ j ≥ max J Q₀, Y j ω = 2 * π * n₀ := by
    intro j hj
    have hξj : ξ j < 0 := by simp only [hξdef, Left.neg_neg_iff]; positivity
    obtain ⟨s, -, hs⟩ := hF.neg (ξ j) hξj
    have hsQ : s < (j : ℝ≥0) := by
      have hsQ₀ : s < (Q₀ : ℝ≥0) := by
        by_contra hle
        refine hball s (not_lt.1 hle) ?_
        rw [← hs, ← hF.zero_left]
        exact hJ j (le_of_max_le_left hj)
      exact hsQ₀.trans_le (by exact_mod_cast le_of_max_le_right hj)
    have hland : Tendsto (c ω).2.1 (𝓝[H] (ξ j : ℂ)) (𝓝 (β ω s)) :=
      hs ▸ hF.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
    have hbr := (hn₀ Wβ Wα htrβ htrα (ξ j) s j hsQ).1 hξj hland
    have hcomp := hbr.comp (hNt j ω)
    have hinv : ∀ k, (c ω).2.1 ((c ω).1 (e (N j k ω))) = e (N j k ω) := fun k =>
      (hconf ω).inv_fwd (by rw [← SetLike.mem_coe, hdom]; exact hNC j k ω)
    have hX : ∀ k, X j k ω = (logDerivFwd (fun r : ℝ => Wβ r.toNNReal) ((j : ℝ≥0) : ℝ) (e (N j k ω))).im -
        (c ω).2.2 (e (N j k ω)) := by
      intro k
      have hzK : e (N j k ω) ∈ H \ fillH (K j ω) :=
        Lemma71O.dom_subset_H_diff_fillH htrβ (hdom ω) (hF.subset_H_diff_fwdHull_left htrβ) j
          (by rw [hdom]; exact hNC j k ω)
      simp only [hXdef, hFdef]
      rw [indicator_of_mem (show ω ∈ {ω' | e (N j k ω) ∈ H \ fillH (K j ω')} from hzK),
        Lemma71O.canonDerivLog_eqOn_logDerivFwd htrβ hWβ hWβ0 j hzK]
    have hXt : Tendsto (fun k => X j k ω) atTop (𝓝 (2 * π * n₀)) := by
      have h' := (tendsto_const_nhds (x := 2 * π * (n₀ : ℝ))).sub hcomp
      rw [sub_zero] at h'
      refine h'.congr fun k => ?_
      simp only [Function.comp_apply, hinv, hX]
      ring
    exact hXt.limsup_eq
  have hZ : Z ω = 2 * π * n₀ := by
    show limsup (fun j => Y j ω) atTop = _
    rw [limsup_congr (eventually_atTop.2 ⟨max J Q₀, hY⟩), limsup_const]
  have hfl : ⌊Z ω / (2 * π) + 1 / 2⌋ = n₀ := by
    rw [hZ, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0), Int.floor_eq_iff]
    constructor <;> linarith
  show IsPocketBranch (β ω) (α ω) (c ω) ⌊Z ω / (2 * π) + 1 / 2⌋
  rw [hfl]
  exact hn₀

end InteractingSLE.Sec7.Aux119Lift
