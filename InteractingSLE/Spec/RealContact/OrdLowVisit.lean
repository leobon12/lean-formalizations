/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemPassiveWord
import InteractingSLE.Spec.Supplement.G12RemSwallow
import InteractingSLE.Spec.Sec7.FlowReflectFlow

/-!
# A real point of cumulative weight `≤ −2` is visited only at the lifetime

Packet PROVE-RC-ORD (ruling R124 (b), the seed case). Lemma G12 (`Supp7.g12FlowStatement`) excludes every visit of a
fixed real point whose outward cumulative weight exceeds `κ/2 − 4`. The complementary fact used for the seeds of
Theorem 1.5 (i) at critical angles: a fixed real point whose cumulative weight is `≤ −2` (in particular `≤ κ/2 − 4`,
as `κ < 4`) can be visited only at the continuation threshold, hence not strictly before the lifetime.

Proof (pathwise, one path of the integrated evolution with its generating trace). At the first visit `t₀ < ζ` of a
right mark `y = x_{j₀} > 0`:
* the gap `V^{j₀} − W` is positive before `t₀` (a mark swallowed off the prefix is never visited,
  `Supp7.G12.trace_ne_of_gap_eq_zero`), so it tends to `0` at `t₀⁻` (`Supp7.G12.tendsto_gap_eq_zero_of_visit`), and
  by continuity at `t₀ < ζ` it vanishes at `t₀`;
* every farther right mark has a positive gap limit at `t₀⁻` (`Supp7.G12.tendsto_gap_pos_of_visit`), hence a positive
  gap at `t₀`;
* so the marks meeting the driver at `t₀` are exactly the marks `x_i ≤ y`, whose weights sum to `≤ −2`: the threshold
  condition holds at `t₀ < ζ`, which the integrated path excludes.

A passive point is first made a zero-weight mark (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`); a left point
is handled by the reflection `R(z) = −z̄` of the flow line (`Sec7.FlowReflect.IsFlowLine.reflect`).

## Main results

* `OrdLow.trace_ne_of_mark_low` (pathwise), `OrdLow.ae_trace_ne_of_mark_low`, `OrdLow.ae_trace_ne_of_passive_low`;
* `OrdLow.ae_ne_of_cumWeightRight_le`, `OrdLow.ae_ne_of_cumWeightLeft_le`: for the angle-`θ` flow line from `x` and a
  real point `y ≠ x` whose outward cumulative weight is `≤ −2`, almost surely `η t ≠ y` for every `t < ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RealContact

namespace OrdLow

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A right mark of cumulative weight `≤ −2` is not visited before the lifetime** (pathwise). For one path of an
integrated `SLE(ρ)` evolution (its force part) of an ordered word with a continuous generating trace `η`, if
`Σ_{x_i ≤ x_{j₀}} ρ_i ≤ −2` for a right mark `x_{j₀} > 0`, then `η t ≠ x_{j₀}` for every `t < ζ`. -/
theorem trace_ne_of_mark_low {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {η : ℝ≥0 → ℂ} (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hη : IsGeneratingTrace w ζ η) {j₀ : Fin nR} (hy : 0 < xR j₀)
    (hS : ∑ i ∈ univ.filter (fun i => xR i ≤ xR j₀), ρR i ≤ -2) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → η t ≠ xR j₀ := by
  intro t₁ ht₁ he₁
  -- the first visit `t₀ ≤ t₁`
  set Sv : Set ℝ≥0 := {t | (t : ℝ≥0∞) ≤ ζ} ∩ η ⁻¹' {(xR j₀ : ℂ)} with hSv
  have hζc : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := isClosed_le ENNReal.continuous_coe continuous_const
  have hSc : IsClosed Sv := hη.2.1.preimage_isClosed_of_isClosed hζc isClosed_singleton
  have hSne : Sv.Nonempty := ⟨t₁, ht₁.le, he₁⟩
  set t₀ := sInf Sv with ht₀def
  have ht₀S : t₀ ∈ Sv := hSc.csInf_mem hSne (OrderBot.bddBelow Sv)
  have ht₀t₁ : t₀ ≤ t₁ := csInf_le (OrderBot.bddBelow Sv) ⟨ht₁.le, he₁⟩
  have ht₀ζ : (t₀ : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 ht₀t₁).trans_lt ht₁
  have hvis : η t₀ = xR j₀ := ht₀S.2
  have hfirst : ∀ s < t₀, η s ≠ xR j₀ := fun s hs he =>
    absurd (csInf_le (OrderBot.bddBelow Sv) ⟨(ENNReal.coe_le_coe.2 hs.le).trans ht₀ζ.le, he⟩) (not_le.2 hs)
  have hltζ : ∀ s : ℝ≥0, s < t₀ → (s : ℝ≥0∞) < ζ := fun s hs => (ENNReal.coe_lt_coe.2 hs).trans ht₀ζ
  have ht₀0 : 0 < t₀ := pos_iff_ne_zero.2 fun h0 => by
    rw [h0, hη.1] at hvis
    exact hy.ne (by exact_mod_cast hvis)
  -- the mark is alive before `t₀`
  have hlife : ∀ t < t₀, w t < vR j₀ t := by
    intro s hs
    refine lt_of_le_of_ne (h.w_le_vR (hltζ s hs) j₀) fun he => ?_
    exact Supp7.G12.trace_ne_of_gap_eq_zero h hη hy (hltζ s hs) he.symm
      (fun s' hs' => hfirst s' (lt_of_le_of_lt hs' hs)) t₀ ht₀ζ.le hvis
  -- a continuous driver agreeing with `w` up to `t₀`
  obtain ⟨t₂, ht₀t₂, ht₂ζ⟩ := Supp7.G11.exists_real_gt_lt ht₀ζ
  set U : ℝ → ℝ := frozenDrive w t₂ with hUdef
  have hU : Continuous U := continuous_frozenDrive_of_lt h.continuousOn_w ht₂ζ
  have hUw : ∀ s : ℝ, 0 ≤ s → s < t₀ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le.trans ht₀t₂.le⟩
  have hU0 : U 0 = 0 := by rw [hUw 0 le_rfl (NNReal.coe_pos.2 ht₀0)]; simpa using h.w_zero
  -- the gaps are continuous at `t₀ < ζ`
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hgap : ∀ j, Tendsto (fun t => vR j t - w t) (𝓝[<] t₀) (𝓝 (vR j t₀ - w t₀)) := fun j =>
    (((h.continuousOn_vR j).sub h.continuousOn_w).continuousAt (hopen.mem_nhds ht₀ζ)).tendsto.mono_left
      nhdsWithin_le_nhds
  have h0 : vR j₀ t₀ - w t₀ = 0 :=
    Supp7.G12.tendsto_gap_eq_zero_of_visit h hη hy ht₀0 ht₀ζ.le hvis hlife hU hU0 hUw (hgap j₀)
  have hpos : ∀ k, xR j₀ < xR k → 0 < vR k t₀ - w t₀ := fun k hk =>
    Supp7.G12.tendsto_gap_pos_of_visit h hord hη hk ht₀0 ht₀ζ.le hvis hlife hU hU0 hUw (hgap k)
  -- the marks meeting the driver at `t₀` are exactly those up to `y`
  have hcol : univ.filter (fun j => vR j t₀ = w t₀) = univ.filter (fun j => xR j ≤ xR j₀) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hjy
      have hp := hpos j (not_le.1 hjy)
      rw [hj, sub_self] at hp
      exact lt_irrefl _ hp
    · intro hj
      have hle : vR j t₀ ≤ vR j₀ t₀ := by
        rcases hj.lt_or_eq with hlt | heq
        · exact h.monotone_vR ht₀ζ (not_lt.1 fun hji => absurd hlt (not_lt.2 (hord.2.2.1 hji.le)))
        · exact (Supp7.G12.eq_of_forceEq_right h heq ht₀ζ).le
      have hw : vR j₀ t₀ = w t₀ := sub_eq_zero.1 h0
      exact le_antisymm (hle.trans hw.le) (h.w_le_vR ht₀ζ j)
  apply h.not_threshold ht₀ζ
  right
  show ∑ i ∈ univ.filter (fun i => vR i t₀ = w t₀), ρR i ≤ -2
  rw [hcol]
  exact hS

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **A right mark of cumulative weight `≤ −2` is almost surely not visited before the lifetime.** -/
theorem ae_trace_ne_of_mark_low (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {j₀ : Fin nR} (hy : 0 < xR j₀)
    (hS : ∑ i ∈ univ.filter (fun i => xR i ≤ xR j₀), ρR i ≤ -2) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ xR j₀ := by
  filter_upwards [hE.2.2.2.2, hη] with ω hp hηω
  exact trace_ne_of_mark_low hp.isForcePath hord hηω hy hS

/-- **A passive right point of cumulative weight `≤ −2` is almost surely not visited before the lifetime**: the
point `y > 0`, not a right mark, with a right mark below it and `Σ_{x_k < y} ρ_k ≤ −2`. It is made a zero-weight mark
of the extended evolution (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`), which has the same driver and
lifetime and the same cumulative weight up to `y`. -/
theorem ae_trace_ne_of_passive_low (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : 0 < y)
    (hny : ∀ j, xR j ≠ y) (hex : ∃ j, xR j < y)
    (hS : ∑ k ∈ Finset.univ.filter (fun k => xR k < y), ρR k ≤ -2) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ y := by
  obtain ⟨j₁, hj₁⟩ := hex
  have hne : (Finset.univ.filter (fun j => xR j < y)).Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨mem_univ _, hj₁⟩⟩
  set k := (Finset.univ.filter (fun j => xR j < y)).max' hne with hkdef
  have hk : xR k < y := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  have hky : ∀ j, xR j < y → j ≤ k := fun j hj =>
    Finset.le_max' _ j (Finset.mem_filter.2 ⟨mem_univ _, hj⟩)
  set p : Fin (nR + 1) := k.succ with hpdef
  have hE' := Supp7.G12.isIntegratedSLEEvolution_insertPassive hE hord hy hk hky
  have hb : ∀ j : Fin nR, j.castSucc < p → xR j ≤ y := fun j hj => by
    rw [hpdef, Fin.castSucc_lt_succ_iff] at hj
    exact (hord.2.2.1 hj).trans hk.le
  have ha : ∀ j : Fin nR, p ≤ j.castSucc → y ≤ xR j := fun j hj => by
    have hkj : k < j := by
      rw [hpdef] at hj
      by_contra hjk; rw [not_lt] at hjk
      exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 hjk))
    by_contra hlt; rw [not_le] at hlt
    exact absurd (hky j hlt) (not_le.2 hkj)
  have hmono := Supp7.G12.monotone_insertNth hord.2.2.1 p hb ha
  have hord' : IsOrderedForceWord xL (Fin.insertNth (α := fun _ => ℝ) p y xR) := by
    refine ⟨hord.1, hord.2.1, hmono, fun i => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hy.le
    · simp only [Fin.insertNth_apply_succAbove]; exact hord.2.2.2 j
  have hyp : Fin.insertNth (α := fun _ => ℝ) p y xR p = y := Fin.insertNth_apply_same _ _ _
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => xR j ≤ y), ρR j =
      ∑ j ∈ Finset.univ.filter (fun j => xR j < y), ρR j :=
    Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => lt_of_le_of_ne h (hny j), le_of_lt⟩) fun _ _ => rfl
  have h3 : ∑ i ∈ Finset.univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ) p y xR i ≤ y),
      Fin.insertNth (α := fun _ => ℝ) p 0 ρR i =
      ∑ j ∈ Finset.univ.filter (fun j => xR j ≤ y), ρR j := by
    rw [Finset.sum_filter, Finset.sum_filter, Supp7.G12.sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  have h := ae_trace_ne_of_mark_low (j₀ := p) hord' hE' hη (by rw [hyp]; exact hy)
    (by rw [hyp, h3, h2]; exact hS)
  rw [hyp] at h
  exact h

end Evolution

/-! ### Flow lines -/

open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- **Right points of cumulative weight `≤ −2` are not visited before the lifetime.** For the angle-`θ` flow line
from `x` and a real point `y > x` with `(b(y⁺) + θχ)/λ − 1 ≤ −2`, almost surely `η t ≠ y` for every `t < ζ`. -/
theorem ae_ne_of_cumWeightRight_le {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ y : ℝ} (hxy : x < y)
    (hS : Sec4.cumWeightRight κ (rightLim b y + θ * QuantumZipper.chiC κ) ≤ -2)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ y := by
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hη
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  have hsum := Supp7.sum_filter_flowLineXR_le hκ hb θ hxy
  have key : ∀ ω t, η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t he => by
    rw [he]; push_cast; ring
  have hyx : 0 < y - x := sub_pos.2 hxy
  by_cases hm : ∃ j, flowLineXR b jumps x j = y - x
  · obtain ⟨j₀, hj₀⟩ := hm
    have hS' : ∑ i ∈ univ.filter (fun i => flowLineXR b jumps x i ≤ flowLineXR b jumps x j₀),
        flowLineRhoR κ b jumps x θ i ≤ -2 := by
      rw [hj₀, hsum]; exact hS
    filter_upwards [ae_trace_ne_of_mark_low hord hcpl.1 htr (hj₀ ▸ hyx) hS'] with ω hω t ht he
    exact hω t ht (by rw [key ω t he, hj₀])
  · push Not at hm
    have hex : ∃ j, flowLineXR b jumps x j < y - x := by
      refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      have h0 : flowLineXR b jumps x ⟨0, Nat.succ_pos _⟩ = 0 := Fin.cons_zero _ _
      rw [h0]; exact hyx
    have h2 : ∑ k ∈ univ.filter (fun k => flowLineXR b jumps x k < y - x), flowLineRhoR κ b jumps x θ k =
        ∑ k ∈ univ.filter (fun k => flowLineXR b jumps x k ≤ y - x), flowLineRhoR κ b jumps x θ k :=
      Finset.sum_congr (Finset.filter_congr fun j _ => ⟨le_of_lt, fun h => lt_of_le_of_ne h (hm j)⟩)
        fun _ _ => rfl
    filter_upwards [ae_trace_ne_of_passive_low hord hcpl.1 htr hyx hm hex (by rw [h2, hsum]; exact hS)]
      with ω hω t ht he
    exact hω t ht (key ω t he)

/-- **Left points of cumulative weight `≤ −2` are not visited before the lifetime**, the reflection of
`ae_ne_of_cumWeightRight_le`: for the angle-`θ` flow line from `x` and a real point `y < x` with
`−(b(y⁻) + θχ)/λ − 1 ≤ −2`, almost surely `η t ≠ y` for every `t < ζ`. -/
theorem ae_ne_of_cumWeightLeft_le {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ y : ℝ} (hyx : y < x)
    (hS : Sec4.cumWeightLeft κ (leftLim b y + θ * QuantumZipper.chiC κ) ≤ -2)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ y := by
  have hR := Sec7.FlowReflect.IsFlowLine.reflect hb hη
  have hb' := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hS' : Sec4.cumWeightRight κ (rightLim (Sec7.FlowReflect.reflData b) (-y) + -θ * QuantumZipper.chiC κ)
      ≤ -2 := by
    rw [Sec7.FlowReflect.rightLim_reflData hb, neg_neg]
    have e : Sec4.cumWeightRight κ (-leftLim b y + -θ * QuantumZipper.chiC κ) =
        Sec4.cumWeightLeft κ (leftLim b y + θ * QuantumZipper.chiC κ) := by
      unfold Sec4.cumWeightRight Sec4.cumWeightLeft
      ring
    rw [e]; exact hS
  filter_upwards [ae_ne_of_cumWeightRight_le hκ hb' (neg_lt_neg hyx) hS' hR] with ω hω t ht he
  apply hω t ht
  rw [he]
  simp [LP.reflectC]

end OrdLow

end RealContact

end InteractingSLE
