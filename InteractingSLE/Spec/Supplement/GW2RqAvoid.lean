/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqFar
import InteractingSLE.Spec.Supplement.SB2WfPk

/-!
# Flow lines avoid the angle regions of their word (decision D33)

PROVE-GW2-ROOTX round 8. The real points a flow line never visits, read from its word alone:

* `avoidQ κ θ β`: real points `z ≠ 0` off the jumps whose cumulative weight at angle `θ` is `≥ κ/2 − 2` (GB7a), and
  jumps whose cumulative weight beyond them is `> κ/2 − 4` (G12), on either side;
* **`ae_avoidQ`**: the angle-`θ` flow line from `0` of a GFF with data `b'` almost surely never visits
  `avoidQ κ θ β` up to its lifetime, for any word `β` equal to `b'` off a finite set
  (`Supp8.gb7aFlowStatement`, `Supp7.g12FlowStatement`);
* **`mem_avoidQ_of_region`**: every real point `≠ 0` of the two angle regions of a `RegionFact` is in
  `avoidQ κ 0 β` (the angle bands give cumulative weights `≥ κ/2 − 2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist Exist.StagedLaw
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

/-- **The real points avoided by the flow lines of a word**: GB7a off the jumps, G12 at the jumps. -/
def avoidQ (κ θ : ℝ) (β : BoundaryWord) : Set ℂ :=
  {z | z.im = 0 ∧
    ((0 < z.re ∧ ((z.re ∉ β.jumps ∧ κ / 2 - 2 ≤ Sec4.cumWeightRight κ (β.fn z.re + θ * chiC κ)) ∨
        (z.re ∈ β.jumps ∧ κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim β.fn z.re + θ * chiC κ)))) ∨
      (z.re < 0 ∧ ((z.re ∉ β.jumps ∧ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn z.re + θ * chiC κ)) ∨
        (z.re ∈ β.jumps ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim β.fn z.re + θ * chiC κ)))))}

/-- **A flow line never visits the avoided points of a word equal to its data off a finite set.** -/
theorem ae_avoidQ {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h' b' J')
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b' J' 0 θ Q h' η ζ) {β : BoundaryWord} {F : Finset ℝ}
    (hβ : ∀ y ∉ F, β.fn y = b' y) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ∉ avoidQ κ θ β := by
  classical
  have hβpc := β.isPiecewiseConstantBoundaryData
  set N : Finset ℝ := β.jumps ∪ J' ∪ F with hN
  have hGB := Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement hκ hκ4 hb' hh hη
  have hG12 : ∀ᵐ ω ∂Q, ∀ y ∈ N,
      (0 < y → κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b' y + θ * chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < 0 → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) := by
    have h1 : ∀ y ∈ N, ∀ᵐ ω ∂Q,
        (0 < y → κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b' y + θ * chiC κ) →
          ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
        (y < 0 → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ) →
          ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) := by
      intro y _
      have hg := Supp7.g12FlowStatement κ hκ hκ4 b' J' hb' 0 θ y Q h' hh η ζ hη
      by_cases hR : 0 < y ∧ κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b' y + θ * chiC κ)
      · filter_upwards [hg.1 hR.1 hR.2] with ω hω
        exact ⟨fun _ _ => hω, fun hy => absurd hR.1 (not_lt.2 hy.le)⟩
      · by_cases hL : y < 0 ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ)
        · filter_upwards [hg.2 hL.1 hL.2] with ω hω
          exact ⟨fun hy => absurd hL.1 (not_lt.2 hy.le), fun _ _ => hω⟩
        · exact Eventually.of_forall fun ω => ⟨fun h1 h2 => absurd ⟨h1, h2⟩ hR, fun h1 h2 => absurd ⟨h1, h2⟩ hL⟩
    exact (Finset.eventually_all N).2 h1
  filter_upwards [hGB, hG12] with ω hgb hg12 t ht hmem
  obtain ⟨him, hR | hL⟩ := hmem
  · set z := (η ω t).re with hz
    have hze : η ω t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    obtain ⟨hpos, hc | ⟨hzJ, hc⟩⟩ := hR
    · obtain ⟨hzJ, hc⟩ := hc
      by_cases hzN : z ∈ N
      · -- an exceptional point off the word's jumps: G12 with the right limit
        have hrl := SB.Wf.rightLim_eq_of_eq_off hb' hβ z
        rw [rightLim_eq_of_notMem hβpc hzJ] at hrl
        rw [hrl] at hc
        exact (hg12 z hzN).1 hpos (by linarith) t ht hze
      · have hzF : z ∉ F := fun h => hzN (Finset.mem_union_right _ h)
        have hzJ' : z ∉ J' := fun h => hzN (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        rw [hβ z hzF] at hc
        exact (hgb t ht z hzJ').1 hpos hc hze
    · have hzN : z ∈ N := Finset.mem_union_left _ (Finset.mem_union_left _ hzJ)
      rw [SB.Wf.rightLim_eq_of_eq_off hb' hβ z] at hc
      exact (hg12 z hzN).1 hpos hc t ht hze
  · set z := (η ω t).re with hz
    have hze : η ω t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    obtain ⟨hneg, hc | ⟨hzJ, hc⟩⟩ := hL
    · obtain ⟨hzJ, hc⟩ := hc
      by_cases hzN : z ∈ N
      · have hll := SB.Wf.leftLim_eq_of_eq_off hb' hβ z
        rw [leftLim_eq_of_notMem hβpc hzJ] at hll
        rw [hll] at hc
        exact (hg12 z hzN).2 hneg (by linarith) t ht hze
      · have hzF : z ∉ F := fun h => hzN (Finset.mem_union_right _ h)
        have hzJ' : z ∉ J' := fun h => hzN (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        rw [hβ z hzF] at hc
        exact (hgb t ht z hzJ').2 hneg hc hze
    · have hzN : z ∈ N := Finset.mem_union_left _ (Finset.mem_union_left _ hzJ)
      rw [SB.Wf.leftLim_eq_of_eq_off hb' hβ z] at hc
      exact (hg12 z hzN).2 hneg hc t ht hze

/-! ### The angle regions are avoided -/

variable {κ : ℝ} {β : BoundaryWord} {φ0 aL aR Hm : ℝ} {N : ℕ}

theorem cumR_of_band (hκ : 0 < κ) (hκ4 : κ < 4) (h : RegionFact κ β φ0 aL aR Hm N) {z : ℝ} (hz0 : 0 < z)
    (hza : z < aR) (hzJ : z ∉ β.jumps) : κ / 2 - 2 ≤ Sec4.cumWeightRight κ (β.fn z + 0 * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [zero_mul, add_zero, Sec4.le_cumWeightRight_iff hκ]
  have hb := h.bandR z hz0 hza hzJ
  have hs := h.start_mem
  have h1 : (sleLambda κ - β.fn z) / chiC κ ≤ Real.pi := by linarith [hb.2, hs.1]
  have h2 := (div_le_iff₀ hχ).1 h1
  linarith

theorem cumL_of_band (hκ : 0 < κ) (hκ4 : κ < 4) (h : RegionFact κ β φ0 aL aR Hm N) {z : ℝ} (hza : aL < z)
    (hz0 : z < 0) (hzJ : z ∉ β.jumps) : κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn z + 0 * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [zero_mul, add_zero, Sec4.le_cumWeightLeft_iff hκ]
  have hb := h.bandL z hza hz0 hzJ
  have hs := h.start_mem
  have h1 : (sleLambda κ + β.fn z) / chiC κ ≤ Real.pi := by linarith [hb.1, hs.2]
  have h2 := (div_le_iff₀ hχ).1 h1
  linarith

/-- **Every real point `≠ 0` of the two angle regions is avoided** by the angle-`0` flow lines of the word. -/
theorem mem_avoidQ_of_region (hκ : 0 < κ) (hκ4 : κ < 4) (h : RegionFact κ β φ0 aL aR Hm N) {z : ℝ}
    (hzL : aL < z) (hzR : z < aR) (hz0 : z ≠ 0) : (z : ℂ) ∈ avoidQ κ 0 β := by
  have hb := β.isPiecewiseConstantBoundaryData
  refine ⟨by simp, ?_⟩
  simp only [Complex.ofReal_re]
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · right
    refine ⟨hneg, ?_⟩
    by_cases hzJ : z ∈ β.jumps
    · right
      refine ⟨hzJ, ?_⟩
      obtain ⟨lo, hlo, hc⟩ := GW2Rd.exists_Ioo_eq_leftLim hb z
      obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps (show max lo aL < z from max_lt hlo hzL)
      rw [← hc y ⟨(le_max_left _ _).trans_lt hy1, hy2⟩]
      have := cumL_of_band hκ hκ4 h ((le_max_right _ _).trans_lt hy1) (hy2.trans hneg) hyJ
      linarith
    · exact Or.inl ⟨hzJ, cumL_of_band hκ hκ4 h hzL hneg hzJ⟩
  · left
    refine ⟨hpos, ?_⟩
    by_cases hzJ : z ∈ β.jumps
    · right
      refine ⟨hzJ, ?_⟩
      obtain ⟨hi, hhi, hc⟩ := GW2Rd.exists_Ioo_eq_rightLim hb z
      obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps (show z < min hi aR from lt_min hhi hzR)
      rw [← hc y ⟨hy1, hy2.trans_le (min_le_left _ _)⟩]
      have := cumR_of_band hκ hκ4 h (hpos.trans hy1) (hy2.trans_le (min_le_right _ _)) hyJ
      linarith
    · exact Or.inl ⟨hzJ, cumR_of_band hκ hκ4 h hpos hzR hzJ⟩

end InteractingSLE.Theorem14.GW2Rq
