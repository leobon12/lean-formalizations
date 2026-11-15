/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordanMeas
import InteractingSLE.Spec.Sec7.CounterflowWords

/-!
# Lemma 7.25's pocket marks: the actual force word of the change pocket (Aux. lemmas 119–121)

Packet PROVE-STRIPSYS17 (specification §7.4.1, Aux. lemmas 119–121, pp. 385–389, and the proof of Lemma 7.25, p. 413:
"The inversion in Aux. lemma 120 gives the two near-entry seed weights `(ρ^L, ρ^R)` in (RS13.6). Every actual
angle-change mark on a selected open arc remains present. Its cumulative value beyond the mark is `d`, by Aux. lemma
121. […] Thus every actual side partial sum is either its prescribed seed value or `d`, and is greater than `−2`.").

The pocket word in the counterflow chart, oriented for the counterflow from `y₀` (entry, seed at `0`) to `x₀`:

* **weights** (Aux. lemma 121, (FW9.1)–(FW9.3)): on the right incoming side (left of the counterflow seed) with final
  angle `θ₁` the seed weight is `R_L(θ₁)` and, when the right wall's change point lies on the open right arc, a second
  mark of weight `R_L(−π/2) − R_L(θ₁)`; on the left incoming side the seed weight is `R_R(θ₂)` and the left wall's
  change point (always on the open left arc of the change pocket) has weight `R_R(π/2) − R_R(θ₂)`
  (`wordL2`, `wordL1`, `wordR2`). Every side partial sum exceeds `−2` (`partialSums_wordL2`, …), the seed weights are
  the prescribed `(r_L, r_R)` for the angles (RS13.6) (`lemma725_word`), and they lie below `2A − 2` (Aux. lemma 122's
  bound).
* **positions**: the images under the counterflow Jordan coordinate of the change points, measurable in the incoming
  walls (`exists_measurable_pocketMarks`), on the correct side of the seed under the boundary orientation of the
  flow chart (`IsFlowChartOriented`, Aux. lemma 119: "The left incoming arc maps to `ℝ₋` and the right one to
  `ℝ₊`"), the inversion of Aux. lemma 120 exchanging the half-lines (`cfCoord_sides`; the left arc's side from the
  right arc's, `IsChangeConfigInc.re_neg_left_of_re_pos`).

The bounded case (`0 < rightLo`, the opening contact is not the flow seed) is a measurable event
(`measurableSet_rightLo_pos`, `zero_notMem_closure_of_rightLo_pos`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.PocketMarks

open WangWu PocketCoord Lemma71I PocketJordan

/-! ### The weights (Aux. lemma 121) -/

/-- The left word with the right wall's change mark: `(R_L(θ₁), R_L(−π/2) − R_L(θ₁))`. -/
def wordL2 (κ θ₁ : ℝ) : Fin 2 → ℝ := ![cf95RhoL κ θ₁, cf95RhoL κ (-(π / 2)) - cf95RhoL κ θ₁]

/-- The left word without a change mark on the open right arc: `(R_L(θ₁))`. -/
def wordL1 (κ θ₁ : ℝ) : Fin 1 → ℝ := ![cf95RhoL κ θ₁]

/-- The right word with the left wall's change mark: `(R_R(θ₂), R_R(π/2) − R_R(θ₂))`. -/
def wordR2 (κ θ₂ : ℝ) : Fin 2 → ℝ := ![cf95RhoR κ θ₂, cf95RhoR κ (π / 2) - cf95RhoR κ θ₂]

theorem sum_filter_le_fin_two (ρ : Fin 2 → ℝ) (m : Fin 2) :
    ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρ i = if m = 0 then ρ 0 else ρ 0 + ρ 1 := by
  fin_cases m
  · simp [Finset.sum_filter]
  · simp [Finset.sum_filter, Fin.sum_univ_two, Fin.le_def]

theorem sum_filter_le_fin_one (ρ : Fin 1 → ℝ) (m : Fin 1) :
    ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρ i = ρ 0 := by
  fin_cases m
  simp

variable {κ θ₁ θ₂ : ℝ}

/-- **The left partial sums exceed `−2`** (seed `R_L(θ₁)`, then the outer total `A − 2`). -/
theorem partialSums_wordL2 (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < π / 2) :
    ∀ m : Fin 2, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordL2 κ θ₁ i := by
  have hA := counterflowA_pos hκ hκ4
  have h0 := (neg_two_lt_cf95RhoL_iff hκ hκ4).2 hθ₁
  intro m
  rw [sum_filter_le_fin_two]
  split_ifs
  · simpa [wordL2] using h0
  · simp only [wordL2, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [(fw93_left κ θ₁).2]
    linarith

theorem partialSums_wordL1 (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < π / 2) :
    ∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordL1 κ θ₁ i := by
  intro m
  rw [sum_filter_le_fin_one]
  simpa [wordL1] using (neg_two_lt_cf95RhoL_iff hκ hκ4).2 hθ₁

/-- **The right partial sums exceed `−2`** (seed `R_R(θ₂)`, then the outer total `A − 2`). -/
theorem partialSums_wordR2 (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₂ : -(π / 2) < θ₂) :
    ∀ m : Fin 2, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordR2 κ θ₂ i := by
  have hA := counterflowA_pos hκ hκ4
  have h0 := (neg_two_lt_cf95RhoR_iff hκ hκ4).2 hθ₂
  intro m
  rw [sum_filter_le_fin_two]
  split_ifs
  · simpa [wordR2] using h0
  · simp only [wordR2, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [(fw93_right κ θ₂).2]
    linarith

/-- **Lemma 7.25's word** for the angles (RS13.6): with `θ₁ = rs136Theta1 κ r_L`, `θ₂ = rs136Theta2 κ r_R` and
`r_L, r_R ∈ (−2, A − 2)` (`A = κ'/2 − 2`, `κ' = 16/κ`), the seed weights are `r_L` and `r_R`, every side partial sum
exceeds `−2` (with or without the right wall's change mark), and the seed weights lie below `2A − 2`. -/
theorem lemma725_word (hκ : 0 < κ) (hκ4 : κ < 4) {rL rR : ℝ} (hL : rL ∈ Ioo (-2) (counterflowA κ - 2))
    (hR : rR ∈ Ioo (-2) (counterflowA κ - 2)) :
    wordL2 κ (rs136Theta1 κ rL) 0 = rL ∧ wordL1 κ (rs136Theta1 κ rL) 0 = rL ∧
      wordR2 κ (rs136Theta2 κ rR) 0 = rR ∧
      (∀ m : Fin 2, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordL2 κ (rs136Theta1 κ rL) i) ∧
      (∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordL1 κ (rs136Theta1 κ rL) i) ∧
      (∀ m : Fin 2, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), wordR2 κ (rs136Theta2 κ rR) i) ∧
      rL < 2 * (16 / κ / 2 - 2) - 2 ∧ rR < 2 * (16 / κ / 2 - 2) - 2 := by
  obtain ⟨h1, h2⟩ := rs136_mem_Ioo hκ hκ4 hL hR
  have hA := counterflowA_pos hκ hκ4
  have hAe : counterflowA κ = 16 / κ / 2 - 2 := rfl
  refine ⟨by simp [wordL2, cf95RhoL_rs136Theta1 hκ hκ4], by simp [wordL1, cf95RhoL_rs136Theta1 hκ hκ4],
    by simp [wordR2, cf95RhoR_rs136Theta2 hκ hκ4], partialSums_wordL2 hκ hκ4 h1.2, partialSums_wordL1 hκ hκ4 h1.2,
    partialSums_wordR2 hκ hκ4 h2.1, ?_, ?_⟩
  · rw [← hAe]; linarith [hL.2]
  · rw [← hAe]; linarith [hR.2]

/-! ### The bounded case -/

section Bounded

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The opening contact is away from the flow seed** when its right-wall parameter is positive. -/
theorem zero_notMem_closure_of_rightLo_pos (h : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) :
    (0 : ℂ) ∉ closure (changePocket R L r) := by
  intro h0
  obtain ⟨-, hj1, hj2, -, -, hC⟩ := h.changeCorners
  obtain ⟨-, hball, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, -⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have hm : cayley 0 ∈ closure (cayley '' changePocket R L r) :=
    (QuantumZipper.CA.differentiableAt_cayley (by simp)).continuousAt.continuousWithinAt.mem_closure_image h0
  rw [show cayley 0 = -1 by simp [QuantumZipper.CA.cayley], closure_eq_self_union_frontier, hfr] at hm
  rcases hm with hD | (⟨s, hs, he⟩ | ⟨t, ht, he⟩)
  · have := hball hD
    simp at this
  · have := hαR.inj ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hαR.zero.symm)
    linarith [hs.1]
  · rw [hj1, hj2] at ht
    have ht0 := hαL.inj ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hαL.zero.symm)
    have hlo : leftLo R L r = 0 := le_antisymm (ht0 ▸ ht.1) ha.1
    have := hαR.inj hu ⟨le_rfl, zero_le_one⟩ (show toDisc (realPath R) (rightLo R L r) = toDisc (realPath R) 0 by
      rw [hαR.zero, ← hαL.zero, ← hlo, hLa]
      rfl)
    linarith

end Bounded

/-! ### The boundary orientation -/

end InteractingSLE.Sec7.PocketMarks

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The left arc goes to the negative half-line** once the right arc goes to the positive one (intermediate values
along the right arc, which `Ψ` sends from `0` to `∞`, and injectivity: the open arcs are disjoint). -/
theorem re_neg_left_of_re_pos (h : IsChangeConfigInc R L r) {Ψ : ℂ → ℂ}
    (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ)
    (hpos : ∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), 0 < (Ψ (toDisc (realPath R) s)).re) :
    ∀ t ∈ Ioo (leftLo R L r) (leftHi R L r), (Ψ (toDisc (realPath L) t)).re < 0 := by
  obtain ⟨-, hj1, hj2, hgL, -, -⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, huv, ha, hb, -, hLa, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have hDo := Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H
  have hqD : closePt R L r ∉ cayley '' changePocket R L r := by
    have := h.closePt_mem_frontier
    rw [hDo.frontier_eq] at this
    exact this.2
  have hpc := frontier_subset_closure h.openPt_mem_frontier
  have hpq := h.openPt_ne_closePt
  have hRfr : ∀ s ∈ Icc (rightLo R L r) (rightHi R L r),
      toDisc (realPath R) s ∈ frontier (cayley '' changePocket R L r) := fun s hs => by
    rw [hfr]; exact Or.inl ⟨s, hs, rfl⟩
  have hLfr : ∀ t ∈ Icc (leftLo R L r) (leftHi R L r),
      toDisc (realPath L) t ∈ frontier (cayley '' changePocket R L r) := fun t ht => by
    rw [hfr, pocketCurve, hj1, hj2]; exact Or.inr ⟨t, ht, rfl⟩
  have hRq : ∀ s ∈ Ico (rightLo R L r) (rightHi R L r), toDisc (realPath R) s ≠ closePt R L r := fun s hs he =>
    hs.2.ne (hαR.inj ⟨hu.1.trans hs.1, hs.2.le.trans hv.2⟩ hv he)
  have hLq : ∀ t ∈ Ico (leftLo R L r) (leftHi R L r), toDisc (realPath L) t ≠ closePt R L r := fun t ht he =>
    ht.2.ne (hαL.inj ⟨ha.1.trans ht.1, ht.2.le.trans hb.2⟩ hb (he.trans hLb.symm))
  -- values on the frontier are real
  have hreal : ∀ w ∈ frontier (cayley '' changePocket R L r), w ≠ closePt R L r → Ψ w = ((Ψ w).re : ℂ) :=
    fun w hw hwq => Complex.ext rfl (by simp [hU.im_eq_zero hDo hqD hw hwq])
  intro t ht
  have htfr := hLfr t (Ioo_subset_Icc_self ht)
  have htq := hLq t (Ioo_subset_Ico_self ht)
  have hne0 : Ψ (toDisc (realPath L) t) ≠ 0 := by
    refine hU.ne_zero hpc hpq ⟨frontier_subset_closure htfr, htq⟩ fun he => ?_
    rw [← hLa] at he
    exact ht.1.ne' (hαL.inj ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩ ha he)
  by_contra hge
  push Not at hge
  set x := (Ψ (toDisc (realPath L) t)).re with hx
  have hxpos : 0 < x := lt_of_le_of_ne hge fun h0 => hne0 (by rw [hreal _ htfr htq, ← hx, ← h0, ofReal_zero])
  -- a point of the open right arc where `Re Ψ > x`
  have hfar : ∃ s ∈ Ioo (rightLo R L r) (rightHi R L r), x < (Ψ (toDisc (realPath R) s)).re := by
    have hct : Tendsto (toDisc (realPath R)) (𝓝[Ioo (rightLo R L r) (rightHi R L r)] (rightHi R L r))
        (𝓝[closure (cayley '' changePocket R L r) \ {closePt R L r}] (closePt R L r)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs =>
        ⟨frontier_subset_closure (hRfr s (Ioo_subset_Icc_self hs)), hRq s (Ioo_subset_Ico_self hs)⟩⟩
      exact (hαR.cont _ hv).tendsto.mono_left (nhdsWithin_mono _ fun s hs =>
        ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩)
    have hn := hU.tendsto.comp hct
    rw [nhdsWithin_Ioo_eq_nhdsLT huv] at hn
    have hev : ∀ᶠ s in 𝓝[<] (rightHi R L r), x < ‖Ψ (toDisc (realPath R) s)‖ ∧
        s ∈ Ioo (rightLo R L r) (rightHi R L r) := by
      refine (hn.eventually (eventually_gt_atTop x)).and ?_
      rw [← nhdsWithin_Ioo_eq_nhdsLT huv]
      exact self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2⟩ := hev.exists
    refine ⟨s, hs2, ?_⟩
    have hsr := hreal _ (hRfr s (Ioo_subset_Icc_self hs2)) (hRq s (Ioo_subset_Ico_self hs2))
    rw [hsr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos s hs2)] at hs1
    exact hs1
  obtain ⟨s₁, hs₁, hxs₁⟩ := hfar
  -- intermediate values along `[rightLo, s₁]`
  have hcont : ContinuousOn (fun s => (Ψ (toDisc (realPath R) s)).re) (Icc (rightLo R L r) s₁) := by
    refine Complex.continuous_re.comp_continuousOn (hU.cont.comp (hαR.cont.mono fun s hs =>
      ⟨hu.1.trans hs.1, hs.2.trans (hs₁.2.le.trans hv.2)⟩) fun s hs =>
        ⟨frontier_subset_closure (hRfr s ⟨hs.1, hs.2.trans hs₁.2.le⟩), hRq s ⟨hs.1, hs.2.trans_lt hs₁.2⟩⟩)
  have h0 : (Ψ (toDisc (realPath R) (rightLo R L r))).re = 0 := by
    rw [show toDisc (realPath R) (rightLo R L r) = openPt R L r from rfl, hU.zero, zero_re]
  obtain ⟨c, hc, hcx0⟩ := intermediate_value_Icc hs₁.1.le hcont ⟨by rw [h0]; exact hxpos.le, hxs₁.le⟩
  have hcx : (Ψ (toDisc (realPath R) c)).re = x := hcx0
  have hc0 : rightLo R L r < c := lt_of_le_of_ne hc.1 fun he => by
    rw [← he, h0] at hcx
    exact hxpos.ne hcx
  have hcI : c ∈ Ioo (rightLo R L r) (rightHi R L r) := ⟨hc0, hc.2.trans_lt hs₁.2⟩
  have hcfr := hRfr c (Ioo_subset_Icc_self hcI)
  have hcq := hRq c (Ioo_subset_Ico_self hcI)
  have heq : Ψ (toDisc (realPath R) c) = Ψ (toDisc (realPath L) t) := by
    rw [hreal _ hcfr hcq, hreal _ htfr htq]
    exact congrArg _ hcx
  have hpt := hU.inj ⟨frontier_subset_closure hcfr, hcq⟩ ⟨frontier_subset_closure htfr, htq⟩ heq
  exact hgL.2.2.2 t ht ⟨⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩, c,
    ⟨hu.1.trans hcI.1.le, hcI.2.le.trans hv.2⟩, hpt⟩

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

namespace InteractingSLE.Sec7.PocketMarks

open WangWu PocketCoord Lemma71I PocketJordan

/-! ### The positions -/

/-- **The boundary orientation of the flow chart** of the change pocket (Aux. lemma 119: "The left incoming arc maps
to `ℝ₋` and the right one to `ℝ₊`"): every two-point uniformizer of the Cayley image (`x₀ ↦ 0`, `y₀ ↦ ∞`) sends the
open right-wall arc into the positive half-line. (`PocketMarksOrient` derives it from the side premises of the
orientation theorem; the left arc then goes into the negative half-line, `re_neg_left_of_re_pos`.) -/
def IsFlowChartOriented (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop :=
  ∀ Ψ : ℂ → ℂ, IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ →
    ∀ s ∈ Ioo (rightLo R L r) (rightHi R L r), 0 < (Ψ (toDisc (realPath R) s)).re

theorem re_negInv (z : ℂ) : (negInv z).re = -(z.re / normSq z) := by
  simp [WangWu.negInv, Complex.inv_re]

/-- **The sides in the counterflow chart**: under the flow-chart orientation, the counterflow coordinate
`cfCoord a Ψ q` sends the open right-wall arc to the negative and the open left-wall arc to the positive half-line
(the inversion `m(w) = −1/w` exchanges the half-lines). -/
theorem cfCoord_sides {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r) (hor : IsFlowChartOriented R L r)
    {Ψ : ℂ → ℂ} (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ) {a : ℝ}
    (ha : 0 < a) :
    (∀ s ∈ Ioo (rightLo R L r) (rightHi R L r),
      (cfCoord a Ψ (closePt R L r) (cfPt (toDisc (realPath R) s))).re < 0) ∧
    ∀ t ∈ Ioo (leftLo R L r) (leftHi R L r),
      0 < (cfCoord a Ψ (closePt R L r) (cfPt (toDisc (realPath L) t))).re := by
  obtain ⟨hu, hv, -, ha', hb, -, -, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have hpos := hor Ψ hU
  have hneg := h.re_neg_left_of_re_pos hU hpos
  have key : ∀ w : ℂ, w ≠ -1 → w ≠ closePt R L r →
      (cfCoord a Ψ (closePt R L r) (cfPt w)).re = -((a * (Ψ w).re) / normSq ((a : ℂ) * Ψ w)) := by
    intro w hw1 hwq
    rw [cfCoord, neg_cayley_cfPt hw1, cfMap_of_ne hwq, re_negInv, re_ofReal_mul]
  have hnz : ∀ w : ℂ, Ψ w ≠ 0 → 0 < normSq ((a : ℂ) * Ψ w) := fun w hw =>
    normSq_pos.2 (mul_ne_zero (by exact_mod_cast ha.ne') hw)
  constructor
  · intro s hs
    have hs1 : toDisc (realPath R) s ≠ -1 := fun he => by
      have := hαR.inj ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hαR.zero.symm)
      linarith [hu.1, hs.1]
    have hsq : toDisc (realPath R) s ≠ closePt R L r := fun he =>
      hs.2.ne (hαR.inj ⟨hu.1.trans hs.1.le, hs.2.le.trans hv.2⟩ hv he)
    have hp := hpos s hs
    have hΨ0 : Ψ (toDisc (realPath R) s) ≠ 0 := fun he => by rw [he, zero_re] at hp; exact lt_irrefl _ hp
    rw [key _ hs1 hsq, neg_lt_zero]
    exact div_pos (mul_pos ha hp) (hnz _ hΨ0)
  · intro t ht
    have ht1 : toDisc (realPath L) t ≠ -1 := fun he => by
      have := hαL.inj ⟨ha'.1.trans ht.1.le, ht.2.le.trans hb.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hαL.zero.symm)
      linarith [ha'.1, ht.1]
    have htq : toDisc (realPath L) t ≠ closePt R L r := fun he =>
      ht.2.ne (hαL.inj ⟨ha'.1.trans ht.1.le, ht.2.le.trans hb.2⟩ hb (he.trans hLb.symm))
    have hn := hneg t ht
    have hΨ0 : Ψ (toDisc (realPath L) t) ≠ 0 := fun he => by rw [he, zero_re] at hn; exact lt_irrefl _ hn
    rw [key _ ht1 htq, neg_pos]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hn) (hnz _ hΨ0)

theorem measurable_cfPt : Measurable cfPt := by
  unfold cfPt QuantumZipper.CA.cayleyInv
  fun_prop

/-- A parameter strictly inside `(lo, hi)` is an affine image of a parameter strictly inside `(0, 1)`. -/
theorem exists_affine_eq {lo hi c : ℝ} (hc : c ∈ Ioo lo hi) :
    ∃ s ∈ Ioo (0 : ℝ) 1, lo + s * (hi - lo) = c := by
  have hd : 0 < hi - lo := by linarith [hc.1, hc.2]
  refine ⟨(c - lo) / (hi - lo), ⟨div_pos (by linarith [hc.1]) hd, (div_lt_one hd).2 (by linarith [hc.2])⟩, ?_⟩
  field_simp
  ring

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

omit mΩ in
theorem rightLo_eq_gapLoα {ω : Ω} (hω : ω ∈ G) : rightLo (R ω) (L ω) r = gapLoα G R L r ω := by
  classical
  simp only [gapLoα, cornerα, gapLoR, hω, ↓reduceIte, rightLo, leftLo]

omit mΩ in
theorem rightHi_eq_gapHiα {ω : Ω} (hω : ω ∈ G) : rightHi (R ω) (L ω) r = gapHiα G R L r ω := by
  classical
  simp only [gapHiα, cornerα, gapHiR, hω, ↓reduceIte, rightHi, leftHi]

/-- **The events of the word shapes are measurable**: the bounded case (`0 < rightLo`) and the presence of a fixed disc
parameter `c₁` of the right wall on the open right arc. -/
theorem measurableSet_rightLo_pos_and (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) :
    MeasurableSet {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} ∧ ∀ c₁ : ℝ,
      MeasurableSet {ω | ω ∈ G ∧ c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} := by
  have hlo := measurable_gapLoα hRm hLm hGm hG
  have hhi := measurable_gapHiα hRm hLm hGm hG
  refine ⟨?_, fun c₁ => ?_⟩
  · have e : {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} = G ∩ {ω | 0 < gapLoα G R L r ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      exact ⟨fun ⟨hω, h⟩ => ⟨hω, (rightLo_eq_gapLoα hω) ▸ h⟩, fun ⟨hω, h⟩ => ⟨hω, (rightLo_eq_gapLoα hω).symm ▸ h⟩⟩
    rw [e]
    exact hGm.inter (measurableSet_lt measurable_const hlo)
  · have e : {ω | ω ∈ G ∧ c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} =
        G ∩ ({ω | gapLoα G R L r ω < c₁} ∩ {ω | c₁ < gapHiα G R L r ω}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨hω, h1, h2⟩
        exact ⟨hω, (rightLo_eq_gapLoα hω) ▸ h1, (rightHi_eq_gapHiα hω) ▸ h2⟩
      · rintro ⟨hω, h1, h2⟩
        exact ⟨hω, (rightLo_eq_gapLoα hω).symm ▸ h1, (rightHi_eq_gapHiα hω).symm ▸ h2⟩
    rw [e]
    exact hGm.inter ((measurableSet_lt hlo measurable_const).inter (measurableSet_lt measurable_const hhi))

omit mΩ in
theorem re_indicator {A : Set Ω} (f : Ω → ℂ) :
    (A.indicator fun ω => (f ω).re) = (fun z : ℂ => z.re) ∘ A.indicator f := by
  classical
  funext ω
  by_cases hω : ω ∈ A <;> simp [hω]

/-- **The measurable marks of the change pocket.** For random walls with measurable coordinates, a measurable event `G`
on which they satisfy `IsChangeConfigInc` in the bounded case, with the boundary orientation of the flow chart, there
is a random Jordan coordinate `ψ ω` of the inverted pocket such that:

* the left wall's change point `L r` (always on the open left arc) has a measurable, positive position;
* for a disc parameter `c₁` of the right wall (the right wall's change point; `c₁ = discTime 1` for the schedule
  `(−π/2, θ₁)` of (RS13.1)), on the measurable event that it lies on the open right arc, its position is measurable and
  negative. -/
theorem exists_measurable_pocketMarks (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hG0 : ∀ ω ∈ G, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r))
    (hor : ∀ ω ∈ G, IsFlowChartOriented (R ω) (L ω) r) (c₁ : ℝ) :
    ∃ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ G, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
        (cfPt (closePt (R ω) (L ω) r)) (ψ ω)) ∧
      Measurable (G.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      (∀ ω ∈ G, 0 < (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      Measurable ({ω | ω ∈ G ∧ c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)}.indicator
        fun ω => (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re) ∧
      ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
        (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re < 0 := by
  classical
  obtain ⟨a, Ψ, haΨ, hmeas0⟩ := exists_measurable_cfCoord hRm hLm hGm hG
  have hJ : ∀ ω ∈ G, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
      (cfPt (closePt (R ω) (L ω) r)) (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) := fun ω hω =>
    (hG ω hω).isJordanCoord_cfCoord (hG0 ω hω) (haΨ ω hω).2 (haΨ ω hω).1
  set ψ : Ω → ℂ → ℂ := fun ω => if ω ∈ G then cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) else 0 with hψdef
  have hψG : ∀ ω ∈ G, ψ ω = cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) := fun ω hω => by
    simp only [hψdef, hω, ↓reduceIte]
  -- measurability at measurable points of the closed pocket away from `m(x₀)`
  have hmeas : ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
      (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) →
      Measurable (A.indicator fun ω => (ψ ω (p ω)).re) := by
    intro A hA hAG p hp hpA
    have h := hmeas0 A hA hAG p hp fun ω hω => ⟨(hpA ω hω).1, ((hJ ω (hAG hω)).1 _ (hpA ω hω)).mono
      fun z hz => ⟨subset_closure hz, fun h' => (hG ω (hAG hω)).cfPt_openPt_notMem (h' ▸ hz)⟩⟩
    rw [re_indicator]
    refine Complex.measurable_re.comp ?_
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, hψG ω (hAG hω)]
    · simp only [indicator_of_notMem hω]
  have hE := (measurableSet_rightLo_pos_and hRm hLm hGm hG).2 c₁
  -- the change points on the open arcs
  have hLpt : ∀ ω ∈ G, ∃ s ∈ Ioo (0 : ℝ) 1, cfArcL (R ω) (L ω) r s = cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    fun ω hω => by
      obtain ⟨s, hs, he⟩ := exists_affine_eq (hG ω hω).changeCorners.2.2.2.2.1
      exact ⟨s, hs, by rw [cfArcL, he]⟩
  have hRpt : ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
      ∃ s ∈ Ioo (0 : ℝ) 1, cfArcR (R ω) (L ω) r s = cfPt (toDisc (realPath (R ω)) c₁) := fun ω _ hc => by
    obtain ⟨s, hs, he⟩ := exists_affine_eq hc
    exact ⟨s, hs, by rw [cfArcR, he]⟩
  -- points of the open arcs are in the closed pocket, away from `m(x₀)`
  have hmemR : ∀ ω ∈ G, ∀ s ∈ Ioo (0 : ℝ) 1, cfArcR (R ω) (L ω) r s ∈
      closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := fun ω hω s hs => by
    have hP := (hG ω hω).isCfPocket (hG0 ω hω)
    refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
    have h0 : cfArcR (R ω) (L ω) r 0 = cfPt (openPt (R ω) (L ω) r) := by
      simp only [cfArcR, zero_mul, add_zero, openPt]
    rw [← h0] at he
    exact hs.1.ne' (hP.inj₁ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)
  have hmemL : ∀ ω ∈ G, ∀ s ∈ Ioo (0 : ℝ) 1, cfArcL (R ω) (L ω) r s ∈
      closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := fun ω hω s hs => by
    have hP := (hG ω hω).isCfPocket (hG0 ω hω)
    refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
    have h0 : cfArcR (R ω) (L ω) r 0 = cfPt (openPt (R ω) (L ω) r) := by
      simp only [cfArcR, zero_mul, add_zero, openPt]
    rw [← h0, ← hP.junction] at he
    exact hs.1.ne' (hP.inj₂ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)
  have hpL : Measurable fun ω => cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hLm _)
  have hpR : Measurable fun ω => cfPt (toDisc (realPath (R ω)) c₁) :=
    measurable_cfPt.comp (measurable_toDisc_apply hRm _)
  refine ⟨ψ, fun ω hω => hψG ω hω ▸ hJ ω hω, ?_, fun ω hω => ?_, ?_, fun ω hω hc => ?_⟩
  · refine hmeas G hGm subset_rfl _ hpL fun ω hω => ?_
    obtain ⟨s, hs, he⟩ := hLpt ω hω
    exact he ▸ hmemL ω hω s hs
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).2 _
      (hG ω hω).changeCorners.2.2.2.2.1
  · refine hmeas _ hE (fun ω hω => hω.1) _ hpR fun ω hω => ?_
    obtain ⟨s, hs, he⟩ := hRpt ω hω.1 hω.2
    exact he ▸ hmemR ω hω.1 s hs
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).1 _ hc

end Random

end InteractingSLE.Sec7.PocketMarks
