/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid
import InteractingSLE.Spec.Sec4.Prob41Charts

/-!
# Lemmas 4.3 and 4.5 for the basic lower constants and every `k > 0` (boundary avoidance, limits at the target)

Packet PROVE-SEC4-A4, item (1). SEC4-A3 proved the boundary parts of Lemma 4.3 (`a ≤ −Λ`, `a ≥ Λ`), Lemma 4.5 and
the end alternatives of Aux. lemma 22 (and the limits at the target from Aux. lemma 7) for lower data satisfying
Remark 4.1 (`≤ −Λ + πX` left of `0`, `≥ Λ − πX` right of `0`). For `k > 4` (the counterflow parameter `κ′`) the basic
lower constants `−Λ`, `Λ` of Figures 4.1–4.4 do not satisfy it: the frozen flow-line word then has zero-weight seed
marks, which collide. Here the lower data only has to satisfy the weaker condition

* `bL x ≤ −Λ + πX` at every `x < 0` such that `bL` differs from `−Λ` somewhere on `[x, 0)`, and
* `bL x ≥ Λ − πX` at every `x > 0` such that `bL` differs from `Λ` somewhere on `(0, x]`

(off the candidates), which both Remark 4.1's data and the basic constants satisfy; for `k ≤ 4` it is Remark 4.1's
condition. The proofs for `k > 4` delete the zero-weight seeds (`IsFlowLine.ae_trace_ne_of_nonzero`); for `k ≤ 4`
they are SEC4-A3's.

* chart `E(z) = e^{πz} − 1` (target `+∞`): `ae_notMem_upperLineH_of_isStripFlowLine_basic`,
  `lemma43_right_of_aux7_basic`;
* chart `1 − e^{−πz}` (target `−∞`): `ae_notMem_upper_of_isLeftEndFlowLine_basic`, `lemma43_left_of_aux7_basic`;
* chart `(e^{πz} − 1)/(e^{πz} + q)` (target `z₀`): `ae_notMem_upper_of_isStripQFlowLine_basic`,
  `lemma45_of_aux7_basic`, `lemma45_strip_of_aux7_basic`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec4

variable {k : ℝ}

/-! ### The chart `E(z) = e^{πz} − 1` -/

/-- The lower-line coordinate `log(y + 1)/π` is monotone. -/
theorem log_add_one_div_pi_le {y y' : ℝ} (hy : -1 < y) (hyy : y ≤ y') :
    Real.log (y + 1) / π ≤ Real.log (y' + 1) / π :=
  div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) Real.pi_pos.le

/-- The left condition for the `E`-transported data, when every upper height is at most `−Λ`. -/
theorem stripHData_le_of_neg_of_exists {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0) (hyJ : y ∉ stripHJumps JL JU)
    (hex : ∃ y', y ≤ y' ∧ y' < 0 ∧ y' ∉ stripHJumps JL JU ∧
      stripHData k bL bU y' ≠ -sleLambda k) :
    stripHData k bL bU y ≤ -sleLambda k + π * chiC k := by
  have hπ := Real.pi_pos
  have hyJ' := hyJ
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ'
  obtain ⟨hy1, hyL, hyU⟩ := hyJ'
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [stripHData_of_lt_neg_one hlt]
    set x := Real.log (-y - 1) / π with hx
    have hxy : -Real.exp (π * x) - 1 = y := by
      rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring
    have := hU x fun h => hyU ⟨x, h, hxy⟩
    linarith
  · rw [stripHData_of_lt hgt]
    have hx0 : Real.log (y + 1) / π < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) hπ
    have hxL : Real.log (y + 1) / π ∉ JL := fun h => hyL ⟨_, h, by
      rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring⟩
    refine hlowL _ hx0 hxL ?_
    obtain ⟨y', hyy, hy', hy'J, hne⟩ := hex
    have hgt' : -1 < y' := hgt.trans_le hyy
    simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy'J
    rw [stripHData_of_lt hgt'] at hne
    refine ⟨Real.log (y' + 1) / π, log_add_one_div_pi_le hgt hyy,
      div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) hπ, fun h => hy'J.2.1
        ⟨_, h, by rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring⟩, hne⟩

/-- The right condition for the `E`-transported data (only the lower line lies right of `0`). -/
theorem le_stripHData_of_pos_of_exists {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y) (hyJ : y ∉ stripHJumps JL JU)
    (hex : ∃ y', 0 < y' ∧ y' ≤ y ∧ y' ∉ stripHJumps JL JU ∧
      stripHData k bL bU y' ≠ sleLambda k) :
    sleLambda k - π * chiC k ≤ stripHData k bL bU y := by
  have hπ := Real.pi_pos
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hyL, -⟩ := hyJ
  rw [stripHData_of_lt (by linarith)]
  have hx0 : 0 < Real.log (y + 1) / π := div_pos (Real.log_pos (by linarith)) hπ
  have hxL : Real.log (y + 1) / π ∉ JL := fun h => hyL ⟨_, h, by
    rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring⟩
  refine hlowR _ hx0 hxL ?_
  obtain ⟨y', hy', hyy, hy'J, hne⟩ := hex
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy'J
  rw [stripHData_of_lt (by linarith)] at hne
  exact ⟨Real.log (y' + 1) / π, div_pos (Real.log_pos (by linarith)) hπ,
    log_add_one_div_pi_le (by linarith) hyy, fun h => hy'J.2.1
      ⟨_, h, by rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring⟩, hne⟩

/-- In the chart `E`, a point left of `−1` (the image of `∂_U𝒮`) carries a value `≠ −Λ` when every upper height is
at most `−Λ` and `k > 4`. -/
theorem stripHData_ne_of_lt_neg_one {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} (hk4 : 4 < k)
    (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k) {y : ℝ} (hy : y < -1)
    (hyJ : y ∉ stripHJumps JL JU) : stripHData k bL bU y ≠ -sleLambda k := by
  have hπ := Real.pi_pos
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  rw [stripHData_of_lt_neg_one hy]
  have hxy : -Real.exp (π * (Real.log (-y - 1) / π)) - 1 = y := by
    rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log (by linarith)]; ring
  have h1 := hU _ fun h => hyJ.2.2 ⟨_, h, hxy⟩
  have h2 := pi_mul_chiC_neg hk4
  exact ne_of_lt (by linarith)

/-- **Lemma 4.3, `a ≤ −Λ`, boundary part; Aux. lemma 22, all upper heights `≤ −Λ`, boundary part — for every
`k > 0`, including `k = κ′ > 4` with the basic lower constants.** For the flow line from `0` towards the right strip
end (chart `E`), with every upper height at most `−Λ` and lower data satisfying the condition of this file: almost
surely the lifetime is infinite and the flow line never hits `∂_U𝒮` (`upperLineH`). -/
theorem ae_notMem_upperLineH_of_isStripFlowLine_basic (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, η ω t ∉ upperLineH := by
  rcases le_or_gt k 4 with hk4 | hk4
  · filter_upwards [ae_notMem_upperLineH_of_isStripFlowLine hk hbL hbU hU
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl]
      with ω hω
    exact ⟨hω.1, fun t => (hω.2 t).1⟩
  · filter_upwards [IsFlowLine.ae_trace_ne_of_nonzero hk
      (isPiecewiseConstantBoundaryData_stripHData k hbL hbU)
      (fun y hy hyJ hex => stripHData_le_of_neg_of_exists hU hlowL hy hyJ hex)
      (fun y hy hyJ hex => le_stripHData_of_pos_of_exists hlowR hy hyJ hex) hfl] with ω hω
    refine ⟨hω.1, fun t => ?_⟩
    rintro ⟨x, hx, hxt⟩
    have hx1 : x < -1 := hx
    obtain ⟨y', h1, h2, hJ⟩ := exists_mem_Ioo_not_mem (stripHJumps JL JU) hx1
    exact (hω.2 t).1 x (by linarith) ⟨y', h1.le, by linarith, hJ,
      stripHData_ne_of_lt_neg_one hk4 hU h2 hJ⟩ hxt.symm

/-- **Lemma 4.3, `a ≤ −Λ`; Aux. lemma 22, all upper heights `≤ −Λ` — for every `k > 0`** (from Aux. lemma 7): almost
surely the lifetime is infinite, the flow line never hits `∂_U𝒮`, and it accumulates at `+∞`. -/
theorem lemma43_right_of_aux7_basic (h7 : Aux7Statement.{u} k) (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ upperLineH) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (stripInv (η ω t)).re) atTop atTop := by
  rcases le_or_gt k 4 with hk4 | hk4
  · exact lemma43_right_of_aux7 h7 hk hbL hbU hU
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl
  · filter_upwards [ae_notMem_upperLineH_of_isStripFlowLine_basic hk hbL hbU hU hlowL hlowR hfl,
      IsFlowLine.ae_tendsto_of_aux7_of_nonzero h7 hk
        (isPiecewiseConstantBoundaryData_stripHData k hbL hbU)
        (fun y hy hyJ hex => stripHData_le_of_neg_of_exists hU hlowL hy hyJ hex)
        (fun y hy hyJ hex => le_stripHData_of_pos_of_exists hlowR hy hyJ hex) hfl] with ω h1 h2
    exact ⟨h1.1, h1.2, h2.2.2, tendsto_re_stripInv h2.2.2⟩

/-! ### The chart `1 − e^{−πz}` -/

/-- The lower-line coordinate `−log(1 − y)/π` is monotone. -/
theorem neg_log_one_sub_div_pi_le {y y' : ℝ} (hy' : y' < 1) (hyy : y ≤ y') :
    -Real.log (1 - y) / π ≤ -Real.log (1 - y') / π :=
  div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log (by linarith) (by linarith)))
    Real.pi_pos.le

/-- The left condition for the transported data of the chart `1 − e^{−πz}` (only the lower line lies left
of `0`). -/
theorem leftEndHData_le_of_neg_of_exists {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0) (hyJ : y ∉ leftEndHJumps JL JU)
    (hex : ∃ y', y ≤ y' ∧ y' < 0 ∧ y' ∉ leftEndHJumps JL JU ∧
      leftEndHData k bL bU y' ≠ -sleLambda k) :
    leftEndHData k bL bU y ≤ -sleLambda k + π * chiC k := by
  have hπ := Real.pi_pos
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hyL, -⟩ := hyJ
  have hy1 : y < 1 := by linarith
  rw [leftEndHData_of_lt hy1]
  have hx0 : -Real.log (1 - y) / π < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by linarith))) hπ
  refine hlowL _ hx0 (fun h => hyL ⟨_, h, one_sub_exp_neg_log hy1⟩) ?_
  obtain ⟨y', hyy, hy', hy'J, hne⟩ := hex
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy'J
  have hy'1 : y' < 1 := by linarith
  rw [leftEndHData_of_lt hy'1] at hne
  exact ⟨_, neg_log_one_sub_div_pi_le hy'1 hyy,
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by linarith))) hπ,
    fun h => hy'J.2.1 ⟨_, h, one_sub_exp_neg_log hy'1⟩, hne⟩

/-- The right condition for the transported data of the chart `1 − e^{−πz}`, when every upper height is at
least `Λ`. -/
theorem le_leftEndHData_of_pos_of_exists {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y) (hyJ : y ∉ leftEndHJumps JL JU)
    (hex : ∃ y', 0 < y' ∧ y' ≤ y ∧ y' ∉ leftEndHJumps JL JU ∧
      leftEndHData k bL bU y' ≠ sleLambda k) :
    sleLambda k - π * chiC k ≤ leftEndHData k bL bU y := by
  have hπ := Real.pi_pos
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨hy1, hyL, hyU⟩ := hyJ
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [leftEndHData_of_lt hlt]
    have hx0 : 0 < -Real.log (1 - y) / π :=
      div_pos (neg_pos.2 (Real.log_neg (by linarith) (by linarith))) hπ
    refine hlowR _ hx0 (fun h => hyL ⟨_, h, one_sub_exp_neg_log hlt⟩) ?_
    obtain ⟨y', hy', hyy, hy'J, hne⟩ := hex
    simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or]
      at hy'J
    have hy'1 : y' < 1 := hyy.trans_lt hlt
    rw [leftEndHData_of_lt hy'1] at hne
    exact ⟨_, div_pos (neg_pos.2 (Real.log_neg (by linarith) (by linarith))) hπ,
      neg_log_one_sub_div_pi_le hlt hyy, fun h => hy'J.2.1 ⟨_, h, one_sub_exp_neg_log hy'1⟩, hne⟩
  · rw [leftEndHData_of_gt hgt]
    have := hU _ fun h => hyU ⟨_, h, one_add_exp_neg_log hgt⟩
    linarith

/-- In the chart `1 − e^{−πz}`, a point right of `1` (the image of `∂_U𝒮`) carries a value `≠ Λ` when every upper
height is at least `Λ` and `k > 4`. -/
theorem leftEndHData_ne_of_one_lt {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} (hk4 : 4 < k)
    (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x) {y : ℝ} (hy : 1 < y)
    (hyJ : y ∉ leftEndHJumps JL JU) : leftEndHData k bL bU y ≠ sleLambda k := by
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  rw [leftEndHData_of_gt hy]
  have h1 := hU _ fun h => hyJ.2.2 ⟨_, h, one_add_exp_neg_log hy⟩
  have h2 := pi_mul_chiC_neg hk4
  exact ne_of_gt (by linarith)

/-- **Lemma 4.3, `a ≥ Λ`, boundary part; Aux. lemma 22, all upper heights `≥ Λ`, boundary part — for every
`k > 0`.** For the flow line from `0` towards the left strip end, with every upper height at least `Λ` and lower
data satisfying the condition of this file: almost surely the lifetime is infinite and the flow line never hits the
image `(1, ∞)` of `∂_U𝒮`. -/
theorem ae_notMem_upper_of_isLeftEndFlowLine_basic (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1 := by
  rcases le_or_gt k 4 with hk4 | hk4
  · filter_upwards [ae_notMem_upper_of_isLeftEndFlowLine hk hbL hbU hU
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl]
      with ω hω
    exact ⟨hω.1, fun t => (hω.2 t).1⟩
  · filter_upwards [IsFlowLine.ae_trace_ne_of_nonzero hk
      (isPiecewiseConstantBoundaryData_leftEndHData hbL hbU)
      (fun y hy hyJ hex => leftEndHData_le_of_neg_of_exists hlowL hy hyJ hex)
      (fun y hy hyJ hex => le_leftEndHData_of_pos_of_exists hU hlowR hy hyJ hex) hfl] with ω hω
    refine ⟨hω.1, fun t => ?_⟩
    rintro ⟨x, hx, hxt⟩
    have hx1 : 1 < x := hx
    obtain ⟨y', h1, h2, hJ⟩ := exists_mem_Ioo_not_mem (leftEndHJumps JL JU) hx1
    exact (hω.2 t).2 x (by linarith) ⟨y', by linarith, h2.le, hJ,
      leftEndHData_ne_of_one_lt hk4 hU h1 hJ⟩ hxt.symm

/-- `‖w‖ → ∞` in the chart `1 − e^{−πz}` is `Re(−log(1 − w)/π) → −∞`: the strip point tends to the left end. -/
theorem tendsto_re_leftEndInv {f : ℝ≥0 → ℂ} (hf : Tendsto (fun t => ‖f t‖) atTop atTop) :
    Tendsto (fun t => (-Complex.log (1 - f t) / π).re) atTop atBot := by
  have hre : ∀ w : ℂ, (-Complex.log (1 - w) / π).re = -(Real.log ‖1 - w‖ / π) := fun w => by
    rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, neg_div]
  simp only [hre]
  refine tendsto_neg_atTop_atBot.comp (Tendsto.atTop_div_const Real.pi_pos
    (Real.tendsto_log_atTop.comp ?_))
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) hf)
  have := norm_sub_norm_le (f t) 1
  rw [norm_one, norm_sub_rev] at this
  linarith

/-- **Lemma 4.3, `a ≥ Λ`; Aux. lemma 22, all upper heights `≥ Λ` — for every `k > 0`** (from Aux. lemma 7): almost
surely the lifetime is infinite, the flow line never hits `∂_U𝒮`, and it accumulates at `−∞`. -/
theorem lemma43_left_of_aux7_basic (h7 : Aux7Statement.{u} k) (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (-Complex.log (1 - η ω t) / π).re) atTop atBot := by
  rcases le_or_gt k 4 with hk4 | hk4
  · exact lemma43_left_of_aux7 h7 hk hbL hbU hU
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl
  · filter_upwards [ae_notMem_upper_of_isLeftEndFlowLine_basic hk hbL hbU hU hlowL hlowR hfl,
      IsFlowLine.ae_tendsto_of_aux7_of_nonzero h7 hk
        (isPiecewiseConstantBoundaryData_leftEndHData hbL hbU)
        (fun y hy hyJ hex => leftEndHData_le_of_neg_of_exists hlowL hy hyJ hex)
        (fun y hy hyJ hex => le_leftEndHData_of_pos_of_exists hU hlowR hy hyJ hex) hfl]
      with ω h1 h2
    exact ⟨h1.1, h1.2, h2.2.2, tendsto_re_leftEndInv h2.2.2⟩

/-! ### The chart `(e^{πz} − 1)/(e^{πz} + q)` -/

section StripQ

variable {q : ℝ}

/-- The lower-line coordinate `log((1 + q y)/(1 − y))/π` is monotone on `(−1/q, 1)`. -/
theorem stripQ_lower_coord_le (hq : 0 < q) {y y' : ℝ} (h1 : -(1 / q) < y) (h2' : y' < 1)
    (hyy : y ≤ y') :
    Real.log ((1 + q * y) / (1 - y)) / π ≤ Real.log ((1 + q * y') / (1 - y')) / π := by
  have hqy : 0 < 1 + q * y := by linarith [(neg_one_lt_mul_iff hq).1 h1]
  have hd : 0 < 1 - y := by linarith
  have hd' : 0 < 1 - y' := by linarith
  refine div_le_div_of_nonneg_right (Real.log_le_log (div_pos hqy hd) ?_) Real.pi_pos.le
  rw [div_le_div_iff₀ hd hd']
  have hdiff : (1 + q * y') * (1 - y) - (1 + q * y) * (1 - y') = (y' - y) * (1 + q) := by ring
  nlinarith [mul_nonneg (sub_nonneg.2 hyy) (le_of_lt (by linarith : (0 : ℝ) < 1 + q))]

theorem stripQ_lower_coord_neg (hq : 0 < q) {y : ℝ} (h1 : -(1 / q) < y) (hy : y < 0) :
    Real.log ((1 + q * y) / (1 - y)) / π < 0 := by
  have hqy : 0 < 1 + q * y := by linarith [(neg_one_lt_mul_iff hq).1 h1]
  have hd : 0 < 1 - y := by linarith
  have hlt1 : (1 + q * y) / (1 - y) < 1 := by
    rw [div_lt_one hd]
    linarith [mul_neg_of_pos_of_neg hq hy]
  exact div_neg_of_neg_of_pos (Real.log_neg (div_pos hqy hd) hlt1) Real.pi_pos

theorem stripQ_lower_coord_pos (hq : 0 < q) {y : ℝ} (hy : 0 < y) (h2 : y < 1) :
    0 < Real.log ((1 + q * y) / (1 - y)) / π := by
  have hd : 0 < 1 - y := by linarith
  have hlt : 1 < (1 + q * y) / (1 - y) := by
    rw [one_lt_div hd]
    linarith [mul_pos hq hy]
  exact div_pos (Real.log_pos hlt) Real.pi_pos

/-- The left condition for the transported data of the chart `(e^{πz} − 1)/(e^{πz} + q)`, when the upper heights
left of `z₀` are at most `−Λ`. -/
theorem stripQHData_le_of_neg_of_exists (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hUle : ∀ x : ℝ, x ∉ JU → Real.exp (π * x) < q → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0) (hyJ : y ∉ stripQHJumps q JL JU)
    (hex : ∃ y', y ≤ y' ∧ y' < 0 ∧ y' ∉ stripQHJumps q JL JU ∧
      stripQHData k q bL bU y' ≠ -sleLambda k) :
    stripQHData k q bL bU y ≤ -sleLambda k + π * chiC k := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨hyq, hy1, hyL, hyU⟩ := hyJ
  rcases lt_or_gt_of_ne hyq with hlt | hgt
  · rw [stripQHData_of_lt hlt]
    have hpos := stripQ_upper_left_pos hq hlt
    have hy1' : y - 1 < 0 := by linarith
    have hexp : Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) < q := by
      rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, div_lt_iff_of_neg hy1']
      linarith
    have := hUle _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
    linarith
  · have hy1' : y < 1 := by linarith
    rw [stripQHData_of_mem hgt hy1']
    refine hlowL _ (stripQ_lower_coord_neg hq hgt hy)
      (fun h => hyL ⟨_, h, stripQ_lower_inv hq hgt hy1'⟩) ?_
    obtain ⟨y', hyy, hy', hy'J, hne⟩ := hex
    simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or]
      at hy'J
    have hgt' : -(1 / q) < y' := hgt.trans_le hyy
    have hy'1 : y' < 1 := by linarith
    rw [stripQHData_of_mem hgt' hy'1] at hne
    exact ⟨_, stripQ_lower_coord_le hq hgt hy'1 hyy, stripQ_lower_coord_neg hq hgt' hy',
      fun h => hy'J.2.2.1 ⟨_, h, stripQ_lower_inv hq hgt' hy'1⟩, hne⟩

/-- The right condition for the transported data of the chart `(e^{πz} − 1)/(e^{πz} + q)`, when the upper heights
right of `z₀` are at least `Λ`. -/
theorem le_stripQHData_of_pos_of_exists (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hUge : ∀ x : ℝ, x ∉ JU → q < Real.exp (π * x) → sleLambda k ≤ bU x)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y) (hyJ : y ∉ stripQHJumps q JL JU)
    (hex : ∃ y', 0 < y' ∧ y' ≤ y ∧ y' ∉ stripQHJumps q JL JU ∧
      stripQHData k q bL bU y' ≠ sleLambda k) :
    sleLambda k - π * chiC k ≤ stripQHData k q bL bU y := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hy1, hyL, hyU⟩ := hyJ
  have hgt : -(1 / q) < y := (neg_one_div_neg hq).trans hy
  rcases lt_or_gt_of_ne hy1 with hlt1 | hgt1
  · rw [stripQHData_of_mem hgt hlt1]
    refine hlowR _ (stripQ_lower_coord_pos hq hy hlt1)
      (fun h => hyL ⟨_, h, stripQ_lower_inv hq hgt hlt1⟩) ?_
    obtain ⟨y', hy', hyy, hy'J, hne⟩ := hex
    simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or]
      at hy'J
    have hgt' : -(1 / q) < y' := (neg_one_div_neg hq).trans hy'
    have hy'1 : y' < 1 := hyy.trans_lt hlt1
    rw [stripQHData_of_mem hgt' hy'1] at hne
    exact ⟨_, stripQ_lower_coord_pos hq hy' hy'1, stripQ_lower_coord_le hq hgt' hlt1 hyy,
      fun h => hy'J.2.2.1 ⟨_, h, stripQ_lower_inv hq hgt' hy'1⟩, hne⟩
  · rw [stripQHData_of_gt hq hgt1]
    have hpos := stripQ_upper_right_pos hq hgt1
    have hexp : q < Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) := by
      rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, lt_div_iff₀ (by linarith)]
      linarith
    have := hUge _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
    linarith

/-- On the image of the upper arc left of `z₀` the transported value is `≠ −Λ` for `k > 4`. -/
theorem stripQHData_ne_of_lt (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} (hk4 : 4 < k)
    (hUle : ∀ x : ℝ, x ∉ JU → Real.exp (π * x) < q → bU x ≤ -sleLambda k) {y : ℝ}
    (hy : y < -(1 / q)) (hyJ : y ∉ stripQHJumps q JL JU) :
    stripQHData k q bL bU y ≠ -sleLambda k := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hy1, -, hyU⟩ := hyJ
  rw [stripQHData_of_lt hy]
  have hpos := stripQ_upper_left_pos hq hy
  have hy1' : y - 1 < 0 := by linarith [neg_one_div_neg hq]
  have hexp : Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) < q := by
    rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, div_lt_iff_of_neg hy1']
    linarith [(lt_neg_one_div_iff hq).1 hy]
  have h1 := hUle _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
  have h2 := pi_mul_chiC_neg hk4
  exact ne_of_lt (by linarith)

/-- On the image of the upper arc right of `z₀` the transported value is `≠ Λ` for `k > 4`. -/
theorem stripQHData_ne_of_gt (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} (hk4 : 4 < k)
    (hUge : ∀ x : ℝ, x ∉ JU → q < Real.exp (π * x) → sleLambda k ≤ bU x) {y : ℝ} (hy : 1 < y)
    (hyJ : y ∉ stripQHJumps q JL JU) : stripQHData k q bL bU y ≠ sleLambda k := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hy1, -, hyU⟩ := hyJ
  rw [stripQHData_of_gt hq hy]
  have hpos := stripQ_upper_right_pos hq hy
  have hexp : q < Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) := by
    rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, lt_div_iff₀ (by linarith)]
    linarith
  have h1 := hUge _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
  have h2 := pi_mul_chiC_neg hk4
  exact ne_of_gt (by linarith)

end StripQ

/-- **Lemma 4.5, boundary part — for every `k > 0`, including `k = κ′ > 4` with the basic lower constants.** For the
flow line from `0` towards `z₀ = x₀ + i`, with upper heights at most `−Λ` left of `z₀` and at least `Λ` right of
`z₀` and lower data satisfying the condition of this file: almost surely the lifetime is infinite and the flow line
never hits the images `(−∞, −e^{−πx₀})` and `(1, ∞)` of the two open upper arcs. -/
theorem ae_notMem_upper_of_isStripQFlowLine_basic (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0,
      η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1) := by
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  have hUle' : ∀ x : ℝ, x ∉ JU → Real.exp (π * x) < Real.exp (π * x₀) → bU x ≤ -sleLambda k :=
    fun x hx hlt => hUle x hx (exp_lt_exp_mul_pi_iff.1 hlt)
  have hUge' : ∀ x : ℝ, x ∉ JU → Real.exp (π * x₀) < Real.exp (π * x) → sleLambda k ≤ bU x :=
    fun x hx hlt => hUge x hx (exp_lt_exp_mul_pi_iff.1 hlt)
  rcases le_or_gt k 4 with hk4 | hk4
  · filter_upwards [ae_notMem_upper_of_isStripQFlowLine hk hbL hbU hUle hUge
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl]
      with ω hω
    exact ⟨hω.1, fun t => (hω.2 t).1⟩
  · filter_upwards [IsFlowLine.ae_trace_ne_of_nonzero hk
      (isPiecewiseConstantBoundaryData_stripQHData hq hbL hbU)
      (fun y hy hyJ hex => stripQHData_le_of_neg_of_exists hq hUle' hlowL hy hyJ hex)
      (fun y hy hyJ hex => le_stripQHData_of_pos_of_exists hq hUge' hlowR hy hyJ hex) hfl]
      with ω hω
    refine ⟨hω.1, fun t => ?_⟩
    rintro ⟨x, hx, hxt⟩
    rcases hx with hx | hx
    · have hx' : x < -(1 / Real.exp (π * x₀)) := hx
      obtain ⟨y', h1, h2, hJ⟩ :=
        exists_mem_Ioo_not_mem (stripQHJumps (Real.exp (π * x₀)) JL JU) hx'
      have h0 := neg_one_div_neg hq
      exact (hω.2 t).1 x (by linarith) ⟨y', h1.le, by linarith, hJ,
        stripQHData_ne_of_lt hq hk4 hUle' h2 hJ⟩ hxt.symm
    · have hx' : 1 < x := hx
      obtain ⟨y', h1, h2, hJ⟩ :=
        exists_mem_Ioo_not_mem (stripQHJumps (Real.exp (π * x₀)) JL JU) hx'
      exact (hω.2 t).2 x (by linarith) ⟨y', by linarith, h2.le, hJ,
        stripQHData_ne_of_gt hq hk4 hUge' h1 hJ⟩ hxt.symm

/-- **Lemma 4.5 — for every `k > 0`** (from Aux. lemma 7): almost surely the lifetime is infinite, the flow line never
hits either open upper arc, and it tends to its target `z₀` (in the chart, `‖η(t)‖ → ∞`). -/
theorem lemma45_of_aux7_basic (h7 : Aux7Statement.{u} k) (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  have hUle' : ∀ x : ℝ, x ∉ JU → Real.exp (π * x) < Real.exp (π * x₀) → bU x ≤ -sleLambda k :=
    fun x hx hlt => hUle x hx (exp_lt_exp_mul_pi_iff.1 hlt)
  have hUge' : ∀ x : ℝ, x ∉ JU → Real.exp (π * x₀) < Real.exp (π * x) → sleLambda k ≤ bU x :=
    fun x hx hlt => hUge x hx (exp_lt_exp_mul_pi_iff.1 hlt)
  rcases le_or_gt k 4 with hk4 | hk4
  · exact lemma45_of_aux7 h7 hk hbL hbU hUle hUge
      (fun x hx hxJ => le_of_forall_exists_ne_left_of_le_four hk hk4 hlowL hx hxJ)
      (fun x hx hxJ => le_of_forall_exists_ne_right_of_le_four hk hk4 hlowR hx hxJ) hfl
  · filter_upwards [ae_notMem_upper_of_isStripQFlowLine_basic hk hbL hbU hUle hUge hlowL hlowR hfl,
      IsFlowLine.ae_tendsto_of_aux7_of_nonzero h7 hk
        (isPiecewiseConstantBoundaryData_stripQHData hq hbL hbU)
        (fun y hy hyJ hex => stripQHData_le_of_neg_of_exists hq hUle' hlowL hy hyJ hex)
        (fun y hy hyJ hex => le_stripQHData_of_pos_of_exists hq hUge' hlowR hy hyJ hex) hfl]
      with ω h1 h2
    exact ⟨h1.1, h1.2, h2.2.2⟩

/-- **Lemma 4.5 in strip coordinates — for every `k > 0`** (from Aux. lemma 7): the strip curve
`stripQInv q ∘ η` exits the strip at `z₀`. -/
theorem lemma45_strip_of_aux7_basic (h7 : Aux7Statement.{u} k) (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => stripQInv (Real.exp (π * x₀)) (η ω t)) atTop (𝓝 ((x₀ : ℂ) + I)) := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  filter_upwards [lemma45_of_aux7_basic h7 hk hbL hbU hUle hUge hlowL hlowR hfl, htr,
    hev.2.2.2.2] with ω h1 hω hp
  obtain ⟨hζ, havoid, hlim⟩ := h1
  rw [hζ] at hω hp
  have hW := continuous_toNNReal_of_isIntegratedSLEPath hp
  exact ⟨hζ, havoid, tendsto_stripQInv hlim (im_nonneg_of_isGeneratingTrace hW hp.1 hω)⟩

end Sec4

end InteractingSLE
