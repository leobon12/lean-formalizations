import HigherDimLQGContinuity.Grid.Arithmetic
import HigherDimLQGContinuity.Param.Interval

/-!
# Continuous interpolants of logarithmic metric profiles

These are the finite hat-function sums of Part C `c:def-interp`.  They are defined
on all real parameters by clamping to the window.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

def posClip (lo hi ξ : ℝ) : ℝ := min (max ξ lo) hi

theorem continuous_posClip (lo hi : ℝ) : Continuous (posClip lo hi) :=
  (continuous_id.max continuous_const).min continuous_const

/-- The hat weight of the `m`-th node of level `j`. -/
def posHat (lo hi : ℝ) (j m : ℕ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |posClip lo hi ξ - posNode lo hi j m| / posWidth lo hi j)

theorem continuous_posHat (lo hi : ℝ) (j m : ℕ) : Continuous (posHat lo hi j m) := by
  unfold posHat
  exact continuous_const.max
    (continuous_const.sub (((continuous_posClip lo hi).sub continuous_const).abs.div_const _))

theorem posHat_nonneg (lo hi : ℝ) (j m : ℕ) (ξ : ℝ) : 0 ≤ posHat lo hi j m ξ :=
  le_max_left _ _

/-- The finite piecewise linear interpolant in `C(ℝᵈ × ℝᵈ, ℝ)`. -/
def interpProfile (d : ℕ) (lo hi : ℝ) (j : ℕ) (ξ : ℝ) (g : DistRd d) :
    C(HigherDimLFPP.Rd d × HigherDimLFPP.Rd d, ℝ) :=
  ∑ m ∈ Finset.range (2 ^ posLevel j + 1),
    posHat lo hi j m ξ • gridProfile d (posNode lo hi j m) g

theorem continuous_interpProfile (d : ℕ) (lo hi : ℝ) (j : ℕ) (g : DistRd d) :
    Continuous (fun ξ => interpProfile d lo hi j ξ g) := by
  unfold interpProfile
  apply continuous_finsetSum
  intro m _
  exact (continuous_posHat lo hi j m).smul continuous_const

theorem measurable_interpProfile (d : ℕ) (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) (j : ℕ) :
    Measurable (Function.uncurry (interpProfile d lo hi j)) := by
  have hsub : Ioc (0 : ℝ) hi ⊆ subcritSet d :=
    (gap24 (by omega : 2 ≤ d) ⟨hhi.1, hhi.2⟩).choose_spec.2.2.2.1
  have hnode (m : ℕ) (hm : m ∈ Finset.range (2 ^ posLevel j + 1)) :
      posNode lo hi j m ∈ subcritSet d := by
    have hm' : m ≤ 2 ^ posLevel j := by
      simp only [Finset.mem_range] at hm
      omega
    have hmem := posNode_mem hlohi (j := j) (m := m) hm'
    exact hsub ⟨hlo.trans_le hmem.1, hmem.2⟩
  apply measurable_uncurry_of_continuous_of_measurable
  · exact fun g => continuous_interpProfile d lo hi j g
  · intro ξ
    unfold interpProfile
    apply Finset.measurable_sum
    intro m hm
    simpa only [Pi.smul_def] using
      (measurable_gridProfile hd (hnode m hm)).const_smul (posHat lo hi j m ξ)

theorem interpProfile_nonneg (d : ℕ) (lo hi : ℝ) (j : ℕ) (ξ : ℝ) (g : DistRd d) :
    0 ≤ interpProfile d lo hi j ξ g := by
  intro p
  change (0 : C(HigherDimLFPP.Rd d × HigherDimLFPP.Rd d, ℝ)) p ≤
    (∑ m ∈ Finset.range (2 ^ posLevel j + 1),
      posHat lo hi j m ξ • gridProfile d (posNode lo hi j m) g) p
  simp only [ContinuousMap.zero_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro m _
  exact mul_nonneg (posHat_nonneg _ _ _ _ _) (gridProfile_nonneg d _ g p)

theorem posClip_eq_self {lo hi ξ : ℝ} (hξ : ξ ∈ Icc lo hi) : posClip lo hi ξ = ξ := by
  unfold posClip
  rw [max_eq_left hξ.1, min_eq_left hξ.2]

theorem posClip_mem {lo hi ξ : ℝ} (h : lo ≤ hi) : posClip lo hi ξ ∈ Icc lo hi := by
  unfold posClip
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

theorem interpProfile_clip (d : ℕ) {lo hi : ℝ} (h : lo ≤ hi)
    (j : ℕ) (ξ : ℝ) (g : DistRd d) :
    interpProfile d lo hi j (posClip lo hi ξ) g = interpProfile d lo hi j ξ g := by
  unfold interpProfile posHat
  rw [posClip_eq_self (posClip_mem h)]

theorem posNode_gap_ge {lo hi : ℝ} (h : lo < hi) (j : ℕ) {m n : ℕ} (hmn : m ≠ n) :
    posWidth lo hi j ≤ |posNode lo hi j m - posNode lo hi j n| := by
  let w := posWidth lo hi j
  have hw : 0 < w := posWidth_pos h j
  have heq : posNode lo hi j m - posNode lo hi j n = ((m : ℝ) - n) * w := by
    unfold posNode
    ring
  rw [heq, abs_mul, abs_of_pos hw]
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have hdiff : ((m : ℝ) - n) ≤ -1 := by linarith
    rw [abs_of_nonpos (by linarith : (m : ℝ) - n ≤ 0)]
    have := mul_le_mul_of_nonneg_right hdiff hw.le
    nlinarith
  · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hgt
    have hdiff : 1 ≤ (m : ℝ) - n := by linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ) - n)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff hw.le

theorem posHat_at_node_same {lo hi : ℝ} (h : lo < hi) (j m : ℕ)
    (hm : m ≤ 2 ^ posLevel j) :
    posHat lo hi j m (posNode lo hi j m) = 1 := by
  have hmem := posNode_mem h (j := j) (m := m) hm
  simp only [posHat, posClip_eq_self hmem, sub_self, abs_zero, zero_div, sub_zero]
  norm_num

theorem posHat_at_node_other {lo hi : ℝ} (h : lo < hi) (j : ℕ) {m n : ℕ}
    (hn : n ≤ 2 ^ posLevel j) (hmn : m ≠ n) :
    posHat lo hi j m (posNode lo hi j n) = 0 := by
  have hmem := posNode_mem h (j := j) (m := n) hn
  have hw : 0 < posWidth lo hi j := posWidth_pos h j
  have hgap : posWidth lo hi j ≤ |posNode lo hi j n - posNode lo hi j m| :=
    posNode_gap_ge h j hmn.symm
  have hdiv : 1 ≤ |posNode lo hi j n - posNode lo hi j m| / posWidth lo hi j :=
    (le_div_iff₀ hw).2 (by simpa only [one_mul] using hgap)
  unfold posHat
  rw [posClip_eq_self hmem, max_eq_left (by linarith :
    1 - |posNode lo hi j n - posNode lo hi j m| / posWidth lo hi j ≤ 0)]

/-- The interpolant agrees exactly with the chosen profile at every node of its level. -/
theorem interpProfile_node (d : ℕ) {lo hi : ℝ} (h : lo < hi) (j : ℕ)
    {m : ℕ} (hm : m ≤ 2 ^ posLevel j) (g : DistRd d) :
    interpProfile d lo hi j (posNode lo hi j m) g = gridProfile d (posNode lo hi j m) g := by
  unfold interpProfile
  have hmem : m ∈ Finset.range (2 ^ posLevel j + 1) := by
    simp only [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single m]
  · rw [posHat_at_node_same h j m hm, one_smul]
  · intro n _ hnm
    rw [posHat_at_node_other h j hm hnm, zero_smul]
  · exact fun hn => (hn hmem).elim

theorem interpProfile_node_refined (d : ℕ) {lo hi : ℝ} (h : lo < hi)
    {j i m : ℕ} (hji : j ≤ i) (hm : m ≤ 2 ^ posLevel j) (g : DistRd d) :
    interpProfile d lo hi i (posNode lo hi j m) g = gridProfile d (posNode lo hi j m) g := by
  obtain ⟨n, hn, heq⟩ := exists_posNode_refine (lo := lo) (hi := hi) hji hm
  rw [← heq]
  exact interpProfile_node d h i hn g

theorem posNode_mono {lo hi : ℝ} (h : lo < hi) (j : ℕ) :
    Monotone (posNode lo hi j) := by
  intro m n hmn
  unfold posNode
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simpa only [add_comm] using
    (add_le_add_left (mul_le_mul_of_nonneg_right hcast (posWidth_pos h j).le) lo)

theorem posNode_step (lo hi : ℝ) (j m : ℕ) :
    posNode lo hi j (m + 1) = posNode lo hi j m + posWidth lo hi j := by
  unfold posNode
  push_cast
  ring

theorem posHat_zero_of_gap {lo hi ξ : ℝ} (h : lo < hi) (j n : ℕ)
    (hξ : ξ ∈ Icc lo hi)
    (hgap : posWidth lo hi j ≤ |ξ - posNode lo hi j n|) :
    posHat lo hi j n ξ = 0 := by
  have hw := posWidth_pos h j
  have hdiv : 1 ≤ |ξ - posNode lo hi j n| / posWidth lo hi j :=
    (le_div_iff₀ hw).2 (by simpa only [one_mul] using hgap)
  unfold posHat
  rw [posClip_eq_self hξ, max_eq_left (by linarith :
    1 - |ξ - posNode lo hi j n| / posWidth lo hi j ≤ 0)]

/-- Away from the two endpoints of a grid cell all hat weights vanish. -/
theorem posHat_zero_outside_cell {lo hi ξ : ℝ} (h : lo < hi) (j m n : ℕ)
    (hξ : ξ ∈ Icc lo hi)
    (hcell : ξ ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)))
    (hnm : n ≠ m) (hnm1 : n ≠ m + 1) :
    posHat lo hi j n ξ = 0 := by
  have hw := posWidth_pos h j
  rcases hcell with ⟨hcellL, hcellU⟩
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hgap := posNode_gap_ge h j (show n ≠ m by omega)
    have horder := posNode_mono h j (show n ≤ m by omega)
    have hgap' : posWidth lo hi j ≤ posNode lo hi j m - posNode lo hi j n := by
      rw [abs_of_nonpos (by linarith)] at hgap
      linarith
    apply posHat_zero_of_gap h j n hξ
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hgt' : m + 1 < n := by omega
    have hgap := posNode_gap_ge h j (show m + 1 ≠ n by omega)
    have horder := posNode_mono h j (show m + 1 ≤ n by omega)
    have hgap' : posWidth lo hi j ≤ posNode lo hi j n - posNode lo hi j (m + 1) := by
      rw [abs_of_nonpos (by linarith)] at hgap
      linarith
    apply posHat_zero_of_gap h j n hξ
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem posHat_lower_cell {lo hi ξ : ℝ} (h : lo < hi) (j m : ℕ)
    (hξ : ξ ∈ Icc lo hi)
    (hcell : ξ ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1))) :
    posHat lo hi j m ξ =
      1 - (ξ - posNode lo hi j m) / posWidth lo hi j := by
  have hw := posWidth_pos h j
  have hstep := posNode_step lo hi j m
  have hα : (ξ - posNode lo hi j m) / posWidth lo hi j ≤ 1 := by
    apply (div_le_iff₀ hw).2
    linarith [hcell.2]
  unfold posHat
  rw [posClip_eq_self hξ, abs_of_nonneg (by linarith [hcell.1]),
    max_eq_right (by linarith)]

theorem posHat_upper_cell {lo hi ξ : ℝ} (h : lo < hi) (j m : ℕ)
    (hξ : ξ ∈ Icc lo hi)
    (hcell : ξ ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1))) :
    posHat lo hi j (m + 1) ξ =
      (ξ - posNode lo hi j m) / posWidth lo hi j := by
  have hw := posWidth_pos h j
  have hstep := posNode_step lo hi j m
  have hβ : (posNode lo hi j (m + 1) - ξ) / posWidth lo hi j ≤ 1 := by
    apply (div_le_iff₀ hw).2
    linarith [hcell.1]
  unfold posHat
  rw [posClip_eq_self hξ, abs_of_nonpos (by linarith [hcell.2]),
    show -(ξ - posNode lo hi j (m + 1)) = posNode lo hi j (m + 1) - ξ by ring,
    max_eq_right (by linarith)]
  have hw0 : posWidth lo hi j ≠ 0 := hw.ne'
  field_simp
  linarith

/-- Within one cell the entire interpolant is the affine combination of its two
endpoint profiles. -/
theorem interpProfile_cell (d : ℕ) {lo hi ξ : ℝ} (h : lo < hi) (j m : ℕ)
    (hξ : ξ ∈ Icc lo hi) (hm : m < 2 ^ posLevel j)
    (hcell : ξ ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)))
    (g : DistRd d) :
    interpProfile d lo hi j ξ g =
      (1 - (ξ - posNode lo hi j m) / posWidth lo hi j) •
        gridProfile d (posNode lo hi j m) g +
      ((ξ - posNode lo hi j m) / posWidth lo hi j) •
        gridProfile d (posNode lo hi j (m + 1)) g := by
  let S := Finset.range (2 ^ posLevel j + 1)
  have hmS : m ∈ S := by simp only [S, Finset.mem_range]; omega
  have hm1S : m + 1 ∈ S := by simp only [S, Finset.mem_range]; omega
  have hpair : ({m, m + 1} : Finset ℕ) ⊆ S := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact hmS
    · exact hm1S
  have hzero (n : ℕ) (hn : n ∈ S) (hnot : n ∉ ({m, m + 1} : Finset ℕ)) :
      posHat lo hi j n ξ • gridProfile d (posNode lo hi j n) g = 0 := by
    have hne : n ≠ m ∧ n ≠ m + 1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
    rw [posHat_zero_outside_cell h j m n hξ hcell hne.1 hne.2, zero_smul]
  unfold interpProfile
  change (∑ n ∈ S, posHat lo hi j n ξ • gridProfile d (posNode lo hi j n) g) = _
  rw [← Finset.sum_subset hpair hzero]
  simp [Finset.sum_insert, Finset.sum_singleton]
  rw [posHat_lower_cell h j m hξ hcell, posHat_upper_cell h j m hξ hcell]

/-- A pointwise convex combination preserves a common local sup-distance bound. -/
theorem supDistLU_convex_le (d : ℕ) {R δ a : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {F A B : C(HigherDimLFPP.Rd d × HigherDimLFPP.Rd d, ℝ)}
    (hFA : supDistLU d R F A ≤ ENNReal.ofReal δ)
    (hFB : supDistLU d R F B ≤ ENNReal.ofReal δ) :
    supDistLU d R F ((1 - a) • A + a • B) ≤ ENNReal.ofReal δ := by
  apply endpt_supDistLU_le_iff.2
  intro p hp
  have hA := endpt_abs_sub_le_of_supDistLU_le hδ hFA hp
  have hB := endpt_abs_sub_le_of_supDistLU_le hδ hFB hp
  have hreal : |F p - ((1 - a) • A + a • B) p| ≤ δ := by
    have heq : F p - ((1 - a) • A + a • B) p =
        (1 - a) * (F p - A p) + a * (F p - B p) := by
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    calc
      |(1 - a) * (F p - A p) + a * (F p - B p)| ≤
          |(1 - a) * (F p - A p)| + |a * (F p - B p)| := abs_add_le _ _
      _ = (1 - a) * |F p - A p| + a * |F p - B p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - a), abs_of_nonneg ha]
      _ ≤ δ := by nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (sub_nonneg.2 hA),
        mul_nonneg ha (sub_nonneg.2 hB)]
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hreal

theorem supDistLU_convex_pair_le (d : ℕ) {R δ a : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {F₀ F₁ G₀ G₁ : C(HigherDimLFPP.Rd d × HigherDimLFPP.Rd d, ℝ)}
    (h₀ : supDistLU d R F₀ G₀ ≤ ENNReal.ofReal δ)
    (h₁ : supDistLU d R F₁ G₁ ≤ ENNReal.ofReal δ) :
    supDistLU d R ((1 - a) • F₀ + a • F₁) ((1 - a) • G₀ + a • G₁) ≤
      ENNReal.ofReal δ := by
  apply endpt_supDistLU_le_iff.2
  intro p hp
  have hA := endpt_abs_sub_le_of_supDistLU_le hδ h₀ hp
  have hB := endpt_abs_sub_le_of_supDistLU_le hδ h₁ hp
  have hreal : |((1 - a) • F₀ + a • F₁) p - ((1 - a) • G₀ + a • G₁) p| ≤ δ := by
    have heq : ((1 - a) • F₀ + a • F₁) p - ((1 - a) • G₀ + a • G₁) p =
        (1 - a) * (F₀ p - G₀ p) + a * (F₁ p - G₁ p) := by
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    calc
      |(1 - a) * (F₀ p - G₀ p) + a * (F₁ p - G₁ p)| ≤
          |(1 - a) * (F₀ p - G₀ p)| + |a * (F₁ p - G₁ p)| := abs_add_le _ _
      _ = (1 - a) * |F₀ p - G₀ p| + a * |F₁ p - G₁ p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - a), abs_of_nonneg ha]
      _ ≤ δ := by nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (sub_nonneg.2 hA),
        mul_nonneg ha (sub_nonneg.2 hB)]
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Restricting an interpolant to a subinterval of one grid cell is affine. -/
theorem interpProfile_affine_on_cell (d : ℕ) {lo hi x y z a : ℝ}
    (h : lo < hi) (j m : ℕ) (hm : m < 2 ^ posLevel j)
    (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) (hz : z ∈ Icc lo hi)
    (hxc : x ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)))
    (hyc : y ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)))
    (hzc : z ∈ Icc (posNode lo hi j m) (posNode lo hi j (m + 1)))
    (hza : z = (1 - a) * x + a * y) (g : DistRd d) :
    interpProfile d lo hi j z g =
      (1 - a) • interpProfile d lo hi j x g + a • interpProfile d lo hi j y g := by
  rw [interpProfile_cell d h j m hz hm hzc g,
    interpProfile_cell d h j m hx hm hxc g,
    interpProfile_cell d h j m hy hm hyc g]
  ext p
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hw : posWidth lo hi j ≠ 0 := (posWidth_pos h j).ne'
  rw [hza]
  field_simp
  ring

end HigherDimLQGContinuity
