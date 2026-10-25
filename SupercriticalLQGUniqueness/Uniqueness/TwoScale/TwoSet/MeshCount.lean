import LQGMetric.Papers.CONF.S3L35




 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.TwoSet

 
def meshStep (ε R : ℝ) : ℝ := ε ^ 2 * R / 8

 
def candidateScale (R : ℝ) (j : ℕ) : ℝ := R / (16 : ℝ) ^ j

 
def referenceScale (R : ℝ) (j : ℕ) : ℝ := 3 * candidateScale R j

theorem candidateScale_pos {R : ℝ} (hR : 0 < R) (j : ℕ) :
    0 < candidateScale R j := by
  unfold candidateScale
  positivity

theorem referenceScale_ratio {R : ℝ} (hR : 0 < R) (j : ℕ) :
    referenceScale R (j + 1) / referenceScale R j = (1 : ℝ) / 16 := by
  unfold referenceScale candidateScale
  rw [pow_succ]
  have hp : (16 : ℝ) ^ j ≠ 0 := by positivity
  field_simp

 

theorem candidateScale_strict_collar {R : ℝ} (hR : 0 < R) (j : ℕ) :
    referenceScale R j / 7 < candidateScale R j / 2 ∧
      2 * candidateScale R j < 3 * referenceScale R j / 4 := by
  have hs := candidateScale_pos hR j
  unfold referenceScale
  constructor <;> linarith

 
def meshSites (ε R B : ℝ) : Finset ℂ :=
  (LQGMetric.CONF.gridBox (meshStep ε R) (B * R) 0).image
    fun k => (⟨(k.1 : ℝ) * meshStep ε R,
      (k.2 : ℝ) * meshStep ε R⟩ : ℂ)

 
def nearestGrid (m : ℝ) (x : ℂ) : ℂ :=
  ⟨(⌊x.re / m + 1 / 2⌋ : ℤ) * m,
    (⌊x.im / m + 1 / 2⌋ : ℤ) * m⟩

theorem nearestGrid_norm_lt {m : ℝ} (hm : 0 < m) (x : ℂ) :
    ‖x - nearestGrid m x‖ < m := by
  let a : ℤ := ⌊x.re / m + 1 / 2⌋
  let b : ℤ := ⌊x.im / m + 1 / 2⌋
  have ha₁ := Int.floor_le (x.re / m + 1 / 2)
  have ha₂ := Int.lt_floor_add_one (x.re / m + 1 / 2)
  have hb₁ := Int.floor_le (x.im / m + 1 / 2)
  have hb₂ := Int.lt_floor_add_one (x.im / m + 1 / 2)
  have ha₁' : (⌊x.re / m + 1 / 2⌋ : ℝ) * m ≤ x.re + m / 2 := by
    calc
      _ ≤ (x.re / m + 1 / 2) * m := mul_le_mul_of_nonneg_right ha₁ hm.le
      _ = x.re + m / 2 := by field_simp
  have ha₂' : x.re + m / 2 < (⌊x.re / m + 1 / 2⌋ : ℝ) * m + m := by
    calc
      _ = (x.re / m + 1 / 2) * m := by field_simp
      _ < ((⌊x.re / m + 1 / 2⌋ : ℝ) + 1) * m :=
        mul_lt_mul_of_pos_right ha₂ hm
      _ = _ := by ring
  have hb₁' : (⌊x.im / m + 1 / 2⌋ : ℝ) * m ≤ x.im + m / 2 := by
    calc
      _ ≤ (x.im / m + 1 / 2) * m := mul_le_mul_of_nonneg_right hb₁ hm.le
      _ = x.im + m / 2 := by field_simp
  have hb₂' : x.im + m / 2 < (⌊x.im / m + 1 / 2⌋ : ℝ) * m + m := by
    calc
      _ = (x.im / m + 1 / 2) * m := by field_simp
      _ < ((⌊x.im / m + 1 / 2⌋ : ℝ) + 1) * m :=
        mul_lt_mul_of_pos_right hb₂ hm
      _ = _ := by ring
  have hre : |(x - nearestGrid m x).re| ≤ m / 2 := by
    rw [abs_le]
    simp only [Complex.sub_re, nearestGrid]
    constructor <;> linarith only [ha₁', ha₂']
  have him : |(x - nearestGrid m x).im| ≤ m / 2 := by
    rw [abs_le]
    simp only [Complex.sub_im, nearestGrid]
    constructor <;> linarith only [hb₁', hb₂']
  have hre2 : (x - nearestGrid m x).re ^ 2 ≤ (m / 2) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (half_pos hm).le] using hre)
  have him2 : (x - nearestGrid m x).im ^ 2 ≤ (m / 2) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (half_pos hm).le] using him)
  have hn := Complex.sq_norm (x - nearestGrid m x)
  rw [Complex.normSq_apply] at hn
  nlinarith [norm_nonneg (x - nearestGrid m x)]

 

theorem nearestGrid_mem_meshSites {ε R B : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (x : ℂ)
    (hx : ‖x‖ + meshStep ε R ≤ B * R) :
    nearestGrid (meshStep ε R) x ∈ meshSites ε R B := by
  let m := meshStep ε R
  have hm : 0 < m := by dsimp [m, meshStep]; positivity
  have hnear : ‖x - nearestGrid m x‖ < m := nearestGrid_norm_lt hm x
  have hball : nearestGrid m x ∈ Metric.ball (0 : ℂ) (B * R) := by
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖nearestGrid m x‖ = ‖(nearestGrid m x - x) + x‖ := by congr 1; ring
      _ ≤ ‖nearestGrid m x - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - nearestGrid m x‖ + ‖x‖ := by rw [norm_sub_rev]
      _ < m + ‖x‖ := by linarith only [hnear]
      _ ≤ B * R := by simpa only [add_comm] using hx
  have hgrid : nearestGrid m x ∈ LQGMetric.Blueprint.gridPts m :=
    ⟨⌊x.re / m + 1 / 2⌋, ⌊x.im / m + 1 / 2⌋, rfl⟩
  obtain ⟨k, hk, heq⟩ := LQGMetric.CONF.grid_ball_subset hm 0
    ⟨hgrid, hball⟩
  unfold meshSites
  exact Finset.mem_image.mpr ⟨k, hk, heq⟩

theorem meshStep_pos {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    0 < meshStep ε R := by
  unfold meshStep
  positivity

 
theorem meshSites_card_le_box (ε R B : ℝ) :
    (meshSites ε R B).card ≤
      (2 * ⌈B * R / meshStep ε R⌉₊ + 1) ^ 2 := by
  unfold meshSites
  exact (Finset.card_image_le).trans
    (le_of_eq (LQGMetric.CONF.gridBox_card _ _ _))

 

theorem meshSites_card_le_epsilon_inv_four
    {ε R B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hB : 0 ≤ B) :
    ((meshSites ε R B).card : ℝ) ≤
      (16 * B + 3) ^ 2 * (ε ^ 4)⁻¹ := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε2le : ε ^ 2 ≤ 1 := by nlinarith
  have hratio : B * R / meshStep ε R = 8 * B / ε ^ 2 := by
    unfold meshStep
    field_simp
  have hcard : ((meshSites ε R B).card : ℝ) ≤
      ((2 * ⌈B * R / meshStep ε R⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast meshSites_card_le_box ε R B
  rw [hratio] at hcard
  have harg : 0 ≤ 8 * B / ε ^ 2 := by positivity
  have hceil : (⌈8 * B / ε ^ 2⌉₊ : ℝ) < 8 * B / ε ^ 2 + 1 :=
    Nat.ceil_lt_add_one harg
  have hbase : ((2 * ⌈8 * B / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤
      16 * B / ε ^ 2 + 3 := by
    push_cast
    calc
      2 * (⌈8 * B / ε ^ 2⌉₊ : ℝ) + 1 ≤
          2 * (8 * B / ε ^ 2 + 1) + 1 := by linarith only [hceil]
      _ = 16 * B / ε ^ 2 + 3 := by ring
  have hbase2 : 16 * B / ε ^ 2 + 3 ≤ (16 * B + 3) / ε ^ 2 := by
    have h3 : (3 : ℝ) ≤ 3 / ε ^ 2 := by
      rw [le_div_iff₀ hε2]
      nlinarith
    calc
      16 * B / ε ^ 2 + 3 ≤ 16 * B / ε ^ 2 + 3 / ε ^ 2 := by linarith
      _ = (16 * B + 3) / ε ^ 2 := by ring
  calc
    ((meshSites ε R B).card : ℝ) ≤
      ((2 * ⌈8 * B / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) ^ 2 := hcard
    _ ≤ ((16 * B + 3) / ε ^ 2) ^ 2 := by
      gcongr
      exact hbase.trans hbase2
    _ = (16 * B + 3) ^ 2 * (ε ^ 4)⁻¹ := by
      rw [div_pow, ← pow_mul]
      ring

 



theorem mesh_failure_from_site_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ε R B c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (M : ℕ) (good : ℂ → Set Ω)
    (hsite : ∀ z ∈ meshSites ε R B,
      P ((good z)ᶜ) ≤ ENNReal.ofReal (c * ε ^ (M + 6))) :
    P ({ω | ∀ z ∈ meshSites ε R B, ω ∈ good z}ᶜ) ≤
      ENNReal.ofReal ((16 * B + 3) ^ 2 * c * ε ^ (M + 2)) := by
  classical
  let F := meshSites ε R B
  let a := c * ε ^ (M + 6)
  have ha : 0 ≤ a := mul_nonneg hc (pow_nonneg hε.le _)
  have hset : {ω | ∀ z ∈ F, ω ∈ good z}ᶜ =
      ⋃ z ∈ F, (good z)ᶜ := by
    ext ω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, mem_iUnion]
  have hpow : (ε ^ 4)⁻¹ * ε ^ (M + 6) = ε ^ (M + 2) := by
    rw [show M + 6 = (M + 2) + 4 by omega, pow_add]
    have h4 : ε ^ 4 ≠ 0 := pow_ne_zero _ hε.ne'
    field_simp
  have hrate : ((F.card : ℝ) * a) ≤
      (16 * B + 3) ^ 2 * c * ε ^ (M + 2) := by
    have hcard := meshSites_card_le_epsilon_inv_four hε hε1 hR hB
    calc
      (F.card : ℝ) * a ≤
          ((16 * B + 3) ^ 2 * (ε ^ 4)⁻¹) * a :=
        mul_le_mul_of_nonneg_right hcard ha
      _ = (16 * B + 3) ^ 2 * c * ε ^ (M + 2) := by
        dsimp [a]
        calc
          (16 * B + 3) ^ 2 * (ε ^ 4)⁻¹ * (c * ε ^ (M + 6)) =
              (16 * B + 3) ^ 2 * c * ((ε ^ 4)⁻¹ * ε ^ (M + 6)) := by ring
          _ = (16 * B + 3) ^ 2 * c * ε ^ (M + 2) := by rw [hpow]
  rw [hset]
  calc
    P (⋃ z ∈ F, (good z)ᶜ) ≤
        ∑ z ∈ F, P ((good z)ᶜ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ F, ENNReal.ofReal a := Finset.sum_le_sum hsite
    _ = (F.card : ℝ≥0∞) * ENNReal.ofReal a := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((F.card : ℝ) * a) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal ((16 * B + 3) ^ 2 * c * ε ^ (M + 2)) :=
      ENNReal.ofReal_le_ofReal hrate


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.TwoSet
