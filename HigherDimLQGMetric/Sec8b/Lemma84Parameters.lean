import HigherDimLQGMetric.Sec8b.Lemma84
import HigherDimLQGMetric.Freq.ScaleCount

/-! Cardinal bounds and small-parameter choice for Lemma 8.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter
open scoped Topology

/-- An integer interval cut out by real ceiling and floor has at most its
real span plus one integer. -/
theorem s7b_card_ceil_floor_le {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Icc (⌈x⌉ : ℤ) ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  by_cases h : (⌈x⌉ : ℤ) ≤ ⌊y⌋
  · have hc := Int.card_Icc_of_le (⌈x⌉ : ℤ) ⌊y⌋ (by omega)
    have hcR := congrArg (fun z : ℤ => (z : ℝ)) hc
    push_cast at hcR
    have hx := Int.le_ceil x
    have hy := Int.floor_le y
    linarith only [hcR, hx, hy]
  · rw [Finset.Icc_eq_empty h, Finset.card_empty]
    norm_num
    linarith only [hxy]

/-- The slightly enlarged dyadic-bin index interval has at most four more
integers than its logarithmic span. -/
theorem s7b_card_floor_bin_le {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Icc (Int.floor x - 1) (Int.floor y + 1)).card : ℝ) ≤
      y - x + 4 := by
  have hfloor := Int.floor_mono hxy
  have hab : Int.floor x - 1 ≤ Int.floor y + 1 + 1 := by omega
  have hc := Int.card_Icc_of_le (Int.floor x - 1) (Int.floor y + 1) hab
  have hcR := congrArg (fun z : ℤ => (z : ℝ)) hc
  push_cast at hcR
  have hx := Int.lt_floor_add_one x
  have hy := Int.floor_le y
  linarith only [hcR, hx, hy]

/-- Upper bound for the number of scales in `[ε²R, εR]`. -/
theorem s7b_scaleWin_card_le {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) :
    (((s4c_scaleWin_finite hε hR).toFinset.card : ℕ) : ℝ) ≤
      Real.logb 64 ε⁻¹ + 1 := by
  let x := Real.logb 64 (ε ^ 2 * R)
  let y := Real.logb 64 (ε * R)
  have hxy : x ≤ y := by
    apply (Real.logb_le_logb (by norm_num) (by positivity)
      (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1)) hR.le]
  have hset : (s4c_scaleWin_finite hε hR).toFinset =
      Finset.Icc (⌈x⌉ : ℤ) ⌊y⌋ := by
    ext j
    rw [(s4c_scaleWin_finite hε hR).mem_toFinset,
      s4c_scaleWin_eq_Icc hε hR]
    simp only [x, y, Set.mem_Icc, Finset.mem_Icc]
  have hlog : y - x = Real.logb 64 ε⁻¹ := by
    dsimp [x, y]
    rw [Real.logb_mul hε.ne' hR.ne',
      Real.logb_mul (pow_ne_zero 2 hε.ne') hR.ne',
      Real.logb_pow, Real.logb_inv]
    ring
  rw [hset]
  simpa only [hlog] using s7b_card_ceil_floor_le hxy

/-- Upper bound for the number of dyadic bins intersecting the scale-bin
range. -/
theorem s7b_binIndices_card_le {ε B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B) :
    ((s7b_binIndices (ε ^ B) (ε ^ (-B))).card : ℝ) ≤
      2 * B * Real.logb 2 ε⁻¹ + 4 := by
  have hlo : 0 < ε ^ B := by positivity
  have hhi : 0 < ε ^ (-B) := by positivity
  have hlowhigh : ε ^ B ≤ ε ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  let x := Real.logb 2 (ε ^ B)
  let y := Real.logb 2 (ε ^ (-B))
  have hxy : x ≤ y :=
    (Real.logb_le_logb (by norm_num) hlo hhi).mpr hlowhigh
  have hlog : y - x = 2 * B * Real.logb 2 ε⁻¹ := by
    dsimp [x, y]
    rw [Real.logb_rpow_eq_mul_logb_of_pos hε,
      Real.logb_rpow_eq_mul_logb_of_pos hε,
      Real.logb_inv]
    ring
  unfold s7b_binIndices
  simpa only [hlog] using s7b_card_floor_bin_le hxy

/-- The number of scale/color/bin classes has only logarithmic growth. -/
theorem s7b_classSet_card_le {d : ℕ} {ε R B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) (hB : 0 ≤ B) :
    ((s7b_classSet d hε hR B).card : ℝ) ≤
      ((1000 * d) ^ d : ℕ) *
        (Real.logb 64 ε⁻¹ + 1) *
        (2 * B * Real.logb 2 ε⁻¹ + 4) := by
  have hscale := s7b_scaleWin_card_le hε hε1 hR
  have hbin := s7b_binIndices_card_le hε hε1 hB
  have hs : 0 ≤ Real.logb 64 ε⁻¹ + 1 := by
    have hinv : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    have hlog : 0 ≤ Real.logb 64 ε⁻¹ :=
      Real.logb_nonneg (by norm_num) hinv
    positivity
  have hc : 0 ≤ ((1000 * d) ^ d : ℕ) := by positivity
  let A := (s4c_scaleWin_finite hε hR).toFinset
  let C := sec8Colors d
  let I := s7b_binIndices (ε ^ B) (ε ^ (-B))
  change ((A ×ˢ (C ×ˢ I)).card : ℝ) ≤ _
  simp only [Finset.card_product]
  push_cast
  have hC : (C.card : ℝ) = ((1000 * d) ^ d : ℕ) := by
    exact_mod_cast sec8Colors_card d
  have hA : (A.card : ℝ) ≤ Real.logb 64 ε⁻¹ + 1 := hscale
  have hI : (I.card : ℝ) ≤ 2 * B * Real.logb 2 ε⁻¹ + 4 := hbin
  calc
    (A.card : ℝ) * ((C.card : ℝ) * I.card) ≤
        (Real.logb 64 ε⁻¹ + 1) * ((C.card : ℝ) * I.card) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ (Real.logb 64 ε⁻¹ + 1) *
        ((C.card : ℝ) * (2 * B * Real.logb 2 ε⁻¹ + 4)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hI (by positivity)) hs
    _ = (1000 * (d : ℝ)) ^ d *
        (Real.logb 64 ε⁻¹ + 1) *
        (2 * B * Real.logb 2 ε⁻¹ + 4) := by
      rw [hC]
      push_cast
      ring

/-- A logarithm is bounded by a fixed small power of the inverse scale. -/
theorem s7b_logb_inv_le_eighth {ε b : ℝ}
    (hε : 0 < ε) (hb : 1 < b) :
    Real.logb b ε⁻¹ ≤ (8 / Real.log b) * (ε⁻¹) ^ (1 / 8 : ℝ) := by
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hlog := Real.log_le_rpow_div (show 0 ≤ ε⁻¹ by positivity)
    (show 0 < (1 / 8 : ℝ) by norm_num)
  dsimp only [Real.logb]
  rw [div_le_iff₀ hlogb]
  calc
    Real.log ε⁻¹ ≤ ε⁻¹ ^ (1 / 8 : ℝ) / (1 / 8 : ℝ) := hlog
    _ = (8 / Real.log b) * ε⁻¹ ^ (1 / 8 : ℝ) * Real.log b := by
      field_simp

/-- Convenient identities for the inverse eighth power. -/
theorem s7b_inv_eighth_powers {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let t := (ε⁻¹) ^ (1 / 8 : ℝ)
    1 ≤ t ∧ t ^ (2 : ℕ) = (ε⁻¹) ^ (1 / 4 : ℝ) ∧
      t ^ (4 : ℕ) = (ε⁻¹) ^ (1 / 2 : ℝ) ∧
      t ^ (8 : ℕ) = ε⁻¹ := by
  dsimp only
  have hεinv : 0 ≤ ε⁻¹ := by positivity
  have ht : 0 < (ε⁻¹) ^ (1 / 8 : ℝ) := by positivity
  constructor
  · simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_inv_iff₀.mpr ⟨hε, hε1⟩)
        (by norm_num : (0 : ℝ) ≤ 1 / 8))
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hεinv]
    norm_num
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hεinv]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hεinv]
    norm_num

def s7b_classConst (d : ℕ) (B : ℝ) : ℝ :=
  ((1000 * d) ^ d : ℕ) * (8 / Real.log 64 + 1) *
    (16 * B / Real.log 2 + 4)

theorem s7b_classConst_pos (d : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 < s7b_classConst d B := by
  have h64 : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < (1000 * d) ^ d := by
    cases d with
    | zero => norm_num
    | succ n => exact pow_pos (by omega) _
  dsimp only [s7b_classConst]
  positivity

theorem s7b_classSet_power_bound {d : ℕ} {ε R B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) (hB : 0 ≤ B) :
    ((s7b_classSet d hε hR B).card : ℝ) ≤
      s7b_classConst d B * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) := by
  let t := (ε⁻¹) ^ (1 / 8 : ℝ)
  have ht : 1 ≤ t := (s7b_inv_eighth_powers hε hε1).1
  have ht0 : 0 ≤ t := by linarith
  have h64 : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : Real.logb 64 ε⁻¹ + 1 ≤ (8 / Real.log 64 + 1) * t := by
    have hlog := s7b_logb_inv_le_eighth hε (by norm_num : (1 : ℝ) < 64)
    nlinarith only [hlog, ht]
  have hI : 2 * B * Real.logb 2 ε⁻¹ + 4 ≤
      (16 * B / Real.log 2 + 4) * t := by
    have hlog := s7b_logb_inv_le_eighth hε (by norm_num : (1 : ℝ) < 2)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * B by positivity)
    calc
      2 * B * Real.logb 2 ε⁻¹ + 4 ≤
          2 * B * (8 / Real.log 2 * t) + 4 := by
        dsimp only [t] at hmul ⊢
        linarith only [hmul]
      _ ≤ 2 * B * (8 / Real.log 2 * t) + 4 * t := by
        linarith only [ht]
      _ = (16 * B / Real.log 2 + 4) * t := by ring
  have hA0 : 0 ≤ Real.logb 64 ε⁻¹ + 1 := by
    have hinv : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    have hlog : 0 ≤ Real.logb 64 ε⁻¹ := Real.logb_nonneg (by norm_num) hinv
    positivity
  have hI0 : 0 ≤ 2 * B * Real.logb 2 ε⁻¹ + 4 := by
    have hinv : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    have hlog : 0 ≤ Real.logb 2 ε⁻¹ := Real.logb_nonneg (by norm_num) hinv
    positivity
  calc
    ((s7b_classSet d hε hR B).card : ℝ) ≤
      ((1000 * d) ^ d : ℕ) * (Real.logb 64 ε⁻¹ + 1) *
        (2 * B * Real.logb 2 ε⁻¹ + 4) :=
      s7b_classSet_card_le hε hε1 hR hB
    _ ≤ ((1000 * d) ^ d : ℕ) * ((8 / Real.log 64 + 1) * t) *
        ((16 * B / Real.log 2 + 4) * t) := by
      have hc : 0 ≤ (((1000 * d) ^ d : ℕ) : ℝ) := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hA hc) hI
        hI0 (mul_nonneg hc (le_trans hA0 hA))
    _ = s7b_classConst d B * t ^ (2 : ℕ) := by
      dsimp [s7b_classConst]
      ring

/-- The required pigeonhole inequality once the inverse eighth power is
large enough. -/
theorem s7b_class_sampling_inequality {d : ℕ} {ε R B η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hB : 0 ≤ B) (hη : 0 < η)
    (hlarge : 160 * s7b_classConst d B ≤
      η * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ)) :
    (s7b_classSet d hε hR B).card *
      ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε := by
  let t := (ε⁻¹) ^ (1 / 8 : ℝ)
  let K := s7b_classConst d B
  have hp := s7b_inv_eighth_powers hε hε1
  have ht : 1 ≤ t := hp.1
  have ht0 : 0 ≤ t := by linarith
  have ht4 : t ^ (4 : ℕ) = (ε⁻¹) ^ (1 / 2 : ℝ) := hp.2.2.1
  have ht8 : t ^ (8 : ℕ) = ε⁻¹ := hp.2.2.2
  have hK : 0 < K := s7b_classConst_pos d hB
  have hclass : ((s7b_classSet d hε hR B).card : ℝ) ≤ K * t ^ (2 : ℕ) :=
    s7b_classSet_power_bound hε hε1 hR hB
  have hn : (⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ : ℝ) ≤ 2 * t ^ (4 : ℕ) := by
    have hceil := Nat.ceil_lt_add_one
      (show 0 ≤ (ε⁻¹) ^ (1 / 2 : ℝ) by positivity)
    have ht4one : 1 ≤ t ^ (4 : ℕ) := one_le_pow₀ ht
    rw [← ht4] at hceil ⊢
    linarith only [hceil, ht4one]
  have hsample : η / (80 * ε) ≤ (s7b_sampleCount η ε : ℝ) := by
    exact Nat.le_ceil _
  have hsample' : η / 80 * t ^ (8 : ℕ) ≤
      (s7b_sampleCount η ε : ℝ) := by
    rw [ht8]
    have heq : η / 80 * ε⁻¹ = η / (80 * ε) := by field_simp
    rw [heq]
    exact hsample
  have hlarge' : 160 * K ≤ η * t ^ (2 : ℕ) := hlarge
  have hmul : (160 * K) * t ^ (6 : ℕ) ≤
      (η * t ^ (2 : ℕ)) * t ^ (6 : ℕ) :=
    mul_le_mul_of_nonneg_right hlarge' (by positivity)
  have hcardmul : ((s7b_classSet d hε hR B).card *
      ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ : ℕ) ≤ s7b_sampleCount η ε := by
    exact_mod_cast (show
      ((s7b_classSet d hε hR B).card : ℝ) *
          (⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ : ℝ) ≤
        (s7b_sampleCount η ε : ℝ) from by
        calc
          ((s7b_classSet d hε hR B).card : ℝ) *
              (⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ : ℝ) ≤
              (K * t ^ (2 : ℕ)) * (2 * t ^ (4 : ℕ)) := by
            exact mul_le_mul hclass hn (by positivity) (by positivity)
          _ = 2 * K * t ^ (6 : ℕ) := by ring
          _ ≤ η / 80 * t ^ (8 : ℕ) := by nlinarith only [hmul]
          _ ≤ (s7b_sampleCount η ε : ℝ) := hsample')
  exact hcardmul

/-- One threshold, independent of the scale and of the pruning parameter,
suffices for the class pigeonhole estimate. -/
theorem s7b_exists_class_threshold (d : ℕ) {B η : ℝ}
    (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {ε R : ℝ}, (hε : 0 < ε) → ε < ε₀ → ε ≤ 1 →
        (hR : 0 < R) → 0 ≤ B →
        (s7b_classSet d hε hR B).card *
          ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε := by
  have htend : Filter.Tendsto
      (fun ε : ℝ => ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ))
      (𝓝[>] 0) Filter.atTop := by
    have h1 : Filter.Tendsto
        (fun ε : ℝ => (ε⁻¹) ^ (1 / 8 : ℝ))
        (𝓝[>] 0) Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
        tendsto_inv_nhdsGT_zero
    have heq : (fun ε : ℝ => ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ)) =
        (fun ε : ℝ => ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℝ)) := by
      funext ε
      exact (Real.rpow_natCast _ 2).symm
    rw [heq]
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp h1
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      160 * s7b_classConst d B / η ≤
        ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) :=
    htend.eventually (Filter.eventually_ge_atTop _)
  obtain ⟨ε₀, hε₀, hεall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε R hε hεlt hε1 hR hB
  have hbound := hεall (show ε ∈ Set.Ioo 0 ε₀ from ⟨hε, hεlt⟩)
  have hlarge : 160 * s7b_classConst d B ≤
      η * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) := by
    have hh := (div_le_iff₀ hη).mp hbound
    nlinarith only [hh]
  exact s7b_class_sampling_inequality hε hε1 hR hB hη hlarge

end HigherDimLQGMetric
