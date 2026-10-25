import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Finite
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Grid




 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5

open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
open LQGMetric (DistC)

def compareFinset (C : Objects.CorrectedEvent.Constants) (k : ℕ) : Finset ℂ := by
  classical
  let a := Objects.CorrectedEvent.compareScale k * C.r / 100
  exact (gridBoxFinset a ⌈(3 * C.r + a) / a⌉₊).filter (· ∈ Objects.CorrectedEvent.compareSites C k)

theorem compareSites_subset (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    Objects.CorrectedEvent.compareSites C k ⊆ ↑(compareFinset C k) := by
  classical
  intro z hz
  have ht : 0 < Objects.CorrectedEvent.compareScale k := by
    unfold Objects.CorrectedEvent.compareScale
    positivity
  have ha : 0 < Objects.CorrectedEvent.compareScale k * C.r / 100 :=
    div_pos (mul_pos ht C.rPos) (by norm_num)
  have hnorm : ‖z‖ ≤ 3 * C.r + Objects.CorrectedEvent.compareScale k * C.r / 100 :=
    norm_le_of_infDist_cann_le (by linarith [C.rPos]) (by linarith [C.rPos]) hz.2
  have hmem := grid_inter_closedBall_subset (ρ := 3 * C.r + Objects.CorrectedEvent.compareScale k * C.r / 100) ha
    ⟨hz.1, by rw [mem_closedBall, dist_zero_right]; exact hnorm⟩
  unfold compareFinset
  rw [Finset.coe_filter]
  exact ⟨hmem, hz⟩

 
theorem card_compareFinset_le (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    ((compareFinset C k).card : ℝ) ≤ 490000 * (Objects.CorrectedEvent.compareScale k)⁻¹ ^ 2 := by
  classical
  set t : ℝ := Objects.CorrectedEvent.compareScale k with htdef
  have ht0 : 0 < t := by rw [htdef]; unfold Objects.CorrectedEvent.compareScale; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef]
    unfold Objects.CorrectedEvent.compareScale
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  set x : ℝ := 100 * t⁻¹ with hxdef
  have hx100 : 100 ≤ x := by
    rw [hxdef]
    have hti : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).2 ht1
    linarith
  let a : ℝ := t * C.r / 100
  have ha : 0 < a := div_pos (mul_pos ht0 C.rPos) (by norm_num)
  have hratio : (3 * C.r + a) / a = 3 * x + 1 := by
    dsimp [a]
    rw [hxdef]
    field_simp [ne_of_gt C.rPos, ne_of_gt ht0]
  set N : ℕ := ⌈(3 * C.r + a) / a⌉₊ with hNdef
  have hN : (N : ℝ) ≤ 3 * x + 2 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ (3 * C.r + a) / a by rw [hratio]; linarith)
    rw [hratio] at hc
    rw [hNdef, hratio]
    linarith
  have hcard : (compareFinset C k).card ≤ (2 * N + 1) ^ 2 := by
    unfold compareFinset
    simpa only [htdef] using
      (Finset.card_filter_le _ _).trans (card_gridBoxFinset_le a N)
  have hcardR : ((compareFinset C k).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 2 :=
    by exact_mod_cast hcard
  have hx2 : x ^ 2 = 10000 * t⁻¹ ^ 2 := by rw [hxdef]; ring
  calc ((compareFinset C k).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 2 := hcardR
    _ ≤ (7 * x) ^ 2 := by
      have : 2 * (N : ℝ) + 1 ≤ 7 * x := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    _ = 490000 * t⁻¹ ^ 2 := by rw [mul_pow, hx2]; ring

 

theorem compare_test_of_tail {R : ℝ} (hR : 0 < R)
    {N outer inner : ℝ≥0∞} (hN0 : 0 < N) (hNtop : N < ⊤)
    (houter : outer ≤ ENNReal.ofReal R * N)
    (hinner : ENNReal.ofReal R⁻¹ * N ≤ inner) (hinnerTop : inner < ⊤) :
    outer ≤ ENNReal.ofReal (R ^ 2) * inner ∧ outer < ⊤ ∧
      0 < inner ∧ inner < ⊤ := by
  have hfac : ENNReal.ofReal (R ^ 2) * ENNReal.ofReal R⁻¹ =
      ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hRtop : ENNReal.ofReal R < ⊤ := ENNReal.ofReal_lt_top
  have hRinv0 : (0 : ℝ≥0∞) < ENNReal.ofReal R⁻¹ :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr hR)
  refine ⟨?_, houter.trans_lt (ENNReal.mul_lt_top hRtop hNtop), ?_, hinnerTop⟩
  · calc outer ≤ ENNReal.ofReal R * N := houter
      _ = ENNReal.ofReal (R ^ 2) * (ENNReal.ofReal R⁻¹ * N) := by
        rw [← mul_assoc, hfac]
      _ ≤ ENNReal.ofReal (R ^ 2) * inner := by gcongr
  · exact lt_of_lt_of_le (ENNReal.mul_pos hRinv0.ne' hN0.ne') hinner

 

theorem s5_site_of_tail (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric)
    (g : DistC) (k : ℕ) (z : ℂ)
    (houter : Objects.CorrectedEvent.around (D g) z ((11/5)*Objects.CorrectedEvent.compareScale k*C.r)
        ((14/5)*Objects.CorrectedEvent.compareScale k*C.r) ≤
      ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z)
    (hinner : ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ ((1:ℝ)/16)) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z ≤
      Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
        ((9/20)*Objects.CorrectedEvent.compareScale k*C.r))
    (hinnerTop : Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
        ((9/20)*Objects.CorrectedEvent.compareScale k*C.r) < ⊤) :
    let t := Objects.CorrectedEvent.compareScale k
    let outer := Objects.CorrectedEvent.around (D g) z ((11/5)*t*C.r) ((14/5)*t*C.r)
    let inner := Objects.CorrectedEvent.acr (D g) z ((3/10)*t*C.r) ((9/20)*t*C.r)
    outer ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) * inner ∧ outer < ⊤ ∧
      0 < inner ∧ inner < ⊤ := by
  dsimp
  set t : ℝ := Objects.CorrectedEvent.compareScale k
  have ht : 0 < t := by rw [show t = Objects.CorrectedEvent.compareScale k by rfl]; unfold Objects.CorrectedEvent.compareScale; positivity
  let R : ℝ := t ^ (-(1:ℝ)/16)
  have hR : 0 < R := Real.rpow_pos_of_pos ht _
  have hRinv : R⁻¹ = t ^ ((1:ℝ)/16) := by
    dsimp [R]
    rw [← Real.rpow_neg ht.le]
    congr 1
    ring
  have hR2 : R^2 = t ^ (-(1:ℝ)/8) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hN0 : 0 < Objects.CorrectedEvent.normalizer C g (t*C.r) z := by
    unfold Objects.CorrectedEvent.normalizer
    apply ENNReal.ofReal_pos.mpr
    have hs : 0 < t*C.r := mul_pos ht C.rPos
    exact mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)
  have hNtop : Objects.CorrectedEvent.normalizer C g (t*C.r) z < ⊤ := by
    unfold Objects.CorrectedEvent.normalizer
    exact ENNReal.ofReal_lt_top
  rw [← hRinv] at hinner
  obtain ⟨h1, h2, h3, h4⟩ :=
    compare_test_of_tail hR hN0 hNtop houter hinner hinnerTop
  rw [hR2] at h1
  exact ⟨h1, h2, h3, h4⟩

 
def s5Site (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (k : ℕ) (z : ℂ) : Prop :=
  let t := Objects.CorrectedEvent.compareScale k
  let outer := Objects.CorrectedEvent.around D z ((11/5)*t*C.r) ((14/5)*t*C.r)
  let inner := Objects.CorrectedEvent.acr D z ((3/10)*t*C.r) ((9/20)*t*C.r)
  outer ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) * inner ∧ outer < ⊤ ∧
    0 < inner ∧ inner < ⊤

 

theorem s5_bad_subset (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric)
    (k : ℕ) (z : ℂ) :
    {g | ¬ s5Site C (D g) k z} ⊆
      {g | ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z <
          Objects.CorrectedEvent.around (D g) z ((11/5)*Objects.CorrectedEvent.compareScale k*C.r)
            ((14/5)*Objects.CorrectedEvent.compareScale k*C.r)} ∪
      {g | Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
          ((9/20)*Objects.CorrectedEvent.compareScale k*C.r) <
        ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ ((1:ℝ)/16)) *
          Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z} ∪
      {g | ¬ Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
          ((9/20)*Objects.CorrectedEvent.compareScale k*C.r) < ⊤} := by
  intro g hg
  by_contra h
  have houter : Objects.CorrectedEvent.around (D g) z ((11/5)*Objects.CorrectedEvent.compareScale k*C.r)
      ((14/5)*Objects.CorrectedEvent.compareScale k*C.r) ≤
      ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z :=
    not_lt.mp (fun hh => h (Or.inl (Or.inl hh)))
  have hinner : ENNReal.ofReal ((Objects.CorrectedEvent.compareScale k) ^ ((1:ℝ)/16)) *
      Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.compareScale k*C.r) z ≤
      Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
        ((9/20)*Objects.CorrectedEvent.compareScale k*C.r) :=
    not_lt.mp (fun hh => h (Or.inl (Or.inr hh)))
  have hfin : Objects.CorrectedEvent.acr (D g) z ((3/10)*Objects.CorrectedEvent.compareScale k*C.r)
      ((9/20)*Objects.CorrectedEvent.compareScale k*C.r) < ⊤ :=
    Classical.byContradiction (fun hh => h (Or.inr hh))
  exact hg (s5_site_of_tail C D g k z houter hinner hfin)

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5
