import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C8TwoHits
import Mathlib.Order.Interval.Set.Union



 
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Complex
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem num_cells_pos (C : Constants) {s : ℝ} (hs : 0 < s) :
    0 < numCells C s := by
  unfold numCells
  apply Nat.ceil_pos.mpr
  have hR : 0 < supRadius C 1 := by
    unfold supRadius
    exact mul_pos (mul_pos (by norm_num) (mul_pos (by norm_num) C.supPos)) C.rPos
  have hden : 0 < (1/20:ℝ)*supRadius C 1/(4*s) := by positivity
  exact div_pos (by positivity) hden

 
theorem circle_cell_width_nonneg (C : Constants) {s : ℝ} (hs : 0 < s)
    (l : ℕ) :
    0 ≤ (circleCell C s l).hi - (circleCell C s l).lo := by
  have hN : 0 < (numCells C s : ℝ) := Nat.cast_pos.mpr (num_cells_pos C hs)
  unfold circleCell
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_right _ hN.le
  gcongr
  omega

 

theorem circle_cell_cover (C : Constants) {s : ℝ} (hs : 0 < s)
    {θ : ℝ} (hθ : θ ∈ Ico (0:ℝ) (2*Real.pi)) :
    ∃ l ∈ Finset.range (numCells C s),
      θ ∈ Ico (circleCell C s l).lo (circleCell C s l).hi := by
  let N := numCells C s
  let a : ℕ → ℝ := fun n => 2*Real.pi*(n:ℝ)/(N:ℝ)
  have hNpos : 0 < N := num_cells_pos C hs
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hNpos)
  have h0 : a 0 = 0 := by simp [a]
  have hN : a N = 2*Real.pi := by
    dsimp [a]
    field_simp
  have hc : θ ∈ ⋃ l ∈ Finset.range N, Ico (a l) (a (l+1)) :=
    Ico_subset_biUnion_Ico N a (by simpa only [h0, hN] using hθ)
  obtain ⟨l, hl, hcell⟩ := by simpa only [mem_iUnion] using hc
  exact ⟨l, hl, by simpa only [circleCell, a] using hcell⟩

 


theorem circle_outer_le_bad_length_of_cell_cover
    (C : Constants) (D : LSCMetric) (c : ℂ) {s : ℝ} (hs : 0 < s)
    (H : Set ℂ)
    (hcover : ∀ θ ∈ Ico (0:ℝ) (2*Real.pi),
      c + (s:ℂ)*cexp (θ*I) ∈ H →
      ∃ l ∈ Finset.range (numCells C s),
        badCell C D c s (circleCell C s l) ∧
        θ ∈ Ico (circleCell C s l).lo (circleCell C s l).hi) :
    Objects.Shadow.circleOuter c ⟨s, hs.le⟩ 0 H ≤
      ENNReal.ofReal (badLength C D c s) := by
  classical
  let K := Finset.range (numCells C s)
  let F : ℕ → Set ℝ := fun l =>
    if badCell C D c s (circleCell C s l) then
      Ico (circleCell C s l).lo (circleCell C s l).hi else ∅
  have hsub : {θ ∈ Ico (0:ℝ) (2*Real.pi) |
      c + (s:ℂ)*cexp (θ*I) ∈ H} ⊆ ⋃ l ∈ K, F l := by
    intro θ hθ
    obtain ⟨l, hl, hbad, hcell⟩ := hcover θ hθ.1 hθ.2
    simp only [mem_iUnion]
    exact ⟨l, hl, by simp [F, hbad, hcell]⟩
  have hsum : volume (⋃ l ∈ K, F l) ≤ ∑ l ∈ K, volume (F l) :=
    measure_biUnion_finset_le K F
  have hterm (l : ℕ) (hl : l ∈ K) :
      0 ≤ if badCell C D c s (circleCell C s l) then
        s*((circleCell C s l).hi-(circleCell C s l).lo) else 0 := by
    split_ifs
    · exact mul_nonneg hs.le (circle_cell_width_nonneg C hs l)
    · exact le_rfl
  have hmain : ENNReal.ofReal s * volume
      {θ ∈ Ico (0:ℝ) (2*Real.pi) | c + (s:ℂ)*cexp (θ*I) ∈ H} ≤
      ENNReal.ofReal (badLength C D c s) := by
    calc
    ENNReal.ofReal s * volume
        {θ ∈ Ico (0:ℝ) (2*Real.pi) | c + (s:ℂ)*cexp (θ*I) ∈ H}
      ≤ ENNReal.ofReal s * volume (⋃ l ∈ K, F l) := by
          gcongr
    _ ≤ ENNReal.ofReal s * ∑ l ∈ K, volume (F l) := by gcongr
    _ = ∑ l ∈ K, ENNReal.ofReal s * volume (F l) := Finset.mul_sum K _ _
    _ = ∑ l ∈ K, ENNReal.ofReal
          (if badCell C D c s (circleCell C s l) then
            s*((circleCell C s l).hi-(circleCell C s l).lo) else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hbad : badCell C D c s (circleCell C s l)
          · simp [F, hbad, Real.volume_Ico, ENNReal.ofReal_mul hs.le]
          · simp [F, hbad]
    _ = ENNReal.ofReal (badLength C D c s) := by
          simpa only [badLength, K] using (ENNReal.ofReal_sum_of_nonneg hterm).symm
  have hR : ((⟨s, hs.le⟩ : NNReal) : ℝ) = s := rfl
  have hC : ((⟨s, hs.le⟩ : NNReal) : ℂ) = (s : ℂ) := by exact_mod_cast hR
  unfold Objects.Shadow.circleOuter
  convert hmain using 1
  simp only [zero_add]
  rfl

 


theorem circle_outer_le_bad_length_of_good_cell_exclusion
    (C : Constants) (D : LSCMetric) (c : ℂ) {s : ℝ} (hs : 0 < s)
    (H : Set ℂ)
    (havoid : ∀ l ∈ Finset.range (numCells C s),
      ∀ k ∈ Finset.Icc 1 (supK C),
      supGood C D c s (circleCell C s l) k →
      ∀ θ ∈ Ico (circleCell C s l).lo (circleCell C s l).hi,
        c + (s:ℂ)*cexp (θ*I) ∉ H) :
    Objects.Shadow.circleOuter c ⟨s, hs.le⟩ 0 H ≤
      ENNReal.ofReal (badLength C D c s) := by
  apply circle_outer_le_bad_length_of_cell_cover C D c hs H
  intro θ hθ hhit
  obtain ⟨l, hl, hcell⟩ := circle_cell_cover C hs hθ
  refine ⟨l, hl, ?_, hcell⟩
  by_contra hbad
  unfold badCell at hbad
  push Not at hbad
  obtain ⟨k, hk, hgood⟩ := hbad
  exact havoid l hl k hk hgood θ hcell hhit

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
