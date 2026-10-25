import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XUpperContinuity
import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousCutoff
import LQGMetric.Papers.DDDF.LenCountable

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private def upperShift (N R j k : ℕ) : C(ℂ, ℝ) :=
  ⟨fun z => min (N : ℝ)
      (PfeAxioms.clampContinuous N (denseSeq C(ℂ, ℝ) j) z +
        1 / ((k : ℝ) + 1) +
        (2 * (N : ℝ)) * max 0 (‖z‖ - (R : ℝ))),
    by fun_prop⟩

private theorem upperShift_bound (N R j k : ℕ) (z : ℂ) :
    |upperShift N R j k z| ≤ (N : ℝ) := by
  have hc := PfeAxioms.clampContinuous_bound (Nat.cast_nonneg N)
    (denseSeq C(ℂ, ℝ) j) z
  have hr : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  have hp : 0 ≤ (2 * (N : ℝ)) * max 0 (‖z‖ - (R : ℝ)) :=
    mul_nonneg (by positivity) (le_max_left _ _)
  change |min (N : ℝ) (_ + _ + _)| ≤ N
  apply abs_le.mpr
  constructor
  · exact le_min (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by
      have := (abs_le.mp hc).1
      linarith)
  · exact min_le_left _ _

private theorem upperShift_dominate
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (N R j k : ℕ) (hN : M + 1 ≤ (N : ℝ))
    (hr : (1 : ℝ) / ((k : ℝ) + 1) < 1)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1),
      |f z - denseSeq C(ℂ, ℝ) j z| <
        (1 : ℝ) / ((k : ℝ) + 1)) :
    ∀ z, f z ≤ upperShift N R j k z := by
  intro z
  have hfup := (abs_le.mp (hM z)).2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM z)
  have hcl := PfeAxioms.clampContinuous_bound (Nat.cast_nonneg N)
    (denseSeq C(ℂ, ℝ) j) z
  have hrad : 0 ≤ max 0 (‖z‖ - (R : ℝ)) := le_max_left _ _
  have hpen : 0 ≤ (2 * (N : ℝ)) * max 0 (‖z‖ - (R : ℝ)) :=
    mul_nonneg (by positivity) hrad
  change f z ≤ min (N : ℝ) (_ + _ + _)
  apply le_min
  · linarith
  · by_cases hz : z ∈ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1)
    · have hgz := hg z hz
      have hgab : |denseSeq C(ℂ, ℝ) j z| ≤ (N : ℝ) := by
        have hf := abs_le.mp (hM z)
        have hd := abs_lt.mp hgz
        apply abs_le.mpr
        constructor <;> linarith
      rw [PfeAxioms.clampContinuous_eq_of_bound _ hgab]
      have hd := (abs_lt.mp hgz).2
      linarith
    · have hfar : (R : ℝ) + 1 < ‖z‖ := by
        simp only [Metric.mem_closedBall, dist_zero_right] at hz
        exact lt_of_not_ge hz
      have hbig : (N : ℝ) ≤
          PfeAxioms.clampContinuous N (denseSeq C(ℂ, ℝ) j) z +
          1 / ((k : ℝ) + 1) +
          (2 * (N : ℝ)) * max 0 (‖z‖ - (R : ℝ)) := by
        have hnc : (1 : ℝ) ≤ N := by linarith
        have hrad1 : 1 < max 0 (‖z‖ - (R : ℝ)) := by
          apply lt_max_of_lt_right
          linarith
        have hp2 : 2 * (N : ℝ) ≤
            (2 * (N : ℝ)) * max 0 (‖z‖ - (R : ℝ)) :=
          le_mul_of_one_le_right (by positivity) hrad1.le
        have hlow := (abs_le.mp hcl).1
        have hr0 : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := by positivity
        linarith
      linarith

private theorem upperShift_local
    (f : C(ℂ, ℝ)) (R j k : ℕ)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1),
      |f z - denseSeq C(ℂ, ℝ) j z| <
        (1 : ℝ) / ((k : ℝ) + 1))
    (N : ℕ) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (hN : M + 1 ≤ (N : ℝ))
    (hr : (1 : ℝ) / ((k : ℝ) + 1) < 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    upperShift N R j k z ≤ f z + 2 / ((k : ℝ) + 1) := by
  have hz1 : z ∈ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1) := by
    have h := Metric.mem_closedBall.mp hz
    exact Metric.mem_closedBall.mpr (h.trans (by norm_cast; omega))
  have hgz := hg z hz1
  have hgab : |denseSeq C(ℂ, ℝ) j z| ≤ (N : ℝ) := by
    have hf := abs_le.mp (hM z)
    have hd := abs_lt.mp hgz
    apply abs_le.mpr
    constructor <;> linarith
  have hrad : max 0 (‖z‖ - (R : ℝ)) = 0 := by
    have h := Metric.mem_closedBall.mp hz
    simp only [dist_zero_right] at h
    rw [max_eq_left]
    linarith
  change min (N : ℝ) (_ + _ + _) ≤ _
  rw [PfeAxioms.clampContinuous_eq_of_bound _ hgab, hrad, mul_zero, add_zero]
  have hd := (abs_lt.mp hgz).1
  have hle : min (N : ℝ)
      (denseSeq C(ℂ, ℝ) j z + 1 / ((k : ℝ) + 1)) ≤
      denseSeq C(ℂ, ℝ) j z + 1 / ((k : ℝ) + 1) := min_le_right _ _
  have htwo : (2 : ℝ) / ((k : ℝ) + 1) =
      1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
  rw [htwo]
  linarith

 
def upperShiftFamily (i : ℕ) : C(ℂ, ℝ) :=
  let a := Nat.unpair i
  let b := Nat.unpair a.2
  let c := Nat.unpair b.2
  upperShift a.1 b.1 c.1 c.2

def upperShiftBound (i : ℕ) : ℝ := (Nat.unpair i).1

theorem upperShiftFamily_bound (i : ℕ) (z : ℂ) :
    |upperShiftFamily i z| ≤ upperShiftBound i := by
  exact upperShift_bound _ _ _ _ z

 

theorem upperShiftFamily_orderDense
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (K : Set ℂ) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ i : ℕ, (∀ z, f z ≤ upperShiftFamily i z) ∧
      (∀ z ∈ K, upperShiftFamily i z ≤ f z + δ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (M + 1)
  obtain ⟨s, hs⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hR⟩ := exists_nat_ge s
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' := Metric.mem_closedBall.mp (hs hz)
    apply Metric.mem_closedBall.mpr
    exact hz'.trans hR
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min (half_pos hδ) one_pos)
  have hr : (1 : ℝ) / ((k : ℝ) + 1) < 1 := hk.trans_le (min_le_right _ _)
  have h2r : (2 : ℝ) / ((k : ℝ) + 1) < δ := by
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) < δ / 2 :=
      hk.trans_le (min_le_left _ _)
    have htwo : (2 : ℝ) / ((k : ℝ) + 1) =
        1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    rw [htwo]
    linarith
  obtain ⟨j, hj⟩ := LQGMetric.DDDF.exists_denseSeq_close
    (K := Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))
    (isCompact_closedBall _ _) f (by positivity : 0 < (1 : ℝ) / ((k : ℝ) + 1))
  let i := Nat.pair N (Nat.pair R (Nat.pair j k))
  have hident : upperShiftFamily i = upperShift N R j k := by
    simp [upperShiftFamily, i, Nat.unpair_pair]
  refine ⟨i, ?_, ?_⟩
  · rw [hident]
    exact upperShift_dominate f M hM N R j k hN hr hj
  · intro z hz
    rw [hident]
    exact (upperShift_local f R j k hj N M hM hN hr (hKR hz)).trans
      (by linarith)

 

theorem exists_upperShiftFamily_approximants
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    ∃ i : ℕ → ℕ, (∀ n z, f z ≤ upperShiftFamily (i n) z) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop, ∀ z ∈ K, upperShiftFamily (i n) z ≤ f z + δ := by
  have hchoice : ∀ n : ℕ, ∃ i : ℕ,
      (∀ z, f z ≤ upperShiftFamily i z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) n,
        upperShiftFamily i z ≤ f z + 1 / ((n : ℝ) + 1)) := by
    intro n
    exact upperShiftFamily_orderDense f M hM _ (isCompact_closedBall _ _)
      _ (by positivity)
  let i : ℕ → ℕ := fun n => Classical.choose (hchoice n)
  refine ⟨i, fun n z => (Classical.choose_spec (hchoice n)).1 z, ?_⟩
  intro K hK δ hδ
  obtain ⟨s, hs⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hR⟩ := exists_nat_ge s
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  filter_upwards [Filter.eventually_ge_atTop (max R k)] with n hn z hz
  have hnR : R ≤ n := (le_max_left _ _).trans hn
  have hnk : k ≤ n := (le_max_right _ _).trans hn
  have hzn : z ∈ Metric.closedBall (0 : ℂ) n := by
    have hzs := Metric.mem_closedBall.mp (hs hz)
    apply Metric.mem_closedBall.mpr
    exact hzs.trans (hR.trans (by exact_mod_cast hnR))
  have hbound := (Classical.choose_spec (hchoice n)).2 z hzn
  exact hbound.trans (add_le_add_right
    ((Nat.one_div_le_one_div hnk).trans hk.le) _)

end SupercriticalLQGUniqueness.B2.PfeWeyl
