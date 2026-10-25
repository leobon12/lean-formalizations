import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.DyadicLimit
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section

open Set Metric Filter LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

def dyadicAround (D : LSCMetric) (w : ℂ) (i : ℕ × Bool) : ENNReal :=
  Objects.CorrectedEvent.around D (Objects.BoundaryUnionDyadic.dyadicCenter w i)
    (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2) (Objects.BoundaryUnionDyadic.dyadicOuter w i)

 
theorem dyadic_internal_le_around_plus
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (w : ℂ) (hw : w ≠ 0)
    (hcost : (∑' i : ℕ × Bool, dyadicAround D w i) ≠ ∞)
    (e : ℕ × Bool → ENNReal) (hepos : ∀ i, 0 < e i)
    (hesum : (∑' i, e i) ≠ ∞) :
    D.internal (closedBall 0 ‖w‖)
      (⟨w, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩,
       ⟨0, mem_closedBall_self (norm_nonneg w)⟩) ≤
      (∑' i : ℕ × Bool, dyadicAround D w i) + ∑' i, e i := by
  classical
  have hloop (i : ℕ × Bool) :
      ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
        P '' Icc a b ⊆ Objects.CorrectedEvent.ann (Objects.BoundaryUnionDyadic.dyadicCenter w i)
          (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2) (Objects.BoundaryUnionDyadic.dyadicOuter w i) ∧
        LQGMetric.Disconnects (P '' Icc a b)
          (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
          (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)) ∧
        D.len P a b < dyadicAround D w i + e i := by
    have hAi : dyadicAround D w i ≠ ∞ :=
      ne_top_of_le_ne_top hcost (ENNReal.le_tsum i)
    have hlt : dyadicAround D w i < dyadicAround D w i + e i :=
      ENNReal.lt_add_right hAi (hepos i).ne'
    unfold dyadicAround Objects.CorrectedEvent.around at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨P, a, b, hP, hA, hS, hL⟩ := hlt
    exact ⟨P, a, b, hP, hA, hS, by simpa only [dyadicAround, Objects.CorrectedEvent.around] using hL⟩
  choose P a b hcurve htrace hsep hlen using hloop
  let K : ℕ × Bool → Set ℂ := fun i => P i '' Icc (a i) (b i)
  have hcostloop : (∑' i : ℕ × Bool, D.len (P i) (a i) (b i)) ≠ ∞ := by
    have hle : (∑' i : ℕ × Bool, D.len (P i) (a i) (b i)) ≤
        (∑' i : ℕ × Bool, dyadicAround D w i) + ∑' i, e i := by
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum (fun i => (hlen i).le)
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hcost, hesum⟩) hle
  have hfinite (i : ℕ × Bool) : D.len (P i) (a i) (b i) < ∞ :=
    lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hcostloop
      (ENNReal.le_tsum (f := fun j => D.len (P j) (a j) (b j)) i))
  have hEucl (i : ℕ × Bool) : ContinuousOn (P i) (Icc (a i) (b i)) :=
    BiLipschitz.Barrier.continuousOn_of_barrier D hB (hcurve i) (hfinite i).ne
  have hcompact (i : ℕ × Bool) : IsCompact (K i) := by
    dsimp [K]
    exact isCompact_Icc.image_of_continuousOn (hEucl i)
  have hann (i : ℕ × Bool) : K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i} := by
    exact htrace i
  have hKtrace (i : ℕ × Bool) : K i = P i '' Icc (a i) (b i) := rfl
  calc
    D.internal (closedBall 0 ‖w‖) _ ≤
        ∑' i : ℕ × Bool, D.len (P i) (a i) (b i) :=
      dyadic_internal_le_sum D w hw K P a b hcurve hEucl hKtrace hfinite
        hcompact hann hsep hcostloop
    _ ≤ (∑' i : ℕ × Bool, dyadicAround D w i) + ∑' i, e i := by
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum (fun i => (hlen i).le)

private def dyadicWeight (i : ℕ × Bool) : ENNReal :=
  (2⁻¹ : ENNReal) ^ (i.1 + 2)

private theorem dyadicWeight_pos (i : ℕ × Bool) : 0 < dyadicWeight i := by
  dsimp [dyadicWeight]
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by simp)) _

private theorem dyadicWeight_tsum :
    (∑' i : ℕ × Bool, dyadicWeight i) = 1 := by
  have hgeom : (∑' k : ℕ, (2⁻¹ : ENNReal) ^ (k + 2)) = 2⁻¹ := by
    calc
      _ = (∑' k : ℕ, (2⁻¹ : ENNReal) ^ k) * (2⁻¹ : ENNReal) ^ 2 := by
        simp_rw [pow_add]
        exact ENNReal.tsum_mul_right
      _ = 2⁻¹ := by
        rw [ENNReal.tsum_geometric_two, pow_two, ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
            (by simp : (2 : ENNReal) ≠ ∞), one_mul]
  rw [ENNReal.tsum_prod']
  simp only [dyadicWeight, tsum_fintype, Fintype.sum_bool]
  rw [ENNReal.tsum_add, hgeom]
  exact ENNReal.inv_two_add_inv_two

 

theorem dyadic_internal_le_around_sum
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (w : ℂ) (hw : w ≠ 0)
    (hcost : (∑' i : ℕ × Bool, dyadicAround D w i) ≠ ∞) :
    D.internal (closedBall 0 ‖w‖)
      (⟨w, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩,
       ⟨0, mem_closedBall_self (norm_nonneg w)⟩) ≤
      ∑' i : ℕ × Bool, dyadicAround D w i := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  let e : ℕ × Bool → ENNReal := fun i => (ε : ENNReal) * dyadicWeight i
  have hepos (i : ℕ × Bool) : 0 < e i := by
    dsimp [e]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.coe_pos.mpr hε, dyadicWeight_pos i⟩
  have hesum : (∑' i, e i) = (ε : ENNReal) := by
    dsimp [e]
    rw [ENNReal.tsum_mul_left, dyadicWeight_tsum, mul_one]
  have hesumfinite : (∑' i, e i) ≠ ∞ := by
    rw [hesum]
    exact ENNReal.coe_ne_top
  simpa only [hesum] using
    dyadic_internal_le_around_plus D hB w hw hcost e hepos hesumfinite

 
theorem dyadic_internal_le_around_sum_all
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (w : ℂ) (hw : w ≠ 0) :
    D.internal (closedBall 0 ‖w‖)
      (⟨w, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩,
       ⟨0, mem_closedBall_self (norm_nonneg w)⟩) ≤
      ∑' i : ℕ × Bool, dyadicAround D w i := by
  by_cases htop : (∑' i : ℕ × Bool, dyadicAround D w i) = ∞
  · rw [htop]
    exact le_top
  · exact dyadic_internal_le_around_sum D hB w hw htop


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
