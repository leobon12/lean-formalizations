import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldCostTransfer




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem shield_two_metric_all_pairs (C : Objects.CorrectedEvent.Constants) (D E : LSCMetric)
    (t : ℝ) (ht : 0 < t) (W : Set ℂ) (hW : ball (0 : ℂ) (3 * t) ⊆ W)
    (hBD : BiLipschitz.Barrier.Barrier D) (hBE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hED : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal Cp * D p)
    (hDE : ∀ p : ℂ × ℂ, D p ≤ ENNReal.ofReal Ci * E p)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (hShield : Objects.Excursions.shieldAt C D t)
    {x y : ℂ} (hx : x ∈ closedBall (0 : ℂ) t)
    (hy : y ∈ closedBall (0 : ℂ) t) :
    (D.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) = D (x,y)) ∧
    (E.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) = E (x,y)) := by
  have hDcheap := shieldAt_strict_zero C D t ht hLam hShield
  have hEa := around_le_mul_of_pointwise D E Cp hCp hED 0 t (2 * t)
  have hDa := acr_le_mul_of_pointwise E D Ci hCi hDE 0 (2 * t) (3 * t)
  have hEfin : Objects.CorrectedEvent.around E 0 t (2 * t) < ⊤ :=
    lt_of_le_of_lt hEa (ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top hShield.1)
  have hEcheap : Objects.CorrectedEvent.around E 0 t (2 * t) <
      Objects.CorrectedEvent.acr E 0 (2 * t) (3 * t) := by
    have hbound : Objects.CorrectedEvent.around E 0 t (2 * t) ≤
        (ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst * ENNReal.ofReal Ci) *
          Objects.CorrectedEvent.acr E 0 (2 * t) (3 * t) := by
      calc
        _ ≤ ENNReal.ofReal Cp * Objects.CorrectedEvent.around D 0 t (2 * t) := hEa
        _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal C.lamConst *
            Objects.CorrectedEvent.acr D 0 (2 * t) (3 * t)) := by gcongr; exact hShield.2
        _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal C.lamConst *
            (ENNReal.ofReal Ci * Objects.CorrectedEvent.acr E 0 (2 * t) (3 * t))) := by
          gcongr
        _ = _ := by ring
    by_cases hEtop : Objects.CorrectedEvent.acr E 0 (2 * t) (3 * t) = ⊤
    · exact hEtop ▸ hEfin
    · have hEpos := shield_acr_pos E 0 t ht
      have hstrict := ENNReal.mul_lt_mul_right hEpos.ne' hEtop hRatio
      exact hbound.trans_lt (by simpa only [mul_comm, one_mul] using hstrict)
  exact ⟨shield_all_pairs D 0 t ht W hW hBD hLD hDcheap hx hy,
    shield_all_pairs E 0 t ht W hW hBE hLE hEcheap hx hy⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
