import SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment.CorrectedComparator




 





set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

 

theorem sup_good_separator (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ)
    (hgood : Objects.CorrectedEvent.supGood C D c s l k) :
    ∃ (π : ℝ → ℂ) (a b : ℝ), D.IsCurve π a b ∧
      π '' Icc a b ⊆ Objects.CorrectedEvent.ann (Objects.CorrectedEvent.cellCenter c s l)
        ((2+1/20)*Objects.CorrectedEvent.supRadius C k) ((3-1/20)*Objects.CorrectedEvent.supRadius C k) ∧
      LQGMetric.Disconnects (π '' Icc a b)
        (sphere (Objects.CorrectedEvent.cellCenter c s l) ((2+1/20)*Objects.CorrectedEvent.supRadius C k))
        (sphere (Objects.CorrectedEvent.cellCenter c s l) ((3-1/20)*Objects.CorrectedEvent.supRadius C k)) ∧
      D.len π a b < ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) *
        Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
          ((1+1/20)*Objects.CorrectedEvent.supRadius C k) ((2-1/20)*Objects.CorrectedEvent.supRadius C k) := by
  dsimp [Objects.CorrectedEvent.supGood] at hgood
  rcases hgood with ⟨_, hpos, hfin, hcompare⟩
  have hsmall : ENNReal.ofReal (1/2 * Real.exp (-C.ξ*C.A_max)) <
      ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    have hexp := Real.exp_pos (-C.ξ*C.A_max)
    nlinarith
  have hprod := ENNReal.mul_lt_mul_right hpos.ne' hfin.ne hsmall
  have hprod' : ENNReal.ofReal (1/2 * Real.exp (-C.ξ*C.A_max)) *
        Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
          ((1+1/20)*Objects.CorrectedEvent.supRadius C k) ((2-1/20)*Objects.CorrectedEvent.supRadius C k) <
      ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) *
        Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
          ((1+1/20)*Objects.CorrectedEvent.supRadius C k) ((2-1/20)*Objects.CorrectedEvent.supRadius C k) := by
    simpa only [mul_comm] using hprod
  have hB := hcompare.trans_lt hprod'
  exact EndpointAttachment.exists_corrected_loop_lt D (Objects.CorrectedEvent.cellCenter c s l)
    ((2+1/20)*Objects.CorrectedEvent.supRadius C k) ((3-1/20)*Objects.CorrectedEvent.supRadius C k) hB


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare
