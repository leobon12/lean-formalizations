import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAnnulusCost

 


set_option autoImplicit false
noncomputable section

open Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem tendsto_acrossDist_smul_dilate
    (G : ℕ → LSCMetric) (D : LSCMetric)
    (a : ℕ → Ioi (0 : ℝ)) (b r : Ioi (0 : ℝ))
    (A : EuclideanAnnulus)
    (ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (b : ℝ)))
    (hG : Tendsto (fun n => acrossDist (G n) (A.dilate r r.property))
      atTop (𝓝 (acrossDist D (A.dilate r r.property)))) :
    Tendsto (fun n => acrossDist
      (B2.LscTop.smulMetric (a n) (B2.LscTop.dilate r (G n))) A)
      atTop (𝓝 (acrossDist (B2.LscTop.smulMetric b
        (B2.LscTop.dilate r D)) A)) := by
  simp only [acrossDist_smul_dilate]
  exact ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal ha)
    (Or.inl (ENNReal.ofReal_pos.mpr b.property).ne') hG
    (Or.inr ENNReal.ofReal_ne_top)

end SupercriticalLQGUniqueness.B2.PfeAxioms
