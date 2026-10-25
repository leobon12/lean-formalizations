import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredGeometrySB
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3

 


set_option autoImplicit false
noncomputable section

open Filter Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem smallAnnulusCosts_of_positive_scale
    (G H : ℕ → LSCMetric) (D E : LSCMetric)
    (a : ℝ) (ha : 0 < a)
    (hD : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal a * D p)
    (hG : ∀ᶠ n in atTop, ∀ p : ℂ × ℂ,
      H n p = ENNReal.ofReal a * G n p)
    (K V : Set ℂ) (hsmall : PfeWeyl.SmallAnnulusCosts G D K V) :
    PfeWeyl.SmallAnnulusCosts H E K V := by
  intro z hz hNS δ hδ ρ hρ
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hafin : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨w, hw, hfin⟩ := hNS
  have hDfin : D (z, w) < ⊤ := by
    have hne : ENNReal.ofReal a * D (z, w) ≠ ⊤ := by
      simpa only [← hD (z, w)] using hfin.ne
    by_contra hn
    have htop : D (z, w) = ⊤ := top_le_iff.mp (le_of_not_gt hn)
    exact hne (by rw [htop, ENNReal.mul_top ha0])
  have hNSD : PfeWeyl.IsNonsingular D z := ⟨w, hw, hDfin⟩
  obtain ⟨A, hrat, hcenter, hradius, hinside, hcost⟩ :=
    hsmall z hz hNSD (δ / a) (div_pos hδ ha) ρ hρ
  refine ⟨A, hrat, hcenter, hradius, hinside, ?_⟩
  filter_upwards [hG, hcost] with n hGn hcn
  have hscale := Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale
    (G n) (H n) (ENNReal.ofReal a) ha0 hafin (fun x y => hGn (x, y)) A
  rw [hscale]
  have hmul := (ENNReal.mul_lt_mul_iff_left ha0 hafin).mpr hcn
  simpa only [mul_comm, ← ENNReal.ofReal_mul ha.le,
    mul_div_cancel₀ δ ha.ne'] using hmul

end SupercriticalLQGUniqueness.B2.PfeAxioms
