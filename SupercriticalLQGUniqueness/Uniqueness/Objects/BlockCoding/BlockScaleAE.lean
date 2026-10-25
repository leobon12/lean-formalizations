import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockScale




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC addConst)

 

theorem ae_blockRaw_addConst_iff
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (c : DistC → ℝ) :
    ∀ᵐ g ∂μ,
      Objects.Excursions.blockRaw C T Ksh Cmid0 D E (addConst g (c g)) ↔
        Objects.Excursions.blockRaw C T Ksh Cmid0 D E g := by
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD c,
    Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q E hE c] with g hgD hgE
  let k : ℝ := Real.exp ((ξ : ℝ) * c g)
  have hk : 0 < k := Real.exp_pos _
  exact blockRaw_iff_of_common_scale C T Ksh Cmid0
    (D g) (E g) (D (addConst g (c g))) (E (addConst g (c g))) k hk
    (fun x y => hgD (x,y)) (fun x y => hgE (x,y)) g

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
