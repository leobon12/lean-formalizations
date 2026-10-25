import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Stochastic

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_weylScale_measurable_shift_of_dg20LimitSkC
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hgeo : ∀ k : ℕ, PfeWeyl.AcrossTailInput P (fun ω => D (h ω))
      ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (F : Ω → C(ℂ, ℝ)) (hF : Measurable F)
    (hFb : ∀ ω, ∃ M : ℝ, ∀ z, |F ω z| ≤ M) :
    ∀ᵐ ω ∂P,
      weylScale (ξ : ℝ) (F ω) (D (h ω)) =
        (D (addFun (h ω) (F ω))).1 := by
  have hLen := B2.DG20Lim.limitLengthSpace0_of_dg20LimitSkC hSkSB
    ξ Q hQ m ε D hm hε hD P h hh
  have hCtrl := B2.DG20Lim.limitEuclideanControl0_of_dg20LimitSkC hSkSB
    ξ Q hQ m ε D hm hε hD P h hh
  exact PfeWeyl.ae_weylScale_eq_of_measurable_shift
    ξ m ε hε D hD P h hh X hX hLen hCtrl hgeo hsmall F hF hFb

theorem ae_addConst_eq_scale_of_dg20LimitSkC_w3
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hgeo : ∀ k : ℕ, PfeWeyl.AcrossTailInput P (fun ω => D (h ω))
      ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      D (addConst (h ω) (c ω)) p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * D (h ω) p := by
  let F : Ω → C(ℂ, ℝ) := fun ω => ContinuousMap.const ℂ (c ω)
  have hF : Measurable F :=
    ContinuousMap.measurable_iff_eval.mpr (fun _ => hc)
  have hFb : ∀ ω, ∃ M : ℝ, ∀ z, |F ω z| ≤ M := by
    intro ω
    exact ⟨|c ω|, fun _ => le_rfl⟩
  have hW := ae_weylScale_measurable_shift_of_dg20LimitSkC
    hSkSB ξ Q hQ m hm ε hε D hD P h hh X hX hgeo hsmall F hF hFb
  have hLen := B2.DG20Lim.limitLengthSpace0_of_dg20LimitSkC hSkSB
    ξ Q hQ m ε D hm hε hD P h hh
  filter_upwards [hW, hLen] with ω hWω hLω p
  exact (congrFun hWω p).symm.trans
    (weylScale_const (ξ : ℝ) (c ω) (D (h ω)) hLω p)

end SupercriticalLQGUniqueness.B2.PfeAxioms
