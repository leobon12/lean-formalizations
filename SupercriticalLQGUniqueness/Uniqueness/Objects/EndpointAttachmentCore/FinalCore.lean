import SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow.Endpoint
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShadowChecks.Checks




 
set_option autoImplicit false

open Set LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore

 



theorem endpoint_attachment_final_core {Y : Type*} [PseudoEMetricSpace Y]
    {U : Set Y} {P : ℝ → Y} {u : Y}
    {a b s t₁ L q lam X K n T A₁ AN : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) (hs0 : 0 ≤ s)
    (hst : s < t₁) (htL : t₁ ≤ L) (hq : 0 < q)
    (hsmall : t₁ - s < 2 * q)
    (hP : ContinuousOn P (Icc s t₁)) (hU : MapsTo P (Icc s t₁) U)
    (hunit : HasUnitSpeedOn P (Icc 0 L))
    (hA₁nonneg : 0 ≤ A₁)
    (hattach : internalEDist U (P t₁) u ≤ ENNReal.ofReal A₁)
    (hK : 1 ≤ K)
    (hspan : (n - 1) * q ≤ T) (htri : T ≤ A₁ + AN)
    (hA₁ : A₁ ≤ 2 * lam * X + 4 * K * q)
    (hAN : AN ≤ 2 * lam * X + 4 * K * q)
    (hcount : 16 * K ≤ n - 1) :
    ∃ t ∈ Icc a b,
      internalEDist U (P t) u ≤ ENNReal.ofReal (5 * lam * X) := by
  obtain ⟨_, hbudgetReal⟩ :=
    Objects.Shadow.absorb hq hK hspan htri hA₁ hAN hcount
  have hbudget : ENNReal.ofReal A₁ + ENNReal.ofReal (2 * q) ≤
      ENNReal.ofReal (5 * lam * X) := by
    rw [← ENNReal.ofReal_add hA₁nonneg (by positivity)]
    exact ENNReal.ofReal_le_ofReal hbudgetReal
  exact Objects.Shadow.splice_first_hit_back has hsb hs0 hst htL hq hsmall hP hU
    hunit hattach hbudget


 

theorem endpoint_attachment_of_separated_returns
    {ι Y : Type*} [DecidableEq ι] [PseudoEMetricSpace Y]
    (S : Finset ι) (hS : S.Nonempty)
    {U : Set Y} {P : ℝ → Y} {u : Y}
    {a b L q lam X K : ℝ}
    (start finish cost : ι → ℝ)
    (hq : 0 < q) (hK : 1 ≤ K)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → q ≤ |finish i - finish j|)
    (hstart : ∀ i ∈ S, a ≤ start i ∧ start i ≤ b ∧ 0 ≤ start i ∧
      start i < finish i ∧ finish i ≤ L ∧ finish i - start i < 2 * q)
    (hP : ∀ i ∈ S, ContinuousOn P (Icc (start i) (finish i)))
    (hU : ∀ i ∈ S, MapsTo P (Icc (start i) (finish i)) U)
    (hgeo : IsGeodesicCurve P 0 L)
    (hunit : HasUnitSpeedOn P (Icc 0 L))
    (hcost0 : ∀ i ∈ S, 0 ≤ cost i)
    (hattach : ∀ i ∈ S,
      internalEDist U (P (finish i)) u ≤ ENNReal.ofReal (cost i))
    (hpaid : ∀ i ∈ S, cost i ≤ 2 * lam * X + 4 * K * q)
    (hcount : 16 * K ≤ (S.card : ℝ) - 1) :
    ∃ t ∈ Icc a b,
      internalEDist U (P t) u ≤ ENNReal.ofReal (5 * lam * X) := by
  obtain ⟨i, hi, j, hj, hspan⟩ :=
    Objects.ShadowChecks.spread_of_separated finish S hS hsep
  have hiData := hstart i hi
  have hjData := hstart j hj
  have hi0 : finish i ∈ Icc 0 L :=
    ⟨hiData.2.2.1.trans hiData.2.2.2.1.le, hiData.2.2.2.2.1⟩
  have hj0 : finish j ∈ Icc 0 L :=
    ⟨hjData.2.2.1.trans hjData.2.2.2.1.le, hjData.2.2.2.2.1⟩
  have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htime : finish i ≤ finish j := by nlinarith [hspan, hq]
  have hdist := hgeo.edist_eq_of_hasUnitSpeedOn hunit hi0 hj0 htime
  have htri : finish j - finish i ≤ cost i + cost j := by
    have hdistLe : edist (P (finish i)) (P (finish j)) ≤
        ENNReal.ofReal (cost i + cost j) := by
      calc
        edist (P (finish i)) (P (finish j)) ≤
            edist (P (finish i)) u + edist u (P (finish j)) := edist_triangle _ _ _
        _ ≤ internalEDist U (P (finish i)) u +
            internalEDist U (P (finish j)) u := by
          rw [edist_comm u]
          exact add_le_add (edist_le_internalEDist U _ _) (edist_le_internalEDist U _ _)
        _ ≤ ENNReal.ofReal (cost i) + ENNReal.ofReal (cost j) :=
          add_le_add (hattach i hi) (hattach j hj)
        _ = ENNReal.ofReal (cost i + cost j) :=
          (ENNReal.ofReal_add (hcost0 i hi) (hcost0 j hj)).symm
    rw [hdist] at hdistLe
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hcost0 i hi) (hcost0 j hj))).mp hdistLe
  exact endpoint_attachment_final_core hiData.1 hiData.2.1 hiData.2.2.1
    hiData.2.2.2.1 hiData.2.2.2.2.1 hq hiData.2.2.2.2.2
    (hP i hi) (hU i hi) hunit (hcost0 i hi) (hattach i hi) hK
    hspan htri (hpaid i hi) (hpaid j hj) hcount


end SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore
