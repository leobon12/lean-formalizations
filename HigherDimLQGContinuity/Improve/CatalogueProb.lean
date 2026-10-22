import HigherDimLQGContinuity.Improve.CatalogueBudget
import HigherDimLQGContinuity.Improve.Catalogue
import HigherDimLQGContinuity.ForcingCount.Prop45
import HigherDimLQGContinuity.Caps.FullScales

/-!
# Proposition 4.5 for every catalogue in the deterministic union
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem q11_catalogue_prob {d : ℕ} (hd : 3 ≤ d)
    {ξbar a v V Δ θ d0 Cb μ U0 Rsrc mc Hlo dsep A45 k45 : ℝ}
    (hξbar : 0 < ξbar) (hQbar : Real.sqrt (2 * d) < distExp d ξbar)
    (ha : 0 < a) (haξ : a ≤ ξbar)
    (hv : 0 < v)
    (hU0 : 0 < U0) (hdsep : 0 < dsep)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : ∀ k ∈ p4_fullScales V,
      Δ ^ (2 : ℕ) ≤ p4_radius k ∧ p4_radius k ≤ Δ)
    (hdepth : polyB A45 k45 a⁻¹ v⁻¹ ≤ Real.log Δ⁻¹)
    (cat : SiteCatalogue d)
    (hP : Prop45Concl cat θ mc Hlo d0 Cb μ U0 Rsrc
      ((160 * Real.sqrt d + 5) ^ d) (2 * (d : ℝ)) 4
      (4 * min (1 / 4) (dsep / (8 * U0))) A45 k45 v)
    {ξ η : ℝ} (hξ : ξ ∈ Icc a ξbar) (hη : η ∈ Icc a ξbar)
    (hdrift : |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ v / 100)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    {c : ℝ} (hc : c ∈ Icc (1 + 20 * v) Cb)
    {x y : Rd d} (hxy : x ≠ y)
    (hx : x ∈ closedBall (0 : Rd d) 2)
    (hy : y ∈ closedBall (0 : Rd d) 2)
    {K0 cseed εloc : ℝ} (hcseed : 0 ≤ cseed)
    (hcseedCert : cseed ≤ θ * d0 / 2)
    (hεloc : 0 ≤ εloc)
    (hεsmall : εloc ≤ q11Error v cseed Δ K0 U0 dsep)
    {cl : ℕ × (Fin d → ℤ) × ℤ}
    (hcl : cl ∈ q11ClassSet d V Δ K0) :
    let gΔ := q11GainDelta v cseed Δ K0 U0
    let K := prop45Data cat D E ξ η θ mc Hlo x y c gΔ εloc U0 Rsrc Δ
    let 𝔆 := q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 x y
    pinLaw d 10 (countEventB K 𝔆) ≤ ENNReal.ofReal (Δ ^ (2 * μ + 2)) := by
  let gΔ : ℝ := q11GainDelta v cseed Δ K0 U0
  let K : CountData d := prop45Data cat D E ξ η θ mc Hlo x y c gΔ εloc U0 Rsrc Δ
  let 𝔆 : Catalogue d := q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 x y
  have hk : cl.1 ∈ p4_fullScales V := (Finset.mem_product.mp hcl).1
  have hrange := hT cl.1 hk
  have hr : 0 < p4_radius cl.1 := lt_of_lt_of_le (pow_pos hΔ _) hrange.1
  have hvalid : 𝔆.Valid x y :=
    q11_catalogue_valid (by omega : 1 ≤ d) hr (hrange.2.trans hΔ1.le)
      cl.2.1 cl.2.2 x y
  have hcard : (𝔆.Z.card : ℝ) ≤
      (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) :=
    q11_catalogue_card_for_prop45 (by omega : 1 ≤ d) hΔ hΔ1.le
      hrange.1 cl.2.1 cl.2.2 x y
  have hbud := q11_catalogue_budget (d := d) (V := V) (K0 := K0)
    hΔ hv.le hcseed hU0 hdsep hcl
  have hQ : 0 ≤ 𝔆.Q := by dsimp [𝔆, q11Catalogue]; positivity
  have hgainCert : gΔ * U0 ≤ 4 * v * (θ * d0 / 2) * 𝔆.Q := by
    have hh := mul_le_mul_of_nonneg_right hcseedCert (by positivity : 0 ≤ 4 * v * 𝔆.Q)
    have heq1 : 4 * v * cseed * 𝔆.Q = cseed * (4 * v * 𝔆.Q) := by ring
    have heq2 : 4 * v * (θ * d0 / 2) * 𝔆.Q =
        (θ * d0 / 2) * (4 * v * 𝔆.Q) := by ring
    rw [← heq1, ← heq2] at hh
    exact hbud.1.trans hh
  have herrCert : εloc ≤
      (4 * min (1 / 4) (dsep / (8 * U0))) * v * (θ * d0 / 2) * 𝔆.Q := by
    have hh := mul_le_mul_of_nonneg_right hcseedCert
      (by positivity : 0 ≤ (4 * min (1 / 4) (dsep / (8 * U0))) * v * 𝔆.Q)
    have heq1 : (4 * min (1 / 4) (dsep / (8 * U0))) * v * cseed * 𝔆.Q =
        cseed * ((4 * min (1 / 4) (dsep / (8 * U0))) * v * 𝔆.Q) := by ring
    have heq2 : (4 * min (1 / 4) (dsep / (8 * U0))) * v * (θ * d0 / 2) * 𝔆.Q =
        (θ * d0 / 2) * ((4 * min (1 / 4) (dsep / (8 * U0))) * v * 𝔆.Q) := by ring
    rw [← heq1, ← heq2] at hh
    exact (hεsmall.trans hbud.2.1).trans hh
  change pinLaw d 10 (countEventB K 𝔆) ≤ ENNReal.ofReal (Δ ^ (2 * μ + 2))
  exact hP ξbar a hξbar hQbar ha haξ ξ η D E hξ hη hdrift hD hE
    c Δ gΔ εloc hc ⟨hΔ, hΔ1⟩ hdepth
    (by dsimp [gΔ, q11GainDelta]; positivity)
    hεloc x y hxy hx hy 𝔆 hvalid hcard hgainCert herrCert

end HigherDimLQGContinuity
