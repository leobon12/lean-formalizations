import HigherDimLQGContinuity.Improve.HupPair
import HigherDimLQGContinuity.Improve.SourceGeom
import HigherDimLQGContinuity.SiteEvents.NetRounding

/-!
# A source upper violation rounds to a separated net pair
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem q11_hup_round_to_net {d : ℕ}
    {D E : DistRd d → ContMetric d} {H : DistRd d}
    {H0 σ0 β0 m M U0 R Hgl σgl βgl w c Cb gΔ ε t : ℝ}
    (hD : (rho D H).IsLength) (hE : (rho E H).IsLength)
    (hH0 : 0 < H0) (hσ0 : 0 < σ0) (hβ0 : 0 < β0) (hm : 0 < m)
    (hrefs : H ∈ PairRefs D E H0 σ0 β0 m M)
    (hw : 0 < w) (hw1 : w ≤ 1) (hwsub : w ≤ subdivW H0 σ0 β0 m M)
    (hgΔ : 0 < gΔ) (hgΔ1 : gΔ ≤ 1)
    (hc : 1 ≤ c) (hcCb : c ≤ Cb) (hcoef : 0 ≤ c - gΔ / 16)
    (hε : 0 ≤ ε) (ht : 0 < t) (htw : t ≤ w / 8)
    (hR : 16 ≤ R) (hHgl : 1 ≤ Hgl)
    (hσgl : 0 < σgl) (hσgl1 : σgl ≤ 1)
    (hβgl : 1 ≤ βgl)
    (hsource : Q11SourceGood (rho D H) U0 R Hgl σgl βgl)
    (hsmall : 4 * Cb * (2 * Hgl) * t ^ σgl + 2 * ε ≤
      7 / 8 * gΔ * (Hgl⁻¹ * (w / 2) ^ βgl))
    (hcomp : CompOn (rho E H) (rho D H) c ε R)
    (N : Finset (Rd d))
    (hN : ∀ p ∈ N, p ∈ closedBall (0 : Rd d) 2)
    (hnet : ∀ x ∈ closedBall (0 : Rd d) 2,
      ∃ p ∈ N, ‖x - p‖ ≤ t)
    (hup : H ∈ Hup D E (c - gΔ / 16)) :
    ∃ x ∈ N, ∃ y ∈ N,
      w / 2 ≤ ‖x - y‖ ∧
      (c - gΔ) * (rho D H).1 (x, y) ≤ (rho E H).1 (x, y) := by
  obtain ⟨x', hx', y', hy', hsep', hbad'⟩ :=
    q11_hup_separated_pair hD hE hH0 hσ0 hβ0 hm hrefs hw hwsub hgΔ
      hcoef hup
  obtain ⟨x, hx, hxx'⟩ := hnet x' hx'
  obtain ⟨y, hy, hyy'⟩ := hnet y' hy'
  have hb := q11_source_rounding_bounds hsource
    (by linarith : 2 ≤ R + 1) hHgl hσgl hσgl1 (by linarith : 0 < βgl) hw
  have hround := net_rounding
    (by linarith : 2 ≤ R) hc hcCb hε hgΔ hgΔ1
    (by linarith : 0 < 2 * Hgl)
    (by positivity : 0 < Hgl⁻¹ * (w / 2) ^ βgl)
    hσgl hσgl1 hw hw1 ht htw hsmall
    hcomp hb.1 hb.2 hx' hy' (hN x hx) (hN y hy)
    hsep' hbad'
    (by simpa only [norm_sub_rev] using hxx')
    (by simpa only [norm_sub_rev] using hyy')
  exact ⟨x, hx, y, hy, hround⟩

end HigherDimLQGContinuity
