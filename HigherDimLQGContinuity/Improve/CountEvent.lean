import HigherDimLQGContinuity.Improve.CatalogueFromCover
import HigherDimLQGContinuity.Improve.SourceGeom

/-!
# From a populated catalogue to the forcing-count event
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

open Classical in
/-- The source event, rounded pair gap, and a populated catalogue are exactly
the four clauses of `countEventB`. -/
theorem q11_countEventB_of_catalogue {d nsite : ℕ}
    (K : CountData d) (H : DistRd d) (𝔆 : Catalogue d)
    {Hgl σgl βgl : ℝ}
    (hsource : Q11SourceGood (rho K.D H) K.U₀ K.Rsrc Hgl σgl βgl)
    (hU0 : 0 ≤ K.U₀)
    (hx : K.x ∈ closedBall (0 : Rd d) 2)
    (hy : K.y ∈ closedBall (0 : Rd d) 2)
    (hcomp : CompOn (rho K.E H) (rho K.D H) K.c K.ηloc K.Rsrc)
    (hgap : (K.c - K.gΔ) * (rho K.D H).1 (K.x, K.y) ≤
      (rho K.E H).1 (K.x, K.y))
    (hthreshold : K.Δ ^ (-(1 / 2 : ℝ)) ≤ (nsite : ℝ))
    (helig : nsite ≤
      (𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card) :
    H ∈ countEventB K 𝔆 := by
  have hpair : (rho K.D H).1 (K.x, K.y) ≤ K.U₀ :=
    (q11_source_pair_le hsource hU0 hx hy).trans (by linarith)
  have hcard : K.Δ ^ (-(1 / 2 : ℝ)) ≤
      ((𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card : ℝ) := by
    exact hthreshold.trans (by exact_mod_cast helig)
  exact ⟨hcomp, hgap, hpair, hsource.2.1, hcard⟩

end HigherDimLQGContinuity
