import HigherDimLQGContinuity.Improve.GridScaling
import HigherDimLQGContinuity.Improve.SiteEligibility
import HigherDimLQGContinuity.Improve.SupplyNear
import HigherDimLQGContinuity.Improve.SiteClass
import HigherDimLQGContinuity.ForcingCount.PathGeom

/-!
# A covered geodesic gives one populated deterministic catalogue
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

open Classical in
theorem q11_catalogue_of_cover {d : ℕ} (hd : 3 ≤ d)
    (K : CountData d)
    {ξbar L Kpin v τ H₀ σ₀ β₀ m M Hsd σsd
      Hup sR Hlo b mc A0 U0 R Hgl σgl βgl Δ V w : ℝ}
    (hξ : 0 < K.ξ) (hξbar : K.ξ ≤ ξbar)
    (hη : 0 < K.η) (hηbar : K.η ≤ ξbar)
    (hL : 0 < L) (hKpin : 0 ≤ Kpin) (Ntr : ℕ)
    {Edge : Type} [Fintype Edge] (centre : Edge → Rd d)
    (H : DistRd d)
    (hGLength : (rho K.D H).IsLength)
    (hgeod : ∃ γ, IsConstSpeedGeod (rho K.D H) K.x K.y γ)
    (hsource : Q11SourceGood (rho K.D H) U0 R Hgl σgl βgl)
    (hR : 16 ≤ R) (hHgl : 1 ≤ Hgl)
    (hσgl : 0 < σgl) (hσgl1 : σgl ≤ 1)
    (hβgl : 1 ≤ βgl) (hmc : 0 < mc) (hA0 : 0 < A0)
    (hv : v ≤ 1)
    (hτ : |K.η - K.ξ| ≤ τ)
    (hτtrial :
      τ ≤ v / (20 * (Real.sqrt (2 * d) + Kpin) *
        (1 + ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| + 3)))
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1 / 4)
    (hΔw : Δ ≤ w / 1000) (hw : 0 < w) (hw1 : w ≤ 1)
    (hΔmax : Δ ≤ min (1 / 4)
      (min (4 ^ βgl / (Hgl * A0)) (mc / Hgl)))
    (hV : 0 ≤ V)
    (hT : ∀ k ∈ p4_fullScales V,
      Δ ^ (2 : ℕ) ≤ p4_radius k ∧ p4_radius k ≤ Δ)
    {ncap : ℕ} (hncap : 2 * V ≤ (ncap : ℝ))
    {nsite : ℕ} (hnsite : 0 < nsite)
    (hm : 0 < Nat.floor (w / (80 * Δ)))
    (hcount :
      (q11ClassSet d V Δ (2 * βgl + 1)).card * nsite ≤
        Nat.floor (w / (80 * Δ)))
    (hx : K.x ∈ closedBall (0 : Rd d) 2)
    (hy : K.y ∈ closedBall (0 : Rd d) 2)
    (hxy : w / 2 ≤ ‖K.x - K.y‖)
    (hcover : ∀ q ∈ closedBall (0 : Rd d) 3,
      ∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
        ‖q - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
          p4_radius k / 10 ∧
        recentre 1 (p4_radius k)
          (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) H ∈
          siteEvent K.D K.E (Finset.univ : Finset Edge) centre L Ntr v
            H₀ σ₀ β₀ m M Hsd σsd Hup sR Hlo b mc A0 Kpin)
    (hscaling : ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
        (countSiteD K p.1 p.2 H = rho K.D (recentre 1 p.1 p.2 H) ∧
         (∃ hratio : 0 < scaleS d K.η 1 p.1 p.2 H /
             scaleS d K.ξ 1 p.1 p.2 H,
           countSiteE K p.1 p.2 H =
             (rho K.E (recentre 1 p.1 p.2 H)).smul
               (scaleS d K.η 1 p.1 p.2 H / scaleS d K.ξ 1 p.1 p.2 H)
               hratio) ∧
         (countSiteD K p.1 p.2 H).IsLength ∧
         (countSiteE K p.1 p.2 H).IsLength) ∧
        ∀ e : Edge, ∀ j : Fin Ntr,
          siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)) ∧
          siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)))
    (hprimaryRatio : ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
      |Real.log (scaleS d K.η 1 p.1 p.2 H /
        scaleS d K.ξ 1 p.1 p.2 H)| ≤ v / 20)
    (hexhaust : ∀ D' E' : ContMetric d,
      D'.IsLength → E'.IsLength → SiteRefs Hup sR Hlo b mc A0 D' →
      (∀ e : Edge, ∃ j : Fin Ntr,
        SeedFav H₀ σ₀ β₀ m M Hsd σsd
          (Real.exp 1 * q11TrialLambda d ξbar L Kpin Ntr) v
          D' E' (centre e) (L / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1))) →
      ∃ ℓ : K.cat.Label, K.cat.Source ℓ D' E') :
    ∃ cl ∈ q11ClassSet d V Δ (2 * βgl + 1),
      let 𝔆 := q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 K.x K.y
      𝔆.Valid K.x K.y ∧
      nsite ≤ (𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card ∧
      (𝔆.Z.card : ℝ) ≤
        (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) := by
  classical
  let P : ℝ → Rd d := q9Path K.D K.x K.y H
  have hP : ContinuousOn P (Icc (0 : ℝ) 1) :=
    (continuous_q9Path K.D K.x K.y H).continuousOn
  obtain ⟨hP0, hP1, -⟩ := q9Path_spec hgeod
  obtain ⟨c, r, k, j, t, hinj, hsupply⟩ :=
    q11_supplied_sites_near (by omega : 2 ≤ d) P hP hP0 hP1
      hw hw1 hΔ hΔw hx hy hxy (p4_fullScales V) hT H _ hcover
  have hki (i : Fin (Nat.floor (w / (80 * Δ)))) : k i ∈ p4_fullScales V := by
    rcases hsupply i with ⟨_, _, _, hki, _, _, _, _, _, _⟩
    exact hki
  have hri (i : Fin (Nat.floor (w / (80 * Δ)))) : r i = p4_radius (k i) := by
    rcases hsupply i with ⟨_, _, hri, _, _, _, _, _, _, _⟩
    exact hri
  have hci (i : Fin (Nat.floor (w / (80 * Δ)))) :
      c i = latPt (r i / (20 * Real.sqrt d)) (j i) := by
    rcases hsupply i with ⟨_, _, _, _, hci, _, _, _, _, _⟩
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hci
  have hgeom (i : Fin (Nat.floor (w / (80 * Δ)))) :
      closedBall (c i) (4 * r i) ⊆ ball (0 : Rd d) 4 ∧
      K.x ∉ closedBall (c i) (4 * r i) ∧
      K.y ∉ closedBall (c i) (4 * r i) := by
    rcases hsupply i with ⟨_, _, _, _, _, _, _, hbox, hxavoid, hyavoid⟩
    exact ⟨hbox, hxavoid, hyavoid⟩
  have hrange (i : Fin (Nat.floor (w / (80 * Δ)))) :
      Δ ^ (2 : ℕ) ≤ r i ∧ r i ≤ Δ := by
    rw [hri i]
    exact hT (k i) (hki i)
  have helig (i : Fin (Nat.floor (w / (80 * Δ)))) :
      (Δ ^ (2 * βgl + 1) ≤ countUnit K (r i) (c i) H ∧
        countUnit K (r i) (c i) H ≤ Δ ^ (-(2 * βgl + 1))) ∧
      ∃ ℓ : K.cat.Label,
        K.cat.Source ℓ (countSiteD K (r i) (c i) H)
          (countSiteE K (r i) (c i) H) := by
    obtain ⟨_, _, _, _, _, hsite, hz3, _, _, _⟩ := hsupply i
    have hrpos : 0 < r i := lt_of_lt_of_le (pow_pos hΔ _) (hrange i).1
    have hpgrid : (r i, c i) ∈
        gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4 := by
      have hcraw : c i = latPt ((1 / (20 * Real.sqrt d)) * p4_radius (k i)) (j i) := by
        rw [← hri i]
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hci i
      have hnorm : ‖c i‖ ≤ 4 := by
        have hh : ‖c i‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hz3
        linarith
      rw [hri i]
      exact q11_primary_grid_mem hV hncap (hki i) hcraw hnorm
    obtain ⟨⟨hD, hE, hLd, hLe⟩, hseed⟩ := hscaling (r i, c i) hpgrid
    have hprimary : countSiteD K (r i) (c i) H =
        rho K.D (recentre 1 (r i) (c i) H) ∧
        ∃ hc : 0 < scaleS d K.η 1 (r i) (c i) H /
            scaleS d K.ξ 1 (r i) (c i) H,
          countSiteE K (r i) (c i) H =
            (rho K.E (recentre 1 (r i) (c i) H)).smul
              (scaleS d K.η 1 (r i) (c i) H /
                scaleS d K.ξ 1 (r i) (c i) H) hc := by
      simpa only using And.intro hD hE
    have hseed' : ∀ e : Edge, ∀ j : Fin Ntr,
        siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
            (recentre 1 (r i) (c i) H) =
          rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
            (recentre 1 (r i) (c i) H)) ∧
        siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
            (recentre 1 (r i) (c i) H) =
          rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
            (recentre 1 (r i) (c i) H)) := by
      simpa only using hseed
    have hs4 : r i ≤ 1 / 4 := (hrange i).2.trans hΔ1
    exact q11_supplied_site_eligible hd K hξ hξbar hη hηbar hL hKpin
      Ntr centre H hrpos (c i) hsite hprimary ⟨hLd, hLe⟩ hseed'
      (hprimaryRatio (r i, c i) hpgrid) hτ hτtrial hv hGLength hsource
      hR hHgl hσgl hσgl1 hβgl hmc hA0 hz3 hs4 hΔ hΔmax (hrange i)
      hexhaust
  have hvisit (i : Fin (Nat.floor (w / (80 * Δ)))) :
      ∃ u ∈ Icc (0 : ℝ) 1,
        q9Path K.D K.x K.y H u ∈ ball (c i) (r i / 10) := by
    rcases hsupply i with ⟨hti, hq, _, _, _, _, _, _, _, _⟩
    exact ⟨t i, hti, hq⟩
  exact q11_sites_to_catalogue (by omega : 1 ≤ d) hm hΔ (by linarith)
    hnsite hcount K H c r k j hinj hki hri hci hgeom hrange
    (fun i => (helig i).1) (fun i => (helig i).2) hvisit

end HigherDimLQGContinuity
