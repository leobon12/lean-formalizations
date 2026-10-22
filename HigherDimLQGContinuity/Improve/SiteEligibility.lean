import HigherDimLQGContinuity.Improve.SiteLabel
import HigherDimLQGContinuity.Improve.SiteWindow
import HigherDimLQGContinuity.Improve.TrialRatio

/-!
# A covered supplied site gives a label and a unit window
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The two pointwise eligibility conditions at a supplied site, after the
finite almost-sure scaling identities and pin-ratio cap are imposed. -/
theorem q11_supplied_site_eligible {d : ℕ} (hd : 3 ≤ d)
    (K : CountData d) {ξbar L Kpin v τ H₀ σ₀ β₀ m M Hsd σsd
      Hup sR Hlo b mc A0 U0 R Hgl σgl βgl Δ : ℝ}
    (hξ : 0 < K.ξ) (hξbar : K.ξ ≤ ξbar)
    (hη : 0 < K.η) (hηbar : K.η ≤ ξbar)
    (hL : 0 < L) (hKpin : 0 ≤ Kpin) (Ntr : ℕ)
    {Edge : Type} [Fintype Edge] (centre : Edge → Rd d)
    (H : DistRd d) {s : ℝ} (hs : 0 < s) (z : Rd d)
    (hsite : recentre 1 s z H ∈
      siteEvent K.D K.E (Finset.univ : Finset Edge) centre L Ntr v
        H₀ σ₀ β₀ m M Hsd σsd Hup sR Hlo b mc A0 Kpin)
    (hprimary :
      countSiteD K s z H = rho K.D (recentre 1 s z H) ∧
      ∃ hc : 0 < scaleS d K.η 1 s z H / scaleS d K.ξ 1 s z H,
        countSiteE K s z H =
          (rho K.E (recentre 1 s z H)).smul
            (scaleS d K.η 1 s z H / scaleS d K.ξ 1 s z H) hc)
    (hlength : (countSiteD K s z H).IsLength ∧
      (countSiteE K s z H).IsLength)
    (hseed : ∀ e : Edge, ∀ j : Fin Ntr,
      siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
          (recentre 1 s z H) =
        rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
          (recentre 1 s z H)) ∧
      siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
          (recentre 1 s z H) =
        rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
          (recentre 1 s z H)))
    (hprimaryRatio :
      |Real.log (scaleS d K.η 1 s z H / scaleS d K.ξ 1 s z H)| ≤ v / 20)
    (hτ : |K.η - K.ξ| ≤ τ)
    (hτtrial :
      τ ≤ v / (20 * (Real.sqrt (2 * d) + Kpin) *
        (1 + ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| + 3)))
    (hv : v ≤ 1)
    (hGLength : (rho K.D H).IsLength)
    (hsource : Q11SourceGood (rho K.D H) U0 R Hgl σgl βgl)
    (hR : 16 ≤ R) (hHgl : 1 ≤ Hgl)
    (hσgl : 0 < σgl) (hσgl1 : σgl ≤ 1)
    (hβgl : 1 ≤ βgl) (hmc : 0 < mc) (hA0 : 0 < A0)
    (hz : z ∈ ball (0 : Rd d) 3) (hs4 : s ≤ 1 / 4)
    (hΔ : 0 < Δ)
    (hΔmax : Δ ≤ min (1 / 4) (min (4 ^ βgl / (Hgl * A0)) (mc / Hgl)))
    (hscale : Δ ^ (2 : ℕ) ≤ s ∧ s ≤ Δ)
    (hexhaust : ∀ D' E' : ContMetric d,
      D'.IsLength → E'.IsLength → SiteRefs Hup sR Hlo b mc A0 D' →
      (∀ e : Edge, ∃ j : Fin Ntr,
        SeedFav H₀ σ₀ β₀ m M Hsd σsd
          (Real.exp 1 * q11TrialLambda d ξbar L Kpin Ntr) v
          D' E' (centre e) (L / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1))) →
      ∃ ℓ : K.cat.Label, K.cat.Source ℓ D' E') :
    (Δ ^ (2 * βgl + 1) ≤ countUnit K s z H ∧
      countUnit K s z H ≤ Δ ^ (-(2 * βgl + 1))) ∧
    ∃ ℓ : K.cat.Label,
      K.cat.Source ℓ (countSiteD K s z H) (countSiteE K s z H) := by
  have hS : 0 < countUnit K s z H := scaleS_pos d K.ξ 1 hs z H
  have hsiteRefs : SiteRefs Hup sR Hlo b mc A0
      (((rho K.D H).affine s hs.ne' z).smul (countUnit K s z H)⁻¹
        (inv_pos.mpr hS)) := by
    have href : SiteRefs Hup sR Hlo b mc A0 (countSiteD K s z H) := by
      simpa only [hprimary.1] using hsite.1
    have hmetric : countSiteD K s z H =
        ((rho K.D H).affine s hs.ne' z).smul (countUnit K s z H)⁻¹
          (inv_pos.mpr hS) := by
      rw [q11_countSiteD_eq_siteNorm K hs z H]
      rfl
    rw [hmetric] at href
    exact href
  have hunit := q11_site_unit_window hd hGLength hsource hR hHgl
    hσgl hσgl1 hβgl hmc (by linarith [hA0]) hz hs hs4 hS
    hsiteRefs hΔ hΔmax hscale
  refine ⟨hunit, ?_⟩
  apply q11_site_label_of_event (by omega : 2 ≤ d) K hξ hξbar hη hηbar hL hKpin Ntr
    centre H hs z hsite hprimary hlength hseed hprimaryRatio ?_ hv hexhaust
  intro e j
  exact q11_trial_ratio_bound (by omega : 2 ≤ d) hξ.le hη.le hL hKpin
    Ntr hτ hτtrial j (centre e) (recentre 1 s z H)
    (hsite.2.2 e (Finset.mem_univ e) j (Finset.mem_range.mpr j.isLt))

end HigherDimLQGContinuity
