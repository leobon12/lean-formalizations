import HigherDimLQGContinuity.Improve.ScalingFamily
import HigherDimLQGContinuity.Improve.SeedTransfer
import HigherDimLQGContinuity.Improve.SeedRatios
import HigherDimLQGContinuity.SiteEvents.SiteEvent

/-!
# From a whole-site event to one forcing label
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A covered primary site has an eligible label once the finite scaling
identities and parameter-ratio bounds have been imposed. -/
theorem q11_site_label_of_event {d : ℕ} (hd : 2 ≤ d)
    (K : CountData d) {ξbar L Kpin v H₀ σ₀ β₀ m M Hsd σsd Hup sR Hlo b mc A0 : ℝ}
    (hξ : 0 < K.ξ) (hξbar : K.ξ ≤ ξbar)
    (hη : 0 < K.η) (hηbar : K.η ≤ ξbar)
    (hL : 0 < L) (hKpin : 0 ≤ Kpin) (Ntr : ℕ)
    {Edge : Type} [Fintype Edge] (centre : Edge → Rd d)
    (H : DistRd d) {s : ℝ} (_hs : 0 < s) (z : Rd d)
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
    (hseedRatio : ∀ e : Edge, ∀ j : Fin Ntr,
      |Real.log (scaleS d K.η 1 (seedTrialRadius L j) (centre e)
          (recentre 1 s z H) /
        scaleS d K.ξ 1 (seedTrialRadius L j) (centre e)
          (recentre 1 s z H))| ≤ v / 20)
    (hv : v ≤ 1)
    (hexhaust : ∀ D' E' : ContMetric d,
      D'.IsLength → E'.IsLength → SiteRefs Hup sR Hlo b mc A0 D' →
      (∀ e : Edge, ∃ j : Fin Ntr,
        SeedFav H₀ σ₀ β₀ m M Hsd σsd
          (Real.exp 1 * q11TrialLambda d ξbar L Kpin Ntr) v
          D' E' (centre e) (L / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1))) →
      ∃ ℓ : K.cat.Label, K.cat.Source ℓ D' E') :
    ∃ ℓ : K.cat.Label,
      K.cat.Source ℓ (countSiteD K s z H) (countSiteE K s z H) := by
  let g : DistRd d := recentre 1 s z H
  let A : ContMetric d := countSiteD K s z H
  let B : ContMetric d := countSiteE K s z H
  obtain ⟨hA, hc, hB⟩ := hprimary
  let cscale : ℝ := scaleS d K.η 1 s z H / scaleS d K.ξ 1 s z H
  have hLtrial : 1 ≤ q11TrialLambda d ξbar L Kpin Ntr :=
    q11_trialLambda_one_le (le_trans hξ.le hξbar)
      hKpin L Ntr
  have hsiteRefs : SiteRefs Hup sR Hlo b mc A0 A := by
    simpa only [A, hA] using hsite.1
  apply hexhaust A B hlength.1 hlength.2 hsiteRefs
  intro e
  obtain ⟨j, hj, htrial⟩ := hsite.2.1 e (Finset.mem_univ e)
  let jf : Fin Ntr := ⟨j, Finset.mem_range.mp hj⟩
  let r : ℝ := seedTrialRadius L jf
  have hr : 0 < r := seedTrialRadius_pos hL jf
  let SD : ℝ := scaleS d K.ξ 1 r (centre e) g
  let SF : ℝ := scaleS d K.η 1 r (centre e) g
  let SE : ℝ := cscale * SF
  have hSD : 0 < SD := scaleS_pos d K.ξ 1 hr _ _
  have hSF : 0 < SF := scaleS_pos d K.η 1 hr _ _
  have hSE : 0 < SE := mul_pos hc hSF
  have hcap : |sphereAvg g r (centre e)| ≤ Kpin := by
    simpa only [r, jf] using hsite.2.2 e (Finset.mem_univ e) j hj
  have hSDwin := q11_trial_scale_window hd hξ.le hξbar hL Ntr jf
    (centre e) g hcap
  have hSFwin := q11_trial_scale_window hd hη.le hηbar hL Ntr jf
    (centre e) g hcap
  have hwin := q11_seed_ratio_window hLtrial hSD hSF hc hv
    hSDwin.1 hSDwin.2 hSFwin.1 hSFwin.2 hprimaryRatio
    (hseedRatio e jf)
  dsimp only at hwin
  rcases hwin with ⟨hSDlo, hSDhi, hSElo, hSEhi, hratio⟩
  have hnorm := q11_seed_normalization_of_scaling hr hc (centre e) A B
    (by simpa only [A, g] using hA)
    (by simpa only [B, g] using hB)
    (hseed e jf).1 (hseed e jf).2
  refine ⟨jf, ?_⟩
  have hrad : r = L / 4 * (8 : ℝ)⁻¹ ^ ((jf : ℕ) + 1) := by
    dsimp [r, seedTrialRadius]
    norm_num
  rw [← hrad]
  exact q11_seedFav_of_trial hr.ne' hSD hSE hSDlo hSDhi hSElo hSEhi
    (by simpa only [SE, SD, SF, cscale] using hratio)
    (by simpa only [SD, A, g] using hnorm.1)
    (by simpa only [SE, SF, B, g] using hnorm.2)
    htrial

end HigherDimLQGContinuity
