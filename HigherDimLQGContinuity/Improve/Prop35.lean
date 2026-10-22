import HigherDimLQGContinuity.Improve.SiteFixed
import HigherDimLQGContinuity.Improve.SourceGood
import HigherDimLQGContinuity.Improve.CapGrid
import HigherDimLQGContinuity.ForcingCount.Prop45
import HigherDimLQGContinuity.Discharge.Estimates
import HigherDimLQGContinuity.SiteEvents.CoverFull
import HigherDimLQGContinuity.Events.RefsProb
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGContinuity.Improve.ClassDepth
import HigherDimLQGContinuity.Improve.ExpThreshold
import HigherDimLQGContinuity.Improve.RoundingPower
import HigherDimLQGContinuity.Improve.StepChoice
import HigherDimLQGContinuity.Improve.GainMesh
import HigherDimLQGContinuity.Improve.DriftCube
import HigherDimLQGContinuity.Improve.LinearDenom
import HigherDimLQGContinuity.Improve.ExponentChoice
import HigherDimLQGContinuity.Improve.PinWindow
import HigherDimLQGContinuity.Improve.FullScaleMesh
import HigherDimLQGContinuity.Improve.Net
import HigherDimLQGContinuity.Improve.CatalogueUnionProb
import HigherDimLQGContinuity.Improve.CatalogueProb
import HigherDimLQGContinuity.Improve.GridScaling
import HigherDimLQGContinuity.ForcingCount.Good
import HigherDimLQGContinuity.Improve.HupMono
import HigherDimLQGContinuity.Improve.PointwiseRounding
import HigherDimLQGContinuity.Improve.CatalogueFromCover
import HigherDimLQGContinuity.Improve.CountEvent
import HigherDimLQGContinuity.Improve.SiteThreshold
import HigherDimLQGContinuity.Improve.EventBudget

/-! Proposition 3.5 from the certified site interface and unconditional estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
namespace HigherDimLQGContinuity
open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

/-- Proposition 3.5: the upper improvement estimate under the certified site interface. -/
theorem prop35_of {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ}
    (hbar : ξbar ∈ subcritSet d) (hcert : SiteCertOfLabel d) :
    Prop35Shape d ξbar := by
  classical
  intro Cb pt hCb hpt
  have hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s := by
    intro s hs
    exact uniformEstimates_holds hd hbar hs.1 hs.2
  obtain ⟨μgap, hμgap, -, -, -, hgap⟩ := gap24 (by omega : 2 ≤ d) hbar
  have hQbar : Real.sqrt (2 * d) < distExp d ξbar := by
    have hgg := (hgap ξbar ⟨hbar.1, le_rfl⟩).2
    have hdiv : 0 < μgap / ξbar := div_pos hμgap hbar.1
    linarith only [hgg, hdiv]
  obtain ⟨Hr0, σr0, βr0, m0, M0, hσr0, hσr01, hβr0, hm0, hmM0,
    hHr0, hrefprob⟩ := refs_prob (by omega : 2 ≤ d)
      (by norm_num : (0 : ℝ) < 10) (hU 10 (by norm_num))
      (show 0 < pt / 4 by positivity)
  obtain ⟨U0, Rsrc, Hgl, σgl, βgl, hU0, hRsrc, hHgl,
    hσgl, hσgl1, hβgl, hsourceprob⟩ := q11_source_good_prob hd
      (hU 10 (by norm_num)) hpt
  obtain ⟨Kcov, Ccov, hKcov, hCcov, hcover⟩ :=
    cover210_full_ann4 (by omega : 2 ≤ d)
  let psite : ℝ := (2 : ℝ) ^ (-Kcov * (2 * (d : ℝ) + 2))
  have hpsite : 0 < psite := by dsimp [psite]; positivity
  obtain ⟨S⟩ := q11_site_fixed_exists hd hU hpsite
  obtain ⟨Edge, inst, centre, L, hL, hball, hprest⟩ :=
    prop45 hd hcert S.Hup S.sR S.Hlo S.b S.mc S.A0
      S.hHup S.hsR S.hsR1 S.hHlo S.hb S.hmc S.hA0
  letI : Fintype Edge := inst
  obtain ⟨Ntr, Kpin, hKpin, hsiteprob⟩ :=
    S.select centre hL (fun e => (hball e).trans interior_subset)
  let Λ : ℝ := Real.exp 1 * q11TrialLambda d ξbar L Kpin Ntr
  have hΛ : 1 ≤ Λ := by
    have htrial := q11_trialLambda_one_le (d := d) hbar.1.le hKpin L Ntr
    dsimp [Λ]
    nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  obtain ⟨d0, vsite, Ap, kp, hd0, hvsite, hvsite1, hP45rest⟩ :=
    hprest Ntr S.H0 S.σ0 S.β0 S.m S.M S.Hsd S.σsd Λ
      S.hH0 S.hσ0 S.hσ01 S.hβ0 S.hm S.hmM
      S.hHsd S.hσsd S.hσsd1 hΛ
  let w : ℝ := min (subdivW Hr0 σr0 βr0 m0 M0) (1 / 128)
  have hw : 0 < w := lt_min (subdivW_pos (by linarith) hm0) (by norm_num)
  have hwsub : w ≤ subdivW Hr0 σr0 βr0 m0 M0 := min_le_left _ _
  have hw1 : w ≤ 1 := by dsimp [w]; linarith [min_le_right (subdivW Hr0 σr0 βr0 m0 M0) (1 / 128)]
  let dsep : ℝ := Hgl⁻¹ * (w / 2) ^ βgl
  have hdsep : 0 < dsep := by dsimp [dsep]; positivity
  let K0 : ℝ := 2 * βgl + 1
  have hK0 : 0 ≤ K0 := by dsimp [K0]; linarith
  let γ : ℝ := (K0 + 1) / σgl
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  let Dnet : ℝ := 2 * (d : ℝ) * γ + 1
  have hDnet : 0 ≤ Dnet := by dsimp [Dnet]; positivity
  let μ : ℝ := Dnet + 3
  have hμ : 0 ≤ μ := by dsimp [μ]; linarith
  let Ccat : ℝ := (160 * Real.sqrt d + 5) ^ d
  have hCcat : 0 < Ccat := by dsimp [Ccat]; positivity
  have hD0 : 0 < 2 * (d : ℝ) := by exact_mod_cast (by omega : 0 < 2 * d)
  let cε : ℝ := min (1 / 4) (dsep / (8 * U0))
  have hcε : 0 < cε := by dsimp [cε]; positivity
  have hcη0 : 0 ≤ 4 * cε := by dsimp [cε]; positivity
  have hcη1 : 4 * cε ≤ 1 := by
    dsimp [cε]
    linarith [min_le_left (1 / 4 : ℝ) (dsep / (8 * U0))]
  obtain ⟨A45, k45, hP45⟩ :=
    hP45rest Cb μ U0 Rsrc Ccat (2 * (d : ℝ)) 4 (4 * cε)
      hCb hμ hU0 hRsrc hCcat hD0 (by norm_num) hcη0 hcη1
  obtain ⟨Ccap, CcapFail, ccap, hCcap, hCcapFail, hccap, hcapgrid⟩ :=
    q11_primary_cap_grid hd
  obtain ⟨Lclass, hLclass, hclass⟩ := q11_class_count_depth (d := d) hK0 hw
  obtain ⟨LclassCard, hLclassCard, hclassCard⟩ :=
    q11_class_count_exp_le (d := d) hK0 hw hw1
  let Δmax : ℝ := min (1 / 4)
    (min (4 ^ βgl / (Hgl * S.A0)) (S.mc / Hgl))
  have hHloPos : 0 < S.Hlo := lt_of_lt_of_le one_pos S.hHlo
  have hA0pos : 0 < S.A0 := lt_of_lt_of_le
    (inv_pos.mpr hHloPos) S.hA0
  have hΔmax : 0 < Δmax := by
    dsimp [Δmax]
    exact lt_min (by norm_num)
      (lt_min (div_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (mul_pos (lt_of_lt_of_le one_pos hHgl) hA0pos))
        (div_pos S.hmc (lt_of_lt_of_le one_pos hHgl)))
  obtain ⟨Lunits, hLunits, hunits⟩ := q11_exp_small_threshold hΔmax
  obtain ⟨Lw, hLw, hwsmall⟩ := q11_exp_small_threshold
    (show 0 < w / 1000 by positivity)
  obtain ⟨Lfloor, hLfloor, hfloor⟩ := q11_exp_small_threshold
    (show 0 < w / 80 by positivity)
  obtain ⟨Lquarter, hLquarter, hquarter⟩ := q11_exp_small_threshold
    (show 0 < (1 / 4 : ℝ) by norm_num)
  obtain ⟨Lcover, hLcover, hcovsmall⟩ :=
    q11_exp_decay_rate_threshold
      (show 0 < Ccov * (1 + 3) ^ d by positivity)
      (show 0 < pt / 16 by positivity) (show 0 < (1 : ℝ) by norm_num)
  obtain ⟨Lcap, hLcap, hcapsmall⟩ :=
    q11_exp_decay_rate_threshold hCcapFail
      (show 0 < pt / 16 by positivity) hccap
  let T : ℝ := min (w / 8)
    ((7 * dsep / (128 * Cb * Hgl * U0)) ^ (1 / σgl))
  have hT : 0 < T := by dsimp [T]; positivity
  have hconst : 0 < (9 * Real.sqrt d / T) ^ (2 * d) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  obtain ⟨Lnet, hLnet, hnetsmall⟩ :=
    q11_exp_small_threshold (inv_pos.mpr hconst)
  obtain ⟨Lprob, hLprob, hprobsmall⟩ :=
    q11_exp_small_threshold (show 0 < pt / 4 by positivity)
  let Laux : ℝ := Lclass + LclassCard + Lunits + Lw + Lfloor +
    Lquarter + Lcover + Lcap + Lnet + Lprob + 1
  have hLaux : 1 ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLclass' : Lclass ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLclassCard' : LclassCard ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLunits' : Lunits ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLw' : Lw ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLfloor,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLfloor' : Lfloor ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw,
      hLquarter, hLcover, hLcap, hLnet, hLprob]
  have hLquarter' : Lquarter ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLcover, hLcap, hLnet, hLprob]
  have hLcover' : Lcover ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcap, hLnet, hLprob]
  have hLcap' : Lcap ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLnet, hLprob]
  have hLnet' : Lnet ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLprob]
  have hLprob' : Lprob ≤ Laux := by
    dsimp [Laux]
    linarith only [hLclass, hLclassCard, hLunits, hLw, hLfloor,
      hLquarter, hLcover, hLcap, hLnet]
  let Rcap : ℝ := 20 * (Real.sqrt (2 * d) + Ccap)
  have hRcap : 0 < Rcap := by
    dsimp [Rcap]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  let Rtrial : ℝ := 20 * (Real.sqrt (2 * d) + Kpin) *
    (1 + ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| + 3)
  have hRtrial : 0 < Rtrial := by
    dsimp [Rtrial]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hsum : 0 ≤ ∑ i ∈ Finset.range Ntr,
        |Real.log (seedTrialRadius L i)| := Finset.sum_nonneg
          (fun _ _ => abs_nonneg _)
    positivity
  let B : ℝ := q11FinalExponent K0 S.C4 γ U0 cε S.c4 Rcap Rtrial T
  have hBdata := q11_final_exponent_bounds
    (K0 := K0) (C4 := S.C4) (γ := γ) (U0 := U0)
    (cε := cε) (c4 := S.c4) (Rcap := Rcap) (Rtrial := Rtrial) (T := T)
    hK0 S.hC4.le hγ
  rcases hBdata with ⟨hB, hBg, hBe, hBdr, hBc4, hBcap, hBtrial, hBT⟩
  let v0 : ℝ := min vsite (min (S.vbase / 2) (1 / 100))
  have hv0 : 0 < v0 := by
    dsimp [v0]
    exact lt_min hvsite (lt_min (by linarith only [S.hvbase]) (by norm_num))
  have hv01 : v0 ≤ 1 / 2 := by
    dsimp [v0]
    linarith [min_le_right vsite (min (S.vbase / 2) (1 / 100)),
      min_le_right (S.vbase / 2) (1 / 100)]
  let dclip : ℝ := min 1 (d0 / 2)
  let Cstep : ℝ := max Laux (max 0 (Real.log dclip⁻¹))
  let Astep : ℝ := 4 * (|A45| + |Ap| + Cstep + 3)
  let kstep : ℝ := max (max k45 kp) 1
  let Afinal : ℝ := B * Astep
  have hstep (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) ξbar)
      (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) v0) :
      ∃ gn εs ts : ℝ,
        Real.exp (-polyB Afinal kstep a⁻¹ v⁻¹) ≤ gn ∧
        gn ≤ v ∧ 0 < εs ∧ εs ≤ v ∧
        Real.log εs⁻¹ ≤ polyB Afinal kstep a⁻¹ v⁻¹ ∧
        Real.exp (-polyB Afinal kstep a⁻¹ v⁻¹) ≤ ts ∧
        ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, |η - ξ| ≤ ts →
          ∀ D E : DistRd d → ContMetric d,
            IsStrongExpMetric d ξ (distExp d ξ) D →
            IsStrongExpMetric d η (distExp d η) E →
            ∀ c : ℝ, 1 + 20 * v ≤ c → c ≤ Cb →
              pinLaw d 10 {H | ¬CompOn (rho E H) (rho D H) c εs Rsrc} ≤
                ENNReal.ofReal (pt / 4) →
              pinLaw d 10 (Hup D E (c - gn)) ≤ ENNReal.ofReal pt := by
    have ha0 : 0 < a := ha.1
    have haξ : a ≤ ξbar := ha.2
    have hv0' : 0 < v := hv.1
    have hvsite' : v ≤ vsite := by
      have hh : v0 ≤ vsite := by dsimp [v0]; exact min_le_left _ _
      linarith only [hv.2, hh]
    have hvbase' : v < S.vbase := by
      have hh : v0 ≤ S.vbase / 2 := by
        dsimp [v0]
        exact (min_le_right vsite _).trans (min_le_left _ _)
      linarith only [hv.2, hh, S.hvbase]
    have hv1 : v ≤ 1 := by linarith only [hv.2, hv01]
    obtain ⟨cat, θ, ς, δsep, εnet, εatt, hsite, hP45v⟩ :=
      hP45 v ⟨hv0', hvsite'⟩
    obtain ⟨hθlo, hθ1, hς, hδsep, hεnet, hεatt,
      hJ, hprof, hmeas, hloc, hrefs, hexhaust, hforce⟩ := hsite
    have hθ : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθlo
    let V : ℝ := polyB Astep kstep a⁻¹ v⁻¹
    let Δ : ℝ := Real.exp (-V)
    obtain ⟨hV1, hLV, haV, hvV, hPS, hP45depth, hΔvc⟩ :=
      q11_step_choice hLaux hd0 ha0 hv0' hθ hθ1 hθlo
    let cseed : ℝ := min 1 (θ * d0 / 2)
    have hseed := q11_seed_clip hθ hθ1.le hd0
    have hcseed : 0 < cseed := hseed.2.1
    have hcseed1 : cseed ≤ 1 := hseed.2.2.1
    have hcseedCert : cseed ≤ θ * d0 / 2 := hseed.2.2.2.2
    have hΔpos : 0 < Δ := by dsimp [Δ]; positivity
    have hΔ1 : Δ ≤ 1 := by
      dsimp [Δ]
      have hVnonneg : 0 ≤ V := (by norm_num : (0 : ℝ) ≤ 1).trans hV1
      exact (Real.exp_le_exp.mpr (neg_nonpos.mpr hVnonneg)).trans_eq Real.exp_zero
    have hΔw : Δ ≤ w / 1000 := hwsmall V (hLw'.trans hLV)
    have hΔfloor : Δ ≤ w / 80 := hfloor V (hLfloor'.trans hLV)
    have hΔquarter : Δ ≤ 1 / 4 := hquarter V (hLquarter'.trans hLV)
    have hΔmax' : Δ ≤ Δmax := hunits V (hLunits'.trans hLV)
    have hclass' := hclass V (hLclass'.trans hLV)
    have hclassCard' := hclassCard V (hLclassCard'.trans hLV)
    have hcap := hcapgrid V hV1
    have hscales := q11_full_scale_mesh (by linarith only [hV1] : 0 ≤ V)
    let e : ℝ := Real.exp (-(B * V))
    obtain ⟨he, hev, heg, heε, hedr⟩ :=
      q11_gain_mesh_bounds hv0' hcseed hcseed1 hV1 rfl hΔvc
        hU0 hdsep hB hBg hBe hBdr
    have hsiteDrift : e ≤ S.c4 * v ^ S.C4 := by
      have hh := q11_exp_below_power hV1 S.hc4 hBc4
      have hΔv : Δ ≤ v := hΔvc.trans
        (mul_le_of_le_one_right hv0'.le hcseed1)
      have hpow := Real.rpow_le_rpow hΔpos.le hΔv S.hC4.le
      have hh' : e ≤ S.c4 * Δ ^ S.C4 := by simpa only [e, Δ] using hh
      exact hh'.trans
        (mul_le_mul_of_nonneg_left hpow S.hc4.le)
    have htrialDrift : e ≤ v / Rtrial := by
      have hh := q11_exp_below_power hV1
        (show 0 < 1 / Rtrial by positivity) hBtrial
      have hΔv : Δ ≤ v := hΔvc.trans
        (mul_le_of_le_one_right hv0'.le hcseed1)
      have heq : (1 / Rtrial) * Δ = Δ / Rtrial := by ring
      have hh' : e ≤ Δ / Rtrial := by
        have hh0 : e ≤ (1 / Rtrial) * Δ := by
          simpa only [e, Δ, Real.rpow_one] using hh
        rwa [heq] at hh0
      exact hh'.trans (div_le_div_of_nonneg_right hΔv hRtrial.le)
    have hcapDrift : e * (3 * V + 4) ≤ Δ / Rcap := by
      have hh := q11_exp_below_linear_denom hV1
        (show 0 < 1 / Rcap by positivity) hBcap
      change e * (3 * V + 4) ≤ (1 / Rcap) * Δ at hh
      rwa [show (1 / Rcap) * Δ = Δ / Rcap by ring] at hh
    have hdrift : ∀ ξ ∈ Icc a ξbar, ∀ η : ℝ, |η - ξ| ≤ e →
        |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ v / 100 := by
      intro ξ hξ η hηξ
      exact q11_drift_of_cube ha0 hξ.1 hθ hθ1 hθlo hPS haV
        rfl (hΔvc.trans (mul_le_of_le_one_right hv0'.le hcseed1))
        he.le hedr hηξ
    let gΔ : ℝ := q11GainDelta v cseed Δ K0 U0
    have hgain := q11_gain_error_bounds hv0' hcseed hcseed1
      hΔpos hΔ1 hK0 hU0 hdsep
    let t : ℝ := q11RoundingRadius w Cb Hgl σgl gΔ dsep
    have hεround : 2 * e ≤ 7 / 16 * gΔ * dsep := by
      have hh := hgain.2.2.2.2
      linarith only [heε, hh]
    obtain ⟨ht, htw, hroundsmall⟩ :=
      q11_rounding_radius_spec hw (by linarith only [hCb])
        (lt_of_lt_of_le one_pos hHgl) hσgl hgain.1 hdsep hεround
    have ht1 : t ≤ 1 := by linarith only [htw, hw1]
    have hpower := q11_rounding_radius_power hw
      (by linarith only [hCb]) (lt_of_lt_of_le one_pos hHgl)
      hσgl hv0' hcseed hΔpos hΔ1 hΔvc hK0
      (lt_of_lt_of_le one_pos hU0) hdsep
    have htlow : T * Δ ^ γ ≤ t := by
      simpa only [T, γ, t, gΔ] using hpower.2.2
    have het : e ≤ t := by
      have hepow : e ≤ T * Δ ^ γ := by
        simpa only [e, Δ] using q11_exp_below_power hV1 hT hBT
      exact hepow.trans htlow
    obtain ⟨N, hNinside, hNcard, hNcover⟩ :=
      q11_ball_net_of_radius (by omega : 1 ≤ d) ht
    have hnetconstant : (9 * Real.sqrt d / T) ^ (2 * d) ≤ Δ⁻¹ := by
      have hh := hnetsmall V (hLnet'.trans hLV)
      have hh' := (inv_le_inv₀ (inv_pos.mpr hconst) hΔpos).2 hh
      simpa only [inv_inv] using hh'
    have hclassCardMesh :
        ((q11ClassSet d V Δ K0).card : ℝ) ≤ Δ ^ (-(1 : ℝ)) := by
      have heq : Δ ^ (-(1 : ℝ)) = Real.exp V := by
        rw [Real.rpow_neg_one]
        dsimp [Δ]
        rw [Real.exp_neg]
        simp
      rw [heq]
      exact hclassCard'
    have hprobMesh : Δ ^ μ ≤ pt / 4 := by
      have hμ1 : 1 ≤ μ := by dsimp [μ]; linarith only [hDnet]
      have hpow : Δ ^ μ ≤ Δ := by
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_ge hΔpos hΔ1 hμ1 :
            Δ ^ μ ≤ Δ ^ (1 : ℝ))
      exact hpow.trans (hprobsmall V (hLprob'.trans hLV))
    have hΔlt1 : Δ < 1 := by
      dsimp [Δ]
      exact Real.exp_lt_one_iff.mpr (by linarith only [hV1])
    have hdepth : polyB A45 k45 a⁻¹ v⁻¹ ≤ Real.log Δ⁻¹ := by
      have heq : Real.log Δ⁻¹ = V := by
        dsimp [Δ]
        rw [Real.exp_neg, inv_inv, Real.log_exp]
      rw [heq]
      exact hP45depth
    let nsite : ℕ := ⌈Real.exp (V / 2)⌉₊
    have hnsite : 0 < nsite :=
      Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
    have hfloorPos : 0 < Nat.floor (w / (80 * Δ)) := by
      apply Nat.floor_pos.mpr
      rw [le_div_iff₀ (by positivity : 0 < 80 * Δ)]
      nlinarith only [hΔfloor, hw]
    have hclassCount : (q11ClassSet d V Δ K0).card * nsite ≤
        Nat.floor (w / (80 * Δ)) := by
      have heq : w / (80 * Δ) = (w / 80) * Real.exp V := by
        dsimp [Δ]
        rw [Real.exp_neg]
        field_simp
      simpa only [nsite, Δ, heq] using hclass'
    have hrun (ξ : ℝ) (hξ : ξ ∈ Icc a ξbar)
        (η : ℝ) (hη : η ∈ Icc a ξbar)
        (hξη : |η - ξ| ≤ e)
        (D E : DistRd d → ContMetric d)
        (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
        (hE : IsStrongExpMetric d η (distExp d η) E)
        (c : ℝ) (hc : c ∈ Icc (1 + 20 * v) Cb)
        (hcompProb : pinLaw d 10
          {H | ¬ CompOn (rho E H) (rho D H) c e Rsrc} ≤
          ENNReal.ofReal (pt / 4)) :
        pinLaw d 10 (Hup D E (c - e)) ≤ ENNReal.ofReal pt := by
      let Bfun : Rd d → Rd d → (ℕ × (Fin d → ℤ) × ℤ) →
          Set (DistRd d) := fun x y cl =>
        countEventB
          (prop45Data cat D E ξ η θ S.mc S.Hlo x y c gΔ e U0 Rsrc Δ)
          (q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 x y)
      have hper : ∀ x ∈ N, ∀ y ∈ N, x ≠ y →
          ∀ cl ∈ q11ClassSet d V Δ K0,
          pinLaw d 10 (Bfun x y cl) ≤
            ENNReal.ofReal (Δ ^ (2 * (Dnet + 3) + 2)) := by
        intro x hx y hy hxy cl hcl
        have hh := q11_catalogue_prob hd hbar.1 hQbar ha0 haξ
          hv0' (lt_of_lt_of_le one_pos hU0) hdsep hΔpos hΔlt1
          hscales hdepth cat hP45v hξ hη (hdrift ξ hξ η hξη)
          hD hE hc hxy (hNinside x hx) (hNinside y hy)
          hcseed.le hcseedCert he.le heε hcl
        simpa only [Bfun, μ] using hh
      have hUnion := q11_catalogue_union_prob (by omega : 1 ≤ d)
        N (q11ClassSet d V Δ K0) (pinLaw d 10)
        ht ht1 hΔpos hΔ1 hT htlow hnetconstant rfl hNcard
        hclassCardMesh Bfun hper
      have hUnionPt : pinLaw d 10
          (⋃ x ∈ N, ⋃ y ∈ N, ⋃ cl ∈ q11ClassSet d V Δ K0,
            {H | x ≠ y ∧ H ∈ Bfun x y cl}) ≤
          ENNReal.ofReal (pt / 4) := by
        exact hUnion.trans (ENNReal.ofReal_le_ofReal (by simpa only [μ] using hprobMesh))
      have hξIoc : ξ ∈ Ioc (0 : ℝ) ξbar :=
        ⟨lt_of_lt_of_le ha0 hξ.1, hξ.2⟩
      have hηIoc : η ∈ Ioc (0 : ℝ) ξbar :=
        ⟨lt_of_lt_of_le ha0 hη.1, hη.2⟩
      let Site : Set (DistRd d) := siteEvent D E
        (Finset.univ : Finset Edge) centre L Ntr v
        S.H0 S.σ0 S.β0 S.m S.M S.Hsd S.σsd
        S.Hup S.sR S.Hlo S.b S.mc S.A0 Kpin
      have hSite := hsiteprob ξ hξIoc η hηIoc D E hD hE
        v hv0' hvbase' (hξη.trans hsiteDrift)
      have hSiteProb : pinLaw d 1 Siteᶜ ≤ ENNReal.ofReal psite := hSite.1
      have hSiteLocal : AEEventIn (pinLaw d 1)
          (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4)) Site := hSite.2
      let CoverBad : Set (DistRd d) := {H | ∃ q ∈ closedBall (0 : Rd d) 3,
        ∀ k ∈ p4_fullScales V, ∀ j : Fin d → ℤ,
          ‖q - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
            p4_radius k / 10 →
          recentre 1 (p4_radius k)
            (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) H ∉ Site}
      have hCoverRaw : pinLaw d 10 CoverBad ≤
          ENNReal.ofReal (Ccov * (1 + (3 : ℝ)) ^ d * Real.exp (-2 * V)) := by
        exact hcover (s := 1) (s₀ := 10)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hSiteLocal (p := psite) (W := 3) (V := V)
          hpsite.le (by dsimp [psite]; exact le_refl _)
          hSiteProb (by norm_num) hV1
      have hCoverSmall : Ccov * (1 + (3 : ℝ)) ^ d * Real.exp (-2 * V) ≤
          pt / 16 := by
        have hh := hcovsmall V (hLcover'.trans hLV)
        have he : Real.exp (-2 * V) ≤ Real.exp (-(1 * V)) :=
          Real.exp_le_exp.mpr (by linarith only [hV1])
        have hmul := mul_le_mul_of_nonneg_left he
          (by positivity : 0 ≤ Ccov * (1 + (3 : ℝ)) ^ d)
        exact hmul.trans hh
      have hCoverProb : pinLaw d 10 CoverBad ≤ ENNReal.ofReal (pt / 16) :=
        hCoverRaw.trans (ENNReal.ofReal_le_ofReal hCoverSmall)
      let ncap : ℕ := ⌈3 * V⌉₊ + 3
      obtain ⟨hncaplo, hncaphi, hcapRaw0, hcapRatio0⟩ := hcap
      let CapBad : Set (DistRd d) := {H | ∃ p ∈
        gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
          Ccap * ncap < |sphereAvg H p.1 p.2|}
      have hCapRaw : pinLaw d 10 CapBad ≤
          ENNReal.ofReal (CcapFail * Real.exp (-ccap * ncap)) := hcapRaw0
      have hCapSmall : CcapFail * Real.exp (-ccap * ncap) ≤ pt / 16 := by
        have hh := hcapsmall V (hLcap'.trans hLV)
        have hn : V ≤ (ncap : ℝ) := by linarith only [hncaplo, hV1]
        have he : Real.exp (-ccap * ncap) ≤ Real.exp (-(ccap * V)) :=
          Real.exp_le_exp.mpr (by nlinarith only [hn, hccap])
        exact (mul_le_mul_of_nonneg_left he hCcapFail.le).trans hh
      have hCapProb : pinLaw d 10 CapBad ≤ ENNReal.ofReal (pt / 16) :=
        hCapRaw.trans (ENNReal.ofReal_le_ofReal hCapSmall)
      have hCapRatio (H : DistRd d) (hH : H ∉ CapBad) :
          ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
            |Real.log (scaleS d η 1 p.1 p.2 H /
              scaleS d ξ 1 p.1 p.2 H)| ≤ v / 20 := by
        have hgood : ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
            |sphereAvg H p.1 p.2| ≤ Ccap * ncap := by
          intro p hp
          exact le_of_not_gt (fun hb => hH ⟨p, hp, hb⟩)
        intro p hp
        have hraw := hcapRatio0 H hgood ξ η hξIoc.1.le hηIoc.1.le p hp
        have hcoeff : 0 < Real.sqrt (2 * d) + Ccap := by
          have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
          positivity
        have hτn : |η - ξ| * (ncap : ℝ) ≤ e * (3 * V + 4) :=
          mul_le_mul hξη hncaphi (Nat.cast_nonneg _) he.le
        have hΔv : Δ ≤ v := hΔvc.trans
          (mul_le_of_le_one_right hv0'.le hcseed1)
        calc
          |Real.log (scaleS d η 1 p.1 p.2 H /
              scaleS d ξ 1 p.1 p.2 H)|
              ≤ (Real.sqrt (2 * d) + Ccap) * |η - ξ| * ncap := hraw
          _ ≤ (Real.sqrt (2 * d) + Ccap) * (e * (3 * V + 4)) := by
            nlinarith only [hτn, hcoeff.le]
          _ ≤ (Real.sqrt (2 * d) + Ccap) * (Δ / Rcap) :=
            mul_le_mul_of_nonneg_left hcapDrift hcoeff.le
          _ = Δ / 20 := by
            dsimp [Rcap]
            field_simp
          _ ≤ v / 20 := div_le_div_of_nonneg_right hΔv (by norm_num)
      have hCoverGood (H : DistRd d) (hH : H ∉ CoverBad) :
          ∀ q ∈ closedBall (0 : Rd d) 3,
            ∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
              ‖q - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
                p4_radius k / 10 ∧
              recentre 1 (p4_radius k)
                (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) H ∈ Site := by
        intro q hq
        by_contra hn
        apply hH
        refine ⟨q, hq, ?_⟩
        intro k hk j hnear
        by_contra hsite'
        apply hn
        exact ⟨k, hk, j, hnear, hsite'⟩
      let Kxy (x y : Rd d) : CountData d :=
        prop45Data cat D E ξ η θ S.mc S.Hlo x y c gΔ e U0 Rsrc Δ
      let PairGood (H : DistRd d) (x y : Rd d) : Prop :=
        q9GoodInput (Kxy x y) H ∧
        ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ncap 4,
          (countSiteD (Kxy x y) p.1 p.2 H =
            rho D (recentre 1 p.1 p.2 H) ∧
           (∃ hratio : 0 < scaleS d η 1 p.1 p.2 H /
               scaleS d ξ 1 p.1 p.2 H,
             countSiteE (Kxy x y) p.1 p.2 H =
               (rho E (recentre 1 p.1 p.2 H)).smul
                 (scaleS d η 1 p.1 p.2 H /
                   scaleS d ξ 1 p.1 p.2 H) hratio) ∧
           (countSiteD (Kxy x y) p.1 p.2 H).IsLength ∧
           (countSiteE (Kxy x y) p.1 p.2 H).IsLength) ∧
          ∀ edge : Edge, ∀ j : Fin Ntr,
            siteNorm ξ D (centre edge) (seedTrialRadius_pos hL j)
                (recentre 1 p.1 p.2 H) =
              rho D (recentre 1 (seedTrialRadius L j) (centre edge)
                (recentre 1 p.1 p.2 H)) ∧
            siteNorm η E (centre edge) (seedTrialRadius_pos hL j)
                (recentre 1 p.1 p.2 H) =
              rho E (recentre 1 (seedTrialRadius L j) (centre edge)
                (recentre 1 p.1 p.2 H))
      have hQξ : Real.sqrt (2 * d) < distExp d ξ := by
        have hh := (hgap ξ hξIoc).2
        have hdiv : 0 < μgap / ξbar := div_pos hμgap hbar.1
        linarith only [hh, hdiv]
      have hAEPair : ∀ᵐ H ∂(pinLaw d 10),
          ∀ x ∈ N, ∀ y ∈ N, PairGood H x y := by
        rw [Filter.eventually_all_finset]
        intro x hx
        rw [Filter.eventually_all_finset]
        intro y hy
        have hgood := q9_ae_goodInput hd (Kxy x y)
          hξIoc.1 hQξ hD hE
          (f := 0) (B := 0) (by intro z; simp)
        have hscale := q11_grid_scaling_ae (n := ncap) (Ntr := Ntr)
          (by omega : 2 ≤ d)
          (Kxy x y) hξIoc.1 hηIoc.1 hD hE hL centre
        filter_upwards [hgood, hscale] with H hg hs
        have hg' : q9GoodInput (Kxy x y) H := by
          simpa only [addFun_zero] using hg
        exact ⟨hg', hs⟩
      let PairBad : Set (DistRd d) :=
        {H | ¬∀ x ∈ N, ∀ y ∈ N, PairGood H x y}
      have hPairNull : pinLaw d 10 PairBad = 0 := ae_iff.mp hAEPair
      let SourceBad : Set (DistRd d) :=
        {H | ¬Q11SourceGood (rho D H) U0 Rsrc Hgl σgl βgl}
      have hSourceProb : pinLaw d 10 SourceBad ≤ ENNReal.ofReal (pt / 8) :=
        hsourceprob ξ hξIoc D hD
      let GeomGood : Set (DistRd d) :=
        {H | H ∉ SourceBad ∧ H ∉ CoverBad ∧ H ∉ CapBad ∧ H ∉ PairBad}
      have hGeomSub : GeomGoodᶜ ⊆
          SourceBad ∪ CoverBad ∪ CapBad ∪ PairBad := by
        intro H hH
        by_contra hnot
        simp only [Set.mem_union, not_or] at hnot
        exact hH ⟨hnot.1.1.1, hnot.1.1.2, hnot.1.2, hnot.2⟩
      have hGeomProb : pinLaw d 10 GeomGoodᶜ ≤ ENNReal.ofReal (pt / 4) := by
        calc
          pinLaw d 10 GeomGoodᶜ ≤
              pinLaw d 10 (SourceBad ∪ CoverBad ∪ CapBad ∪ PairBad) :=
            measure_mono hGeomSub
          _ ≤ pinLaw d 10 SourceBad + pinLaw d 10 CoverBad +
              pinLaw d 10 CapBad + pinLaw d 10 PairBad := by
            have h1 := measure_union_le (μ := pinLaw d 10) SourceBad CoverBad
            have h2 := measure_union_le (μ := pinLaw d 10)
              (SourceBad ∪ CoverBad) CapBad
            have h3 := measure_union_le (μ := pinLaw d 10)
              (SourceBad ∪ CoverBad ∪ CapBad) PairBad
            calc
              pinLaw d 10 (SourceBad ∪ CoverBad ∪ CapBad ∪ PairBad)
                  ≤ pinLaw d 10 (SourceBad ∪ CoverBad ∪ CapBad) +
                      pinLaw d 10 PairBad := h3
              _ ≤ (pinLaw d 10 (SourceBad ∪ CoverBad) +
                    pinLaw d 10 CapBad) + pinLaw d 10 PairBad := by gcongr
              _ ≤ (pinLaw d 10 SourceBad + pinLaw d 10 CoverBad) +
                    pinLaw d 10 CapBad + pinLaw d 10 PairBad := by gcongr
          _ ≤ ENNReal.ofReal (pt / 8) + ENNReal.ofReal (pt / 16) +
              ENNReal.ofReal (pt / 16) + 0 := by
            exact add_le_add (add_le_add
              (add_le_add hSourceProb hCoverProb) hCapProb)
              (le_of_eq hPairNull)
          _ = ENNReal.ofReal (pt / 4) := by
            rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
      have hRoundField (H : DistRd d)
          (hup : H ∈ Hup D E (c - e))
          (href : H ∈ PairRefs D E Hr0 σr0 βr0 m0 M0)
          (hcomp : CompOn (rho E H) (rho D H) c e Rsrc)
          (hGeom : H ∈ GeomGood) :
          ∃ x ∈ N, ∃ y ∈ N,
            w / 2 ≤ ‖x - y‖ ∧
            (c - gΔ) * (rho D H).1 (x, y) ≤ (rho E H).1 (x, y) := by
        have hSource : Q11SourceGood (rho D H) U0 Rsrc Hgl σgl βgl :=
          not_not.mp hGeom.1
        have hPairAll : ∀ x ∈ N, ∀ y ∈ N, PairGood H x y :=
          not_not.mp hGeom.2.2.2
        have hzero : (0 : Rd d) ∈ closedBall (0 : Rd d) 2 := by
          simp only [mem_closedBall, dist_self]
          norm_num
        obtain ⟨p, hp, -⟩ := hNcover 0 hzero
        have hpp := (hPairAll p hp p hp).1
        have hDlen : (rho D H).IsLength := hpp.1
        have hElen : (rho E H).IsLength := hpp.2.1
        have hcoef : 0 ≤ c - gΔ / 16 := by
          have hgv : gΔ ≤ v := hgain.2.1
          linarith only [hc.1, hv0', hgv]
        have hco : c - gΔ / 16 ≤ c - e := by linarith only [heg]
        have hup' : H ∈ Hup D E (c - gΔ / 16) :=
          q11_hup_antitone hco hup
        exact q11_hup_round_to_net hDlen hElen
          (by linarith only [hHr0]) hσr0 (by linarith only [hβr0]) hm0
          href hw hw1 hwsub hgain.1 (hgain.2.1.trans hv1)
          (by exact (show (1 : ℝ) ≤ 1 + 20 * v by linarith only [hv0']).trans hc.1)
          hc.2 hcoef he.le ht htw
          hRsrc hHgl hσgl hσgl1.le
          (by linarith only [hβgl]) hSource hroundsmall
          hcomp N hNinside hNcover hup'
      have hCatalogueField (H : DistRd d) (hGeom : H ∈ GeomGood)
          (x : Rd d) (hx : x ∈ N) (y : Rd d) (hy : y ∈ N)
          (hxy : w / 2 ≤ ‖x - y‖) :
          ∃ cl ∈ q11ClassSet d V Δ K0,
            let 𝔆 := q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 x y
            𝔆.Valid x y ∧
            nsite ≤ (𝔆.Z.filter fun z => IsEligible (Kxy x y) 𝔆 z H).card ∧
            (𝔆.Z.card : ℝ) ≤
              (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) := by
        have hSource : Q11SourceGood (rho D H) U0 Rsrc Hgl σgl βgl :=
          not_not.mp hGeom.1
        have hPairAll : ∀ x ∈ N, ∀ y ∈ N, PairGood H x y :=
          not_not.mp hGeom.2.2.2
        have hPair := hPairAll x hx y hy
        exact q11_catalogue_of_cover hd (Kxy x y)
          hξIoc.1 hξ.2 hηIoc.1 hη.2 hL hKpin Ntr centre H
          hPair.1.1 hPair.1.2.2.1 hSource hRsrc hHgl hσgl hσgl1.le
          (by linarith only [hβgl]) S.hmc hA0pos hv1
          hξη (by simpa only [Rtrial] using htrialDrift)
          hΔpos hΔquarter hΔw hw hw1 hΔmax'
          (by linarith only [hV1] : 0 ≤ V) hscales hncaplo
          hnsite hfloorPos hclassCount
          (hNinside x hx) (hNinside y hy) hxy
          (hCoverGood H hGeom.2.1) hPair.2
          (hCapRatio H hGeom.2.2.1) hexhaust
      have hPointwise (H : DistRd d)
          (hup : H ∈ Hup D E (c - e))
          (href : H ∈ PairRefs D E Hr0 σr0 βr0 m0 M0)
          (hcomp : CompOn (rho E H) (rho D H) c e Rsrc)
          (hGeom : H ∈ GeomGood) :
          ∃ x ∈ N, ∃ y ∈ N,
            ∃ cl ∈ q11ClassSet d V Δ K0,
              x ≠ y ∧ H ∈ Bfun x y cl := by
        obtain ⟨x, hx, y, hy, hsep, hgap⟩ :=
          hRoundField H hup href hcomp hGeom
        obtain ⟨cl, hcl, hvalid, helig, hcard⟩ :=
          hCatalogueField H hGeom x hx y hy hsep
        have hxy : x ≠ y := by
          intro heq
          subst y
          simp only [sub_self, norm_zero] at hsep
          linarith only [hsep, hw]
        have hSource : Q11SourceGood (rho D H) U0 Rsrc Hgl σgl βgl :=
          not_not.mp hGeom.1
        have hthreshold : Δ ^ (-(1 / 2 : ℝ)) ≤ (nsite : ℝ) := by
          simpa only [Δ, nsite] using q11_site_threshold V
        have hBmem : H ∈ Bfun x y cl := by
          exact q11_countEventB_of_catalogue (Kxy x y) H
            (q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 x y)
            hSource (le_trans (by norm_num : (0 : ℝ) ≤ 1) hU0) (hNinside x hx) (hNinside y hy)
            hcomp hgap hthreshold helig
        exact ⟨x, hx, y, hy, cl, hcl, hxy, hBmem⟩
      let Bunion : Set (DistRd d) :=
        ⋃ x ∈ N, ⋃ y ∈ N, ⋃ cl ∈ q11ClassSet d V Δ K0,
          {H | x ≠ y ∧ H ∈ Bfun x y cl}
      let CompGood : Set (DistRd d) :=
        {H | CompOn (rho E H) (rho D H) c e Rsrc}
      have hSub : Hup D E (c - e) ⊆
          (PairRefs D E Hr0 σr0 βr0 m0 M0)ᶜ ∪
          CompGoodᶜ ∪ GeomGoodᶜ ∪ Bunion := by
        intro H hup
        simp only [Set.mem_union, Set.mem_compl_iff]
        by_cases href : H ∈ PairRefs D E Hr0 σr0 βr0 m0 M0
        · by_cases hcomp : H ∈ CompGood
          · by_cases hGeom : H ∈ GeomGood
            · obtain ⟨x, hx, y, hy, cl, hcl, hxy, hB⟩ :=
                hPointwise H hup href hcomp hGeom
              have hBunion : H ∈ Bunion := by
                simp only [Bunion, Set.mem_iUnion, Set.mem_ofPred_eq]
                exact ⟨x, hx, y, hy, cl, hcl, hxy, hB⟩
              exact Or.inr hBunion
            · exact Or.inl (Or.inr hGeom)
          · exact Or.inl (Or.inl (Or.inr hcomp))
        · exact Or.inl (Or.inl (Or.inl href))
      have hRprob := hrefprob ξ hξIoc η hηIoc D E hD hE
      have hBprob : pinLaw d 10 Bunion ≤ ENNReal.ofReal (pt / 4) := hUnionPt
      have hCprob : pinLaw d 10 CompGoodᶜ ≤ ENNReal.ofReal (pt / 4) := hcompProb
      exact q11_hup_event_budget (pinLaw d 10) hpt.le
        hSub hRprob hCprob hGeomProb hBprob
    have hpoly : polyB Afinal kstep a⁻¹ v⁻¹ = B * V := by
      dsimp [Afinal, V, polyB]
      ring
    refine ⟨e, e, e, ?_, hev, he, hev, ?_, ?_, ?_⟩
    · rw [hpoly]
    · change Real.log (Real.exp (-(B * V)))⁻¹ ≤
        polyB Afinal kstep a⁻¹ v⁻¹
      rw [Real.exp_neg, inv_inv, Real.log_exp, hpoly]
    · rw [hpoly]
    · intro ξ hξ η hη hξη D E hD hE c hc1 hc2 hcompProb
      exact hrun ξ hξ η hη hξη D E hD hE c ⟨hc1, hc2⟩ hcompProb
  refine ⟨Rsrc, pt / 4, Afinal, kstep, v0, ?_, ?_, hv0, hv01, ?_⟩
  · linarith only [hRsrc]
  · positivity
  · intro a ha v hv
    exact hstep a ha v hv

end HigherDimLQGContinuity
