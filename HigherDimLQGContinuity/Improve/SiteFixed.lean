import HigherDimLQGContinuity.SiteEvents.SiteProb
import HigherDimLQGContinuity.SiteEvents.Trials
import HigherDimLQGContinuity.SiteEvents.RefsLocal

/-!
# Site-event constants selected before the certificate edge set
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The part of the site-event data independent of the eventual finite edge
set. The edge set and trial count can then be chosen in the order required by
`prop45`. -/
structure Q11SiteFixed (d : ℕ) (ξbar p : ℝ) where
  Hup : ℝ
  sR : ℝ
  Hlo : ℝ
  b : ℝ
  mc : ℝ
  A0 : ℝ
  H0 : ℝ
  σ0 : ℝ
  β0 : ℝ
  m : ℝ
  M : ℝ
  Hsd : ℝ
  σsd : ℝ
  vbase : ℝ
  C4 : ℝ
  c4 : ℝ
  hHup : 1 ≤ Hup
  hsR : 0 < sR
  hsR1 : sR ≤ 1
  hHlo : 1 ≤ Hlo
  hb : 1 ≤ b
  hmc : 0 < mc
  hA0 : Hlo⁻¹ ≤ A0
  hH0 : 1 ≤ H0
  hσ0 : 0 < σ0
  hσ01 : σ0 < 1
  hβ0 : 1 < β0
  hm : 0 < m
  hmM : m < M
  hHsd : 1 ≤ Hsd
  hσsd : 0 < σsd
  hσsd1 : σsd ≤ 1
  hvbase : 0 < vbase
  hvbase1 : vbase ≤ 1 / 2
  hC4 : 0 < C4
  hc4 : 0 < c4
  select : ∀ {Edge : Type} [Fintype Edge] (centre : Edge → Rd d)
      {L : ℝ}, 0 < L →
      (∀ e : Edge, closedBall (centre e) L ⊆ siteC d) →
      ∃ Ntr : ℕ, ∃ Kpin : ℝ, 0 ≤ Kpin ∧
        ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar,
          ∀ D E : DistRd d → ContMetric d,
            IsStrongExpMetric d ξ (distExp d ξ) D →
            IsStrongExpMetric d η (distExp d η) E →
            ∀ v : ℝ, 0 < v → v < vbase →
              |η - ξ| ≤ c4 * v ^ C4 →
              pinLaw d 1 (siteEvent D E (Finset.univ : Finset Edge)
                centre L Ntr v H0 σ0 β0 m M Hsd σsd
                Hup sR Hlo b mc A0 Kpin)ᶜ ≤ ENNReal.ofReal p ∧
              AEEventIn (pinLaw d 1)
                (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
                (siteEvent D E (Finset.univ : Finset Edge)
                  centre L Ntr v H0 σ0 β0 m M Hsd σsd
                  Hup sR Hlo b mc A0 Kpin)

/-- Select the site references and trial-base constants before any edge
geometry is fixed; only the finite trial count and cap are selected later. -/
theorem q11_site_fixed_exists {d : ℕ} (hd : 3 ≤ d) {ξbar p : ℝ}
    (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s)
    (hp : 0 < p) : Nonempty (Q11SiteFixed d ξbar p) := by
  let p4 : ℝ := p / 4
  have hp4 : 0 < p4 := by dsimp [p4]; positivity
  obtain ⟨Hup, sR, Hlo, b, mc, A0,
    hHup, hsR, hsR1, hHlo, hb, hmc, hA0, href⟩ :=
    siteRefs_prob (by omega : 2 ≤ d) (hU 1 (by norm_num)) hp4
  obtain ⟨pstar, vbase, C4, c4, H0, σ0, β0, m, M, Hsd, σsd, K,
    hpstar, hpstar1, hvbase, hvbase1, hC4, hc4, hσ0, hσ01,
    hβ0, hm, hmM, hH0, hHsd, hσsd, hσsd1, hK, htrials⟩ :=
    seedTrials_prob (by omega : 2 ≤ d) hU
  refine ⟨{
    Hup := Hup, sR := sR, Hlo := Hlo, b := b, mc := mc, A0 := A0,
    H0 := H0, σ0 := σ0, β0 := β0, m := m, M := M,
    Hsd := Hsd, σsd := σsd, vbase := vbase, C4 := C4, c4 := c4,
    hHup := hHup, hsR := hsR, hsR1 := hsR1, hHlo := hHlo,
    hb := hb, hmc := hmc, hA0 := hA0, hH0 := hH0,
    hσ0 := hσ0, hσ01 := hσ01, hβ0 := hβ0, hm := hm,
    hmM := hmM, hHsd := hHsd, hσsd := hσsd,
    hσsd1 := hσsd1, hvbase := hvbase, hvbase1 := hvbase1,
    hC4 := hC4, hc4 := hc4, select := ?_ }⟩
  intro Edge instEdge centre L hL hbox
  obtain ⟨Ntr, htrial⟩ := htrials (Finset.univ : Finset Edge) centre hp4 hL
  obtain ⟨Kpin, hKpin, hpin⟩ :=
    sitePinCap_trials_prob (by omega : 2 ≤ d)
      (Finset.univ : Finset Edge) centre hL Ntr hp4
  refine ⟨Ntr, Kpin, hKpin, ?_⟩
  intro ξ hξ η hη D E hD hE v hv hvbase' hτ
  have href' := (href ξ hξ D hD).1
  have htrial' := htrial ξ hξ η hη D E hD hE v hv hvbase' hτ
  have hprob := siteEvent_prob_of_bounds D E (Finset.univ : Finset Edge)
    centre L Ntr v H0 σ0 β0 m M Hsd σsd Hup sR Hlo b mc A0 Kpin p
    hp.le href' htrial' hpin
  have hlocal := siteEvent_aeEventIn
    (v := v) (H₀ := H0) (σ₀ := σ0) (β₀ := β0) (m := m) (M := M)
    (Hsd := Hsd) (σsd := σsd) (Hup := Hup) (σ := sR)
    (Hlo := Hlo) (β := b) (mc := mc) (A0 := A0) (Kpin := Kpin)
    (by omega : 2 ≤ d)
    hξ.1 hη.1 hD hE (Finset.univ : Finset Edge) centre hL
    (fun e _ => hbox e) Ntr (show 0 ≤ Hsd by linarith) hσsd.le
    (show 0 ≤ Hup by linarith) hsR.le
  exact ⟨hprob, hlocal⟩

end HigherDimLQGContinuity
