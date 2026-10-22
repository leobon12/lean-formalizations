import HigherDimLQGContinuity.Forcing.Shortcut

/-! # Deterministic site forcing, Lemma 4.3 -/

set_option autoImplicit false

noncomputable section

open Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The full deterministic forcing statement of the frozen §4 interface. -/
theorem lemma43_forcing_holds (d : ℕ) : Lemma43Forcing d := by
  intro D E D' E' f ξ η M θ h δsep ε₀ εnet εatt btrig aout H b v d₀ Ω
    cert hWD hWE hξ hη hd₀ hmis hv hvmax hΩmax hcollar hnet htrig hsep hbudget
    P a c hgeo ha hc hpasses
  let u := firstVisit P a c (siteC d)
  let w := lastVisit P a c (siteC d)
  obtain ⟨hau, huw, hwc, _, _, hA⟩ :=
    lemma43_confine d cert hWD hWE hξ hη hd₀ hmis hv hvmax hΩmax hcollar
      hnet htrig hsep hbudget P a c hgeo ha hc hpasses.1
  obtain ⟨_, _, _, hu, hw⟩ :=
    q6_collector_visit_times hgeo ha hc hpasses.1
  have hH : 0 < H := q6_H_pos cert hu hsep hbudget
  have hb : 0 ≤ b := q6_b_nonneg cert hu hH
  have hM : 0 ≤ M := (cert.f_bd 0).1.trans (cert.f_bd 0).2
  have hΩ : 0 ≤ Ω :=
    (mul_nonneg (abs_nonneg _) hM).trans hmis
  obtain ⟨e, ⟨s₀, hs₀, hs₀V, hs₀N⟩, ⟨t₀, ht₀, ht₀V, ht₀N⟩⟩ :=
    q6_opposite_gates_visited cert hWD hξ hH hb hsep hbudget hnet htrig
      hgeo hau.le huw hwc.le hu hw hA hpasses.2
  obtain ⟨p, q, hdq, hleft, hright, hcost⟩ :=
    q6_gate_arc_cost cert hWE hη hmis hd₀ hv hΩ e hs₀N ht₀N
  by_cases hst : s₀ ≤ t₀
  · have hPst : ContinuousOn P (Icc s₀ t₀) :=
      hgeo.2.1.mono (Icc_subset_Icc (hau.le.trans hs₀.1) (ht₀.2.trans hwc.le))
    obtain ⟨hlow, hupper⟩ := q6_gate_block_estimates cert hWD hξ hd₀ hv hvmax hΩ
      hst hPst hdq hleft hright hcost
    exact ⟨s₀, t₀, hau.le.trans hs₀.1, hst, ht₀.2.trans hwc.le,
      (fun τ hτ => hA τ ⟨hs₀.1.trans hτ.1, hτ.2.trans ht₀.2⟩), hlow, hupper⟩
  · have hts : t₀ ≤ s₀ := le_of_not_ge hst
    have hPts : ContinuousOn P (Icc t₀ s₀) :=
      hgeo.2.1.mono (Icc_subset_Icc (hau.le.trans ht₀.1) (hs₀.2.trans hwc.le))
    have hdq' : d₀ ≤ D.1 (q, p) := by simpa only [D.apply_comm] using hdq
    have hleft' : D.1 (q, P t₀) ≤ v * d₀ / 1000 := by
      simpa only [D.apply_comm] using hright
    have hright' : D.1 (P s₀, p) ≤ v * d₀ / 1000 := by
      simpa only [D.apply_comm] using hleft
    have hcost' : E'.internal (siteB d) (P t₀) (P s₀) ≤
        ENNReal.ofReal (θ * Real.exp Ω * (1 + 5 * v) * D.1 (q, p)) := by
      simpa only [E'.internal_comm, D.apply_comm] using hcost
    obtain ⟨hlow, hupper⟩ := q6_gate_block_estimates cert hWD hξ hd₀ hv hvmax hΩ
      hts hPts hdq' hleft' hright' hcost'
    exact ⟨t₀, s₀, hau.le.trans ht₀.1, hts, hs₀.2.trans hwc.le,
      (fun τ hτ => hA τ ⟨ht₀.1.trans hτ.1, hτ.2.trans hs₀.2⟩), hlow, hupper⟩

end HigherDimLQGContinuity
