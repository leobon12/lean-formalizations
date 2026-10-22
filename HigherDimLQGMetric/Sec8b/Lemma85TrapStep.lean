import HigherDimLQGMetric.Sec8b.Lemma85ExcPiece

/-! A very-good label produces a quantitative local shortcut by (T3). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_T3_of_exc {ξ cs Cs s r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hs : 0 < s) (hr : 0 < r)
    (site : Rd d × ℕ) (hJ : site.2 < T.J)
    (Dplus Dtplus Dminus Dtminus : ContMetric d)
    (hlen : Dplus.IsLength) (htlen : Dtplus.IsLength)
    (hcomp : ∀ u v : Rd d,
      cs * Dplus.1 (u, v) ≤ Dtplus.1 (u, v) ∧
      Dtplus.1 (u, v) ≤ Cs * Dplus.1 (u, v))
    (hcfg : config Dplus Dtplus s r site.1 ∈ T.N site.2)
    (hDweyl : IsWeylOf ξ (-bumpAt (T.f site.2) r site.1) Dplus Dminus)
    (hDtWeyl : IsWeylOf ξ (-bumpAt (T.f site.2) r site.1) Dtplus Dtminus)
    (η : C(unitInterval, Rd d))
    (hgeo : IsGeod Dminus (s7b_realPath η))
    (hExc : Exc η Dplus (sec8Collector T.V r site.1)
      site.1 r (T.b * s)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      (∀ t ∈ Icc a b,
        s7b_realPath η t ∈ ball site.1 (4 * r)) ∧
      ∃ R : ℝ → Rd d,
        IsGeodIn Dminus (ball site.1 (4 * r)) R ∧
        R 0 = s7b_realPath η a ∧ R 1 = s7b_realPath η b ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          R t = s7b_realPath η (a + t * (b - a))) ∧
        ∃ τ₁ τ₂ : ℝ, 0 ≤ τ₁ ∧ τ₁ ≤ τ₂ ∧ τ₂ ≤ 1 ∧
          ENNReal.ofReal (T.c * s) ≤ Dminus.len R τ₁ τ₂ ∧
          Dtminus.internal (ball site.1 (4 * r)) (R τ₁) (R τ₂) ≤
            ENNReal.ofReal T.c' * Dminus.len R τ₁ τ₂ := by
  have hVball : closure (sec8Collector T.V r site.1) ⊆
      ball site.1 (4 * r) :=
    (S6a.closure_collector_subset hr site.1 T.closureV).trans
      (S6a.ann_subset_ball hr site.1)
  obtain ⟨a, b, ha, hab, hb, hinside, R, hRgeo, hR0, hR1, hRV0, hRV1,
    hthreshold, hRform⟩ :=
    s7b_exc_geod_piece η Dminus Dplus (sec8Collector T.V r site.1)
      site.1 r (T.b * s) hgeo hVball hExc
  have htrap := T.traps Dplus Dtplus hlen htlen hcomp s r site.1 site.2
    hs hr hJ hcfg
  have hT3 := htrap.2.2.1 Dminus Dtminus hDweyl hDtWeyl R hRgeo
    0 1 le_rfl zero_le_one le_rfl hRV0 hRV1
    (fun τ hτ _ => hτ) hthreshold
  obtain ⟨τ₁, τ₂, hτ₁, hτ₁₂, hτ₂, hcost, hshort⟩ := hT3
  exact ⟨a, b, ha, hab, hb, hinside, R, hRgeo, hR0, hR1,
    hRform, τ₁, τ₂, hτ₁, hτ₁₂, hτ₂, hcost, hshort⟩

end HigherDimLQGMetric
