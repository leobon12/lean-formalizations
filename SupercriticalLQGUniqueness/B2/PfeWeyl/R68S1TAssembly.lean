import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TUpperFamily

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem subseqLimit_of_fixedFieldWeyl_and_circles
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (Φ : DistC → LSCMetric)
    (hW3 : FixedFieldWeylAllBounded ξ m ε Φ)
    (hcircles : FixedFieldWeylAllCircles ξ m ε Φ)
    (hweyl : BoundedShiftWeyl ξ Φ) :
    SubseqLimit ξ m ε Φ := by
  intro Ω _ P _ h' hh' Y hY
  have hlsc := ae_lsc_boundedShift_of_fixedFieldWeyl ξ m ε Φ hW3 hweyl
    P h' hh' Y hY
  obtain ⟨k, F, hk, hF, hFb, hdec⟩ := exists_normalized_bdd_decomposition hh'
  have hkb : IsGFFPlusBddCont k P := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hk.1
  have hXex : ∀ δ : Ioi (0 : ℝ), ∃ X : Ω → C(ℂ, ℝ), IsHeatSmoothing P k δ X :=
    fun δ => (PfeAxioms.exists_heatVersion_bdd hkb δ).imp fun _ hX => hX.2
  choose X hX using hXex
  have hFb' := hFb
  choose Mf hMf using hFb'
  have hh'eq : h' = fun ω => addFun (k ω) (F ω) := funext hdec
  subst hh'eq
  have hbasec := hcircles P k hk X hX
  have hshift := ae_heatVersion_shift_eq ε P k hk F Mf hMf hh' X Y hX hY
  have hW := hweyl P k hk F hF hFb
  refine ⟨hlsc, fun O O' hO hO' => ?_⟩
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  let A : B2.DG20Lim.RatCircle := ⟨x, y, r, hr⟩
  let B : B2.DG20Lim.RatCircle := ⟨x', y', r', hr'⟩
  filter_upwards [hbasec, hshift, hW] with ω hb hs hw
  have hc := hb (F ω) (Mf ω) (hMf ω) A B
  have hseq : (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
      (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
        (F ω) (Mf ω) (hMf ω))) A.toSet B.toSet) =
      fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        setDistance (lfppDistance (ξ : ℝ) (Y (ε n) ω)) A.toSet B.toSet := by
    funext n
    rw [hs n, setDistance_normalizedLFPPMetric]
  rw [hseq, ← hw] at hc
  simpa only [A, B, B2.DG20Lim.RatCircle.toSet,
    B2.DG20Lim.RatCircle.center] using hc

end SupercriticalLQGUniqueness.B2.PfeWeyl
