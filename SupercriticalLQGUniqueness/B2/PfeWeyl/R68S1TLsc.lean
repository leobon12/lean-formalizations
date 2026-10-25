import SupercriticalLQGUniqueness.B2.Iface.FixedFieldWeyl
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem fixedFieldWeylAllBounded_comp
    {ξ : Ioi (0 : ℝ)} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {ε : ℕ → Ioi (0 : ℝ)} {D : DistC → LSCMetric}
    (hW3 : FixedFieldWeylAllBounded ξ m ε D)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    FixedFieldWeylAllBounded ξ m (ε ∘ ψ) D := by
  intro Ω _ P _ h hh X hX
  filter_upwards [hW3 P h hh X hX] with ω hω f M hM
  obtain ⟨E, hE, hconv⟩ := hω f M hM
  exact ⟨E, hE, hconv.comp hψ.tendsto_atTop⟩

 

theorem ae_lsc_boundedShift_of_fixedFieldWeyl
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hW3 : FixedFieldWeylAllBounded ξ m ε D)
    (hweyl : BoundedShiftWeyl ξ D) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h' : Ω → DistC), IsGFFPlusBddCont h' P →
      ∀ Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
        (∀ δ, IsHeatSmoothing P h' δ (Y δ)) →
        ∀ᵐ ω ∂P, LSCTendsto
          (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (Y (ε n) ω))
          (D (h' ω)).toLSCFun.1 := by
  intro Ω _ P _ h' hh' Y hY
  obtain ⟨k, F, hk, hF, hFb, hdec⟩ := exists_normalized_bdd_decomposition hh'
  have hkb : IsGFFPlusBddCont k P := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hk.1
  have hXex : ∀ δ : Ioi (0 : ℝ), ∃ X : Ω → C(ℂ, ℝ), IsHeatSmoothing P k δ X :=
    fun δ => (PfeAxioms.exists_heatVersion_bdd hkb δ).imp fun _ hX => hX.2
  choose X hX using hXex
  have hFb' := hFb
  choose Mf hMf using hFb'
  have hh'eq : h' = fun ω => addFun (k ω) (F ω) := funext hdec
  subst hh'eq
  have hbase := hW3 P k hk X hX
  have hshift := ae_heatVersion_shift_eq ε P k hk F Mf hMf hh' X Y hX hY
  have hW := hweyl P k hk F hF hFb
  filter_upwards [hbase, hshift, hW] with ω hb hs hw
  obtain ⟨E, hE, hconv⟩ := hb (F ω) (Mf ω) (hMf ω)
  have hseq : (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
      (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
        (F ω) (Mf ω) (hMf ω))) =
      fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (Y (ε n) ω) := by
    funext n
    rw [hs n]
  rw [hseq] at hconv
  have hED : E = D (addFun (k ω) (F ω)) := LSCMetric.ext fun p => by
    rw [hE p]
    exact (congrFun hw p).symm
  rw [hED] at hconv
  exact (tendsto_normalizedLFPP_iff_lscTendsto _ _ _ _).1 hconv

 


theorem r68_boundedShiftWeyl_of_isPfeWeakMetric
    {ξ : Ioi (0 : ℝ)} {D : DistC → LSCMetric}
    {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    (hD : IsPfeWeakMetric ξ D c) : BoundedShiftWeyl ξ D :=
  boundedShiftWeyl_of_isPfeWeakMetric hD

end SupercriticalLQGUniqueness.B2.PfeWeyl
