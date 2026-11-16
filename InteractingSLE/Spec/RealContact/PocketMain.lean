/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.PocketCarrier
import InteractingSLE.Spec.RealContact.Hit
import InteractingSLE.Spec.Sec7.Lemma76Kernel

/-!
# The pocket-corner exclusion from the conditional law of the first path given the completed second path

Packet PROVE-RC-POCKET (ruling R124). **`RealContact.PocketCornerStatement` is not proved here.** This file proves it,
and hence the real first-hit exclusion `G7GB7aFirstHitRealStatement`, from the single named input
`TerminalRetainedPairStatement` (`PocketCarrier.lean`): Lemma G7 at the retained pair `(0, ζ₂)`, the conditional law
of the first path given the completed second path. Everything else is closed.

## The argument

At a pocket corner (`η₁ x = η₂ T = q`, `x < ζ₁`, `T = ζ₂`, `q < x₂`):

* the trigger event of the carrier holds (`η₂` ends at the real point `q < x₂`, and `η₁` visits `q ≤ q`), so the
  outcome lies in `M` and the first path is read in the chart of the completed second path;
* `x` is in the range of the clock: the first path has no earlier new contact with `η₂([0, T])`. A contact at a
  positive second time is a pocket corner at the same point `q` (`Hit.ae_contact_cases`), so it has the parameter `x`
  (Aux. lemma 25); the second seed is not revisited (Aux. lemma 25 if `x₁ = x₂`, G12 at the fixed point `x₂` with the
  live incident bound if `x₂ < x₁`);
* hence the chart path visits the junction `0` within its lifetime;
* the datum just left of `0` is the original datum just left of `q`, and the live incident bound of `η₁` at `q`
  (`Restart.FCPlumb.ae_live_real_incident_bounds`) gives it left cumulative weight `> −2 > κ/2 − 4`;
* under almost every conditional law the chart path is the angle-`θ₁` flow line from `w > 0` of a GFF with that datum,
  so Lemma G12 (`Supp7.g12FlowStatement`, closed) makes the visit of `0` null, terminal endpoint included;
* integrating through the kernel (`Supp7.ae_not_mem_prod_of_compProd_eq`) gives a contradiction almost surely. The
  weight condition is not assumed measurable in the datum: the kernel integration uses the measurable set of data
  whose conditional law charges the visit.

## Main results

* **`pocketCorner_of_terminalRetained`**: `TerminalRetainedPairStatement → PocketCornerStatement`;
* `g7GB7aFirstHitReal_of_terminalRetained`: the real first-hit exclusion from the same input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (chiC)

universe u

namespace InteractingSLE.RealContact

open Restart

open PiecewiseConstantBoundaryData (leftLim rightLim)

namespace Pocket

section Visit

variable {S : Type*} [MeasurableSpace S] {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}

/-- The outcomes whose path visits the point `0` on its closed available interval `[0, U]`. -/
def visitsZero (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) : Set S :=
  {s | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s ∧ Γ s t = 0}

/-- Visiting `0` is a measurable event (`Sec7.measurableSet_visitPointSet` at the point `0`). -/
theorem measurableSet_visitsZero (hU : Measurable U) (hΓ : ∀ t, Measurable fun s => Γ s t)
    (hc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) : MeasurableSet (visitsZero Γ U) := by
  have hm : Measurable fun s : S => ((0 : ℝ), s) := measurable_const.prodMk measurable_id
  have heq : visitsZero Γ U = (fun s : S => ((0 : ℝ), s)) ⁻¹' Sec7.visitPointSet Γ U := by
    ext s
    simp only [visitsZero, Sec7.visitPointSet, mem_preimage, mem_ofPred_eq, Complex.ofReal_zero]
  rw [heq]
  exact hm (Sec7.measurableSet_visitPointSet hU hΓ hc)

end Visit

/-- **Lemma G12 under a conditional law, at the junction `0`.** If `H` is a GFF with the datum of the word `c` and
`Γ` is its angle-`θ` flow line from `w > 0`, and the left cumulative weight of `c` just beyond `0` exceeds `κ/2 − 4`,
then the path almost surely does not visit `0`, terminal endpoint included. -/
theorem measure_visitsZero_eq_zero {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type} [MeasurableSpace S]
    {Q : Measure S} [IsProbabilityMeasure Q] {H : S → LQGMetric.DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ}
    {U : S → ℝ≥0∞} {c : BoundaryWord} {w : ℝ} (hw : 0 < w) (hH : IsGFFWithBoundaryData Q H c.fn c.jumps)
    (hΓ : IsFlowLine κ c.fn c.jumps w θ Q H Γ U)
    (hwt : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim c.fn 0 + θ * chiC κ)) :
    Q (visitsZero Γ U) = 0 := by
  have hno := (Supp7.g12FlowStatement κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData w θ 0 Q H hH Γ U
    hΓ).2 hw hwt
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hno] with s hs hmem
  obtain ⟨t, htU, ht0⟩ := hmem
  exact hs t htU (ht0.trans Complex.ofReal_zero.symm)

end Pocket

open Pocket Hit

/-- **The pocket-corner exclusion from Lemma G7 at the retained pair `(0, ζ₂)`.** See the module docstring. -/
theorem pocketCorner_of_terminalRetained (hK : TerminalRetainedPairStatement.{u}) :
    PocketCornerStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨S, mS, H, Γ, U, M, β, X, K, -, hU, hΓ, hc, hM, hβ, hX, hKm, hlaw, hker, hpath⟩ :=
    hK κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hV : MeasurableSet (visitsZero Γ U) := measurableSet_visitsZero hU hΓ hc
  -- G12 under almost every conditional law
  have hG12 : ∀ᵐ d ∂(P.restrict M).map β,
      κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim d.1.fn 0 + θ₁ * chiC κ) → K d (visitsZero Γ U) = 0 := by
    filter_upwards [hker] with d hd hwt
    exact measure_visitsZero_eq_zero hκ hκ4 hd.1 hd.2.1 hd.2.2 hwt
  -- the measurable set of data whose conditional law charges the visit
  have hNm : MeasurableSet ((fun d => K d (visitsZero Γ U)) ⁻¹' {0}ᶜ) :=
    (K.measurable_coe hV) (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have h1 := Supp7.ae_not_mem_prod_of_compProd_eq hM hβ hX hlaw hNm.compl hV
    (Eventually.of_forall fun d hd => by simpa using hd)
  have h2 : ∀ᵐ ω ∂P, ω ∈ M →
      κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim (β ω).1.fn 0 + θ₁ * chiC κ) →
      β ω ∈ ((fun d => K d (visitsZero Γ U)) ⁻¹' {0}ᶜ)ᶜ := by
    have h' := ae_of_ae_map hβ.aemeasurable hG12
    rw [ae_restrict_iff' hM] at h'
    filter_upwards [h'] with ω hω hωM hwt hmem
    exact hmem (hω hωM hwt)
  -- G12 for the first path at the second seed
  have hG₁ : ∀ᵐ ω ∂P, x₂ < x₁ → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω t ≠ x₂ := by
    by_cases hcs : x₂ < x₁ ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ)
    · filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 b jumps hb x₁ θ₁ x₂ P h hh η₁ ζ₁ hη₁).2 hcs.1 hcs.2]
        with ω hω _ _ using hω
    · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hcs
  filter_upwards [h1, h2, hpath, ae_contact_cases hκ hκ4 hb hx hD hh hη₁ hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₁,
    Supp10.ae_apply_zero_of_isFlowLine hη₁, Supp10.ae_apply_zero_of_isFlowLine hη₂, hG₁]
    with ω h1ω h2ω hpω hCω hinj hinc h0₁ h0₂ hG₁ω
  intro x T q hxζ hT hq h₁ h₂
  obtain ⟨hωM, φ, ψ, lift, c₁, σ, -, -, -, -, -, -, -, hσU, -, himg, -, hjun, hword⟩ :=
    hpω T q hT h₂ hq ⟨x, q, hxζ, h₁, le_rfl⟩
  -- the corner time is in the range of the clock: no earlier new contact with the completed second path
  have hxmem : x ∈ c₁ '' {s | (s : ℝ≥0∞) ≤ σ} := by
    rw [himg]
    refine ⟨hxζ.le, fun t' ht'0 ht'x hmem => ?_⟩
    obtain ⟨t, ht, he⟩ := hmem
    have ht'ζ : (t' : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_lt_coe.2 ht'x).trans hxζ
    rcases eq_or_ne t 0 with rfl | ht0
    · -- the first path would revisit the second seed
      rw [h0₂] at he
      rcases hx.lt_or_eq with hlt | heq
      · have hw : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ) := by
          have := (Restart.FCPlumb.cumWeightLeft_gt_iff hκ).2 ((hinc t' ht'ζ x₂ he.symm).1 hx)
          linarith
        exact hG₁ω hlt hw t' ht'ζ.le he.symm
      · have h0mem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ω} := by
          show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω
          simp
        have hst : η₁ ω t' = η₁ ω 0 := by rw [← he, h0₁, heq]
        exact ht'0.ne' (hinj ht'ζ.le h0mem hst)
    · have htζ : (t : ℝ≥0∞) ≤ ζ₂ ω := by rw [← hT]; exact ENNReal.coe_le_coe.2 ht.2
      obtain ⟨-, htT, -⟩ := hCω t' t ht'ζ htζ (pos_iff_ne_zero.2 ht0) he.symm
      rw [← hT] at htT
      have htT' : t = T := ENNReal.coe_injective htT
      subst htT'
      have hst : η₁ ω t' = η₁ ω x := by rw [← he, h₂, h₁]
      exact ht'x.ne (hinj ht'ζ.le hxζ.le hst)
  obtain ⟨s, hs, hcs⟩ := hxmem
  -- the chart path is at the junction
  have hΓ0 : Γ (X ω) s = 0 := hjun s hs (by rw [hcs, h₁, h₂])
  have hvis : X ω ∈ visitsZero Γ U := ⟨s, le_trans hs hσU, hΓ0⟩
  -- the junction's left weight
  have hwt : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim (β ω).1.fn 0 + θ₁ * chiC κ) := by
    have hre : (η₂ ω T).re = q := by rw [h₂]; simp
    rw [hword, hre]
    have := (Restart.FCPlumb.cumWeightLeft_gt_iff hκ).2 ((hinc x hxζ q h₁).1 (hq.le.trans hx))
    linarith
  exact h1ω hωM ⟨h2ω hωM hwt, hvis⟩

/-- **The real first-hit exclusion from Lemma G7 at the retained pair `(0, ζ₂)`** (through the pocket corner,
`g7GB7aFirstHitReal_of_pocketCorner`). -/
theorem g7GB7aFirstHitReal_of_terminalRetained (hK : TerminalRetainedPairStatement.{u}) :
    G7GB7aFirstHitRealStatement.{u} :=
  g7GB7aFirstHitReal_of_pocketCorner (pocketCorner_of_terminalRetained hK)

end InteractingSLE.RealContact
