/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj
import InteractingSLE.Spec.Supplement.G7RestartMeas
import InteractingSLE.Spec.Theorem15D5Code
import InteractingSLE.Spec.Sec7.Aux97ProofIdent
import InteractingSLE.Spec.Restart.RetPlumbProofHist

/-!
# Theorem 1.5's leaf 3: the ordinary-pair event is, up to a null set, a retained event

Packet PROVE-T15-ASTOP-PART (item 1 of `RLC.OrdModel.AStopSourceInputs`: the parts of the type partition must lie,
almost surely, in the ordinary pairs, where all pathwise inputs hold; this is the ordinary-pair analogue of
PROVE-T15-RET3's `RetFin.exists_retSigma76_pairEvent` for disjoint pairs).

* `ordRecSet d`: the recorded conditions of an ordinary pair for retained data `d` (chart event, first tip interior,
  adherent to the active domain and off the second prefix) — measurable (`measurableSet_ordRecSet`);
* W0's completion condition through the dyadic codes of the two prefixes (PROVE-T15-D5's
  `Theorem15D5.hasOrderedProperCompletions_iff_exists`): a projection of a Borel set, hence universally measurable
  (`Theorem15D5.uMeasurableSet_hopcCode`, Lusin), so equal almost surely to a Borel condition on the codes;
* **`mem_ordRecSet_iff`**: at live cutoffs, on the good event of retained data agreeing with two paths on the prefixes,
  `ordRecSet` and W0's condition are exactly `IsOrdinaryRetainedPair` of the paths (deterministic);
* **`exists_retSigma76_ordEvent`**: the ordinary-pair event of two flow lines agrees almost surely with an event of the
  retained σ-algebra `retSigma76` (with the stopped retained data of CONDDET-HIST, `RLC.exists_retStop`).

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

namespace AStopPart

open Supp7 Restart Sec7.Lemma76F Theorem15D5

section Det

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **The recorded conditions of an ordinary pair** for retained data `d`: the chart event (second tip interior, off the
first prefix and adherent to the active domain), the first tip interior and adherent to the active domain, and the first
tip off the second prefix. -/
def ordRecSet (d : RetData Ω) : Set Ω :=
  (d.E ∩ {ω | d.η₁ ω d.u ∈ H} ∩ {ω | d.η₁ ω d.u ∈ closure (d.D ω)}) \
    (d.G ∩ {ω | ∃ s ≤ d.r, ∃ t ≤ (0 : ℝ≥0), d.η₂ ω s = d.η₁ ω d.u})

theorem measurableSet_ordRecSet (hd : d.IsMeasGood) : MeasurableSet (ordRecSet d) := by
  have h1 : MeasurableSet {ω | d.η₁ ω d.u ∈ H} :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp (hd.meas₁ d.u))
  have h2 : MeasurableSet {ω | d.η₁ ω d.u ∈ closure (d.D ω)} :=
    measurableSet_mem_closure hd.isOpen_D hd.measurableSet_mem_D (hd.meas₁ d.u)
  have h3 := measurableSet_inter_exists_eq hd.measurableSet_G hd.meas₂ (f₂ := fun ω (_ : ℝ≥0) => d.η₁ ω d.u)
    (fun _ => hd.meas₁ d.u) (c₁ := fun _ => d.r) (c₂ := fun _ => 0) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω).2.1) (fun _ _ => continuousOn_const)
  exact ((hd.measurableSet_E.inter h1).inter h2).diff h3

/-- The dyadic codes of the two paths of retained data. -/
def ordCode (d : RetData Ω) (ω : Ω) : CCode × CCode := (encC (d.η₁ ω), encC (d.η₂ ω))

theorem measurable_ordCode (hd : d.IsMeasGood) : Measurable (ordCode d) :=
  (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hd.meas₁ (Sec2.Assembly.dyad n k)).prodMk
    (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hd.meas₂ (Sec2.Assembly.dyad n k))

/-- The coded completion event (W0's condition on the codes of the two prefixes). -/
def hopcSet (a c : ℝ≥0) : Set (CCode × CCode) := {p | ∃ y, (p, y) ∈ CompRel a c}

/-- On the good event, W0's condition for the paths of retained data is the coded completion event. -/
theorem hasOrderedProperCompletions_iff_hopcSet (hd : d.IsMeasGood) {ω : Ω} (hG : ω ∈ d.G) :
    HasOrderedProperCompletions (d.η₁ ω) d.u (d.η₂ ω) d.r ↔ ordCode d ω ∈ hopcSet d.u d.r := by
  have hg := hd.good ω hG
  exact hasOrderedProperCompletions_iff_exists (by rw [← Icc_zero_eq_Iic]; exact hg.1)
    (by rw [← Icc_zero_eq_Iic]; exact hg.2.1)

/-- **The ordinary pair through the recorded conditions** (deterministic): at live cutoffs, for a sample of the good
event of retained data agreeing with paths `α`, `β` on the prefixes, the recorded conditions and W0's condition for the
data's paths are exactly `IsOrdinaryRetainedPair α ζ₁ u β ζ₂ r`. -/
theorem mem_ordRecSet_iff (hd : d.IsMeasGood) {ω : Ω} (hG : ω ∈ d.G) {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} (a₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (a₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hu : (d.u : ℝ≥0∞) < ζ₁) (hr : (d.r : ℝ≥0∞) < ζ₂) :
    (ω ∈ ordRecSet d ∧ HasOrderedProperCompletions (d.η₁ ω) d.u (d.η₂ ω) d.r) ↔
      IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r := by
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => a₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => a₂ t ht.2
  have t₁ : d.η₁ ω d.u = α d.u := a₁ d.u le_rfl
  have t₂ : d.η₂ ω d.r = β d.r := a₂ d.r le_rfl
  have hoff : (¬ (ω ∈ d.G ∧ ∃ s ≤ d.r, ∃ t ≤ (0 : ℝ≥0), d.η₂ ω s = d.η₁ ω d.u)) ↔ α d.u ∉ β '' Icc 0 d.r := by
    rw [← e₂.image_eq, ← t₁]
    constructor
    · rintro hn ⟨s, hs, he⟩
      exact hn ⟨hG, s, hs.2, 0, le_rfl, he⟩
    · rintro hn ⟨-, s, hs, -, -, he⟩
      exact hn ⟨s, ⟨zero_le, hs⟩, he⟩
  constructor
  · rintro ⟨⟨⟨⟨hE, h1H⟩, h1c⟩, h1off⟩, hW0⟩
    have hDeq : d.D ω = activeDomain α d.u β d.r := by
      rw [hd.D_of_mem hE, activeDomain_congr_Icc e₁ e₂]
    obtain ⟨⟨⟨-, h2H⟩, h2off⟩, h2c⟩ := hE
    have hE₀ : ω ∈ d.E₀ := ⟨⟨hG, h2H⟩, h2off⟩
    have h2c' : d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω) := h2c
    rw [hd.DOf_of_mem RetData.E₀_subset_G hE₀, activeDomain_congr_Icc e₁ e₂, t₂] at h2c'
    have h2H' : d.η₂ ω d.r ∈ H := h2H
    have h2off' : d.η₂ ω d.r ∉ d.η₁ ω '' Icc 0 d.u := h2off
    have h1H' : d.η₁ ω d.u ∈ H := h1H
    have h1c' : d.η₁ ω d.u ∈ closure (d.D ω) := h1c
    rw [hDeq, t₁] at h1c'
    rw [t₂] at h2H'
    rw [t₂, e₁.image_eq] at h2off'
    rw [t₁] at h1H'
    exact ⟨hu, hr, h1H', h2H', h2off', hoff.1 h1off, h1c', h2c',
      Sec7.HasOrderedProperCompletions.congr_prefix a₁ a₂ hW0⟩
  · intro hp
    have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hp
    have hDeq : d.D ω = activeDomain α d.u β d.r := by
      rw [hd.D_of_mem hE, activeDomain_congr_Icc e₁ e₂]
    refine ⟨⟨⟨⟨hE, ?_⟩, ?_⟩, hoff.2 hp.2.2.2.2.2.1⟩,
      Sec7.HasOrderedProperCompletions.congr_prefix (fun s hs => (a₁ s hs).symm) (fun t ht => (a₂ t ht).symm)
        hp.2.2.2.2.2.2.2.2⟩
    · show d.η₁ ω d.u ∈ H
      rw [t₁]; exact hp.2.2.1
    · show d.η₁ ω d.u ∈ closure (d.D ω)
      rw [hDeq, t₁]; exact hp.2.2.2.2.2.2.1

end Det

section Event

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The ordinary-pair event is, up to a null set, an event of the retained σ-algebra.** -/
theorem exists_retSigma76_ordEvent (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (u₀ : ℂ → ℝ) (a r : ℝ≥0) :
    ∃ B : Set Ω, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] B ∧
      ∀ᵐ ω ∂P, ω ∈ B ↔ IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) a (η₂ ω) (ζ₂ ω) r := by
  obtain ⟨ηs₁, ηs₂, hd'R, hag'⟩ := exists_retStop hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ a r
  set d' := stopRet ηs₁ ηs₂ a r with hd'def
  have hR := retSigma76_le P η₁ η₂ ζ₁ ζ₂ a r
  have hd' : d'.IsMeasGood := RetData.IsMeasGood.mono_sigma hd'R hR
  -- the recorded conditions and the live event
  have hrec : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] (ordRecSet d') :=
    @measurableSet_ordRecSet Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ a r) d' hd'R
  have hLive := RetAux79.measurableSet_retLive P η₁ η₂ ζ₁ ζ₂ (measurable_lifetime_of_isFlowLine hη₁)
    (measurable_lifetime_of_isFlowLine hη₂) a r
  -- W0's condition: a Borel version of the coded completion event under the law of the codes
  have hFR : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] (ordCode d') :=
    @measurable_ordCode Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ a r) d' hd'R
  have hF : Measurable (ordCode d') := hFR.mono hR le_rfl
  set Q : Measure (CCode × CCode) := P.map (ordCode d') with hQ
  have hnull : NullMeasurableSet (hopcSet a r) Q := (uMeasurableSet_hopcCode a r).nullMeasurableSet Q
  set A' := toMeasurable Q (hopcSet a r) with hA'
  have hAA' : ∀ᵐ ω ∂P, ordCode d' ω ∈ A' ↔ ordCode d' ω ∈ hopcSet a r :=
    ae_of_ae_map hF.aemeasurable hnull.toMeasurable_ae_eq.mem_iff
  have hA'm : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] (ordCode d' ⁻¹' A') :=
    hFR (measurableSet_toMeasurable Q _)
  refine ⟨(ordRecSet d' ∩ {ω | (a : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω}) ∩ ordCode d' ⁻¹' A',
    (hrec.inter hLive).inter hA'm, ?_⟩
  filter_upwards [hag', hAA'] with ω hω hcode
  constructor
  · rintro ⟨⟨hrecω, hu, hr⟩, hA⟩
    obtain ⟨hG', a₁, a₂⟩ := hω hu hr
    exact (mem_ordRecSet_iff hd' hG' a₁ a₂ hu hr).1
      ⟨hrecω, (hasOrderedProperCompletions_iff_hopcSet hd' hG').2 (hcode.1 hA)⟩
  · intro hp
    obtain ⟨hG', a₁, a₂⟩ := hω hp.1 hp.2.1
    obtain ⟨hrecω, hW0⟩ := (mem_ordRecSet_iff hd' hG' a₁ a₂ hp.1 hp.2.1).2 hp
    exact ⟨⟨hrecω, hp.1, hp.2.1⟩, hcode.2 ((hasOrderedProperCompletions_iff_hopcSet hd' hG').1 hW0)⟩

end Event

end AStopPart

end RLC

end InteractingSLE
