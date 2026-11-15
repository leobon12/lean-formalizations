/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.HistBorel
import InteractingSLE.Spec.Sec4.SpecialHeights
import InteractingSLE.Spec.Coupling.LawUniqueTransfer
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.Spec.Dimension.Finite

/-!
# Theorem 1.2 under (4.4): the transfer to every coupling

Packet PROVE-SEC4-B5 (specification §4.2, proof of Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4),
`source/spec/p097-144.md` L582–L586, p. 122, and Aux. lemma 23, L589–L627, pp. 122–123).

The proof of Theorem 1.2 under (4.4) has two halves: a reference coupling in which the trace is a Borel function
of the field (Proposition 4.11 and conditional independence), and the transfer of this function to every coupling
with the original optional hull specification (Aux. lemma 23: "every such coupling has the same joint law of the
entire field and the driving history through `S`", then "Equality of all these finite joint laws gives equality of
the field and full-history laws on the countable sequence space"). This file proves the second half in full:

* `isOptionalHullLawUnique_of_admissible`: for `0 < κ ≤ 4` and an ordered force word with admissible side partial
  sums (in particular every word satisfying (4.4), `isOptionalHullLawUnique_of_cond44`), any two couplings with the
  optional hull specification of Theorem 1.1 have the same joint law of the field and the **entire** killed driving
  history (`LawUnique.IsOptionalHullLawUnique`). Proof: the lifetime is infinite and the trace is simple and in `ℍ`
  at positive times (Remark 2.3 for `κ ≤ 4`, `Zhan.IsIntegratedSLEEvolution.ae_simple_trace`), with interior
  dimension `< 2` (Aux. lemma 15); so Aux. lemma 23 (`map_stopHistory_prod_eq_of_thinTrace`) applies at the
  deterministic stops `n ∈ ℕ`; the stopped histories at `0, …, N − 1` are functions of the one at `N`, so all finite
  joint laws agree, hence the joint law of the field and the whole sequence (`map_prod_eq_of_forall_map_fin`); on
  `{ζ = ∞}` the killed history is a measurable function of that sequence (`histOfStops`).
* `hasFieldDeterminedHistories_of_admissible_of_reference`, `hasFieldDeterminedHistories_of_cond44_of_reference`,
  `exists_measurable_lifetime_trace_eq_comp_field_of_cond44_of_reference`: if **one** coupling (on any probability
  space) of such a word has its killed driving history determined by its field, then every coupling has, and the
  conclusion of the frozen Theorem 1.2 holds for every coupling of the word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec4

open LawUnique

variable {nL nR : ℕ}

/-! ### The killed history from its stops at the integers -/

/-- The deterministic stopping rule `s ≡ n`. -/
def natStop (n : ℕ) : HistorySpace nL nR → ℝ≥0 := fun _ => (n : ℝ≥0)

theorem measurable_natStop (n : ℕ) : Measurable (natStop (nL := nL) (nR := nR) n) := measurable_const

/-- Stopping at `m ≤ n` after stopping at `n` is stopping at `m`. -/
theorem stopHistory_natStop_stopHistory_natStop {m n : ℕ} (hmn : m ≤ n) (γ : HistorySpace nL nR) :
    stopHistory (natStop m) (stopHistory (natStop n) γ) = stopHistory (natStop m) γ := by
  simp only [stopHistory, natStop, Prod.mk.injEq, true_and]
  funext p
  by_cases hp : dyadicTime p ≤ (m : ℝ≥0)
  · have hpn : dyadicTime p ≤ (n : ℝ≥0) := hp.trans (by exact_mod_cast hmn)
    simp only [hp, hpn, ↓reduceIte]
  · simp only [hp, ↓reduceIte]

/-- The history with infinite lifetime read off its stops at the integers: the sample at the dyadic time `p` is
read from the stop at `⌈p⌉`. -/
def histOfStops (x : ℕ → HistorySpace nL nR) : HistorySpace nL nR :=
  (⊤, fun p => (x ⌈(dyadicTime p : ℝ)⌉₊).2 p)

theorem measurable_histOfStops : Measurable (histOfStops (nL := nL) (nR := nR)) := by
  refine measurable_const.prodMk (measurable_pi_iff.2 fun p => ?_)
  exact (measurable_pi_apply p).comp (measurable_snd.comp (measurable_pi_apply _))

/-- On `{ζ = ∞}` the killed history is read off its stops at the integers. -/
theorem histOfStops_stopHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤) :
    histOfStops (fun n => stopHistory (natStop n) (killedHistory W VL VR ζ ω)) =
      killedHistory W VL VR ζ ω := by
  simp only [histOfStops, killedHistory, stopHistory, natStop, hζ, Prod.mk.injEq, true_and]
  funext p
  have hp : dyadicTime p ≤ ((⌈(dyadicTime p : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact Nat.le_ceil _
  simp only [hp, ↓reduceIte]

/-! ### Every coupling of an admissible word has the same joint law of field and history -/

section Transfer

open QuantumZipper (H)

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The thin-trace premise of Aux. lemma 23 at every integer stop** (Remark 2.3 for `κ ≤ 4` and Aux. lemma 15).
For an integrated evolution of an ordered word with admissible side partial sums, `0 < κ ≤ 4`, almost surely the
lifetime is infinite and, for every `n`, some generating trace is injective on `[0, n]`, lies in `ℍ` on `(0, n]`,
and has interior dimension at most `d_κ < 2` there. -/
theorem ae_thinTrace_natStop (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : HasAdmissiblePartialSums κ ρL ρR xL xR) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ n : ℕ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      InjOn η (Icc 0 (n : ℝ≥0)) ∧ (∀ t ∈ Ioc 0 (n : ℝ≥0), η t ∈ H) ∧
      dimH (η '' Icc 0 (n : ℝ≥0) ∩ H) ≤ ENNReal.ofReal (Dimension.interiorDimBound κ) := by
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hF hadm hE,
    hE.ae_dimH_image_inter_H_le hκ (by linarith)] with ω hω hdim
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := hω
  have hη' : IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by rw [hζ]; exact hη
  refine ⟨hζ, fun n => ⟨η, hη', hinj.injOn, fun t ht => hH t ht.1, ?_⟩⟩
  exact hdim η hη' (Icc 0 (n : ℝ≥0)) fun t _ => by
    show (t : ℝ≥0∞) ≤ ζ ω
    rw [hζ]; exact le_top

/-- **Aux. lemma 23 for admissible words, the entire history** (Theorem 1.2 under (4.4), transfer step;
Aux. lemma 23's proof, p. 123: "Equality of all these finite joint laws gives equality of the field and
full-history laws on the countable sequence space"). For `0 < κ ≤ 4` and an ordered force word with admissible side
partial sums, any two couplings with the original optional hull specification of Theorem 1.1, on probability spaces
of the universes `u` and `v`, have the same joint law of the field and the killed driving history. -/
theorem isOptionalHullLawUnique_of_admissible (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : HasAdmissiblePartialSums κ ρL ρR xL xR) :
    IsOptionalHullLawUnique.{u, v} κ xL xR ρL ρR := by
  intro Ω₁ m₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂
  have hd : Dimension.interiorDimBound κ < 2 := Dimension.interiorDimBound_lt_two (by linarith)
  have hT₁ := ae_thinTrace_natStop hκ hκ4 hF hadm hC₁.1
  have hT₂ := ae_thinTrace_natStop hκ hκ4 hF hadm hC₂.1
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hK₁ := measurable_killedHistory hX₁
  have hK₂ := measurable_killedHistory hX₂
  -- Aux. lemma 23 at the deterministic stops `n`
  have hstop : ∀ n : ℕ,
      P₁.map (fun ω => (stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω)) =
        P₂.map (fun ω => (stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω)) := by
    intro n
    have hst₁ : ∀ hX : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁,
        IsStoppingTime (drivingFiltration P₁ hX) (ruleTime (natStop n) W₁ VL₁ VR₁ ζ₁) := fun hX => by
      show IsStoppingTime _ fun _ => ((n : ℝ≥0) : WithTop ℝ≥0)
      exact isStoppingTime_const _ _
    have hst₂ : ∀ hX : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂,
        IsStoppingTime (drivingFiltration P₂ hX) (ruleTime (natStop n) W₂ VL₂ VR₂ ζ₂) := fun hX => by
      show IsStoppingTime _ fun _ => ((n : ℝ≥0) : WithTop ℝ≥0)
      exact isStoppingTime_const _ _
    refine map_stopHistory_prod_eq_of_thinTrace hκ hF (measurable_natStop n) hd hC₁ hst₁ ?_ ?_ hC₂ hst₂ ?_
    · filter_upwards [hT₁] with ω hω
      rw [hω.1]; exact ENNReal.coe_lt_top
    · filter_upwards [hT₁] with ω hω
      exact hω.2 n
    · filter_upwards [hT₂] with ω hω
      rw [hω.1]; exact ENNReal.coe_lt_top
  -- the finite joint laws
  have hXm₁ : ∀ n : ℕ, Measurable fun ω => stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω) :=
    fun n => (measurable_stopHistory (measurable_natStop n)).comp hK₁
  have hXm₂ : ∀ n : ℕ, Measurable fun ω => stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    fun n => (measurable_stopHistory (measurable_natStop n)).comp hK₂
  have hfin : ∀ N : ℕ,
      P₁.map (fun ω => (h₁ ω, fun i : Fin N => stopHistory (natStop i) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
        P₂.map (fun ω => (h₂ ω, fun i : Fin N => stopHistory (natStop i) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
    intro N
    let R : HistorySpace nL nR × LQGMetric.DistOn upperHalfPlaneOpens →
        LQGMetric.DistOn upperHalfPlaneOpens × (Fin N → HistorySpace nL nR) :=
      fun q => (q.2, fun i => stopHistory (natStop i) q.1)
    have hR : Measurable R := measurable_snd.prodMk
      (measurable_pi_iff.2 fun i => (measurable_stopHistory (measurable_natStop i)).comp measurable_fst)
    have e₁ : (fun ω => (h₁ ω, fun i : Fin N => stopHistory (natStop i) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
        R ∘ fun ω => (stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω) := by
      funext ω
      simp only [R, Function.comp_apply, Prod.mk.injEq, true_and]
      funext i
      exact (stopHistory_natStop_stopHistory_natStop i.2.le _).symm
    have e₂ : (fun ω => (h₂ ω, fun i : Fin N => stopHistory (natStop i) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) =
        R ∘ fun ω => (stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω) := by
      funext ω
      simp only [R, Function.comp_apply, Prod.mk.injEq, true_and]
      funext i
      exact (stopHistory_natStop_stopHistory_natStop i.2.le _).symm
    rw [e₁, e₂, ← Measure.map_map hR ((hXm₁ N).prodMk hC₁.2.1),
      ← Measure.map_map hR ((hXm₂ N).prodMk hC₂.2.1), hstop N]
  -- the field and the whole sequence of stops
  have hseq := map_prod_eq_of_forall_map_fin (P := P₁) (P' := P₂) hC₁.2.1 hXm₁ hC₂.2.1 hXm₂ hfin
  -- the killed history from the sequence of stops
  let G : LQGMetric.DistOn upperHalfPlaneOpens × (ℕ → HistorySpace nL nR) →
      LQGMetric.DistOn upperHalfPlaneOpens × HistorySpace nL nR := fun q => (q.1, histOfStops q.2)
  have hG : Measurable G := measurable_fst.prodMk (measurable_histOfStops.comp measurable_snd)
  have e₁ : P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      (P₁.map fun ω => (h₁ ω, fun n => stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))).map G := by
    rw [Measure.map_map hG (hC₁.2.1.prodMk (measurable_pi_iff.2 hXm₁))]
    refine Measure.map_congr ?_
    filter_upwards [hT₁] with ω hω
    simp only [G, Function.comp_apply, histOfStops_stopHistory hω.1]
  have e₂ : P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      (P₂.map fun ω => (h₂ ω, fun n => stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))).map G := by
    rw [Measure.map_map hG (hC₂.2.1.prodMk (measurable_pi_iff.2 hXm₂))]
    refine Measure.map_congr ?_
    filter_upwards [hT₂] with ω hω
    simp only [G, Function.comp_apply, histOfStops_stopHistory hω.1]
  rw [e₁, e₂, hseq]

/-- **Aux. lemma 23 under (4.4), the entire history** (Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4), transfer
step). -/
theorem isOptionalHullLawUnique_of_cond44 (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Cond44 κ ρL ρR) : IsOptionalHullLawUnique.{u, v} κ xL xR ρL ρR :=
  isOptionalHullLawUnique_of_admissible hκ hκ4.le hF (hasAdmissiblePartialSums_of_cond44 hκ4 hF h44)

/-- **Field determination of every coupling from one reference, admissible words** (Theorem 1.2 under (4.4),
"The result follows" with Aux. lemma 23's "Consequently"). For `0 < κ ≤ 4` and an ordered word with admissible side
partial sums: if one coupling with the optional hull specification (on a probability space of the universe `v`)
has its killed driving history determined by its field, then so has every such coupling. -/
theorem hasFieldDeterminedHistories_of_admissible_of_reference (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : HasAdmissiblePartialSums κ ρL ρR xL xR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR :=
  hasFieldDeterminedHistories_of_isOptionalHullLawUnique
    (isOptionalHullLawUnique_of_admissible.{v, u} hκ hκ4 hF hadm) href

/-- **Field determination of every coupling from one reference, under (4.4)** (`0 < κ < 4`). -/
theorem hasFieldDeterminedHistories_of_cond44_of_reference (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Cond44 κ ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR :=
  hasFieldDeterminedHistories_of_admissible_of_reference hκ hκ4.le hF
    (hasAdmissiblePartialSums_of_cond44 hκ4 hF h44) href

/-- **Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4), from one reference coupling** (conditional helper: the
reference is the remaining input, see `planning/handoffs/PROVE-SEC4-B5.md`). If one coupling of the word with the
optional hull specification has a field-determined killed driving history, then in **every** such coupling the
lifetime and the entire capacity-parametrized trace (frozen after a finite lifetime) are a Borel function of the
field: the conclusion of the frozen Theorem 1.2. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_cond44_of_reference (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Cond44 κ ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hcoup
    (hasFieldDeterminedHistories_of_cond44_of_reference hκ hκ4 hF h44 href P 𝓕 W VL VR B ζ h hcoup)

end Transfer

end Sec4

end InteractingSLE
