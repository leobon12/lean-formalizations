/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411QOrder
import InteractingSLE.Spec.Sec5.Prop55N

/-!
# Proposition 4.11 in Lemma 4.5's chart `Q` from its per-time inputs

Packet PROVE-SEC5-O. Specification §4.2, Lemma 4.7, Proposition 4.9 and Proposition 4.11
(`source/spec/p097-144.md#lem-4.7`, `#prop-4.9`, pp. 117–122), on the glued space of `Cond44Ref.Prop411QStatement`
(PROVE-SEC5-N): the flow line `η` of `h` and the counterflow line `η′ = R ∘ β` of `h − π/2 χ` from `∞`,
conditionally independent given `h`.

The source proves Proposition 4.11 from two per-time statements and a pathwise argument:

* **Lemma 4.7 at a flow time `q`** (`Lemma47QHitStatement`): "`η′` almost surely first hits `∂_L𝒮 ∪ η([0, τ])` at
  `η(τ)`" — in the chart `Q`, the counterflow visits `η(q)` and avoids `η((0, q])` before that visit
  (`Prop411QOrder.IsFirstHitQ`). Its proof is the conditional law of `η′` given `η([0, q])` (Propositions 3.7–3.8,
  Theorem 2.4) followed by Lemma 4.5.
* **Proposition 4.9's first exit at a counterflow time `s`** (`Prop49QExitStatement`): "`η` almost surely exits
  `𝒮 ∖ η′([0, τ′])` on the left side of `η′([0, τ′])`" — in the chart `Ψ = R ∘ f_s ∘ R` of `ℍ ∖ R(K_s)`, which
  fixes `0` and sends the tip to `∞`, `η` reaches the counterflow prefix at a time `t₀`, avoiding `R(K_s)` before, and
  `Ψ ∘ η` tends to a negative real point as `t ↑ t₀` (the left side of the prefix maps to the far negative half-line).
  Its proof is the converse conditional law (`η` given `η′([0, s])`) followed by Aux. lemma 22 (Remark 4.10).
* **The counterflow's regularity** (`CfRegQStatement`): the counterflow has infinite lifetime and its continuous
  driver generates the continuous Loewner trace read from its history (Remark 4.8 (b), Lemma 4.5 and Aux. lemma 7 at
  `κ′ = 16/κ`).

**Proved here** (`prop411QStatement_of_lemma47Q_of_prop49Q`): the three per-time inputs give
`Cond44Ref.Prop411QStatement`, through the pathwise steps of `Prop411QOrder` (containment and reverse chronological
order: Lemma 4.7's "in particular") and `Prop411QSide` (Proposition 4.9's no-wrap step). The consumers
`Cond44Ref.cond44ReferenceStatement_of_prop411Q` and `Cond44Ref.exists_isThreeCurveSpace_of_prop411Q_of_prop51Q`
then apply unchanged. These are conditional helpers: they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Prop411Q

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref

/-- The counterflow driver read from a history, on real times (the chart-`R` driver of `β = histLine y`). -/
def cfDrv {nL nR : ℕ} (y : HistorySpace nL nR) (s : ℝ) : ℝ := (WangWu.pathsOfHistory y).2.1 s.toNNReal

/-- **Almost surely on the glued space of every chart-`Q` configuration** (the setting of
`Cond44Ref.Prop411QStatement`): for `0 < κ < 4`, an ordered (4.4) word, an optional hull coupling `(h, W, …)` on `Ω`, a
centred counterflow coupling on `Ω₂` whose field has the law of `h − π/2 χ`, and a regular conditional law `k` of its
killed history given its field, the property `Φ` of the flow line `seedLine ζ W p.1` and the counterflow history `p.2`
holds for almost every glued sample `p`. -/
def CfGlueAE (Φ : (ℝ → ℂ) → HistorySpace 0 0 → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
          Φ (seedLine ζ W p.1) p.2

/-- **Named input: the counterflow's regularity in the chart `Q`** (Remark 4.8 (b), Lemma 4.5, Aux. lemma 7 at
`κ′ = 16/κ`): almost surely the counterflow history has infinite lifetime, its driver is continuous and starts at `0`,
and the curve `β = histLine` read from the history is a Loewner trace of it (so `η′ = R ∘ β` is continuous). -/
def CfRegQStatement : Prop :=
  CfGlueAE.{u} fun _ y => y.1 = ⊤ ∧ Continuous (cfDrv y) ∧ cfDrv y 0 = 0 ∧ IsLoewnerTrace (cfDrv y) (histLine y)

/-- **Named input: Lemma 4.7 at a rational flow time, in the chart `Q`** ("`η′` almost surely first hits
`∂_L𝒮 ∪ η([0, τ])` at `η(τ)`", at the deterministic stopping time `τ = q`): the counterflow `η′ = R ∘ β` visits
`η(q)` at some time `u > 0` and avoids `η((0, q])` before `u`. -/
def Lemma47QHitStatement : Prop :=
  ∀ q : ℚ, 0 < q → CfGlueAE.{u} fun η y => IsFirstHitQ η (histLine y) q

/-- **Named input: Proposition 4.9's first exit at a rational counterflow time, in the chart `Q`** ("`η` almost surely
exits `𝒮 ∖ η′([0, τ′])` on the left side of `η′([0, τ′])`", proof of Proposition 4.9 with Remark 4.10 and Aux. lemma
22): the flow line reaches the counterflow prefix `η′((0, s])` at a time `t₀ > 0`, avoids the counterflow hull
`R(K_s)` before `t₀`, and in the chart `Ψ = R ∘ f_s ∘ R` of `ℍ ∖ R(K_s)` (tip at `∞`, `0` fixed) it tends to a
negative real point as `t ↑ t₀`: the left side of the prefix. -/
def Prop49QExitStatement : Prop :=
  ∀ s : ℚ, 0 < s → CfGlueAE.{u} fun η y => ∃ t₀ x₀ : ℝ, 0 < t₀ ∧ x₀ < 0 ∧
    (∃ v ∈ Ioc (0 : ℝ) s, η t₀ = revLine y v) ∧
    (∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull (cfDrv y) s) ∧
    Tendsto (fun t => revChart (cfDrv y) s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ))

/-- The counterflow points at positive rational times are `R(β(r))` when the lifetime is infinite. -/
theorem cfPts_of_pos {nL nR : ℕ} {y : HistorySpace nL nR} (hy : y.1 = ⊤) {r : ℚ} (hr : 0 < r) :
    cfPts y r = negInv (histLine y r) := by
  simp only [cfPts, hr, hy, ENNReal.coe_lt_top, and_self, ↓reduceIte]
  rfl

/-- **The pathwise part of Proposition 4.11 in the chart `Q`**: from the counterflow's regularity, the first-contact
property at every positive rational flow time and the first-exit property at every positive rational counterflow
time, the flow line lies in the completed counterflow range and no counterflow point at a rational time is on its left
side. -/
theorem prop411Q_pathwise {η : ℝ → ℂ} {y : HistorySpace 0 0} (hη : IsProperArc η)
    (hreg : y.1 = ⊤ ∧ Continuous (cfDrv y) ∧ cfDrv y 0 = 0 ∧ IsLoewnerTrace (cfDrv y) (histLine y))
    (hhit : ∀ q : ℚ, 0 < q → IsFirstHitQ η (histLine y) q)
    (hexit : ∀ s : ℚ, 0 < s → ∃ t₀ x₀ : ℝ, 0 < t₀ ∧ x₀ < 0 ∧
      (∃ v ∈ Ioc (0 : ℝ) s, η t₀ = revLine y v) ∧
      (∀ t ∈ Ioo 0 t₀, η t ∉ negInv '' fwdHull (cfDrv y) s) ∧
      Tendsto (fun t => revChart (cfDrv y) s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ))) :
    (∀ t : ℚ, 0 < t → η t ∈ cfRange y) ∧ ∀ s : ℚ, cfPts y s ∉ leftSideOf (arcRange η) := by
  obtain ⟨hy, hw, hw0, hβ⟩ := hreg
  refine ⟨fun t ht => ?_, fun s => ?_⟩
  · exact mem_closure_range_of_isFirstHitQ hη hβ.2.1 (by exact_mod_cast ht) (hhit t ht)
      fun r hr => cfPts_of_pos hy hr
  · by_cases hs : 0 < s
    · rw [cfPts_of_pos hy hs]
      obtain ⟨t₀, x₀, ht₀, hx₀, ⟨v, hv, he⟩, hpre, hlim⟩ := hexit s hs
      have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
      exact negInv_notMem_leftSideOf_of_exit hη hβ hw hw0 hs' ht₀ hx₀ hpre hlim
        fun t ht => mem_negInv_fwdHull_of_isFirstHitQ hη hβ hhit hs' ht₀ hv he ht
    · have h0 : cfPts y s = 0 := by simp [cfPts, hs]
      rw [h0]
      exact fun h => ne_zero_of_mem_H h.1.1 rfl

/-- **Proposition 4.11 in the chart `Q` (`Cond44Ref.Prop411QStatement`) from its per-time inputs** (conditional
helper): Lemma 4.7 at rational flow times, Proposition 4.9's first exit at rational counterflow times, and the
counterflow's regularity. -/
theorem prop411QStatement_of_lemma47Q_of_prop49Q (hreg : CfRegQStatement.{u}) (h47 : Lemma47QHitStatement.{u})
    (h49 : Prop49QExitStatement.{u}) : Prop411QStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hr := hreg κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hh : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) hXm),
      ∀ q : ℚ, 0 < q → IsFirstHitQ (seedLine ζ W p.1) (histLine p.2) q := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < q
    · filter_upwards [h47 q hq κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk]
        with p hp using fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h hq
  have he : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) hXm),
      ∀ s : ℚ, 0 < s → ∃ t₀ x₀ : ℝ, 0 < t₀ ∧ x₀ < 0 ∧
        (∃ v ∈ Ioc (0 : ℝ) s, seedLine ζ W p.1 t₀ = revLine p.2 v) ∧
        (∀ t ∈ Ioo 0 t₀, seedLine ζ W p.1 t ∉ negInv '' fwdHull (cfDrv p.2) s) ∧
        Tendsto (fun t => revChart (cfDrv p.2) s (seedLine ζ W p.1 t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ)) := by
    refine ae_all_iff.2 fun s => ?_
    by_cases hs : 0 < s
    · filter_upwards [h49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk]
        with p hp using fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h hs
  filter_upwards [hline, hr, hh, he] with p hp hrp hhp hep
  exact prop411Q_pathwise hp.2.2 hrp hhp hep

/-- **The §4.2 reference coupling (Theorem 1.2 under (4.4)) from the per-time inputs of Proposition 4.11.** -/
theorem cond44ReferenceStatement_of_lemma47Q_of_prop49Q (hreg : CfRegQStatement.{u})
    (h47 : Lemma47QHitStatement.{u}) (h49 : Prop49QExitStatement.{u}) :
    Sec7.Lemma71H.Cond44ReferenceStatement.{u} :=
  cond44ReferenceStatement_of_prop411Q (prop411QStatement_of_lemma47Q_of_prop49Q hreg h47 h49)

end InteractingSLE.Sec5.Prop411Q
