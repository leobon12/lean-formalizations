/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Sec7.Aux125Inputs2
import InteractingSLE.Spec.Sec7.Lemma725Ref

/-!
# The pocket references of Lemma 7.25 and Theorem R.7 from `P`-side inputs (K2)

Packet PROVE-LEMMA725REF. Specification §7.4, Aux. lemma 125 (`source/spec/p385-432.md#aux-125`, pp. 395–398), Aux.
lemma 127 (L318–L333, pp. 402–403) and Lemma 7.25 (L489–L515, pp. 413–414).

PROVE-STRIPSYS15 reduced the references `Aux50Hit.Lemma725DetReferenceStatement` (`href725`) and
`R7.R7ReferenceStatement` (`hR7`) to the named input `Aux125Inputs2.PocketTwoSeedStatement`, whose first part is
"under the regular conditional law given the exterior information `ℰ`, the pocket pair is a two-seed optional hull
coupling" (`IsCondTwoSeedCoupling`). PROVE-DOMAINMARKOV5's K2 (`Restart.DomainMarkov.K2.ae_isOptionalHullCoupling_k`)
produces exactly such conditional couplings from three `P`-side inputs: (E) the continuation is an integrated evolution
of an `ℰ`-measurable random word (`Aux122Disint.IsRandomWordEvolution`, Aux. lemma 122's form), (S) the conditional
law of the field off the continuation hulls (`HasSafeLaw`), (L) the member identities of the hulls
(`HasSafeMembers`). This is Aux. lemma 125's "The canonical law survives the exterior reveal" in `P`-side form.

## Main results

* `ae_isCondTwoSeedCoupling_of_pSide`: the conditional two-seed coupling from (E), (S), (L) and a trace under the
  conditional laws (`ae_lifetime_pos_twoSeed`: the lifetime is positive, both seed weights exceeding `−2`);
* `PocketTwoSeedPSideStatement` (**named input**, the `P`-side form of `PocketTwoSeedStatement`) and
  **`pocketTwoSeedStatement_of_pSide`**; the consequences **`lemma725DetReferenceStatement_of_pSide`**,
  **`lemma725DetReferenceStatement_of_pSide_of_trace`** (the trace taken from Lemma 7.25's trace statement instead of
  the pocket) and **`r7ReferenceStatement_of_pSide`**;
* `ae_ae_condExpKernel_eq_self`: an `ℰ`-measurable record with values in a countably separated space is almost surely
  constant under almost every regular conditional law given `ℰ` — so a determination `X = g(E, H)` becomes
  `X = g(E ω₀, H)` under the conditional law at `ω₀`, for any word (no Aux. lemma 50 needed);
* `PocketWordFieldStatement` (**named input**, the `P`-side pocket of Lemma 7.25 with its actual distant marks: the
  random word `Θ` of Aux. lemmas 119–121, the evolution of Aux. lemma 122, the field data (S), (L) and the global
  determination) and **`aux126Reference_of_pocketWordField`** (Aux. lemma 127 at the level of the field: the reference
  of Aux. lemma 126 for the seed weights), **`lemma725ReferenceStatement_of_pocketWordField`**.

Ruling R48: nothing here takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Lemma725RefK2

open LawUnique LQGMetric Restart.DomainMarkov.K2 Aux122Disint Aux125Inputs2

/-! ### A record measurable for the conditioning σ-algebra is constant under the conditional laws -/

section Record

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **An `ℰ`-measurable record is constant under almost every conditional law given `ℰ`** (values in a countably
separated space). -/
theorem ae_ae_condExpKernel_eq_self (h𝓔 : 𝓔 ≤ mΩ) {ε : Type*} [MeasurableSpace ε] [MeasurableSpace.CountablySeparated ε]
    {E : Ω → ε} (hE : Measurable[𝓔] E) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), E ω = E ω₀ := by
  obtain ⟨S, hSc, hSm, hS⟩ := exists_countable_separating ε MeasurableSet univ
  have h1 : ∀ᵐ ω₀ ∂P, ∀ s ∈ S, ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), (E ω ∈ s ↔ E ω₀ ∈ s) := by
    refine (ae_ball_iff hSc).2 fun s hs => ?_
    have hm : MeasurableSet[𝓔] (E ⁻¹' s) := hE (hSm s hs)
    filter_upwards [ae_ae_condExpKernel_mem (P := P) h𝓔 hm, ae_ae_condExpKernel_mem (P := P) h𝓔 hm.compl]
      with ω₀ h1 h2
    by_cases hω₀ : E ω₀ ∈ s
    · filter_upwards [h1 hω₀] with ω hω using iff_of_true hω hω₀
    · filter_upwards [h2 hω₀] with ω hω using iff_of_false hω hω₀
  filter_upwards [h1] with ω₀ hω₀
  filter_upwards [(ae_ball_iff hSc).2 hω₀] with ω hω using hS _ trivial _ trivial hω

end Record

/-! ### The conditional two-seed coupling from the `P`-side inputs -/

section TwoSeed

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ rL rR : ℝ} {F : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {H : Ω → DistOn upperHalfPlaneOpens} {𝓗 𝓗' : Filtration ℝ≥0 mΩ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The lifetime of a two-seed random-word evolution (seed weights `> −2`) is positive on the live event. -/
theorem ae_lifetime_pos_twoSeed (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsRandomWordEvolution κ P 𝓔 F (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun _ => rL)
      (fun _ => rR) 𝓗 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω := by
  obtain ⟨-, -, -, -, -, -, -, -, hpath⟩ := hE
  filter_upwards [hpath] with ω h hω
  -- the zero-lifetime clause of `IsIntegratedSLEPath` (as `WangWu.IsIntegratedSLEPath.lifetime_pos`)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := h hω
  exact pos_iff_ne_zero.2 fun h0 => Sec2.Assembly2.not_thr_twoSeed hL hR 0 _ _ (h19 h0)

/-- **The conditional two-seed coupling from the `P`-side inputs** (K2 for the constant two-seed word): (E) the pocket
driver is an integrated `SLE_κ(r_L; r_R)` evolution in a filtration containing `ℰ` at time `0`, (S) and (L) for the
field `H` in a filtration `𝓗'` in which the driver is adapted, and a trace under almost every conditional law. -/
theorem ae_isCondTwoSeedCoupling_of_pSide (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsRandomWordEvolution κ P 𝓔 F (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun _ => rL)
      (fun _ => rR) 𝓗 W VL VR B ζ) (hH : Measurable H) (h𝓔' : 𝓔 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' ζ W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    (hlaw : HasSafeLaw κ (fun _ => rL) (fun _ => rR) P 𝓗' F ζ W VL VR H) (hmem : HasSafeMembers P 𝓗' F ζ W H)
    (htr : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₀ := by
  filter_upwards [ae_isOptionalHullCoupling_k hE hH (ae_lifetime_pos_twoSeed hL hR hE) h𝓔' hW' hVL' hVR' hlaw
    hmem, htr] with ω₀ hk ht hω₀
  exact ⟨hk hω₀, ht hω₀⟩

/-- **The conditional two-seed coupling, the trace taken from a two-seed trace statement** (for the both-low words,
Lemma 7.25's finite-time continuity): under the conditional law the versions form a two-seed evolution, whose driver
has a trace by `htw`; the versions agree with the pocket driver. -/
theorem ae_isCondTwoSeedCoupling_of_pSide_of_trace (hL : -2 < rL) (hR : -2 < rR)
    (htw : ∀ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' VR' : Fin 1 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ)
      (ν : Measure Ω) [IsProbabilityMeasure ν],
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) ν 𝓕 W' VL' VR' B' ζ →
        ∀ᵐ ω ∂ν, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ ω) η)
    (hE : IsRandomWordEvolution κ P 𝓔 F (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun _ => rL)
      (fun _ => rR) 𝓗 W VL VR B ζ) (hH : Measurable H) (h𝓔' : 𝓔 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' ζ W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    (hlaw : HasSafeLaw κ (fun _ => rL) (fun _ => rR) P 𝓗' F ζ W VL VR H) (hmem : HasSafeMembers P 𝓗' F ζ W H) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₀ := by
  filter_upwards [ae_isOptionalHullCoupling_k hE hH (ae_lifetime_pos_twoSeed hL hR hE) h𝓔' hW' hVL' hVR' hlaw
    hmem] with ω₀ hk hω₀
  obtain ⟨𝓕', W', VL', VR', B', hC, hag⟩ := hk hω₀
  refine ⟨⟨𝓕', W', VL', VR', B', hC, hag⟩, ?_⟩
  filter_upwards [htw 𝓕' W' VL' VR' B' _ hC.1, hag] with ω ⟨η, hη⟩ h1
  have e : (fun t => W t ω) = fun t => W' t ω := funext fun t => ((h1 t).1).symm
  exact ⟨η, e ▸ hη⟩

end TwoSeed

/-! ### The `P`-side named input and the two references -/

section Wrap

universe u

/-- **Named input: the pocket of a fixed two-seed word `SLE_κ(r_L; r_R)`, `P`-side form** (Aux. lemma 125's setting,
pp. 395–397, with Aux. lemma 122's evolution). On a standard Borel probability space with initial information `ℰ`
("the initial marked `A`"), a selection event `F ∈ ℰ` of positive probability and an `ℰ`-measurable record `E`:

* (E) the relative pocket driver `(W, V^L, V^R, B, ζ)` is an integrated evolution of the two-seed word in a filtration
  `𝓗` with `ℰ ≤ 𝓗 0` (`IsRandomWordEvolution` with the constant word: "the canonical integrated finite-force SDE in
  that filtration", p. 397);
* (S), (L) for the pocket field `H` in a filtration `𝓗'` with `ℰ ≤ 𝓗' 0` in which the driver is adapted: the
  conditional law of `H` off the relative hulls is the canonical two-seed Gaussian one, and the hulls are local sets
  (`HasSafeLaw`, `HasSafeMembers`: "The canonical law survives the exterior reveal", (ER1) with Aux. lemma 124);
* the pathwise property `Good` (a continuous trace; for Theorem R.7 a transient one) almost surely on `F` ("the erased
  counterflow is therefore a complete continuous traversal … with a continuous relative driver");
* on `F` the killed history is a Borel function of `(E, H)` ("the already established global field determination,
  followed by the measurable selected-pocket erasure", p. 398).

**Not proved in Lean.** -/
def PocketTwoSeedPSideStatement (κ rL rR : ℝ) (Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop) : Prop :=
  ∃ (Ω : Type u) (𝓔 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (F : Set Ω) (ε : Type u) (_ : MeasurableSpace ε) (E : Ω → ε)
    (H : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (𝓗 𝓗' : Filtration ℝ≥0 mΩ),
    IsRandomWordEvolution (mΩ := mΩ) κ P 𝓔 F (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun _ => rL)
      (fun _ => rR) 𝓗 W VL VR B ζ ∧
    P F ≠ 0 ∧ Measurable[𝓔] E ∧ Measurable H ∧ 𝓔 ≤ 𝓗' 0 ∧ AdaptedBefore 𝓗' ζ W ∧
    (∀ i, AdaptedBefore 𝓗' ζ (VL i)) ∧ (∀ j, AdaptedBefore 𝓗' ζ (VR j)) ∧
    HasSafeLaw κ (fun _ => rL) (fun _ => rR) P 𝓗' F ζ W VL VR H ∧ HasSafeMembers P 𝓗' F ζ W H ∧
    (∀ᵐ ω ∂P, ω ∈ F → Good (fun t => W t ω) (ζ ω)) ∧
    ∃ g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ F → killedHistory W VL VR ζ ω = g (E ω, H ω)

/-- **`PocketTwoSeedStatement` from its `P`-side form** (K2): the extra per-datum property is `Good` almost surely
under the conditional law. -/
theorem pocketTwoSeedStatement_of_pSide {κ rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR)
    {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hGood : ∀ w ζ, Good w ζ → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η)
    (h : PocketTwoSeedPSideStatement.{u} κ rL rR Good) :
    PocketTwoSeedStatement.{u} κ rL rR fun ν W ζ => ∀ᵐ ω ∂ν, Good (fun t => W t ω) (ζ ω) := by
  obtain ⟨Ω, 𝓔, mΩ, hSB, P, hP, F, ε, mε, E, H, W, VL, VR, B, ζ, 𝓗, 𝓗', hE, hF0, hEm, hH, h𝓔', hW', hVL', hVR',
    hlaw, hmem, hGoodP, hdet⟩ := h
  have h𝓔 : 𝓔 ≤ mΩ := hE.1.trans (𝓗.le 0)
  have hF : MeasurableSet[𝓔] F := hE.2.1
  have hGν : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), Good (fun t => W t ω) (ζ ω) := by
    filter_upwards [ae_ae_condExpKernel h𝓔 hGoodP, ae_ae_condExpKernel_mem (P := P) h𝓔 hF] with ω₀ h1 h2 hω₀
    filter_upwards [h1, h2 hω₀] with ω h3 h4 using h3 h4
  have hcpl := ae_isCondTwoSeedCoupling_of_pSide hL hR hE hH h𝓔' hW' hVL' hVR' hlaw hmem
    (hGν.mono fun ω₀ h hω₀ => (h hω₀).mono fun ω hω => hGood _ _ hω)
  refine ⟨Ω, 𝓔, mΩ, hSB, P, hP, F, ε, mε, E, H, W, VL, VR, ζ, h𝓔, hF, hF0, hEm, hH,
    Coupling.isMeasurableKilledDriving_of_adaptedBefore hW' hVL' hVR', ?_, hdet⟩
  filter_upwards [hcpl, hGν] with ω₀ h1 h2 hω₀ using ⟨h1 hω₀, h2 hω₀⟩

/-- **Lemma 7.25's determination reference (`href725`) from the `P`-side pockets** of the both-low two-seed words. -/
theorem lemma725DetReferenceStatement_of_pSide
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketTwoSeedPSideStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  lemma725DetReferenceStatement_of_pocket fun κ hκ rL rR hL hL' hR hR' =>
    ⟨_, pocketTwoSeedStatement_of_pSide hL hR (fun _ _ h => h) (h κ hκ rL rR hL hL' hR hR')⟩

/-- **Theorem R.7's reference (`hR7`) from the `P`-side pockets** of the mixed and outer two-seed words, with
transient traces. -/
theorem r7ReferenceStatement_of_pSide
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      PocketTwoSeedPSideStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
        (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    R7.R7ReferenceStatement.{u} :=
  r7ReferenceStatement_of_pocket fun κ hκ rL rR hL hR hmax =>
    pocketTwoSeedStatement_of_pSide hL hR (fun _ _ ⟨η, h1, _⟩ => ⟨η, h1⟩) (h κ hκ rL rR hL hR hmax)

/-- **`PocketTwoSeedStatement` from its `P`-side form without a pocket trace**, when every two-seed evolution of the
word (on any probability space in `Type u`) has a trace. -/
theorem pocketTwoSeedStatement_of_pSide_of_trace {κ rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR)
    (htw : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) ν 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂ν, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (h : PocketTwoSeedPSideStatement.{u} κ rL rR Good) :
    PocketTwoSeedStatement.{u} κ rL rR fun ν W ζ => ∀ᵐ ω ∂ν, Good (fun t => W t ω) (ζ ω) := by
  obtain ⟨Ω, 𝓔, mΩ, hSB, P, hP, F, ε, mε, E, H, W, VL, VR, B, ζ, 𝓗, 𝓗', hE, hF0, hEm, hH, h𝓔', hW', hVL', hVR',
    hlaw, hmem, hGoodP, hdet⟩ := h
  have h𝓔 : 𝓔 ≤ mΩ := hE.1.trans (𝓗.le 0)
  have hF : MeasurableSet[𝓔] F := hE.2.1
  have hGν : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), Good (fun t => W t ω) (ζ ω) := by
    filter_upwards [ae_ae_condExpKernel h𝓔 hGoodP, ae_ae_condExpKernel_mem (P := P) h𝓔 hF] with ω₀ h1 h2 hω₀
    filter_upwards [h1, h2 hω₀] with ω h3 h4 using h3 h4
  have hcpl := ae_isCondTwoSeedCoupling_of_pSide_of_trace hL hR
    (fun 𝓕 W' VL' VR' B' ν _ hEv => htw ν 𝓕 W' VL' VR' B' ζ hEv) hE hH h𝓔' hW' hVL' hVR' hlaw hmem
  refine ⟨Ω, 𝓔, mΩ, hSB, P, hP, F, ε, mε, E, H, W, VL, VR, ζ, h𝓔, hF, hF0, hEm, hH,
    Coupling.isMeasurableKilledDriving_of_adaptedBefore hW' hVL' hVR', ?_, hdet⟩
  filter_upwards [hcpl, hGν] with ω₀ h1 h2 hω₀ using ⟨h1 hω₀, h2 hω₀⟩

/-- **Lemma 7.25's determination reference (`href725`) from the `P`-side pockets without a pocket trace**: the trace
under the conditional laws is Lemma 7.25's finite-time continuity (`LP.Lemma725TraceStatement`, which the driver-level
reference already gives: `Aux126.lemma725TraceStatement_of_driverReference`). -/
theorem lemma725DetReferenceStatement_of_pSide_of_trace (h725t : LP.Lemma725TraceStatement.{u})
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketTwoSeedPSideStatement.{u} κ rL rR fun _ _ => True) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  lemma725DetReferenceStatement_of_pocket fun κ hκ rL rR hL hL' hR hR' =>
    ⟨_, pocketTwoSeedStatement_of_pSide_of_trace hL hR
      (fun ν _ 𝓕 W VL VR B ζ hEv => h725t κ hκ rL rR hL hL' hR hR' ν 𝓕 W VL VR B ζ hEv)
      (h κ hκ rL rR hL hL' hR hR')⟩

/-! ### Lemma 7.25's pocket with its distant marks: Aux. lemma 127 at the level of the field -/

/-- **Named input: the pocket of Lemma 7.25 with its actual distant marks, `P`-side form** (Lemma 7.25's proof,
pp. 413–414: the pockets of Aux. lemma 130 on a positive-probability initial event `F`, the word of Aux. lemmas
119–121, "the remote marks are removed only in that proved local transfer; they were not discarded from `Q_Θ`"). As
`Lemma725Ref.PocketWordEvolution` (a word shape with deterministic weights, seed weights `r_L, r_R` at the first marks,
an `ℰ`-measurable random word `Θ` which on `F` is ordered with both seeds at `0` and its other marks strictly separated
from `0`; the relative driver an integrated evolution of `Θ` with a trace before its lifetime on `F`), together with
the field data of Aux. lemma 125: the pocket field `H` with (S), (L) in a filtration `𝓗'` with `ℰ ≤ 𝓗' 0` in which
the driver is adapted, and on `F` the killed relative history a Borel function of `(E, H)` for an `ℰ`-measurable
record `E` with values in a standard Borel space. **Not proved in Lean.** -/
def PocketWordFieldStatement (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), ρL 0 = rL ∧ ρR 0 = rR ∧
    ∃ (Ω : Type u) (𝓔 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (F : Set Ω) (ΘL : Ω → Fin (nL + 1) → ℝ) (ΘR : Ω → Fin (nR + 1) → ℝ),
      P F ≠ 0 ∧
      (∀ ω ∈ F, IsOrderedForceWord (ΘL ω) (ΘR ω) ∧ ΘL ω 0 = 0 ∧ ΘR ω 0 = 0 ∧
        (∀ i, i ≠ 0 → ΘL ω i < 0) ∧ (∀ i, i ≠ 0 → 0 < ΘR ω i)) ∧
      ∃ (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε) (E : Ω → ε)
        (H : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (𝓗 𝓗' : Filtration ℝ≥0 mΩ),
        IsRandomWordEvolution (mΩ := mΩ) κ P 𝓔 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ ∧
        (∀ᵐ ω ∂P, ω ∈ F → ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
          ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η) ∧
        Measurable[𝓔] E ∧ Measurable H ∧ 𝓔 ≤ 𝓗' 0 ∧ AdaptedBefore 𝓗' ζ W ∧
        (∀ i, AdaptedBefore 𝓗' ζ (VL i)) ∧ (∀ j, AdaptedBefore 𝓗' ζ (VR j)) ∧
        HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR H ∧ HasSafeMembers P 𝓗' F ζ W H ∧
        ∃ g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1), Measurable g ∧
          ∀ᵐ ω ∂P, ω ∈ F → killedHistory W VL VR ζ ω = g (E ω, H ω)

/-- **Aux. lemma 127 at the level of the field** (p. 403: "Choose one deterministic `θ_*` outside that null set …
Therefore `Q_{θ_*}` satisfies the hypotheses of Aux. lemma 126"): the `P`-side pocket of Lemma 7.25 gives the
hypothesis of Aux. lemma 126 (`Aux126Reference`) for the seed weights. At almost every `ω₀ ∈ F` the conditional law
given `ℰ` carries an optional hull coupling of the word `Θ ω₀` (K2), the trace survives, and the record `E` is constant
(`ae_ae_condExpKernel_eq_self`), so the killed history is `g (E ω₀, H)`: a Borel function of the field. -/
theorem aux126Reference_of_pocketWordField {κ rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR)
    (h : PocketWordFieldStatement.{u} κ rL rR) : Aux126Reference.{u} κ rL rR := by
  obtain ⟨nL, nR, ρL, ρR, hρL, hρR, Ω, 𝓔, mΩ, hSB, P, hP, F, ΘL, ΘR, hF0, hΘ, ε, mε, hSBε, E, H, W, VL, VR, B,
    ζ, 𝓗, 𝓗', hE, htr, hEm, hH, h𝓔', hW', hVL', hVR', hlaw, hmem, g, hg, hdet⟩ := h
  have h𝓔 : 𝓔 ≤ mΩ := hE.1.trans (𝓗.le 0)
  have hF : MeasurableSet[𝓔] F := hE.2.1
  have hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω := by
    obtain ⟨-, -, -, -, -, -, -, -, hpath⟩ := id hE
    filter_upwards [hpath] with ω hp hω
    obtain ⟨-, hL0, hR0, hLn, hRp⟩ := hΘ ω hω
    have hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 (ΘL ω) (ΘR ω) :=
      (Sec2.not_thr_iff_seedSum _ _ ρL ρR).2
        ⟨by rw [Aux126.seedSum_eq hL0 fun i hi => (hLn i hi).ne, hρL]; exact hL,
          by rw [Aux126.seedSum_eq hR0 fun j hj => (hRp j hj).ne', hρR]; exact hR⟩
    -- the zero-lifetime clause of `IsIntegratedSLEPath`
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hp hω
    exact pos_iff_ne_zero.2 fun h0 => hthr (h19 h0)
  have hk := ae_isOptionalHullCoupling_k hE hH hζ0 h𝓔' hW' hVL' hVR' hlaw hmem
  have hmemF := ae_ae_condExpKernel_mem (P := P) h𝓔 hF
  have htrν : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η := by
    filter_upwards [ae_ae_condExpKernel h𝓔 htr, hmemF] with ω₀ h1 h2 hω₀
    filter_upwards [h1, h2 hω₀] with ω h3 h4 using h3 h4
  have hdetν : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀),
      killedHistory W VL VR ζ ω = g (E ω, H ω) := by
    filter_upwards [ae_ae_condExpKernel h𝓔 hdet, hmemF] with ω₀ h1 h2 hω₀
    filter_upwards [h1, h2 hω₀] with ω h3 h4 using h3 h4
  have hEν := ae_ae_condExpKernel_eq_self (P := P) h𝓔 hEm
  obtain ⟨ω₀, hω₀F, hk0, htr0, hdet0, hE0⟩ := exists_mem_of_ae hF0
    ((hk.and (htrν.and (hdetν.and hEν))).mono fun ω h hω =>
      And.intro (h.1 hω) (And.intro (h.2.1 hω) (And.intro (h.2.2.1 hω) h.2.2.2)))
  obtain ⟨𝓕', W', VL', VR', B', hC, hag⟩ := hk0
  obtain ⟨hord, hL0, hR0, hLn, hRp⟩ := hΘ ω₀ hω₀F
  have hdetW' : IsAEDeterminedBy (condExpKernel P 𝓔 ω₀) H (killedHistory W' VL' VR' ζ) := by
    refine ⟨fun x => g (E ω₀, x), hg.comp (measurable_const.prodMk measurable_id), ?_⟩
    filter_upwards [hdet0, hE0, hag] with ω h1 h2 h3
    rw [killedHistory_eq_of_forall h3, h1, h2]
  refine ⟨nL, nR, ΘL ω₀, ΘR ω₀, ρL, ρR, hord, hL0, hR0, hLn, hRp, hρL, hρR, Ω, mΩ, condExpKernel P 𝓔 ω₀,
    inferInstance, 𝓕', W', VL', VR', B', ζ, H, hC, ?_,
    Prop73Ref.isFieldDeterminedHistory_of_isAEDeterminedBy hdetW'
      (IsIntegratedSLEEvolution.ae_continuousOn_driving hC.1)⟩
  filter_upwards [htr0, hag] with ω h1 h2 T hT
  obtain ⟨η, hη⟩ := h1 T hT
  have e : (fun t => W' t ω) = fun t => W t ω := funext fun t => (h2 t).1
  exact ⟨η, e ▸ hη⟩

/-- **Lemma 7.25's reference at the level of the field** (`Lemma725ReferenceStatement`, the hypothesis of Aux.
lemma 126 for every both-low pair) from the `P`-side pockets with their distant marks. -/
theorem lemma725ReferenceStatement_of_pocketWordField
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketWordFieldStatement.{u} κ rL rR) :
    Lemma725ReferenceStatement.{u} := fun κ hκ rL rR hL hL' hR hR' =>
  aux126Reference_of_pocketWordField hL hR (h κ hκ rL rR hL hL' hR hR')

end Wrap

end Lemma725RefK2

end Sec7

end InteractingSLE
