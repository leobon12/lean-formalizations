/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefSafeChart
import InteractingSLE.Spec.Sec7.Lemma725RefFull

/-!
# Theorem 1.2's inputs `href725` and `hR7` from the pocket's field-level data

Packet PROVE-LEMMA725REF3. Lemma 7.25's proof (`source/spec/p385-432.md` L489–L515, pp. 413–414) and Theorem R.7's
references. With (S) and (L) proved (`Lemma725RefSafeChart`), the named inputs of the two references reduce to the
pocket's field-level data on its ambient probability space:

* `PocketChartFieldStatement κ r_L r_R` (**named input**): the hypotheses of `pocketWordFieldStatement_of_chart` — the
  pocket of Lemma 7.25 on a walls-event of positive probability, its traversal and word, the pocket chart, the field,
  the physical kernel and mean identification (the inputs of the landed chain for (E)), the marked union law of the
  canonical set `ℍ ∖ activeDom` (for (L)), and the determination `hdet` (Proposition 5.13 and the pocket erasure);
* **`lemma725DetReferenceStatement_of_pocketChartField`**: `href725` from `PocketChartFieldStatement` for every both-low
  pair (through `Lemma725RefFull.lemma725DetReferenceStatement_of_pocketWordField'`);
* `PocketChartTwoSeedStatement κ r_L r_R Good` (**named input**): the hypotheses of
  `pocketTwoSeedPSideStatement_of_chart` for the constant two-seed word;
* **`r7ReferenceStatement_of_pocketChartTwoSeed`**: `hR7` from `PocketChartTwoSeedStatement` on the part of the R.7
  range inside Aux. lemma 122's range (both seed weights `< κ − 6`), and from `PocketTwoSeedPSideStatement` itself on
  the rest (a seed weight `≥ κ − 6`, where Aux. lemma 122's phase selection does not apply and Theorem R.7's own exact
  phase selection is needed).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 PhaseSel PocketCoupling LocalSets Coupling MartChar
  PocketTraversal Lemma71C LawUnique PocketStop WholeField

universe u

/-- **Named input: Lemma 7.25's pocket with its field-level data** (the hypotheses of
`pocketWordFieldStatement_of_chart`; Aux. lemmas 119–125 and 130, Lemma 7.25's proof). A standard Borel probability
space with the walls' σ-algebra `𝓦`, a walls-event `A` of positive probability, the erased traversal `γ` and the word
`(ρL; ρR)` with seed weights `r_L, r_R` and all side partial sums `> −2` at the marks `xL`, `xR`; a pocket chart `c`
measurable for the walls with a continuous harmonic lift; the ambient field `h` with `h − u₀` a zero-boundary GFF for a
harmonic `u₀`; the physical kernel and the mean identification; the marked union law of `ℍ ∖ activeDom`; and the
determination of the killed relative history by a walls' record `E` and the pocket field. **Not proved in Lean.** -/
def PocketChartFieldStatement (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), ρL 0 = rL ∧ ρR 0 = rR ∧
    (∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i) ∧
    (∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i) ∧
    ∃ (Ω : Type u) (𝓦 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ)
      (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (hc : ∀ ω, (c ω).IsConformal) (a k : ℝ)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (𝓜 : ℝ≥0 → MeasurableSpace Ω)
      (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε)
      (E : Ω → ε) (g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)),
      𝓦 ≤ mΩ ∧ MeasurableSet[𝓦] A ∧ 0 < P A ∧ (∀ ω ∈ A, IsDrivenCurve (γ ω)) ∧
      (∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) ∧
      (∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) ∧
      Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω) ∧
      Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω) ∧
      (∀ ω ∈ A, xL ω 0 = 0) ∧ (∀ ω ∈ A, xR ω 0 = 0) ∧ (∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) ∧
      (∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ) ∧ (∀ ω ∈ A, Antitone (xL ω)) ∧ (∀ ω ∈ A, Monotone (xR ω)) ∧
      (∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧ (∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) ∧
      Measurable h ∧ InnerProductSpace.HarmonicOnNhd u₀ H ∧
      IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P ∧
      PocketKernel 𝓦 P A γ c h 𝓜 M ∧ PocketMeanIdent κ ρL ρR P A γ xL xR c a k M ∧
      (∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s)) ∧
      (∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P) ∧
      Measurable[𝓦] E ∧ Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ A → killedHistory (fun t ω => segDriver (γ ω) t)
        (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR)
        (fun ω => capLife (γ ω)) ω = g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω))

/-- **`PocketWordFieldStatement` from the pocket's field-level data** (`pocketWordFieldStatement_of_chart`). -/
theorem pocketWordFieldStatement_of_pocketChartField {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) (h : PocketChartFieldStatement.{u} κ rL rR) :
    Lemma725RefK2.PocketWordFieldStatement.{u} κ rL rR := by
  obtain ⟨nL, nR, ρL, ρR, hρL, hρR, hsL, hsR, Ω, 𝓦, mΩ, hSB, P, hP, A, γ, xL, xR, c, hc, a, k, hf, u₀, 𝓜, M, ε,
    mε, hSBε, E, g, h𝓦, hA, hPA, hγ, hγm, hunb, hxLm, hxRm, hseedL, hseedR, hxLd, hxRd, hxLi, hxRi, hdom, hfwd,
    hliftm, hliftc, hlift, hhm, hu₀, hh0, hker, hmean, hKm, hKloc, hEm, hg, hdet⟩ := h
  exact pocketWordFieldStatement_of_chart hκ hLd hRd hρL hρR hsL hsR h𝓦 hA hPA hγ hγm hunb hxLm hxRm hseedL
    hseedR hxLd hxRd hxLi hxRi hc hdom hfwd hliftm hliftc hlift a k hhm hu₀ hh0 hker hmean hKm hKloc hEm hg hdet

/-- **Lemma 7.25's determination reference (`href725`) from the pocket's field-level data** for every both-low pair:
`pocketWordFieldStatement_of_pocketChartField` and `Lemma725RefFull.lemma725DetReferenceStatement_of_pocketWordField'`
(Aux. lemmas 126–127). -/
theorem lemma725DetReferenceStatement_of_pocketChartField
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketChartFieldStatement.{u} κ rL rR) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  Lemma725RefFull.lemma725DetReferenceStatement_of_pocketWordField' fun κ hκ rL rR hL hLd hR hRd =>
    pocketWordFieldStatement_of_pocketChartField hκ hLd hRd (h κ hκ rL rR hL hLd hR hRd)

/-- **Named input: a two-seed pocket with its field-level data** (the hypotheses of
`pocketTwoSeedPSideStatement_of_chart` for the constant two-seed word `SLE_κ(r_L; r_R)`, with the pathwise property
`Good` of the relative driver with infinite lifetime). **Not proved in Lean.** -/
def PocketChartTwoSeedStatement (κ rL rR : ℝ) (Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop) : Prop :=
  ∃ (Ω : Type u) (𝓦 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (A : Set Ω) (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (hc : ∀ ω, (c ω).IsConformal) (a k : ℝ)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (𝓜 : ℝ≥0 → MeasurableSpace Ω)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (ε : Type u) (_ : MeasurableSpace ε) (E : Ω → ε)
    (g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1),
    𝓦 ≤ mΩ ∧ MeasurableSet[𝓦] A ∧ 0 < P A ∧ (∀ ω ∈ A, IsDrivenCurve (γ ω)) ∧
    (∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) ∧
    (∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) ∧
    (∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom}) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
    (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧ (∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) ∧
    Measurable h ∧ InnerProductSpace.HarmonicOnNhd u₀ H ∧
    IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P ∧
    PocketKernel 𝓦 P A γ c h 𝓜 M ∧
    PocketMeanIdent κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ (fun _ => LP.twoSeedXL)
      (fun _ => LP.twoSeedXR) c a k M ∧
    (∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s)) ∧
    (∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P) ∧
    (∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤) ∧
    Measurable[𝓦] E ∧ Measurable g ∧
    ∀ᵐ ω ∂P, ω ∈ A → killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR)
      (fun ω => capLife (γ ω)) ω = g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω))

/-- **`PocketTwoSeedPSideStatement` from the two-seed pocket's field-level data**
(`pocketTwoSeedPSideStatement_of_chart`), for seed weights in Aux. lemma 122's range `(−2, κ − 6)`. -/
theorem pocketTwoSeedPSideStatement_of_pocketChartTwoSeed {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL)
    (hLd : rL < κ - 6) (hR : -2 < rR) (hRd : rR < κ - 6) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h : PocketChartTwoSeedStatement.{u} κ rL rR Good) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  obtain ⟨Ω, 𝓦, mΩ, hSB, P, hP, A, γ, c, hc, a, k, hf, u₀, 𝓜, M, ε, mε, E, g, h𝓦, hA, hPA, hγ, hγm, hunb, hdom,
    hfwd, hliftm, hliftc, hlift, hhm, hu₀, hh0, hker, hmean, hKm, hKloc, hGood, hEm, hg, hdet⟩ := h
  exact pocketTwoSeedPSideStatement_of_chart hκ hL hLd hR hRd h𝓦 hA hPA hγ hγm hunb hc hdom hfwd hliftm hliftc hlift
    a k hhm hu₀ hh0 hker hmean hKm hKloc hGood hEm hg hdet

/-- **Theorem R.7's reference (`hR7`), split along Aux. lemma 122's range**: on the mixed and outer pairs with both seed
weights `< κ − 6`, from the two-seed pockets' field-level data (`PocketChartTwoSeedStatement`); on the pairs with a seed
weight `≥ κ − 6` (outside Aux. lemma 122's range, where Theorem R.7's exact phase selection is needed), from the
`P`-side pockets themselves (`Lemma725RefK2.PocketTwoSeedPSideStatement`). -/
theorem r7ReferenceStatement_of_pocketChartTwoSeed
    (hlow : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR → rL < κ - 6 →
      rR < κ - 6 → PocketChartTwoSeedStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
        (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop))
    (hhigh : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ - 6 ≤ max rL rR →
      Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
        (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    R7.R7ReferenceStatement.{u} :=
  Lemma725RefK2.r7ReferenceStatement_of_pSide fun κ hκ rL rR hL hR hmax => by
    by_cases hh : κ - 6 ≤ max rL rR
    · exact hhigh κ hκ rL rR hL hR hh
    · have h' := lt_of_not_ge hh
      exact pocketTwoSeedPSideStatement_of_pocketChartTwoSeed hκ hL (lt_of_le_of_lt (le_max_left _ _) h') hR
        (lt_of_le_of_lt (le_max_right _ _) h') (hlow κ hκ rL rR hL hR hmax (lt_of_le_of_lt (le_max_left _ _) h')
          (lt_of_le_of_lt (le_max_right _ _) h'))

end InteractingSLE.Sec7.Lemma725RefSafe
