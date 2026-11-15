/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71Joint
import InteractingSLE.Spec.Sec7.Prop73Ref
import InteractingSLE.Spec.Sec7.Lemma71DUsual
import InteractingSLE.Spec.Sec7.TwoForceMainDetermine

/-!
# Lemma 7.2: the embedded pair on one space, and Proposition 7.3's reference

Packet PROVE-LEMMA72. Specification §7.1 (`source/spec/p193-240.md` L540–L642, pp. 221–227): Lemma 7.1 ("The joint
pair with `h_ψ` has the original coupling specification […] its full joint law is independent of the two outer
curves") and Lemma 7.2 ("In the embedded coupling constructed above, `h_ψ` almost surely determines `η_ψ`").

PROVE-PROP73R reduced Proposition 7.3's reference to `Prop73Ref.EmbeddedPairStatement`: the embedded pair as an
**optional hull coupling**, with the original field `h` and an exterior record `Q` satisfying Lemma 7.2's three
ingredients. This file proves `EmbeddedPairStatement` from `Lemma71JointStatement`, which asks only for data in the
form the landed pocket statements produce:

* the pocket coupling **in chart form** on one probability space: exactly the clauses of
  `Lemma71C.Lemma71PocketChartStatement` (the mapped middle-curve segment `γ`, its driver `W` up to the terminal
  capacity time `T`, the measurable field `h`, the `𝓖₀`-measurable pocket chart `c`, and the coupling clause of the
  two-seed word with the (CPF2) weights in the pocket);
* the pulled-back field `h_ψ` (`IsChartTransport (c ω) 1 a k`: `h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′`);
* **the locality** of the hulls of `W` for `h_ψ` at the stopping times of `𝓖` before `T` (p. 225: "the history-locality
  statement of Lemma 6.2 applies to the revealed outer curves and the middle prefix […] the optional history marking of
  the original coupling supplies the required history locality");
* the exterior record `Q = (A, h')` with Lemma 7.2's ingredients for the killed driving history of `(W, T)`:
  (i) `h` is determined by `(Q, h_ψ)` (p. 226–227, thin-support removal, Aux. lemma 12); (ii) the history is
  determined by `(h, Q)` (p. 227, the non-boundary field determination of the middle flow line and the pocket chart from
  the outer curves); (iii) `(history, h_ψ)` is independent of `Q` (p. 227, the component-pair factorization, Aux. lemma
  46, Lemma 7.1's joint law).

Everything else of "the original coupling specification" is proved
(`Lemma71J.exists_isOptionalHullCoupling_of_pocketChart`): the terminal capacity is infinite, the global driver
with its geometric force points and the Brownian motion of the martingale characterization is an integrated
two-seed evolution, `h_ψ − 𝔥₀` is a zero-boundary GFF (the clause at
`τ = 0`), and the conditional-law conjunct holds at every stopping time of the frozen driving filtration.

## Main results

* `Lemma71JointStatement` (**named input**);
* **`embeddedPairStatement_of_joint`**: `Lemma71JointStatement → Prop73Ref.EmbeddedPairStatement`;
* `lemma71PocketChartStatement_of_joint`: the named input contains the landed chart-form pocket statement;
* wiring: `prop73ReferenceStatement_of_joint`, `prop73DeterminationStatement_of_joint`;
* ingredient (ii) from a field-determined filtration: `isAEDeterminedBy_of_measurable_sup_nullSets` (Doob–Dynkin up to
  null sets), **`isAEDeterminedBy_killedHistory_of_le`** (if every `𝓖_t ⊆ σ(h) ∨ 𝒩`, the killed driving history of
  `(W, T)` is a Borel function of `h`), `isAEDeterminedBy_prod_of_isAEDeterminedBy` (then also of `(h, Q)`).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma72

open LawUnique

/-! ### Lemma 7.2's ingredient (ii) from field-determined filtrations -/

section History

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Doob–Dynkin up to null sets.** A variable with standard Borel values that is measurable for `σ(H) ∨ 𝒩` is almost
surely a Borel function of `H` (null sets do not change conditional expectations). -/
theorem isAEDeterminedBy_of_measurable_sup_nullSets {γ β : Type*} [mγ : MeasurableSpace γ] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β] {H : Ω → γ} (hH : Measurable H) {Y : Ω → β}
    (hY : Measurable[MeasurableSpace.comap H mγ ⊔ Ito.nullSets P] Y) : Sec7.IsAEDeterminedBy P H Y := by
  obtain ⟨c, d, hc, hd, hcb, hdc⟩ := Sec7.exists_bounded_code (β := β)
  rw [Sec7.isAEDeterminedBy_iff_code hc hd hdc]
  refine Sec7.isAEDeterminedBy_of_ae_eq_condExp ?_
  set 𝓐 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 (MeasurableSpace.comap H mγ) hH.comap_le with h𝓐
  have hZm : StronglyMeasurable[Ito.nullAugmented 𝓐 P 0] fun ω => c (Y ω) := (hc.comp hY).stronglyMeasurable
  have hZi : Integrable (fun ω => c (Y ω)) P :=
    Integrable.of_bound ((hZm.mono ((Ito.nullAugmented 𝓐 P).le 0)).aestronglyMeasurable) 2
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb (Y ω))
  have h1 := Lemma71D.condExp_nullAugmented_ae_eq (𝓐 := 𝓐) hZi 0
  rw [condExp_of_stronglyMeasurable ((Ito.nullAugmented 𝓐 P).le 0) hZm hZi] at h1
  exact h1

omit [IsProbabilityMeasure P] in
/-- A variable determined by `H` is determined by `(H, Q)`. -/
theorem isAEDeterminedBy_prod_of_isAEDeterminedBy {γ δ β : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSpace β] {H : Ω → γ} {Q : Ω → δ} {Y : Ω → β} (hY : Sec7.IsAEDeterminedBy P H Y) :
    Sec7.IsAEDeterminedBy P (fun ω => (H ω, Q ω)) Y := by
  obtain ⟨g, hg, hYg⟩ := hY
  exact ⟨fun p => g p.1, hg.comp measurable_fst, hYg⟩

/-- **The killed driving history is determined by the field when the filtration is** (Lemma 7.2's ingredient (ii),
p. 227: "The outer curves determine `C`, `ψ`, and its inherited argument branch […] The already proved non-boundary
field-determination theorem recovers `γ` from `h`"). If every `𝓖_t` lies in the completion `σ(H) ∨ 𝒩` and the driver is
adapted and continuous before `T`, the killed driving history of `W` with its geometric force points is an almost
sure Borel function of `H`. -/
theorem isAEDeterminedBy_killedHistory_of_le {γ : Type*} [mγ : MeasurableSpace γ] {H : Ω → γ} (hH : Measurable H)
    {𝓖 : Filtration ℝ≥0 mΩ} (hle : ∀ t, 𝓖 t ≤ MeasurableSpace.comap H mγ ⊔ Ito.nullSets P)
    {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞} (hWa : AdaptedBefore 𝓖 T W)
    (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) :
    Sec7.IsAEDeterminedBy P H
      (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) := by
  let 𝓖' : @Filtration Ω ℝ≥0 _ (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) :=
    ⟨fun t => 𝓖 t, fun _ _ hst => 𝓖.mono hst, hle⟩
  have hWa' : @AdaptedBefore Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 𝓖' T W := hWa
  have hL : ∀ i, @AdaptedBefore Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 𝓖' T
      (MartChar.geomL W LP.twoSeedXL i) := fun i =>
    @Lemma71C.adaptedBefore_geomL Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 1 T W hc 𝓖' hWa' LP.twoSeedXL i
  have hR : ∀ i, @AdaptedBefore Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 𝓖' T
      (MartChar.geomR W LP.twoSeedXR i) := fun i =>
    @Lemma71C.adaptedBefore_geomR Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 1 T W hc 𝓖' hWa' LP.twoSeedXR i
  have hX := @Coupling.isMeasurableKilledDriving_of_adaptedBefore Ω
    (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 𝓖' 1 1 W
    (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T hWa' hL hR
  have hY := @measurable_killedHistory Ω (MeasurableSpace.comap H mγ ⊔ Ito.nullSets P) 1 1 W _ _ T hX
  exact isAEDeterminedBy_of_measurable_sup_nullSets hH hY

end History

/-! ### The named input and `EmbeddedPairStatement` -/

/-- **Named input: Lemma 7.1's embedded pair on one space, with Lemma 7.2's ingredients** (specification §7.1,
pp. 221–227). For `0 < κ < 4` and angles `θ₁ < 0 < θ₂` there is one probability space carrying
* the clauses of `Lemma71C.Lemma71PocketChartStatement`: a right-continuous filtration `𝓖` with the null sets at time
  `0`, the mapped segment `γ` (almost surely a continuous simple path in `ℍ̄` from `0` to `∞` whose real boundary times
  have empty interior), its driver `W` up to the terminal capacity time `T` (`W₀ = 0`, continuous and adapted before
  `T`, generating every filled prefix of `γ`), the measurable original field `h`, the `𝓖₀`-measurable conformal pocket
  chart `c` with lifts continuous on the pocket, and the coupling clause of the two-seed word with the (CPF2) weights in
  the pocket chart, killed at `T`;
* the pulled-back field `h_ψ`, the chart transport of `h` (rule (1.4), `σ = 1`, constants `a`, `k`);
* the locality of the hulls `K_τ` of `W` for `h_ψ` at every stopping time `τ < T` of `𝓖`;
* an exterior record `Q` (`(A, h')`: the two outer curves and the field off `C̄`) with (i) `h` determined by
  `(Q, h_ψ)`, (ii) the killed driving history of `(W, T)` determined by `(h, Q)`, (iii) `(history, h_ψ)` independent
  of `Q`. -/
def Lemma71JointStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (γ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ)
      (T : Ω → ℝ≥0∞) (h hψ : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ)
      (δ : Type u) (_ : MeasurableSpace δ) (Q : Ω → δ),
      (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
      (∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
        γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) ∧
      AdaptedBefore 𝓖 T W ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
        fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
        (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
        T c a k h ∧
      (∀ ω, IsChartTransport (c ω) 1 a k (h ω) (hψ ω)) ∧
      (∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hψ P) ∧
      Measurable Q ∧ Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) h ∧
      Sec7.IsAEDeterminedBy P (fun ω => (h ω, Q ω))
        (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) ∧
      IndepFun (fun ω => (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T ω,
        hψ ω)) Q P

/-- **`Prop73Ref.EmbeddedPairStatement` from the embedded pair on one space.** The chart-form pocket coupling with the
locality of its hulls is an optional hull coupling of `h_ψ` with the global driver `W'`
(`Lemma71J.exists_isOptionalHullCoupling_of_pocketChart`); the killed driving histories of `W'` and of `(W, T)` agree
almost surely, so Lemma 7.2's ingredients (ii)–(iii) pass to the coupling. Conditional helper. -/
theorem embeddedPairStatement_of_joint (hj : Lemma71JointStatement.{u}) : Prop73Ref.EmbeddedPairStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, h, hψ, c, a, k, δ, mδ, Q, hnull, hγ, hW0, hc, hWa, hK, hh, hcc,
    hdom, hfwd, hliftm, hliftc, hcf, ht, hloc, hQ, hrec, hdet, hind⟩ := hj κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  have hψe : hψ = fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  subst hψe
  obtain ⟨W', B, ζ, hC, -, hhist⟩ := Lemma71J.exists_isOptionalHullCoupling_of_pocketChart hκ hκ4 hθ₁ hθ₂ hnull
    hγ hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcf hloc
  refine ⟨Ω, mΩ, P, hP, 𝓖, W', MartChar.geomL W' LP.twoSeedXL, MartChar.geomR W' LP.twoSeedXR, B, ζ, _, h, δ, mδ,
    Q, hC, hQ, hrec, hdet.congr_ae hhist.symm, hind.congr ?_ (ae_eq_refl Q)⟩
  filter_upwards [hhist] with ω hω
  rw [hω]

/-- The named input contains the landed chart-form pocket statement (forget `h_ψ`, the locality and `Q`). -/
theorem lemma71PocketChartStatement_of_joint (hj : Lemma71JointStatement.{u}) :
    Lemma71C.Lemma71PocketChartStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, h, -, c, a, k, -, -, -, hnull, hγ, hW0, hc, hWa, hK, hh, hcc,
    hdom, hfwd, hliftm, hliftc, hcf, -⟩ := hj κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  exact ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, h, c, a, k, hnull, hγ, hW0, hc, hWa, hK, hh, hcc, hdom, hfwd, hliftm,
    hliftc, hcf⟩

/-- **Proposition 7.3's reference coupling** (`Prop73Det.Prop73ReferenceStatement`) from the embedded pair on one
space: `embeddedPairStatement_of_joint` and Lemma 7.2 (`Prop73Ref.prop73ReferenceStatement_of_embeddedPair`). -/
theorem prop73ReferenceStatement_of_joint (hj : Lemma71JointStatement.{u}) : Prop73Det.Prop73ReferenceStatement.{u} :=
  Prop73Ref.prop73ReferenceStatement_of_embeddedPair (embeddedPairStatement_of_joint hj)

/-- **Proposition 7.3's determination** (`Determination.Prop73DeterminationStatement`) from the embedded pair on one
space, Aux. lemma 50 at the integer times for the boundary-hitting pairs, and the trace part of Proposition 7.3. -/
theorem prop73DeterminationStatement_of_joint (h73t : Sec7.Prop73TraceStatement.{u})
    (hj : Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR) :
    Determination.Prop73DeterminationStatement.{u} :=
  Prop73Ref.prop73DeterminationStatement_of_embeddedPair h73t (embeddedPairStatement_of_joint hj) h50

end InteractingSLE.Sec7.Lemma72
