/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Kernel

/-!
# Proposition 7.3's reference coupling: Lemma 7.2 and the range of (CPF2)

Packet PROVE-PROP73R. Specification §7.1, Lemmas 7.1–7.2 and the remark after them (`source/spec/p193-240.md`
L576–L642, pp. 223–227). `Prop73Det.Prop73ReferenceStatement` asks, for `0 < κ < 4` and seed weights
`ρ^L, ρ^R > −2`, for one coupling of the two-seed word with the original optional hull specification whose killed
driving history is a Borel function of its field. The source obtains it from the embedded construction:

* **Lemma 7.1** (p. 223): the mapped middle-curve segment `η_ψ` and the pulled-back field `h_ψ` form a coupling of
  `SLE_κ(ρ^L; ρ^R)` with the weights (CPF2) satisfying "the original coupling specification", and "its full joint law
  is independent of the two outer curves";
* **Lemma 7.2** (pp. 226–227): with `Q = (A, h')` (the outer curves and the field off `C̄`), "the pair `(Q, h_ψ)`
  determines `h` off `∂C`" and, by thin-support removal (Aux. lemma 12), everywhere; "the already proved
  non-boundary field-determination theorem recovers `γ` from `h`, and hence recovers `η_ψ` from `(Q, h_ψ)`"; "the
  component-pair factorization […] says that `(η_ψ, h_ψ)` is independent of `Q`"; then (CPF3)
  `F(η_ψ) = E[F(η_ψ) | Q, h_ψ] = E[F(η_ψ) | h_ψ]`, so the curve is a measurable function of `h_ψ`;
* **the remark after Lemma 7.2** (p. 227): "As `θ₁ < 0 < θ₂` vary, (CPF2) ranges over every pair `ρ^L, ρ^R > −2`,
  because `χ > 0` for `0 < κ < 4`. The embedded construction therefore covers every admissible two-seed pair."

## What is proved here

* `exists_cpf2_angles`: the range of (CPF2) (the remark after Lemma 7.2);
* `pathsOfHistory`, `isFieldDeterminedHistory_of_isAEDeterminedBy`: a killed history determined (on the dyadic
  times) by the field, with a driver continuous before the lifetime, is field-determined in the sense of
  `LP.IsFieldDeterminedHistory` (the paths are dyadic limits from below);
* **`isFieldDeterminedHistory_of_cpf3`** — **Lemma 7.2** at the level of couplings: from the recovery of `h` from
  `(Q, h_ψ)`, the determination of the history by `(h, Q)` and the independence of `(history, h_ψ)` from `Q`
  (CPF3, `Sec7.IsAEDeterminedBy.of_indepFun`);
* **`prop73ReferenceStatement_of_embeddedPair`**: `Prop73Det.Prop73ReferenceStatement` from the named input
  `EmbeddedPairStatement` (the embedded pair of Lemma 7.1 with Lemma 7.2's three ingredients), with the angle
  choice of (CPF2);
* wiring: `prop73DeterminationStatement_of_embeddedPair` (Proposition 7.3's determination from the embedded pair,
  Aux. lemma 50 at the integer times and the trace part).

## What is not proved here (the named input)

`EmbeddedPairStatement`: for `0 < κ < 4` and `θ₁ < 0 < θ₂`, one probability space carrying the embedded pair
`(η_ψ, h_ψ)` of Lemma 7.1 as an optional hull coupling with the weights (CPF2), the original field `h` and the
exterior record `Q = (A, h')`, with (i) `h` determined by `(Q, h_ψ)` (Aux. lemma 12 on the thin outer union),
(ii) the history of `η_ψ` determined by `(h, Q)` (§4.2 field determination of the middle flow line; the pocket chart
and its segment from the outer curves), (iii) `(history, h_ψ)` independent of `Q` (Lemma 7.1's joint law, Aux.
lemma 46 with thin-support removal on the outer arcs). The landed pocket statements (`Lemma71E.Lemma71PocketStatement`,
`Lemma71F.Lemma71PocketPinStatement`) give the chart coupling clause of the mapped segment at fixed times of the prefix
filtration; they carry neither the field `h_ψ` as an optional hull coupling (its GFF marginal, its local-set clause at
every driving stopping time), nor (i)–(iii). See `planning/handoffs/PROVE-PROP73R.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Prop73Ref

open LawUnique LQGMetric

/-! ### The range of (CPF2) -/

/-- **(CPF2) covers every pair of seed weights** (p. 227: "As `θ₁ < 0 < θ₂` vary, (CPF2) ranges over every pair
`ρ^L, ρ^R > −2`, because `χ > 0` for `0 < κ < 4`"): `θ₂ = (ρ^L + 2)λ/χ` and `θ₁ = −(ρ^R + 2)λ/χ`. -/
theorem exists_cpf2_angles {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hL : -2 < rL) (hR : -2 < rR) :
    ∃ θ₁ θ₂ : ℝ, θ₁ < 0 ∧ 0 < θ₂ ∧ Sec7.cpf2RhoL κ θ₂ = rL ∧ Sec7.cpf2RhoR κ θ₁ = rR := by
  have hχ : 0 < QuantumZipper.chiC κ := Sec4.chiC_pos hκ hκ4
  have hlam : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hL2 : 0 < rL + 2 := by linarith
  have hR2 : 0 < rR + 2 := by linarith
  refine ⟨-((rR + 2) * sleLambda κ / QuantumZipper.chiC κ), (rL + 2) * sleLambda κ / QuantumZipper.chiC κ,
    ?_, by positivity, ?_, ?_⟩
  · have : 0 < (rR + 2) * sleLambda κ / QuantumZipper.chiC κ := by positivity
    linarith
  · unfold Sec7.cpf2RhoL
    field_simp
    ring
  · unfold Sec7.cpf2RhoR
    field_simp
    ring

/-! ### From the dyadic killed history to `LP.IsFieldDeterminedHistory` -/

section Paths

variable {nL nR : ℕ}

/-- The paths read off a recorded (dyadic) history: the lifetime, and at each time `t` the limit of the recorded
states at the dyadic times `⌊2ⁿt⌋/2ⁿ` below `t`. -/
def pathsOfHistory (x : HistorySpace nL nR) :
    ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) :=
  (x.1, (fun t => limUnder atTop fun n => (x.2 (lowerDyadic t n)).1),
    (fun i t => limUnder atTop fun n => (x.2 (lowerDyadic t n)).2.1 i),
    fun i t => limUnder atTop fun n => (x.2 (lowerDyadic t n)).2.2 i)

theorem measurable_pathsOfHistory : Measurable (pathsOfHistory (nL := nL) (nR := nR)) := by
  have hlim : ∀ f : ℕ → HistorySpace nL nR → ℝ, (∀ n, Measurable (f n)) →
      Measurable fun x => limUnder atTop fun n => f n x :=
    fun f hf => (StronglyMeasurable.limUnder fun n => (hf n).stronglyMeasurable).measurable
  refine measurable_fst.prodMk ((Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
    ((Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
      (Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_)))
  · exact measurable_fst.comp ((measurable_pi_apply _).comp measurable_snd)
  · exact (measurable_pi_apply i).comp (measurable_snd.fst.comp ((measurable_pi_apply _).comp measurable_snd))
  · exact (measurable_pi_apply i).comp (measurable_snd.snd.comp ((measurable_pi_apply _).comp measurable_snd))

/-- **A field-determined dyadic history gives `LP.IsFieldDeterminedHistory`.** If the killed history at the dyadic
times is almost surely a Borel function `g` of the field and the driving process is continuous before the lifetime,
then `pathsOfHistory ∘ g` recovers the lifetime and the driving and force paths at every time before the lifetime. -/
theorem isFieldDeterminedHistory_of_isAEDeterminedBy {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hdet : Sec7.IsAEDeterminedBy P h (killedHistory W VL VR ζ))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨g, hg, hK⟩ := hdet
  refine ⟨fun d => pathsOfHistory (g d), measurable_pathsOfHistory.comp hg, ?_⟩
  filter_upwards [hK, hcont] with ω hω hc
  have hζ : (g (h ω)).1 = ζ ω := (congrArg Prod.fst hω).symm
  have hdy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ n, (g (h ω)).2 (lowerDyadic t n) =
      (W (dyadicTime (lowerDyadic t n)) ω, (fun i => VL i (dyadicTime (lowerDyadic t n)) ω),
        fun i => VR i (dyadicTime (lowerDyadic t n)) ω) := by
    intro t ht n
    have hlt : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
    have e := congrFun (congrArg Prod.snd hω) (lowerDyadic t n)
    simp only [killedHistory, hlt, ↓reduceIte] at e
    exact e.symm
  refine ⟨hζ, fun t ht => ⟨?_, fun i => ?_, fun i => ?_⟩⟩
  · refine Tendsto.limUnder_eq ?_
    refine (tendsto_lowerDyadic_of_continuousOn hc.1 ht).congr fun n => ?_
    rw [hdy t ht n]
  · refine Tendsto.limUnder_eq ?_
    refine (tendsto_lowerDyadic_of_continuousOn (hc.2.1 i) ht).congr fun n => ?_
    rw [hdy t ht n]
  · refine Tendsto.limUnder_eq ?_
    refine (tendsto_lowerDyadic_of_continuousOn (hc.2.2 i) ht).congr fun n => ?_
    rw [hdy t ht n]

end Paths

/-! ### Lemma 7.2 -/

section Lemma72

variable {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {hψ h : Ω → DistOn upperHalfPlaneOpens} {δ : Type*} [MeasurableSpace δ] {Q : Ω → δ}

/-- **Lemma 7.2, (CPF3)** (pp. 226–227). Let `Q` be the exterior record (`(A, h')`), `h` the original field and `h_ψ`
the pulled-back field. If `h` is determined by `(Q, h_ψ)` (thin-support removal on `∂C`, Aux. lemma 12), the killed
history `Y` of `η_ψ` is determined by `(h, Q)` (field determination of the middle flow line; the pocket chart from the
outer curves) and the pair `(Y, h_ψ)` is independent of `Q` (the component-pair factorization), then `Y` is a
measurable function of `h_ψ` alone: `F(Y) = E[F(Y) | Q, h_ψ] = E[F(Y) | h_ψ]`. -/
theorem isAEDeterminedBy_of_cpf3 (hX : IsMeasurableKilledDriving W VL VR ζ) (hhψ : Measurable hψ)
    (hQ : Measurable Q) (hrec : Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) h)
    (hdet : Sec7.IsAEDeterminedBy P (fun ω => (h ω, Q ω)) (killedHistory W VL VR ζ))
    (hind : IndepFun (fun ω => (killedHistory W VL VR ζ ω, hψ ω)) Q P) :
    Sec7.IsAEDeterminedBy P hψ (killedHistory W VL VR ζ) := by
  obtain ⟨ga, hga, ha⟩ := hrec
  obtain ⟨gb, hgb, hb⟩ := hdet
  have hQZ : Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) (killedHistory W VL VR ζ) := by
    refine ⟨fun p => gb (ga p, p.1), hgb.comp (hga.prodMk measurable_fst), ?_⟩
    filter_upwards [ha, hb] with ω hωa hωb
    rw [hωb, hωa]
  exact Sec7.IsAEDeterminedBy.of_indepFun hQ hhψ (measurable_killedHistory hX) hQZ hind

/-- **Lemma 7.2 for an optional hull coupling** ("In the embedded coupling constructed above, `h_ψ` almost surely
determines `η_ψ`"): under the three ingredients of `isAEDeterminedBy_of_cpf3`, the killed driving history of the
coupling is field-determined (`LP.IsFieldDeterminedHistory`). -/
theorem isFieldDeterminedHistory_of_cpf3 {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ hψ) (hQ : Measurable Q)
    (hrec : Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) h)
    (hdet : Sec7.IsAEDeterminedBy P (fun ω => (h ω, Q ω)) (killedHistory W VL VR ζ))
    (hind : IndepFun (fun ω => (killedHistory W VL VR ζ ω, hψ ω)) Q P) :
    LP.IsFieldDeterminedHistory P hψ W VL VR ζ :=
  isFieldDeterminedHistory_of_isAEDeterminedBy
    (isAEDeterminedBy_of_cpf3 hC.2.2.2.1 hC.2.1 hQ hrec hdet hind)
    (IsIntegratedSLEEvolution.ae_continuousOn_driving hC.1)

end Lemma72

/-! ### The named input and the reference -/

/-- **Named input: the embedded pair of Lemma 7.1 with the three ingredients of Lemma 7.2** (specification §7.1,
pp. 221–227). For `0 < κ < 4` and angles `θ₁ < 0 < θ₂` there is one probability space carrying

* the embedded pair: the Loewner driver `(W, V^L, V^R)` of the mapped middle-curve segment `η_ψ` with its Brownian
  motion and lifetime, and the pulled-back field `h_ψ`, forming an optional hull coupling of `SLE_κ(ρ^L; ρ^R)` with the
  seed weights (CPF2) (Lemma 7.1: "The conditional law of `η_ψ` is `SLE_κ(ρ^L; ρ^R)` with seed weights (CPF2) […] The
  joint pair with `h_ψ` has the original coupling specification");
* the original field `h` and the exterior record `Q` (`(A, h')`: the two outer curves and the field off `C̄`), with
  1. `h` determined by `(Q, h_ψ)` (Lemma 7.2's proof: "The pair `(Q, h_ψ)` determines `h` off `∂C` […] **Aux.**
     lemma 12 makes it zero. Thus the entire field `h = N` is measurable from the recorded pair");
  2. the killed driving history of `η_ψ` determined by `(h, Q)` ("The outer curves determine `C`, `ψ`, and its
     inherited argument branch"; "The already proved non-boundary field-determination theorem recovers `γ` from `h`,
     and hence recovers `η_ψ` from `(Q, h_ψ)`");
  3. `(history, h_ψ)` independent of `Q` ("The component-pair factorization in the preceding proof says that
     `(η_ψ, h_ψ)` is independent of `Q`", with Lemma 7.1's "its full joint law is independent of the two outer
     curves", Aux. lemma 46). -/
def EmbeddedPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (hψ h : Ω → DistOn upperHalfPlaneOpens) (δ : Type u) (_ : MeasurableSpace δ) (Q : Ω → δ),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => Sec7.cpf2RhoL κ θ₂)
          (fun _ => Sec7.cpf2RhoR κ θ₁) P 𝓕 W VL VR B ζ hψ ∧
        Measurable Q ∧ Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) h ∧
        Sec7.IsAEDeterminedBy P (fun ω => (h ω, Q ω)) (killedHistory W VL VR ζ) ∧
        IndepFun (fun ω => (killedHistory W VL VR ζ ω, hψ ω)) Q P

/-- **Proposition 7.3's reference coupling** (`Prop73Det.Prop73ReferenceStatement`; Proposition 7.3's proof, p. 242:
"The embedded construction has produced one pair in which the field determines the curve") from the embedded pair:
the angles of (CPF2) for the given weights (`exists_cpf2_angles`, the remark after Lemma 7.2) and Lemma 7.2
(`isFieldDeterminedHistory_of_cpf3`). -/
theorem prop73ReferenceStatement_of_embeddedPair (h71 : EmbeddedPairStatement.{u}) :
    Prop73Det.Prop73ReferenceStatement.{u} := by
  intro κ hκ hκ4 rL rR hL hR
  obtain ⟨θ₁, θ₂, h1, h2, eL, eR⟩ := exists_cpf2_angles hκ hκ4 hL hR
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hψ, h, δ, mδ, Q, hC, hQ, hrec, hdet, hind⟩ :=
    h71 κ hκ hκ4 θ₁ θ₂ h1 h2
  rw [eL, eR] at hC
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hψ, hC, isFieldDeterminedHistory_of_cpf3 hC hQ hrec hdet hind⟩

/-- **Proposition 7.3's determination** (`Determination.Prop73DeterminationStatement`) from the embedded pair (Lemmas
7.1–7.2), Aux. lemma 50 at the integer times for the boundary-hitting pairs, and the trace part of Proposition 7.3. -/
theorem prop73DeterminationStatement_of_embeddedPair (h73t : Sec7.Prop73TraceStatement.{u})
    (h71 : EmbeddedPairStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR) :
    Determination.Prop73DeterminationStatement.{u} :=
  Aux50.prop73DeterminationStatement_of_aux50 h73t (prop73ReferenceStatement_of_embeddedPair h71) h50

/-- **Lemma 7.5, universal form** (`Theorem15.Lemma75Statement`, Theorem 1.5's input) from the embedded pair, Aux.
lemma 50 at the integer times, the trace part of Proposition 7.3 and LOCEXT's inputs of Aux. lemmas 53–55
(`Prop73Det.lemma75Statement_of_reference` with both of its Proposition 7.3 inputs discharged). -/
theorem lemma75Statement_of_embeddedPair (h73t : Sec7.Prop73TraceStatement.{u})
    (h71 : EmbeddedPairStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartSeedCouplingStatement.{u} κ) :
    Theorem15.Lemma75Statement.{u} :=
  Prop73Det.lemma75Statement_of_reference h73t (prop73ReferenceStatement_of_embeddedPair h71)
    (Aux50.prop73FieldKernelStatement_of_aux50 h50) hext hrs

end Prop73Ref

end InteractingSLE
