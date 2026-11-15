/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Main
import InteractingSLE.Spec.Supplement.R7Reference
import InteractingSLE.Spec.Sec7.Prop73Ref

/-!
# Aux. lemma 125 for a fixed two-seed word: (ER3) from the conditional coupling, and the two-seed references

Packet PROVE-STRIPSYS15. Specification §7.4, Aux. lemma 125 and its proof (`source/spec/p385-432.md#aux-125`,
pp. 395–398):

> Then, conditionally on `ℰ`, their full joint law is one kernel `Q_Θ` depending only on `Θ`. […] If `Θ` is fixed by
> the construction, the individual normalized pair is independent of the exterior information and of `A`, and its curve
> is determined by `H_C` alone.

> *Full field–curve law.* Apply Aux. lemma 50 under this conditional law on each deterministic relative capacity
> horizon `n`. […] Hence the full joint law of `(H_C, X_C|_{[0,n]})` given `ℰ` depends only on `Θ`.

> The already established global field determination, followed by the measurable selected-pocket erasure, thus makes
> `X_C` measurable from `(ℰ, H_C)`. But its joint conditional law with `H_C` given `ℰ` is `Q_Θ`. […]
> `F(X_C) = E[F(X_C) | ℰ, H_C] = ∫ F(x) Q_Θ(dx | H_C) = E[F(X_C) | Θ, H_C]`.  (ER3)

For a **fixed two-seed word** `SLE_κ(r_L; r_R)` (`r_L, r_R > −2`, the words of Lemma 7.25's reference and of Theorem
R.7's reference), Aux. lemmas 50–51 are proved for every `κ > 0` (`Aux50Ge8.hasTraceStopKernel`,
`Aux50.map_prod_killedHistory_eq`): any two optional hull couplings with continuous traces have the same joint law of
field and killed driving history. So "Aux. lemma 50 under the conditional law" needs no new kernel: the conditional law
of the pair `(H_C, killed history)` given `ℰ` is the same measure `Q` at almost every initial datum of the selection
event `F ∈ ℰ`. This file proves:

* `measureReal_inter_preimage_eq`, `measure_inter_preimage_eq`, **`indepFun_cond_of_condExpKernel_map_eq`**: if the
  regular conditional law of `X` given `ℰ` is `Q` on `F ∈ ℰ`, then under `P[· | F]` the variable `X` has law `Q` and
  is independent of every `ℰ`-measurable record;
* **`ae_isFieldDeterminedHistory_condExpKernel`** ((ER3) for a fixed word): if, under the regular conditional law
  given `ℰ` at almost every `ω₀ ∈ F`, the pocket field `H` and the relative driving processes form an optional hull
  coupling of `SLE_κ(r_L; r_R)` with a continuous trace (`IsCondTwoSeedCoupling`: "the canonical law survives the
  exterior reveal", the infinite relative lifetime and the continuous erasure — the parts of Aux. 125's proof before
  "Full field–curve law"), and the killed history is a Borel function of `(E, H)` for an `ℰ`-measurable record `E`
  on `F` (the global field determination followed by the measurable selected-pocket erasure), then under almost every
  such conditional law the killed history is field-determined (`LP.IsFieldDeterminedHistory`);
* `isFieldDeterminedHistory_of_condExpKernel_map_eq` (any word): the same conclusion for a reference coupling whose
  joint law is the conditional law on `F` (the input "joint conditional law `Q_Θ`" given directly);
* the named input `PocketTwoSeedStatement` (the two hypotheses above on one probability space, with an extra
  per-datum property such as transience) and the two consequences **`lemma725DetReferenceStatement_of_pocket`**
  (`Aux50Hit.Lemma725DetReferenceStatement`, the both-low words) and **`r7ReferenceStatement_of_pocket`**
  (`R7.R7ReferenceStatement`, with transient traces).

Ruling R48: nothing here takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis; the
imported results used are unconditional (`Aux50Ge8.hasTraceStopKernel`, `Aux50.map_prod_killedHistory_eq`,
`Sec7.IsAEDeterminedBy.of_indepFun`, `Sec7.IsAEDeterminedBy.of_map_eq`,
`Prop73Ref.isFieldDeterminedHistory_of_isAEDeterminedBy`, `LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux125Inputs2

/-! ### A conditional law that is constant on an event of the conditioning σ-algebra -/

section Cond

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {β : Type*} [mβ : MeasurableSpace β]

/-- If the regular conditional law of `X` given `ℰ` is `Q` at almost every point of `F`, then
`P(A ∩ {X ∈ S}) = Q(S) P(A)` for every `A ∈ ℰ` inside `F` (real form). -/
theorem measureReal_inter_preimage_eq (h𝓔 : 𝓔 ≤ mΩ) {F : Set Ω} {X : Ω → β} (hX : Measurable X)
    {Q : Measure β} (hlaw : ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝓔 ω).map X = Q) {A : Set Ω}
    (hA : MeasurableSet[𝓔] A) (hAF : A ⊆ F) {S : Set β} (hS : MeasurableSet S) :
    P.real (A ∩ X ⁻¹' S) = Q.real S * P.real A := by
  have hXS : MeasurableSet (X ⁻¹' S) := hX hS
  have h1 : ∫ ω in A, (P⟦X ⁻¹' S | 𝓔⟧) ω ∂P = P.real (A ∩ X ⁻¹' S) := by
    rw [setIntegral_condExp h𝓔 ((integrable_const (1 : ℝ)).indicator hXS) hA,
      integral_indicator hXS, Measure.restrict_restrict hXS, setIntegral_const, smul_eq_mul, mul_one]
    rw [inter_comm]
  have h2 : ∫ ω in A, (P⟦X ⁻¹' S | 𝓔⟧) ω ∂P = ∫ ω in A, Q.real S ∂P := by
    refine setIntegral_congr_ae (h𝓔 _ hA) ?_
    filter_upwards [condExpKernel_ae_eq_condExp (μ := P) h𝓔 hXS, hlaw] with ω e1 e2 hωA
    rw [← e1, measureReal_def, ← Measure.map_apply hX hS, e2 (hAF hωA), measureReal_def]
  rw [← h1, h2, setIntegral_const, smul_eq_mul, mul_comm]

/-- If the regular conditional law of `X` given `ℰ` is `Q` at almost every point of `F`, then
`P(A ∩ {X ∈ S}) = Q(S) P(A)` for every `A ∈ ℰ` inside `F`. -/
theorem measure_inter_preimage_eq (h𝓔 : 𝓔 ≤ mΩ) {F : Set Ω} {X : Ω → β} (hX : Measurable X)
    {Q : Measure β} [IsFiniteMeasure Q] (hlaw : ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝓔 ω).map X = Q) {A : Set Ω}
    (hA : MeasurableSet[𝓔] A) (hAF : A ⊆ F) {S : Set β} (hS : MeasurableSet S) :
    P (A ∩ X ⁻¹' S) = Q S * P A := by
  have h := measureReal_inter_preimage_eq h𝓔 hX hlaw hA hAF hS
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 h

/-- **A conditional law constant on `F ∈ ℰ` gives independence under `P[· | F]`.** If the regular conditional law of
`X` given `ℰ` is `Q` at almost every point of `F` (`P F ≠ 0`), then under `P[· | F]` the law of `X` is `Q` and `X` is
independent of every `ℰ`-measurable `E` ("If `Θ` is fixed by the construction, the individual normalized pair is
independent of the exterior information"). -/
theorem indepFun_cond_of_condExpKernel_map_eq (h𝓔 : 𝓔 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝓔] F)
    (hF0 : P F ≠ 0) {X : Ω → β} (hX : Measurable X) {Q : Measure β} [IsFiniteMeasure Q]
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝓔 ω).map X = Q) {γ : Type*} [mγ : MeasurableSpace γ]
    {E : Ω → γ} (hE : Measurable[𝓔] E) :
    IndepFun X E (P[|F]) ∧ (P[|F]).map X = Q := by
  have hFm : MeasurableSet F := h𝓔 _ hF
  have hFt : P F ≠ ⊤ := measure_ne_top _ _
  have hXF : ∀ S, MeasurableSet S → P[X ⁻¹' S | F] = Q S := by
    intro S hS
    rw [cond_apply hFm, measure_inter_preimage_eq h𝓔 hX hlaw hF subset_rfl hS, ← mul_assoc,
      mul_comm (P F)⁻¹, mul_assoc, ENNReal.inv_mul_cancel hF0 hFt, mul_one]
  refine ⟨(indepFun_iff_measure_inter_preimage_eq_mul).2 fun S T hS hT => ?_, ?_⟩
  · have hT' : MeasurableSet[𝓔] (F ∩ E ⁻¹' T) := hF.inter (hE hT)
    rw [hXF S hS, cond_apply hFm, cond_apply hFm, ← inter_assoc, inter_comm F, inter_assoc,
      inter_comm (X ⁻¹' S), measure_inter_preimage_eq h𝓔 hX hlaw hT' inter_subset_left hS]
    ring
  · ext S hS
    rw [Measure.map_apply hX hS, hXF S hS]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A property holding almost surely on an event of positive measure holds at some point of it. -/
theorem exists_mem_of_ae {F : Set Ω} (hF0 : P F ≠ 0) {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, ω ∈ F → p ω) :
    ∃ ω ∈ F, p ω := by
  by_contra hne
  push Not at hne
  refine hF0 (measure_mono_null (fun ω hω => ?_) (ae_iff.1 hp))
  exact fun h => hne ω hω (h hω)

end Cond

/-! ### (ER3) for a fixed two-seed word -/

section TwoSeed

open LawUnique LQGMetric

universe u

/-- **The pocket pair is a two-seed coupling under the regular conditional law at `ω₀`** (Aux. lemma 125's proof,
"The canonical law survives the exterior reveal", "There is no extra killing time" and the continuous erasure): under
`condExpKernel P ℰ ω₀`, the pocket field `H` and versions `(W', V^L', V^R')` of the relative driving processes
(almost surely equal to `(W, V^L, V^R)` at every time) with lifetime `ζ` form an optional hull coupling of
`SLE_κ(r_L; r_R)` (marks at `0⁻`, `0⁺`) for some filtration and Brownian motion, and the driver almost surely has a
continuous generating trace through its lifetime. (Versions are allowed because
`Restart.DomainMarkov.K2.ae_isOptionalHullCoupling_k` produces them.) -/
def IsCondTwoSeedCoupling {Ω : Type u} (𝓔 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ rL rR : ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (H : Ω → DistOn upperHalfPlaneOpens) (ω₀ : Ω) : Prop :=
  (∃ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' VR' : Fin 1 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (condExpKernel P 𝓔 ω₀) 𝓕
      W' VL' VR' B' ζ H ∧
    ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) ∧
  ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

/-- Processes that agree at every time have the same killed history. -/
theorem killedHistory_eq_of_forall {Ω : Type*} {nL nR : ℕ} {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (h : ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) :
    killedHistory W' VL' VR' ζ ω = killedHistory W VL VR ζ ω := by
  simp only [killedHistory, (h _).1, (h _).2.1, (h _).2.2]

variable {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ rL rR : ℝ} {ε : Type*} [mε : MeasurableSpace ε] {E : Ω → ε}
  {H : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- Under a two-seed conditional coupling, the conditional joint law of the field and the killed history of the
original processes equals that of every other such conditional coupling (Aux. lemmas 50–51 for the word). -/
theorem map_eq_of_isCondTwoSeedCoupling (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {ω₀ ω₁ : Ω}
    (h₀ : IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₀) (h₁ : IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₁) :
    (condExpKernel P 𝓔 ω₀).map (fun ω => (H ω, killedHistory W VL VR ζ ω)) =
      (condExpKernel P 𝓔 ω₁).map (fun ω => (H ω, killedHistory W VL VR ζ ω)) := by
  obtain ⟨K, hKm, hK, -⟩ := Aux50Ge8.hasTraceStopKernel.{u, u} hκ hL hR
  have key : ∀ {ω₂ : Ω}, IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₂ →
      ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' VR' : Fin 1 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (condExpKernel P 𝓔 ω₂) 𝓕
          W' VL' VR' B' ζ H ∧
        (∀ᵐ ω ∂(condExpKernel P 𝓔 ω₂), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ ω) η) ∧
        (condExpKernel P 𝓔 ω₂).map (fun ω => (H ω, killedHistory W VL VR ζ ω)) =
          (condExpKernel P 𝓔 ω₂).map (fun ω => (H ω, killedHistory W' VL' VR' ζ ω)) := by
    intro ω₂ h
    obtain ⟨⟨𝓕, W', VL', VR', B', hC, hag⟩, htr⟩ := h
    refine ⟨𝓕, W', VL', VR', B', hC, ?_, Measure.map_congr ?_⟩
    · filter_upwards [hag, htr] with ω h1 ⟨η, hη⟩
      refine ⟨η, ?_⟩
      have e : (fun t => W' t ω) = fun t => W t ω := funext fun t => (h1 t).1
      rw [e]; exact hη
    · filter_upwards [hag] with ω h1
      rw [killedHistory_eq_of_forall h1]
  obtain ⟨_, W₀, VL₀, VR₀, _, hC₀, htr₀, e₀⟩ := key h₀
  obtain ⟨_, W₁, VL₁, VR₁, _, hC₁, htr₁, e₁⟩ := key h₁
  rw [e₀, e₁]
  exact Aux50.map_prod_killedHistory_eq hκ hL hR hKm hK hK hC₀ htr₀ hC₁ htr₁

/-- **(ER3) for a fixed two-seed word** (Aux. lemma 125, p. 398, with `Θ` fixed). Let `F ∈ ℰ` with `P F ≠ 0`. Suppose
that at almost every `ω₀ ∈ F` the pocket pair is a two-seed coupling under the regular conditional law given `ℰ`
(`IsCondTwoSeedCoupling`), and that on `F` the killed driving history is almost surely a Borel function of `(E, H)`
for an `ℰ`-measurable record `E` ("the already established global field determination, followed by the measurable
selected-pocket erasure, thus makes `X_C` measurable from `(ℰ, H_C)`"). Then under the regular conditional law at
almost every `ω₀ ∈ F`, every such coupling has a field-determined killed history.

Proof: Aux. lemmas 50–51 for the word (`map_eq_of_isCondTwoSeedCoupling`) make the conditional joint law of
`(H, killed history)` one measure `Q` on `F`; so under `P[· | F]` the pair has law `Q` and is independent of `E`
(`indepFun_cond_of_condExpKernel_map_eq`); (ER3)/(CPF3) (`Sec7.IsAEDeterminedBy.of_indepFun`) removes `E`; the
determining function transfers along `Q` to each conditional law (`Sec7.IsAEDeterminedBy.of_map_eq`) and to the
versions; continuity of the driving processes recovers `LP.IsFieldDeterminedHistory`. -/
theorem ae_isFieldDeterminedHistory_condExpKernel (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) (h𝓔 : 𝓔 ≤ mΩ)
    {F : Set Ω} (hF : MeasurableSet[𝓔] F) (hF0 : P F ≠ 0) (hE : Measurable[𝓔] E) (hHm : Measurable H)
    (hXk : IsMeasurableKilledDriving W VL VR ζ)
    (hcpl : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₀)
    (hdet : ∃ g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ F → killedHistory W VL VR ζ ω = g (E ω, H ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' VR' : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (condExpKernel P 𝓔 ω₀) 𝓕
        W' VL' VR' B' ζ H →
      (∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
        ∀ j, VR' j t ω = VR j t ω) →
      LP.IsFieldDeterminedHistory (condExpKernel P 𝓔 ω₀) H W' VL' VR' ζ := by
  obtain ⟨ω₁, -, hω₁⟩ := exists_mem_of_ae hF0 hcpl
  have hY : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hXk
  set X : Ω → DistOn upperHalfPlaneOpens × HistorySpace 1 1 := fun ω => (H ω, killedHistory W VL VR ζ ω)
    with hXdef
  have hXm : Measurable X := hHm.prodMk hY
  set Q := (condExpKernel P 𝓔 ω₁).map X with hQdef
  have hlaw : ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝓔 ω).map X = Q := by
    filter_upwards [hcpl] with ω hω hωF
    exact map_eq_of_isCondTwoSeedCoupling hκ hL hR (hω hωF) hω₁
  obtain ⟨hind, hmapF⟩ := indepFun_cond_of_condExpKernel_map_eq h𝓔 hF hF0 hXm hlaw hE
  -- determination by the record and the field, under `P[· | F]`
  have hdetF : Sec7.IsAEDeterminedBy (P[|F]) (fun ω => (E ω, H ω)) (killedHistory W VL VR ζ) := by
    obtain ⟨g, hg, hYg⟩ := hdet
    refine ⟨g, hg, ?_⟩
    filter_upwards [cond_absolutelyContinuous.ae_le hYg, ae_cond_mem (h𝓔 _ hF)] with ω h1 h2 using h1 h2
  have hind' : IndepFun (fun ω => (killedHistory W VL VR ζ ω, H ω)) E (P[|F]) :=
    hind.comp (measurable_snd.prodMk measurable_fst) measurable_id
  have : IsProbabilityMeasure (P[|F]) := cond_isProbabilityMeasure hF0
  -- (ER3): the record is removed
  have hdetH : Sec7.IsAEDeterminedBy (P[|F]) H (killedHistory W VL VR ζ) :=
    hdetF.of_indepFun (hE.mono h𝓔 le_rfl) hHm hY hind'
  -- transfer to each conditional law along the common law `Q`, then to the versions
  filter_upwards [hlaw] with ω hωl hωF 𝓕 W' VL' VR' B' hC hag
  have h1 : Sec7.IsAEDeterminedBy (condExpKernel P 𝓔 ω) H (killedHistory W VL VR ζ) :=
    hdetH.of_map_eq hXm.aemeasurable hXm.aemeasurable (hmapF.trans (hωl hωF).symm)
  have h2 : Sec7.IsAEDeterminedBy (condExpKernel P 𝓔 ω) H (killedHistory W' VL' VR' ζ) :=
    h1.congr_ae (hag.mono fun ω' h => (killedHistory_eq_of_forall h).symm)
  exact Prop73Ref.isFieldDeterminedHistory_of_isAEDeterminedBy h2
    (LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving hC.1)

/-- **(ER3) transferred to a reference coupling, for any word.** Let `(H, X)` (field, killed history) on `Ω` have, at
almost every point of `F ∈ ℰ` (`P F ≠ 0`), regular conditional law given `ℰ` equal to the joint law of field and
killed history of an optional hull coupling on another probability space ("its joint conditional law with `H_C`
given `ℰ` is `Q_Θ`", `Θ` fixed), and let `X` be on `F` a Borel function of `(E, H)` with `E` `ℰ`-measurable. Then the
reference coupling has a field-determined killed history. -/
theorem isFieldDeterminedHistory_of_condExpKernel_map_eq {nL nR : ℕ} (h𝓔 : 𝓔 ≤ mΩ) {F : Set Ω}
    (hF : MeasurableSet[𝓔] F) (hF0 : P F ≠ 0) (hE : Measurable[𝓔] E) {Y : Ω → HistorySpace nL nR}
    (hHm : Measurable H) (hY : Measurable Y) {Ω' : Type*} {m' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓕' : Filtration ℝ≥0 m'} {W' : ℝ≥0 → Ω' → ℝ} {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ}
    {B' : ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞} {h' : Ω' → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ' h')
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝓔 ω).map (fun ω => (H ω, Y ω)) =
      P'.map (fun ω' => (h' ω', killedHistory W' VL' VR' ζ' ω')))
    (hdet : ∃ g : ε × DistOn upperHalfPlaneOpens → HistorySpace nL nR, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ F → Y ω = g (E ω, H ω)) :
    LP.IsFieldDeterminedHistory P' h' W' VL' VR' ζ' := by
  obtain ⟨hXk, -⟩ := hC.2.2.2
  have hXm : Measurable fun ω => (H ω, Y ω) := hHm.prodMk hY
  have hX' : Measurable fun ω' => (h' ω', killedHistory W' VL' VR' ζ' ω') :=
    hC.2.1.prodMk (measurable_killedHistory hXk)
  obtain ⟨hind, hmapF⟩ := indepFun_cond_of_condExpKernel_map_eq h𝓔 hF hF0 hXm hlaw hE
  have hdetF : Sec7.IsAEDeterminedBy (P[|F]) (fun ω => (E ω, H ω)) Y := by
    obtain ⟨g, hg, hYg⟩ := hdet
    refine ⟨g, hg, ?_⟩
    filter_upwards [cond_absolutelyContinuous.ae_le hYg, ae_cond_mem (h𝓔 _ hF)] with ω h1 h2 using h1 h2
  have hind' : IndepFun (fun ω => (Y ω, H ω)) E (P[|F]) :=
    hind.comp (measurable_snd.prodMk measurable_fst) measurable_id
  have : IsProbabilityMeasure (P[|F]) := cond_isProbabilityMeasure hF0
  have hdetH : Sec7.IsAEDeterminedBy (P[|F]) H Y := hdetF.of_indepFun (hE.mono h𝓔 le_rfl) hHm hY hind'
  refine Prop73Ref.isFieldDeterminedHistory_of_isAEDeterminedBy ?_
    (LawUnique.IsIntegratedSLEEvolution.ae_continuousOn_driving hC.1)
  exact hdetH.of_map_eq hXm.aemeasurable hX'.aemeasurable hmapF

end TwoSeed

/-! ### The named inputs and the two two-seed references -/

section Wrap

open LawUnique LQGMetric

universe u

/-- **Named input: Aux. lemma 125's pocket for a fixed two-seed word `SLE_κ(r_L; r_R)`, conditional-law form** (the
hypotheses of `ae_isFieldDeterminedHistory_condExpKernel` on one probability space). On a standard Borel probability
space with initial information `ℰ`, a selection event `F ∈ ℰ` of positive probability and an `ℰ`-measurable record
`E`:

* at almost every `ω₀ ∈ F`, under `condExpKernel P ℰ ω₀` the pocket field `H` and versions of the relative driving
  processes form an optional hull coupling of the word with a continuous trace (`IsCondTwoSeedCoupling`), and the
  per-datum property `Extra` holds (for Theorem R.7's reference: transience, `LP.HasTransientGeneratingTrace`);
* on `F` the killed relative driving history is almost surely a Borel function of `(E, H)`.

This is Aux. lemma 125's setting before "Full field–curve law" together with its input "global field determination,
followed by the measurable selected-pocket erasure". **Not proved in Lean.** -/
def PocketTwoSeedStatement (κ rL rR : ℝ) (Extra : ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω →
    (ℝ≥0 → Ω → ℝ) → (Ω → ℝ≥0∞) → Prop) : Prop :=
  ∃ (Ω : Type u) (𝓔 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (F : Set Ω) (ε : Type u) (_ : MeasurableSpace ε) (E : Ω → ε)
    (H : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    𝓔 ≤ mΩ ∧ MeasurableSet[𝓔] F ∧ P F ≠ 0 ∧ Measurable[𝓔] E ∧ Measurable H ∧
    IsMeasurableKilledDriving W VL VR ζ ∧
    (∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω₀ ∧
      Extra (condExpKernel P 𝓔 ω₀) W ζ) ∧
    ∃ g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ F → killedHistory W VL VR ζ ω = g (E ω, H ω)

/-- **A two-seed reference from the pocket** (Aux. lemma 125 with `Θ` fixed: "its curve is determined by `H_C`
alone"): an optional hull coupling of `SLE_κ(r_L; r_R)` whose killed driving history is field-determined, with driver
almost surely equal to a process with the per-datum property `Extra`. It is the pocket pair under the regular
conditional law at a suitable initial datum. -/
theorem exists_reference_of_pocketTwoSeedStatement {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    {Extra : ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (ℝ≥0 → Ω → ℝ) → (Ω → ℝ≥0∞) → Prop}
    (hP : PocketTwoSeedStatement.{u} κ rL rR Extra) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin 1 → ℝ≥0 → Ω → ℝ) (VR' : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W' VL' VR' B' ζ h ∧
        LP.IsFieldDeterminedHistory P h W' VL' VR' ζ ∧ (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) ∧ Extra P W ζ := by
  obtain ⟨Ω, 𝓔, mΩ, _, P, _, F, ε, _, E, H, W, VL, VR, ζ, h𝓔, hF, hF0, hE, hHm, hXk, hcpl, hdet⟩ := hP
  have hfd := ae_isFieldDeterminedHistory_condExpKernel hκ hL hR h𝓔 hF hF0 hE hHm hXk
    (hcpl.mono fun ω h hω => (h hω).1) hdet
  have hboth : ∀ᵐ ω ∂P, ω ∈ F → (IsCondTwoSeedCoupling 𝓔 κ rL rR P W VL VR ζ H ω ∧
      Extra (condExpKernel P 𝓔 ω) W ζ) ∧
      ∀ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' VR' : Fin 1 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (condExpKernel P 𝓔 ω) 𝓕
          W' VL' VR' B' ζ H →
        (∀ᵐ ω' ∂(condExpKernel P 𝓔 ω), ∀ t, W' t ω' = W t ω' ∧ (∀ i, VL' i t ω' = VL i t ω') ∧
          ∀ j, VR' j t ω' = VR j t ω') →
        LP.IsFieldDeterminedHistory (condExpKernel P 𝓔 ω) H W' VL' VR' ζ := by
    filter_upwards [hcpl, hfd] with ω h1 h2 hω using ⟨h1 hω, h2 hω⟩
  obtain ⟨ω₀, -, ⟨⟨⟨𝓕, W', VL', VR', B', hC, hag⟩, -⟩, hex⟩, hfd₀⟩ := exists_mem_of_ae hF0 hboth
  exact ⟨Ω, mΩ, condExpKernel P 𝓔 ω₀, inferInstance, 𝓕, W', VL', VR', B', ζ, H, W, hC,
    hfd₀ 𝓕 W' VL' VR' B' hC hag, hag.mono fun ω h t => (h t).1, hex⟩

/-- Transience of the trace transfers to a driver equal at every time almost surely. -/
theorem hasTransientGeneratingTrace_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W W' : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (h : LP.HasTransientGeneratingTrace P W ζ) (hag : ∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) :
    LP.HasTransientGeneratingTrace P W' ζ := by
  filter_upwards [h, hag] with ω ⟨η, hη, hT⟩ h1
  have e : (fun t => W' t ω) = fun t => W t ω := funext h1
  exact ⟨η, e ▸ hη, hT⟩

/-- **Lemma 7.25's determination reference from the pocket** (`Aux50Hit.Lemma725DetReferenceStatement`, the both-low
two-seed words, `κ > 4`): from the named input `PocketTwoSeedStatement` for every such word. -/
theorem lemma725DetReferenceStatement_of_pocket
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      ∃ Extra : ∀ {Ω : Type u} [MeasurableSpace Ω], Measure Ω → (ℝ≥0 → Ω → ℝ) → (Ω → ℝ≥0∞) → Prop,
        PocketTwoSeedStatement.{u} κ rL rR Extra) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  intro κ hκ rL rR hL hL' hR hR'
  obtain ⟨Extra, hP⟩ := h κ hκ rL rR hL hL' hR hR'
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W', VL', VR', B', ζ, H, -, hC, hfd, -, -⟩ :=
    exists_reference_of_pocketTwoSeedStatement (by linarith) hL hR hP
  exact ⟨Ω, mΩ, P, hP, 𝓕, W', VL', VR', B', ζ, H, hC, hfd⟩

/-- **Theorem R.7's reference from the pocket** (`R7.R7ReferenceStatement`, `κ > 4`, `r_L, r_R > −2`,
`κ/2 − 4 ≤ max(r_L, r_R)`): from the named input `PocketTwoSeedStatement` with transient traces. -/
theorem r7ReferenceStatement_of_pocket
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      PocketTwoSeedStatement.{u} κ rL rR fun P W ζ => LP.HasTransientGeneratingTrace P W ζ) :
    R7.R7ReferenceStatement.{u} := by
  intro κ hκ rL rR hL hR hmax
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W', VL', VR', B', ζ, H, W, hC, hfd, hag, hT⟩ :=
    exists_reference_of_pocketTwoSeedStatement (by linarith) hL hR (h κ hκ rL rR hL hR hmax)
  exact ⟨Ω, mΩ, P, hP, 𝓕, W', VL', VR', B', ζ, H, hC, hasTransientGeneratingTrace_congr hT hag, hfd⟩

end Wrap

end Aux125Inputs2

end Sec7

end InteractingSLE
