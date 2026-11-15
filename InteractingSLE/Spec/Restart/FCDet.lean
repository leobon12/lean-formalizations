/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ConverseBeforeK2
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop

/-!
# (Det) for a continuation from K2's inputs (S) and (L): the generic assembly

Packet PROVE-FCDET (specification Lemma 7.8's continuation assertion, p. 294: "Aux. lemma 77 supplies the nested
marked Gaussian kernels at every continuation stopping time […] Aux. lemma 79 identifies its canonical finite-force
mean and its continuous local martingale property. Theorem 2.4 now identifies the integrated relative driving
equations up to their continuation threshold"; Theorem W8's proof, pp. 539–541). The chain of
PROVE-DOMAINMARKOV5/7/8 from the conditional-law inputs of a continuation to the determination identity (Det) of the
consumers (`FirstContactCanonCondDetStatement`, …) is assembled here once, for a continuation read in a chart:

* the continuation is a **globally continuous** driver `W` from `0` (frozen after its lifetime) with the geometric
  images `geomLW W xL`, `geomRW W xR` of a random word as force points; its lifetime is the **continuation threshold**
  `thr ρL ρR W xL xR` of these coordinates;
* the inputs are K2's (S) `HasSafeLaw` and (L) `HasSafeMembers` for a filtration `𝓗` in which `W` is adapted and the
  word is `𝓗₀`-measurable, with the live event `univ` (condition on the live event first), an announcing sequence of
  the threshold, integrability of the field's pairings, and an admissible seed.

## Main results

* `thr`, `measurableSet_thr_le`, `measurable_thr`, `isStoppingTime_thr`, `thr_mem_thresholdSet`, **`thr_pos`** (an
  admissible seed gives a positive threshold);
* **`exists_ae_isOptionalHullCoupling`**: (S) and (L) give, on the enlargement `Ω × (ℕ → ℝ)`, an optional hull coupling
  of the word under almost every regular conditional law given the initial σ-algebra
  (`Aux79.isCouplingCharFun_of_hasSafeLaw` → `ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun` →
  `ConverseBefore.ae_isOptionalHullCoupling_k_prod`);
* `IsFlowType`, `isOptionalHullCoupling_cast`, **`isFlowLine_of_isOptionalHullCoupling`**: DOMAINMARKOV5's step (N),
  the coupling of the flow-line type is a flow line of the chart field;
* **`ae_codeMatch_of_hasSafeLaw`**: the code match (Det) with any canonical flow code
  (`ConverseBefore.ae_codeMatch_prod`).

**R43/R48.** The last result takes a canonical flow code (whose instances come from Theorems 1.2–1.3), so it serves
Theorems 1.4–1.5 only; the others use neither.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCDet

open DomainMarkov DomainMarkov.K2 Sec7.Aux122Disint Sec7.PocketTraversal

section Generic

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The continuation threshold of a driver with the geometric images of a random word. -/
def thr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  MartChar.thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The threshold is a stopping time of every filtration in which the driver is adapted and the word initial. -/
theorem measurableSet_thr_le {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝓗 0] xL)
    (hxR : Measurable[𝓗 0] xR) (t : ℝ≥0) :
    MeasurableSet[𝓗 t] {ω | thr ρL ρR W xL xR ω ≤ t} :=
  MartChar.measurableSet_thresholdTime_le hWc (fun i ω => (isForcePath_geomLW hWc xL ω i).1)
    (fun j ω => (isForcePath_geomRW hWc xR ω j).1) hWa (fun i => stronglyAdapted_geomLW hWa hWc hxL i)
    (fun j => stronglyAdapted_geomRW hWa hWc hxR j) (fun ω i j s t hst h => geomLW_merge hWc xL ω i j s t hst h)
    (fun ω i j s t hst h => geomRW_merge hWc xR ω i j s t hst h) t

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The threshold is measurable. -/
theorem measurable_thr {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝓗 0] xL)
    (hxR : Measurable[𝓗 0] xR) : Measurable (thr ρL ρR W xL xR) := by
  refine measurable_of_Iic fun t => ?_
  induction t using ENNReal.recTopCoe with
  | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
  | coe t => exact 𝓗.le t _ (measurableSet_thr_le hWc hWa hxL hxR t)

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The geometric coordinates of a continuous driver from `0` are regular before every lifetime. -/
theorem isForceReg_thr {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    Aux79.IsForceReg W (geomLW W xL) (geomRW W xR) ζ ω :=
  ⟨hW0 ω, (hWc ω).continuousOn, fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
    fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn,
    fun t _ => ⟨fun i => geomLW_le hWc xL ω t i, fun j => le_geomRW hWc xR ω t j⟩⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The threshold as a stopping time. -/
theorem isStoppingTime_thr {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝓗 0] xL)
    (hxR : Measurable[𝓗 0] xR) :
    IsStoppingTime 𝓗 fun ω => (thr ρL ρR W xL xR ω : WithTop ℝ≥0) := fun t =>
  measurableSet_thr_le hWc hWa hxL hxR t

/-- **K2 for a globally continuous continuation whose lifetime is its threshold** (all inputs almost sure). The
chain `Aux79.isCouplingCharFun_of_hasSafeLaw` → `ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun` →
`ConverseBefore.ae_isOptionalHullCoupling_k_prod`, with the live event `univ`. -/
theorem exists_ae_isOptionalHullCoupling (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hζ0 : ∀ᵐ ω ∂P, 0 < thr ρL ρR W xL xR ω)
    {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P (thr ρL ρR W xL xR) T)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ (thr ρL ρR W xL xR) W X) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀),
      ∀ᵐ p₀ ∂(P.prod P₀), ∃ (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))))
        (W' : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ) (VL' : Fin nL → ℝ≥0 → Ω × (ℕ → ℝ) → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω × (ℕ → ℝ) → ℝ) (B' : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
        IsOptionalHullCoupling κ (xL p₀.1) (xR p₀.1) ρL ρR (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀)
          𝓕' W' VL' VR' B' (fun p => thr ρL ρR W xL xR p.1) (fun p => X p.1) ∧
        ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀), ∀ t, W' t p = W t p.1 ∧
          (∀ i, VL' i t p = geomLW W xL i t p.1) ∧ ∀ j, VR' j t p = geomRW W xR j t p.1 := by
  set ζ := thr ρL ρR W xL xR with hζdef
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | ζ ω ≤ t} := measurableSet_thr_le hWc hWa hxL₀ hxR₀
  have hWa₀ : AdaptedBefore 𝓗 ζ W := MartChar.adaptedBefore_of_stronglyAdapted hζm hWa
  have hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (geomLW W xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hζm (stronglyAdapted_geomLW hWa hWc hxL₀ i)
  have hVRa₀ : ∀ j, AdaptedBefore 𝓗 ζ (geomRW W xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hζm (stronglyAdapted_geomRW hWa hWc hxR₀ j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX
  have hcf := Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlaw
    (ae_of_all _ (isForceReg_thr hW0 hWc xL xR ζ)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa₀ hVLa₀
    hVRa₀
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hζU : IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (ζ ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation 𝓗 P t _ (hζm t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun
    (𝒢 := 𝒢) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)) MeasurableSet.univ hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWaU
    hζU hT hint hcf (ae_of_all _ fun _ _ => le_rfl)
  refine ⟨P₀, hP₀, ?_⟩
  have hK := ConverseBefore.ae_isOptionalHullCoupling_k_prod (P₀ := P₀) (F := univ) hE hX
    (hζ0.mono fun ω h _ => h) h𝒢 hWa₀ hVLa₀ hVRa₀ hlaw hmem
  filter_upwards [hK] with p₀ hp₀
  exact hp₀ (mem_univ _)

/-- **The flow-line type of a boundary word**: the angle-`θ` flow-line word of `c` from `0` has `nL` left and `nR`
right marks, positions `xL`, `xR` and weights `ρL`, `ρR` (after the identification of the index types). -/
def IsFlowType (κ θ : ℝ) (c : BoundaryWord) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Prop :=
  ∃ (eL : flowLineNL c.fn c.jumps 0 = nL) (eR : flowLineNR c.fn c.jumps 0 = nR),
    (fun i => xL (Fin.cast eL i)) = flowLineXL c.fn c.jumps 0 ∧
    (fun j => xR (Fin.cast eR j)) = flowLineXR c.fn c.jumps 0 ∧
    (fun i => ρL (Fin.cast eL i)) = flowLineRhoL κ c.fn c.jumps 0 θ ∧
    (fun j => ρR (Fin.cast eR j)) = flowLineRhoR κ c.fn c.jumps 0 θ

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The threshold is attained** by a continuous driver with the geometric images of a random word. -/
theorem thr_mem_thresholdSet {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) {ω : Ω} {T : ℝ≥0} (hT : thr ρL ρR W xL xR ω = T) :
    T ∈ MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) :=
  MartChar.thresholdTime_mem_thresholdSet (hWc ω) (fun i => (isForcePath_geomLW hWc xL ω i).1)
    (fun j => (isForcePath_geomRW hWc xR ω j).1) (fun i j s t hst h => geomLW_merge hWc xL ω i j s t hst h)
    (fun i j s t hst h => geomRW_merge hWc xR ω i j s t hst h) hT

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **A positive threshold from an admissible seed**: if the word at time `0` is not at the threshold, the threshold
time of the geometric images is positive. -/
theorem thr_pos {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) {ω : Ω}
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω)) : 0 < thr ρL ρR W xL xR ω := by
  refine pos_iff_ne_zero.2 fun h0 => hseed ?_
  have hmem := thr_mem_thresholdSet (ρL := ρL) (ρR := ρR) hWc xL xR (T := 0) (by rw [h0]; rfl)
  have hL : (fun i => geomLW W xL i 0 ω) = xL ω := funext fun i => geomLW_zero hWc hW0 (hxL0 ω i)
  have hR : (fun j => geomRW W xR j 0 ω) = xR ω := funext fun j => geomRW_zero hWc hW0 (hxR0 ω j)
  simp only [MartChar.thresholdSet, mem_ofPred_eq] at hmem
  rw [hL, hR, hW0 ω] at hmem
  exact hmem

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- An optional hull coupling read along equalities of the numbers of marks. -/
theorem isOptionalHullCoupling_cast {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'} {nL' nR' : ℕ}
    (eL : nL' = nL) (eR : nR' = nR) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 m'}
    {W : ℝ≥0 → Ω' → ℝ} {VL : Fin nL → ℝ≥0 → Ω' → ℝ} {VR : Fin nR → ℝ≥0 → Ω' → ℝ} {B : ℝ≥0 → Ω' → ℝ}
    {ζ : Ω' → ℝ≥0∞} {h : Ω' → DistOn upperHalfPlaneOpens}
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i => xL (Fin.cast eL i)) (fun j => xR (Fin.cast eR j))
      (fun i => ρL (Fin.cast eL i)) (fun j => ρR (Fin.cast eR j)) Q 𝓕 W (fun i => VL (Fin.cast eL i))
      (fun j => VR (Fin.cast eR j)) B ζ h := by
  subst eL eR
  exact hc

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **An optional hull coupling of the flow-line type is a flow line.** -/
theorem isFlowLine_of_isOptionalHullCoupling {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'} {θ : ℝ}
    {c : BoundaryWord} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (htype : IsFlowType κ θ c xL xR ρL ρR)
    {𝓕 : Filtration ℝ≥0 m'} {W : ℝ≥0 → Ω' → ℝ} {VL : Fin nL → ℝ≥0 → Ω' → ℝ} {VR : Fin nR → ℝ≥0 → Ω' → ℝ}
    {B : ℝ≥0 → Ω' → ℝ} {ζ : Ω' → ℝ≥0∞} {Hc X : Ω' → DistOn upperHalfPlaneOpens}
    (hX : ∀ p, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc p) (X p))
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B ζ X) {γ : Ω' → ℝ≥0 → ℂ}
    (htr : ∀ᵐ p ∂Q, IsGeneratingTrace (fun t => W t p) (ζ p) (γ p)) :
    IsFlowLine κ c.fn c.jumps 0 θ Q Hc γ ζ := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  have h' := isOptionalHullCoupling_cast eL eR hc
  rw [hxL, hxR, hρL, hρR] at h'
  refine ⟨X, 𝓕, W, fun i => VL (Fin.cast eL i), fun j => VR (Fin.cast eR j), B, hX, h', ?_⟩
  filter_upwards [htr] with p hp
  simpa only [Complex.ofReal_zero, sub_zero] using hp

/-- **(Det) from (S) and (L)** for a globally continuous continuation whose lifetime is its threshold, on a standard
Borel space in `Type`. The continuation `W` of a random flow-line word `c` (type `(xL, xR, ρL, ρR)` almost surely) and
the field `X = Hc + θχ` satisfy K2's inputs (S) and (L) with the live event `univ`; the path `γ` is almost surely the
generating trace of `W` up to the threshold. Then almost surely `γ` is the decoded canonical flow code of `(c, Hc)`
(K2 on the enlargement, the flow-line form (N), `ConverseBefore.ae_codeMatch_prod`). -/
theorem ae_codeMatch_of_hasSafeLaw {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (htype : ∀ᵐ ω ∂P, IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {Hc X : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hX : Measurable X) (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hseed : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P (thr ρL ρR W xL xR) T)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ (thr ρL ρR W xL xR) W X) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ t, Measurable fun ω => γ ω t) (hγc : ∀ ω, Continuous (γ ω))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (thr ρL ρR W xL xR ω) (γ ω))
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) :
    ∀ᵐ ω ∂P, IsCodeMatch (F ((c ω, 0), Hc ω)) (γ ω) (thr ρL ρR W xL xR ω) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  obtain ⟨P₀, hP₀, hK⟩ := exists_ae_isOptionalHullCoupling hκ h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hX
    hint (hseed.mono fun ω h => thr_pos hW0 hWc hxL0 hxR0 h) hT hlaw hmem
  have hthrm : Measurable (thr ρL ρR W xL xR) :=
    measurable_thr hWc hWa (hxL.mono h𝒢 le_rfl) (hxR.mono h𝒢 le_rfl)
  have hβ : Measurable[𝒢] fun ω => (c ω, (0 : ℝ)) := hc.prodMk measurable_const
  have htr' : ∀ᵐ p₀ ∂(P.prod P₀), ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
      IsGeneratingTrace (fun t => W t p.1) (thr ρL ρR W xL xR p.1) (γ p.1) :=
    Sec7.Aux122Disint.ae_ae_condExpKernel ((MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le)
      (ConverseBefore.ae_fst_of_ae htr)
  have htype' : ∀ᵐ p₀ ∂(P.prod P₀), IsFlowType κ θ (c p₀.1) (xL p₀.1) (xR p₀.1) ρL ρR :=
    ConverseBefore.ae_fst_of_ae htype
  have h := ConverseBefore.ae_codeMatch_prod (P₀ := P₀) (M := univ) h𝒢m MeasurableSet.univ hβ hHc hγ hthrm
    (fun ω => (hγc ω).continuousOn) hF (by
      filter_upwards [hK, htr', htype'] with p₀ hp₀ htr₀ hty₀ _
      obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hp₀
      refine isFlowLine_of_isOptionalHullCoupling hty₀ (fun p : Ω × (ℕ → ℝ) => hXH p.1) hcpl ?_
      filter_upwards [hag, htr₀] with p hp hgt
      have e : (fun t => W' t p) = fun t => W t p.1 := funext fun t => (hp t).1
      rw [e]
      exact hgt)
  filter_upwards [h] with ω hω using hω (mem_univ ω)

end Generic

end InteractingSLE.Restart.FCDet
