/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCDet

/-!
# The kernel coupling of a continuation with infinite threshold, on the space itself

Packet PROVE-CFGIVEN. The kernel assembly K2 (`DomainMarkov.K2.ae_isOptionalHullCoupling_k`) needs its input (E), the
integrated equations of the continuation with a Brownian motion of a filtration containing the initial σ-algebra.
The converse of Theorem 2.4 (`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun`) produces (E) only on
the enlargement `Ω × (ℕ → ℝ)`, because after the lifetime the driving Brownian motion is continued by fresh noise; the
consumers then obtain the coupling under the regular conditional law **of the enlargement** (`FCDet`).

When the continuation threshold is infinite almost surely, no continuation of the noise is needed: the Brownian motion
produced on the enlargement is the normalized martingale part `M/√κ` of the coordinates at **every** time, a function
of the first coordinate. Then (E) descends to `Ω` and K2 runs on `Ω` itself, so the conclusion is a coupling under
`condExpKernel P 𝒢 ω₀` (the form of the consumers' carriers, e.g. `RestartSw.CounterflowGivenPrefixStatement`).

## Main results

* `measurable_prodMk_const_prodFiltration`: the section `ω ↦ (ω, w₀)` is measurable from `𝓖 t` to the product
  filtration at `t`;
* **`isFilteredBrownianReal_of_prod`**: a Brownian motion of the product filtration that is a function of the first
  coordinate is a Brownian motion of the first filtration;
* **`isRandomWordEvolution_of_prod`**: (E) on the enlargement with such a noise descends to `Ω`;
* `isRandomWordEvolution_congr_life`: (E) only sees the lifetime almost surely on the live event;
* **`ae_isOptionalHullCoupling_of_hasSafeLaw_top`**: K2's inputs (S) and (L) with infinite lifetime, for a globally
  continuous continuation with the geometric images of a random word and almost surely infinite threshold, give for
  almost every `ω₀` an optional hull coupling (lifetime `⊤`) of the word at `ω₀` under `condExpKernel P 𝒢 ω₀`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfGiven

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.Aux122Disint Sec7.PocketTraversal

/-! ### Descending a Brownian motion from the enlargement -/

section Descend

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]

/-- **The section `ω ↦ (ω, w₀)` is measurable from `𝓖 t` to the product filtration at `t`.** -/
theorem measurable_prodMk_const_prodFiltration (𝓖 : Filtration ℝ≥0 mΩ) (𝓦 : Filtration ℝ≥0 m₀) (w₀ : Ω₀)
    (t : ℝ≥0) : Measurable[𝓖 t, WholeField.prodFiltration 𝓖 𝓦 t] fun ω => (ω, w₀) := by
  refine Measurable.of_comap_le ?_
  rw [WholeField.prodFiltration_apply, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]
  refine sup_le ?_ ?_
  · have e : (Prod.fst ∘ fun ω : Ω => (ω, w₀)) = id := rfl
    rw [e, MeasurableSpace.comap_id]
  · have e : (Prod.snd ∘ fun ω : Ω => (ω, w₀)) = fun _ => w₀ := rfl
    rw [e, MeasurableSpace.comap_const]
    exact bot_le

variable {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

omit [IsProbabilityMeasure P] in
/-- The product measure of a cylinder over the first coordinate. -/
theorem prod_preimage_fst (A : Set Ω) : (P.prod P₀) (Prod.fst ⁻¹' A) = P A := by
  rw [show Prod.fst ⁻¹' A = A ×ˢ (univ : Set Ω₀) from (prod_univ).symm, Measure.prod_prod, measure_univ, mul_one]

/-- **A Brownian motion of the product filtration that is a function of the first coordinate is a Brownian motion of
the first filtration.** -/
theorem isFilteredBrownianReal_of_prod [Nonempty Ω₀] {𝓖 : Filtration ℝ≥0 mΩ} {𝓦 : Filtration ℝ≥0 m₀}
    {B' : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) (fun t p => B' t p.1) (P.prod P₀)) :
    IsFilteredBrownianReal 𝓖 B' P := by
  obtain ⟨hBM, hBa, hBi⟩ := hB
  obtain ⟨w₀⟩ := ‹Nonempty Ω₀›
  -- adaptedness through the section `ω ↦ (ω, w₀)`
  have hBa' : ∀ t, Measurable[𝓖 t] (B' t) := fun t =>
    (hBa t).comp (measurable_prodMk_const_prodFiltration 𝓖 𝓦 w₀ t)
  have hBm : ∀ t, Measurable (B' t) := fun t => (hBa' t).mono (𝓖.le t) le_rfl
  refine ⟨⟨⟨fun I => ?_⟩, ?_⟩, hBa', fun s t hst => ?_⟩
  · -- finite-dimensional laws through `fst`
    have hX : Measurable fun ω => I.restrict fun x => B' x ω :=
      measurable_pi_iff.2 fun x => hBm x.1
    have hlaw := (hBM.hasLaw I).map_eq
    refine ⟨hX.aemeasurable, ?_⟩
    rw [← hlaw]
    change P.map (fun ω => I.restrict fun x => B' x ω) =
      (P.prod P₀).map ((fun ω => I.restrict fun x => B' x ω) ∘ Prod.fst)
    rw [← Measure.map_map hX measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  · exact ConverseBefore.ae_of_ae_fst (P₀ := P₀) hBM.cont
  · -- independence of the increments through `fst`
    rw [Indep_iff]
    rintro _ A ⟨S, hS, rfl⟩ hA
    have hAm : MeasurableSet A := 𝓖.le s _ hA
    have hinc : Measurable fun ω => B' t ω - B' s ω := (hBm t).sub (hBm s)
    have hSm : MeasurableSet ((fun ω => B' t ω - B' s ω) ⁻¹' S) := hinc hS
    have h := (Indep_iff _ _ _).1 (hBi s t hst) (Prod.fst ⁻¹' ((fun ω => B' t ω - B' s ω) ⁻¹' S))
      (Prod.fst ⁻¹' A) ⟨S, hS, rfl⟩ (by
        rw [WholeField.prodFiltration_apply]
        exact (le_sup_left : (𝓖 s).comap Prod.fst ≤ _) _ ⟨A, hA, rfl⟩)
    rw [← preimage_inter, prod_preimage_fst, prod_preimage_fst, prod_preimage_fst] at h
    exact h

/-- **(E) descends from the enlargement** when the noise is a function of the first coordinate (all the other data
are read through `fst`; the measurability and adaptedness clauses are supplied on `Ω`). -/
theorem isRandomWordEvolution_of_prod [Nonempty Ω₀] {a : ℝ} {nL nR : ℕ} {F : Set Ω}
    {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
    {𝓦 : Filtration ℝ≥0 m₀} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω × Ω₀ → ℝ} {B' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsRandomWordEvolution a (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR (WholeField.prodFiltration 𝓖 𝓦) (fun t p => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) B (fun p => ζ p.1))
    (hBB' : ∀ t p, B t p = B' t p.1) (h𝒢 : 𝒢 ≤ 𝓖 0) (hF : MeasurableSet[𝒢] F) (hΘL : Measurable[𝒢] ΘL)
    (hΘR : Measurable[𝒢] ΘR) (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j)) :
    IsRandomWordEvolution a P 𝒢 F ΘL ΘR ρL ρR 𝓖 W VL VR B' ζ := by
  have e : B = fun t p => B' t p.1 := funext fun t => funext fun p => hBB' t p
  subst e
  obtain ⟨-, -, -, -, hBM, -, -, -, hpath⟩ := hE
  refine ⟨h𝒢, hF, hΘL, hΘR, isFilteredBrownianReal_of_prod hBM, hW, hVL, hVR, ?_⟩
  exact ConverseBefore.ae_of_ae_fst (P₀ := P₀)
    (q := fun ω => ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B' t ω) (ζ ω)) hpath

end Descend

/-! ### Changing the lifetime on a null set -/

section Life

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {a : ℝ} {nL nR : ℕ}
  {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **(E) only sees the lifetime almost surely on the live event** (adaptedness for the new lifetime supplied). -/
theorem isRandomWordEvolution_congr_life {ζ ζ' : Ω → ℝ≥0∞}
    (hE : IsRandomWordEvolution a P 𝒢 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ω ∈ F → ζ ω = ζ' ω)
    (hW : AdaptedBefore 𝓖 ζ' W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ' (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓖 ζ' (VR j)) :
    IsRandomWordEvolution a P 𝒢 F ΘL ΘR ρL ρR 𝓖 W VL VR B ζ' := by
  obtain ⟨h0, hF, hΘL, hΘR, hBM, -, -, -, hpath⟩ := hE
  refine ⟨h0, hF, hΘL, hΘR, hBM, hW, hVL, hVR, ?_⟩
  filter_upwards [hpath, hζ] with ω h1 h2 hωF
  rw [← h2 hωF]
  exact h1 hωF

/-- A strongly adapted process is adapted before the constant lifetime `⊤`. -/
theorem adaptedBefore_top_of_stronglyAdapted {Y : ℝ≥0 → Ω → ℝ} (hY : StronglyAdapted 𝓖 Y) :
    AdaptedBefore 𝓖 (fun _ => (⊤ : ℝ≥0∞)) Y :=
  MartChar.adaptedBefore_of_stronglyAdapted (fun t => by
    have e : {ω : Ω | (⊤ : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, top_le_iff, ENNReal.coe_ne_top, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty _ (𝓖 t)) hY

end Life

/-! ### K2 on the space itself when the threshold is infinite -/

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The constant stopping time `⊤`. -/
theorem isStoppingTime_top (𝓖 : Filtration ℝ≥0 mΩ) :
    IsStoppingTime 𝓖 fun _ : Ω => ((⊤ : ℝ≥0∞) : WithTop ℝ≥0) := fun t => by
  convert @MeasurableSet.empty _ (𝓖 t)
  ext ω
  refine iff_of_false (fun h => ?_) (notMem_empty ω)
  exact (not_le.2 (WithTop.coe_lt_top t)) h

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The constant announcing sequence `T n = n` of the infinite lifetime. -/
theorem isAnnouncingSeq_top (𝓖 : Filtration ℝ≥0 mΩ) :
    Coupling.IsAnnouncingSeq 𝓖 P (fun _ => ⊤) fun n _ => (n : ℝ≥0) := by
  refine ⟨fun n => isStoppingTime_const 𝓖 _, fun ω m n hmn => by simp only [Nat.cast_le]; exact hmn,
    fun n => ae_of_all _ fun ω => ENNReal.coe_lt_top, ae_of_all _ fun ω t _ => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ≥0)
  exact ⟨n, hn⟩

/-- **K2 on `Ω` for a continuation with almost surely infinite threshold.** A globally continuous driver `W` from `0`,
adapted to `𝓗 ⊇ 𝒢`, with the geometric images of a `𝒢`-measurable ordered word `(xL, xR)` as force points and almost
surely infinite continuation threshold, and a field `X` with integrable pairings satisfying K2's inputs (S)
`HasSafeLaw` and (L) `HasSafeMembers` with the live event `univ` and the lifetime `⊤`: for almost every `ω₀`, under
`condExpKernel P 𝒢 ω₀`, processes equal to `(W, geomLW W xL, geomRW W xR)` almost surely at every time form with `X`
an optional hull coupling of the word `(xL ω₀, xR ω₀)` with lifetime `⊤`. -/
theorem ae_isOptionalHullCoupling_of_hasSafeLaw_top (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hthr : ∀ᵐ ω ∂P, FCDet.thr ρL ρR W xL xR ω = ⊤)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (fun _ => ⊤) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ (fun _ => ⊤) W X) :
    ∀ᵐ ω₀ ∂P, ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ (xL ω₀) (xR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' (fun _ => ⊤) X ∧
      ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = geomLW W xL i t ω) ∧
        ∀ j, VR' j t ω = geomRW W xR j t ω := by
  set 𝓖 := usualAugmentation 𝓗 P with h𝓖
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  have hVLs : ∀ i, StronglyAdapted 𝓗 (geomLW W xL i) := fun i => stronglyAdapted_geomLW hWa hWc hxL₀ i
  have hVRs : ∀ j, StronglyAdapted 𝓗 (geomRW W xR j) := fun j => stronglyAdapted_geomRW hWa hWc hxR₀ j
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp hX
  -- the coupling characteristic functional from (S)
  have hcf := Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlaw
    (ae_of_all _ (FCDet.isForceReg_thr hW0 hWc xL xR _)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h)
    (adaptedBefore_top_of_stronglyAdapted hWa) (fun i => adaptedBefore_top_of_stronglyAdapted (hVLs i))
    (fun j => adaptedBefore_top_of_stronglyAdapted (hVRs j))
  have hWaU : StronglyAdapted 𝓖 W := fun t => (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have h𝒢U : 𝒢 ≤ 𝓖 0 := h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)
  -- (E) on the enlargement, with the noise `M/√κ` at every time
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, hBf⟩ := ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun
    (𝒢 := 𝒢) (ζ := fun _ => ⊤) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) h𝒢U
    MeasurableSet.univ hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWaU (isStoppingTime_top 𝓖)
    (isAnnouncingSeq_top 𝓖) hint hcf (ae_of_all _ fun _ _ => le_top)
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => MartChar.martProc (MartChar.jointρ ρL ρR) W
    (MartChar.jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt κ with hB'def
  have hBB' : ∀ t p, B t p = B' t p.1 := fun t p => hBf p t le_top
  -- descend (E) and replace the threshold lifetime by `⊤`
  have hthrm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | FCDet.thr ρL ρR W xL xR ω ≤ t} :=
    FCDet.measurableSet_thr_le hWc hWaU (hxL.mono h𝒢U le_rfl) (hxR.mono h𝒢U le_rfl)
  have hVLU : ∀ i, StronglyAdapted 𝓖 (geomLW W xL i) := fun i t =>
    (hVLs i t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hVRU : ∀ j, StronglyAdapted 𝓖 (geomRW W xR j) := fun j t =>
    (hVRs j t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hE' := isRandomWordEvolution_of_prod (B' := B') hE hBB' h𝒢U MeasurableSet.univ hxL hxR
    (MartChar.adaptedBefore_of_stronglyAdapted hthrm hWaU)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hthrm (hVLU i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hthrm (hVRU j))
  have hE'' := isRandomWordEvolution_congr_life (ζ' := fun _ => ⊤) hE'
    (hthr.mono fun ω h _ => h) (adaptedBefore_top_of_stronglyAdapted hWaU)
    (fun i => adaptedBefore_top_of_stronglyAdapted (hVLU i)) (fun j => adaptedBefore_top_of_stronglyAdapted (hVRU j))
  have hK := ae_isOptionalHullCoupling_k (F := univ) hE'' hX (ae_of_all _ fun _ _ => ENNReal.zero_lt_top)
    h𝒢 (adaptedBefore_top_of_stronglyAdapted hWa) (fun i => adaptedBefore_top_of_stronglyAdapted (hVLs i))
    (fun j => adaptedBefore_top_of_stronglyAdapted (hVRs j)) hlaw hmem
  filter_upwards [hK] with ω₀ h using h (mem_univ ω₀)

end Kernel

end InteractingSLE.Sec5.CfGiven
