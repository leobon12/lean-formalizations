/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ConverseBefore
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Restart.DomainMarkovK2Det
import InteractingSLE.Spec.Coupling.Assembly11BCoord
import InteractingSLE.Spec.Coupling.MartMeans2Local

/-!
# K2 on the enlargement `Ω × Ω₀`

Packet PROVE-DOMAINMARKOV7 (item E2 of `planning/handoffs/PROVE-DOMAINMARKOV5.md`, continued). The input (E) of the
kernel assembly K2 (`DomainMarkov.K2.ae_isOptionalHullCoupling_k`) is produced by `isRandomWordEvolution_prod` on the
enlargement `Ω × (ℕ → ℝ)`, while the inputs (S) (`HasSafeLaw`) and (L) (`HasSafeMembers`) of a setting live on `Ω`.
This file moves (S), (L), adaptedness and almost sure statements through the first projection, runs K2 on the
enlargement, and brings almost sure conclusions back to `Ω`:

* `setIntegral_preimage_fst`: `∫_{fst⁻¹ D} f(p.1) d(P ⊗ P₀) = ∫_D f dP` (no measurability needed);
* `ae_fst_of_ae`, `ae_of_ae_fst`: almost sure statements about the first coordinate, both ways;
* `adaptedBefore_fst`, `hasSafeLaw_fst`, `hasSafeMembers_fst`: the inputs read through the first projection, for the
  pulled-back filtration `Coupling.filtrationComap 𝓗 measurable_fst`;
* **`ae_isOptionalHullCoupling_k_prod`**: K2 on `Ω × Ω₀` from (E) on the enlargement and (S), (L) on `Ω`: for almost
  every `p₀` with `p₀.1 ∈ F`, under `condExpKernel (P ⊗ P₀) (𝒢 ∘ fst) p₀`, processes equal to the continuation read
  through `fst` form, with the field read through `fst`, an optional hull coupling of the word at `p₀.1`;
* **`ae_codeMatch_prod`**: PROVE-DOMAINMARKOV5's (Det) lift (`ae_codeMatch_of_ae_condExpKernel_isFlowLine`) on the
  enlargement, with the conclusion brought back to `Ω`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace ConverseBefore

open DomainMarkov DomainMarkov.K2 Sec7.Aux122Disint

/-! ### Integrals and almost sure statements through the first projection -/

section Fst

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- **A set integral of a function of the first coordinate over a cylinder** (no measurability needed). -/
theorem setIntegral_preimage_fst [SFinite P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Ω → E) (D : Set Ω) : ∫ p in Prod.fst ⁻¹' D, f p.1 ∂(P.prod P₀) = ∫ ω in D, f ω ∂P := by
  rw [show Prod.fst ⁻¹' D = D ×ˢ (univ : Set Ω₀) from (prod_univ).symm, ← Measure.prod_restrict,
    Measure.restrict_univ, integral_fun_fst]
  simp

/-- An almost sure statement about `ω` holds almost surely for the first coordinate on `Ω × Ω₀`. -/
theorem ae_fst_of_ae [SFinite P] {q : Ω → Prop} (h : ∀ᵐ ω ∂P, q ω) : ∀ᵐ p ∂(P.prod P₀), q p.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

/-- **An almost sure statement about the first coordinate on `Ω × Ω₀` holds almost surely on `Ω`.** -/
theorem ae_of_ae_fst [SFinite P] {q : Ω → Prop} (h : ∀ᵐ p ∂(P.prod P₀), q p.1) : ∀ᵐ ω ∂P, q ω := by
  have h' := Measure.ae_ae_of_ae_prod h
  have : (ae P₀).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero P₀)
  filter_upwards [h'] with ω hω
  exact hω.exists.choose_spec

end Fst

/-! ### K2's inputs read through the first projection -/

section Inputs

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {nL nR : ℕ} {𝓗 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

/-- **Adaptedness before the lifetime, read through the first projection.** -/
theorem adaptedBefore_fst {Y : ℝ≥0 → Ω → ℝ} (h : AdaptedBefore 𝓗 ζ Y) :
    AdaptedBefore (Coupling.filtrationComap 𝓗 (measurable_fst (α := Ω) (β := Ω₀))) (fun p => ζ p.1)
      (fun t p => Y t p.1) := fun t A hA => ⟨_, h t A hA, rfl⟩

/-- **(S) read through the first projection.** -/
theorem hasSafeLaw_fst [SFinite P] {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}
    (h : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    HasSafeLaw κ ρL ρR (P.prod P₀) (Coupling.filtrationComap 𝓗 (measurable_fst (α := Ω) (β := Ω₀)))
      (Prod.fst ⁻¹' F) (fun p => ζ p.1) (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1)
      (fun p => X p.1) := by
  intro ψ q D hD hDae
  obtain ⟨D₀, hD₀, rfl⟩ := hD
  have hae : ∀ᵐ ω ∂P, ω ∈ D₀ → ω ∈ F ∧ ω ∈ avoidSet W ζ ψ q := ae_of_ae_fst (P₀ := P₀) hDae
  exact (setIntegral_preimage_fst (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) D₀).trans
    ((h ψ q D₀ hD₀ hae).trans
      (setIntegral_preimage_fst (fun ω => Coupling.cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω)
        D₀).symm)

/-- **(L) read through the first projection.** -/
theorem hasSafeMembers_fst [SFinite P] {F : Set Ω} {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}
    (h : HasSafeMembers P 𝓗 F ζ W X) :
    HasSafeMembers (P.prod P₀) (Coupling.filtrationComap 𝓗 (measurable_fst (α := Ω) (β := Ω₀)))
      (Prod.fst ⁻¹' F) (fun p => ζ p.1) (fun t p => W t p.1) (fun p => X p.1) := by
  intro s Fb hFb D hD hDae f Ξ
  obtain ⟨D₀, hD₀, rfl⟩ := hD
  have hae : ∀ᵐ ω ∂P, ω ∈ D₀ → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := ae_of_ae_fst (P₀ := P₀) hDae
  rw [setIntegral_preimage_fst
      (fun ω => Complex.exp (Complex.I * (X ω (LocalSets.lapTest (ballsOpen Fb) f + Ξ) : ℂ))) D₀,
    setIntegral_preimage_fst (fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ))) D₀]
  exact h s Fb hFb D₀ hD₀ hae f Ξ

end Inputs

/-! ### From the means of (S) at stopping times to E2's martingale hypothesis -/

section Means

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

/-- **E2's hypothesis `hmart` from MartMeans2's output.** `MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`
gives, from the conditional-law clause (S) at stopping times, the coupling mean of `z` (for the explicit extensions
`meanExt`) as a local martingale before `ζ ∧ s(z)` after setting it to `0` off a full event `G ∈ 𝓖₀`. If `𝓖₀`
contains the measurable null sets and the mean at time `0` is measurable, the mean itself (`coupProc`) is a local
martingale before `s(z) ∧ ζ`, the form of `isRandomWordEvolution_prod`'s `hmart`. -/
theorem isLocalMartingaleBefore_coupProc_of_meanProcOn
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) {G : Set Ω} (hG : MeasurableSet[𝓖 0] G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {z : ℂ}
    (hX0 : Measurable (MartChar.coupProc κ ρL ρR W VL VR z 0))
    (h : MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (ζ ω) (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z))
      (Coupling.MartMeans2.meanProcOn κ W
        (fun ω t => MartChar.meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω)) z G)) :
    MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath W ω) z : WithTop ℝ≥0) (ζ ω))
      (MartChar.coupProc κ ρL ρR W VL VR z) := by
  have h' := Sec7.PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => min_comm _ _) h
  refine isLocalMartingaleBefore_of_eqOn hnull hG hGae hX0 (fun ω hω t => ?_) h'
  simp only [Coupling.MartMeans2.meanProcOn, hω, ↓reduceIte]
  rfl

end Means

section OneShot

open Sec7.PocketTraversal

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ}

/-- The explicit coupling mean at time `0` is measurable (it is the explicit extension at the initial word). -/
theorem measurable_coupProc_zero {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hVL : ∀ i, Measurable (VL i 0)) (hVR : ∀ j, Measurable (VR j 0)) {z : ℂ} (hz : z ∈ H) :
    Measurable (MartChar.coupProc κ ρL ρR W VL VR z 0) := by
  have hz0 : z ≠ 0 := fun h0 => lt_irrefl (0 : ℝ) (by simpa [h0] using (show 0 < z.im from hz))
  have e : MartChar.coupProc κ ρL ρR W VL VR z 0 =
      fun ω => MartChar.meanExt κ ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω) z := by
    funext ω
    exact Coupling.MartMeans2.couplingMean_zero κ (by simp [MartChar.wpath, hW0 ω]) _ hz0
  rw [e]
  exact Sec7.PhaseSelAdapt.measurable_meanExt κ ρL ρR (w := fun ω => W 0 ω) (by simp only [hW0]; exact measurable_const)
    (measurable_pi_iff.2 hVL) (measurable_pi_iff.2 hVR) measurable_const

/-- **(E2) from the conditional-law clause at stopping times, in one step.** Let `𝓖` be a right-continuous filtration
containing the measurable null sets, `W` a continuous adapted driver from `0` (frozen after the lifetime `ζ`, a
stopping time with an announcing sequence), the force points the geometric images of a sorted random word
`xL ≤ 0 ≤ xR` measurable for `𝒢 ≤ 𝓖₀`, and let the field `h` (integrable pairings) satisfy the coupling
characteristic-functional clause before `ζ` (`MartMeans.IsCouplingCharFun`, the conditional law (S) at stopping times).
If the threshold time comes at or before `ζ` almost surely on the `𝒢`-event `F`, then on `Ω × (ℕ → ℝ)` the
coordinates read through the first factor are K2's input (E) (`MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`,
`isLocalMartingaleBefore_coupProc_of_meanProcOn`, `isRandomWordEvolution_prod`). -/
theorem isRandomWordEvolution_prod_of_isCouplingCharFun [IsProbabilityMeasure P] [𝓖.IsRightContinuous] {κ : ℝ}
    (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (h𝒢 : 𝒢 ≤ 𝓖 0) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    {ζ : Ω → ℝ≥0∞} (hζ : IsStoppingTime 𝓖 fun ω => (ζ ω : WithTop ℝ≥0)) {T : ℕ → Ω → ℝ≥0}
    (hT : Coupling.IsAnnouncingSeq 𝓖 P ζ T) {h : Ω → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) ζ h)
    (hTζ : ∀ᵐ ω ∂P, ω ∈ F → MartChar.thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) ≤ ζ ω) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsRandomWordEvolution κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F)
        (fun p => xL p.1) (fun p => xR p.1) ρL ρR (WholeField.prodFiltration 𝓖 𝓦) (fun t p => W t p.1)
        (fun i t p => geomLW W xL i t p.1) (fun j t p => geomRW W xR j t p.1) B
        (fun p => MartChar.thresholdTime ρL ρR (fun t => W t p.1) (fun i t => geomLW W xL i t p.1)
          (fun j t => geomRW W xR j t p.1)) ∧
      (∀ p, Continuous fun t => B t p) ∧
      ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ ζ p.1 →
        B t p = MartChar.martProc (MartChar.jointρ ρL ρR) W (MartChar.jointV (geomLW W xL) (geomRW W xR)) t p.1 /
          Real.sqrt κ := by
  have hxL' : Measurable[𝓖 0] xL := hxL.mono h𝒢 le_rfl
  have hxR' : Measurable[𝓖 0] xR := hxR.mono h𝒢 le_rfl
  have hVLa : ∀ i, StronglyAdapted 𝓖 (geomLW W xL i) := fun i => stronglyAdapted_geomLW hWa hWc hxL' i
  have hVRa : ∀ j, StronglyAdapted 𝓖 (geomRW W xR j) := fun j => stronglyAdapted_geomRW hWa hWc hxR' j
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t} := fun t => hζ t
  have hmart : ∀ z ∈ H, MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath W ω) z : WithTop ℝ≥0) (ζ ω))
      (MartChar.coupProc κ ρL ρR W (geomLW W xL) (geomRW W xR) z) := by
    intro z hz
    obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
      (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
      (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn,
        ⟨fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
          fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn⟩,
        fun t _ => ⟨fun i => geomLW_le hWc xL ω t i, fun j => le_geomRW hWc xR ω t j⟩⟩)
      hT hint hcf (fun ω t => MartChar.meanExt κ ρL ρR (W t ω) (fun i => geomLW W xL i t ω)
        (fun j => geomRW W xR j t ω))
      (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _) hz
    exact isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
      (measurable_coupProc_zero hW0 (fun i => ((hVLa i 0).measurable.mono (𝓖.le 0) le_rfl))
        (fun j => ((hVRa j 0).measurable.mono (𝓖.le 0) le_rfl)) hz) hloc
  exact isRandomWordEvolution_prod hκ h𝒢 hF hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hζ hmart hTζ

end OneShot

/-! ### K2 and the (Det) lift on the enlargement -/

section K2

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type*}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω}
  {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}

/-- **K2 on the enlargement `Ω × Ω₀`** (`DomainMarkov.K2.ae_isOptionalHullCoupling_k` on the product, with (S), (L)
and adaptedness supplied on `Ω` and read through the first projection). The input (E) is the evolution on the
enlargement, as produced by `isRandomWordEvolution_prod`. For almost every `p₀` with `p₀.1 ∈ F`, under the regular
conditional law given `𝒢` read through `fst`, processes equal to the continuation (almost surely, at every time) form,
with the field read through `fst`, an optional hull coupling of the word at `p₀.1`. -/
theorem ae_isOptionalHullCoupling_k_prod
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolution κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => ζ p.1))
    (hX : Measurable X) (hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' ζ W) (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR X) (hmem : HasSafeMembers P 𝓗' F ζ W X) :
    ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))) (W' : ℝ≥0 → Ω × Ω₀ → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × Ω₀ → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × Ω₀ → ℝ) (B' : ℝ≥0 → Ω × Ω₀ → ℝ),
        IsOptionalHullCoupling κ (ΘL p₀.1) (ΘR p₀.1) ρL ρR (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀)
          𝓕' W' VL' VR' B' (fun p => ζ p.1) (fun p => X p.1) ∧
        ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀), ∀ t, W' t p = W t p.1 ∧
          (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1 :=
  ae_isOptionalHullCoupling_k (𝒢 := 𝒢.comap Prod.fst) hE (hX.comp measurable_fst)
    (ae_fst_of_ae (P₀ := P₀) hζ0) (𝓗' := Coupling.filtrationComap 𝓗' measurable_fst)
    (MeasurableSpace.comap_mono h𝒢') (adaptedBefore_fst hW') (fun i => adaptedBefore_fst (hVL' i))
    (fun j => adaptedBefore_fst (hVR' j)) (hasSafeLaw_fst hlaw) (hasSafeMembers_fst hmem)

end K2

section Det

/-- **(Det) through the enlargement**: if, for almost every `p₀` of `Ω × Ω₀` with `p₀.1 ∈ M`, the path `γ` read through
`fst` is a flow line of the field read through `fst` under the regular conditional law given `𝒢` read through `fst`
(boundary data the `𝒢`-measurable word `β` at `p₀.1`), then `P`-almost surely on `M` the path `γ` is the decoded
canonical flow code of `(β, Hc)` (`DomainMarkov.K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine` on `Ω × Ω₀`, brought
back by `ae_of_ae_fst`). -/
theorem ae_codeMatch_prod {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Ω₀ : Type} [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord × ℝ} (hβ : Measurable[𝒢] β) {Hc : Ω → DistOn upperHalfPlaneOpens} (hH : Measurable Hc)
    {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ t, Measurable fun ω => γ ω t) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ U ω}) {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    (hfl : ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ M →
      IsFlowLine κ (β p₀.1).1.fn (β p₀.1).1.jumps (β p₀.1).2 θ
        (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) (fun p => Hc p.1) (fun p => γ p.1) (fun p => U p.1)) :
    ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F (β ω, Hc ω)) (γ ω) (U ω) := by
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × Ω₀ → Ω) := Measurable.of_comap_le le_rfl
  have h := ae_codeMatch_of_ae_condExpKernel_isFlowLine (Ω := Ω × Ω₀) (𝒢 := 𝒢.comap Prod.fst)
    (P := P.prod P₀) ((MeasurableSpace.comap_mono h𝒢).trans measurable_fst.comap_le) ⟨M, hM, rfl⟩
    (hβ.comp hfst) (hH.comp measurable_fst) (fun t => (hγ t).comp measurable_fst) (hU.comp measurable_fst)
    (fun p => hγc p.1) hF hfl
  exact ae_of_ae_fst (P₀ := P₀) (q := fun ω => ω ∈ M → IsCodeMatch (F (β ω, Hc ω)) (γ ω) (U ω)) h

end Det

end ConverseBefore

end Restart

end InteractingSLE
