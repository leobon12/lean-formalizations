/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Cond

/-!
# Aux. lemma 54 for general words: the statement and its assembly

Packet PROVE-AUX54. Specification Aux. lemma 54 (p. 246): "Fix the initial force data and a bounded own-filtration
stopping rule `S < T_*` … Suppose `(h, W_{·∧S}, V_{·∧S})` is another stopped coupling with the same driving law and the
same original optional hull specification through `S` … Then the stopped coupling extends to a full coupling with the
original optional hull specification. The extension preserves the whole initial field and uses only the stopped history
and its active field when sampling the future."

**The statement proved here** (`StoppedHullExtendRStatement`) is PROVE-DOMAINMARKOV10's Galmarino form
(`StoppedExtendWF.StoppedHullExtendGKStatement`: the stop is a Galmarino rule `V = R(history killed at V)`, the source's
"own-filtration stopping rule") with the source's **regularity at the stop** (`IsRegularStop`): when the state at a
finite stop is not a threshold state, the driver is continuous a little beyond the stop. The source's stopped coupling
has the stopped driver `W_{·∧S}`, which is continuous, so this holds there; it is needed because
`StoppedExtend.IsStoppedHullCoupling` leaves the driver arbitrary after `V`, and then its clause at `τ = V` reads the
hull `fwdHull W V` of a driver that may jump right after `V` (all of `ℍ`), and is vacuous (PROVE-WFS0, finding 1).
With the regularity, the clause at `V` is the source's "conditional second marginal is the specified Gaussian kernel".

* `StoppedHullExtendRStatement κ`: Aux. lemma 54, kernel form, Galmarino rule, regular stop;
* `ExtLocalityStatement κ`: locality of the hulls on the record extension (proved in `Aux54Loc`,
  `extLocalityStatement`; the unconditional theorem is `Aux54Loc`'s `stoppedHullExtendRStatement`);
* **`stoppedHullExtendRStatement_of_locality`**: Aux. lemma 54 from `ExtLocalityStatement`, every `κ > 0`: the
  reference is Theorem 1.1's construction with its families (`WholeFieldStopped.exists_isFamilyRef`), the extension is
  one disintegration of it given the record (`exists_isRecExt`), the evolution is the reference's read through the
  second factor, the conditional-law clause is `isDyadicSampled_ext` with
  `DomainMarkov.isOptionalHullCoupling_of_dyadic`, and the coordinates agree through the stop (`IsRecExt.ae_agree`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov

/-- **Aux. lemma 54 for general words** (specification p. 246), kernel form: for an ordered word, a measurable Galmarino
rule `R` and a coupling through `V = R(history killed at V)` that is regular at the stop, there is a Markov kernel `K`
such that, under `P ⊗ K`, the field read through the first factor has a full optional hull coupling whose lifetime is
at least `V` and whose coordinates agree with the stopped ones at every time `t ≤ V` before the lifetime. -/
def StoppedHullExtendRStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) → IsRegularStop ρL ρR P W VL VR V →
      ∃ (C : Type u) (_ : MeasurableSpace C) (K : Kernel Ω C) (_ : IsMarkovKernel K)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × C → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ)
        (ζ' : Ω × C → ℝ≥0∞),
        IsOptionalHullCoupling κ xL xR ρL ρR (P ⊗ₘ K) 𝓕' W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1

/-- **Named input: locality on the record extension.** For a coupling through a Galmarino stop that is regular at the
stop, a family reference on a standard Borel space, and a record extension `E` of the two, every hull of the reference's
driving read through `Prod.snd`, at a stopping time of its driving filtration before the lifetime, is a local set of the
original field read through `Prod.fst`. -/
def ExtLocalityStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) → IsRegularStop ρL ρR P W VL VR V →
    ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} [StandardBorelSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
      (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞) (h₀ : Ω₀ → DistOn upperHalfPlaneOpens),
      WholeFieldStopped.IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
    ∀ (E : Measure (Ω × Ω₀)) [IsProbabilityMeasure E],
      IsRecExt P P₀ (recHull ρL ρR xL xR) h (killedHistory W VL VR V) h₀
        (killedHistory W₀ VL₀ VR₀ (ruleStop R W₀ VL₀ VR₀ ζ₀)) E →
    ∀ (hXE : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
        (fun j t p => VR₀ j t p.2) fun p => ζ₀ p.2) (τ : Ω × Ω₀ → WithTop ℝ≥0),
      IsStoppingTime (drivingFiltration E hXE) τ → (∀ᵐ p ∂E, (τ p : ℝ≥0∞) < ζ₀ p.2) →
        IsLocalSet (fun p => fwdHull (fun s : ℝ => W₀ s.toNNReal p.2) ((τ p).untopD 0 : ℝ≥0)) (fun p => h p.1) E

/-- **Aux. lemma 54 for general words from the locality on the record extension** (every `κ > 0`). -/
theorem stoppedHullExtendRStatement_of_locality {κ : ℝ} (hκ : 0 < κ) (hL : ExtLocalityStatement.{u} κ) :
    StoppedHullExtendRStatement.{u} κ := by
  classical
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV hreg
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, href⟩ :=
    WholeFieldStopped.exists_isFamilyRef.{u} (ρL := ρL) (ρR := ρR) hκ hF
  have hC₀ := href.isOptionalHullCoupling hκ
  have hlaw := map_recOfA_eq_reference hκ hF hRm hRg hSC hV hreg hC₀
  have hSC' := hSC
  obtain ⟨hEv, hcont, hh, hgff, hX, -⟩ := hSC'
  have hX₀ := IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  have hY₂ : Measurable (killedHistory W₀ VL₀ VR₀ (ruleStop R W₀ VL₀ VR₀ ζ₀)) :=
    measurable_killedHistory (isMeasurableKilledDriving_of_le hX₀
      ((hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)) (ruleStop_le R))
  obtain ⟨E, hEp, hE⟩ := exists_isRecExt (isMeasHull_recHull ρL ρR xL xR) hh (measurable_killedHistory hX)
    hC₀.2.1 hY₂ hlaw
  have hE' := hE
  obtain ⟨hfst, hsnd, -, -, hrm, κ₀, hκ₀, hEeq⟩ := hE'
  -- the coupling on `E`
  have hEv' := IsIntegratedSLEEvolution.comap measurable_snd hsnd href.1
  have hgff' : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ (p : Ω × Ω₀) => h p.1 φ - ∫ z, u₀ z * φ z) E := by
    intro u₀ hu₀
    have h1 := hgff u₀ hu₀
    rw [← hfst] at h1
    exact Restart.isZBGFFProcess_comp measurable_fst h1
  have hCE : IsOptionalHullCoupling κ xL xR ρL ρR E (filtrationComap 𝓕₀ measurable_snd)
      (fun t p => W₀ t p.2) (fun i t p => VL₀ i t p.2) (fun j t p => VR₀ j t p.2) (fun t p => B₀ t p.2)
      (fun p => ζ₀ p.2) (fun p => h p.1) :=
    isOptionalHullCoupling_of_dyadic hEv' (hh.comp measurable_fst) hgff'
      (bheProc κ ρL ρR (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2) (fun j t p => VR₀ j t p.2))
      (fun p s => isBoundedHarmonicExtension_bheProc p s)
      (fun hXE => isDyadicSampled_ext hκ hSC href hRm hRg hE hXE)
      (fun hXE τ hτ hτζ => hL xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B V h hSC hV hreg P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀
        href E hE hXE τ hτ hτζ)
  -- the agreement through the stop
  have hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (dState W VL VR ω) (Iic T)) ∧
      dState W VL VR ω 0 = initVal xL xR := by
    filter_upwards [hEv.ae_path, hcont] with ω hp hcω
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, hcω, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hc₀ : ∀ᵐ ω₀ ∂P₀, ContinuousOn (dState W₀ VL₀ VR₀ ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀} ∧
      dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR := by
    filter_upwards [hC₀.1.isSLEEvolutionUpTo.ae_path] with ω₀ hp
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hag := hE.ae_agree hc hc₀ (ruleStop_le R)
  refine ⟨Ω₀, mΩ₀, κ₀.comap _ hrm, inferInstance, filtrationComap 𝓕₀ measurable_snd, fun t p => W₀ t p.2,
    fun i t p => VL₀ i t p.2, fun j t p => VR₀ j t p.2, fun t p => B₀ t p.2, fun p => ζ₀ p.2, ?_, ?_⟩
  · rw [← hEeq]; exact hCE
  · rw [← hEeq]
    filter_upwards [hag] with p ⟨hVV, hst⟩
    refine ⟨hVV ▸ ruleStop_le R p.2, fun t htV htζ => ?_⟩
    have e := (hst t htV htζ).symm
    simp only [dState, Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    exact ⟨e1, fun i => congrFun e2 i, fun j => congrFun e3 j⟩

end Aux54

end Restart

end InteractingSLE
