/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkov
import InteractingSLE.Spec.Sec7.Aux122DisintEvol
import InteractingSLE.Spec.Sec7.LocalExtGKernel

/-!
# The domain Markov step, part 2: transfers to the regular conditional law

Packet PROVE-DOMAINMARKOV. Tools for disintegrating a restarted coupling along `condExpKernel P 𝓔` (standard Borel
`Ω`), the kernel form of Aux. lemma 53:

* **`exists_ae_condExpKernel_agree`**: Aux. lemma 122
  (`Sec7.Aux122Disint.IsRandomWordEvolution.exists_ae_condExpKernel`)
  with **every** coordinate of the modified evolution (driver, marks, Brownian motion) equal to the given one off a
  null set on `F` (the landed statement records the driver only; the proof is the same);
* **`ae_setIntegral_condExpKernel_eq`**: a conditional identity `E[X | 𝓜] = Y` with `𝓔 ≤ 𝓜` gives, for every
  `𝓜`-event `A`, `∫_A X = ∫_A Y` under almost every kernel measure; `ae_forall_setIntegral_condExpKernel_eq`: the same
  simultaneously for a countable family of events;
* **`setIntegral_eq_of_isPiSystem`**: under one finite measure, an identity `∫_A X = ∫_A Y` on a π-system (and on
  `univ`) extends to the generated σ-algebra (Dynkin);
* `KernelRestartCouplingStatement` (**named input**, not proved here): Aux. lemma 53 in kernel form — under almost every
  conditional law given the stopped driving history `𝓓_T`, the restarted driving processes and the restarted field
  `restartField κ (h, K)` form an optional hull coupling of the current word `(V_T − W_T)(ω₀)`. By
  `isOptionalHullCoupling_of_dyadic` (`DomainMarkov.lean`) it reduces, at each kernel measure, to the restarted
  evolution (Aux. lemma 122: `exists_ae_condExpKernel_agree` with `Sec2.Restart.exists_restart`), the GFF law at time
  `0`, the dyadic protected-kernel law `IsDyadicSampled` (transferred from `LocalExt.isCouplingCharFun_restart` by
  `ae_forall_setIntegral_condExpKernel_eq` and `setIntegral_eq_of_isPiSystem`, then to all test functions through local
  Gaussian laws) and the locality of the restarted hulls (see `planning/handoffs/PROVE-DOMAINMARKOV.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

/-! ### Aux. lemma 122 with every coordinate recorded -/

section Disint

open Sec7.Aux122Disint

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
variable [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ}
  {nL nR : ℕ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Disintegration over the initial information, every coordinate recorded** (Aux. lemma 122, p. 391): the
modified driver, marks and Brownian motion agree with the given ones off a measurable null set `N` on `F`, and for
`P`-almost every `ω₀ ∈ F` they form an integrated `SLE_a(ΘL ω₀; ΘR ω₀)` evolution under `condExpKernel P 𝓔 ω₀`. -/
theorem exists_ae_condExpKernel_agree
    (h : IsRandomWordEvolution a P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ) :
    ∃ (N : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      MeasurableSet N ∧ P N = 0 ∧ (∀ ω, ω ∉ N → ω ∈ F → ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
        (∀ j, VR' j t ω = VR j t ω) ∧ B' t ω = B t ω) ∧
      ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
        IsIntegratedSLEEvolution a (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝓔 ω₀) 𝓖 W' VL' VR' B' ζ := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, hW, hVL, hVR, hpath⟩ := h
  have hgood : ∀ᵐ ω ∂P, (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) :=
    (hB.1.cont.and hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero).and hpath
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hoff : ∀ ω, ω ∉ N → (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  set X := wordData F W VL VR with hX
  have hF𝓕 : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] F := fun t => 𝓕.mono (by positivity) _ (h0 _ hF)
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := fun t => by
    have := hW t univ MeasurableSet.univ
    simpa using this
  have hkill : ∀ i t, Measurable[𝓕 t] (killAt ζ (X i) t) := by
    rintro (_ | i | j) t
    · exact measurable_killAt_onF hW (hF𝓕 t)
    · exact measurable_killAt_onF (hVL i) (hF𝓕 t)
    · exact measurable_killAt_onF (hVR j) (hF𝓕 t)
  have hS : DisintSetting P 𝓔 𝓕 B N ζ X :=
    ⟨h0, hB, hNm, hN0, fun ω hω => (hoff ω hω).1.1, fun ω hω => (hoff ω hω).1.2, hlt, hkill⟩
  have hXc : ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => X i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    intro ω hω i
    by_cases hωF : ω ∈ F
    · have hp := (hoff ω hω).2 hωF
      rcases i with _ | i | j
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.1
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.2.1 i
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.2.2.1 j
    · rcases i with _ | i | j <;> simp only [hX, wordData, onF_of_notMem hωF] <;> exact continuousOn_const
  have hle : 𝓔 ≤ mΩ := hS.le_mΩ
  refine ⟨N, dataFilt N ζ B X, zeroOn N (X none), fun i => zeroOn N (X (some (Sum.inl i))),
    fun j => zeroOn N (X (some (Sum.inr j))), zeroOn N B, hNm, hN0, ?_, ?_⟩
  · intro ω hω hωF t
    simp only [zeroOn_of_notMem hω, hX, wordData, onF_of_mem hωF, implies_true, and_self]
  filter_upwards [hS.ae_isFilteredBrownianReal, hS.ae_condExpKernel_N, ae_ae_condExpKernel_mem hle hF,
    ae_ae_condExpKernel_eq hle hΘL, ae_ae_condExpKernel_eq hle hΘR] with ω₀ hBr hνN hmemF hL hR hω₀F
  refine ⟨hBr, hS.dataMeas.adaptedBefore_zeroOn hXc none,
    fun i => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inl i)),
    fun j => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inr j)), ?_⟩
  filter_upwards [hmemF hω₀F, hL, hR, measure_eq_zero_iff_ae_notMem.1 hνN] with ω hωF hωL hωR hωN
  have hp := (hoff ω hωN).2 hωF
  rw [hωL, hωR] at hp
  have e1 : (fun t => zeroOn N (X none) t ω) = fun t => W t ω := funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e2 : (fun i t => zeroOn N (X (some (Sum.inl i))) t ω) = fun i t => VL i t ω := funext fun i => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e3 : (fun j t => zeroOn N (X (some (Sum.inr j))) t ω) = fun j t => VR j t ω := funext fun j => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e4 : (fun t => zeroOn N B t ω) = fun t => B t ω := funext fun t => zeroOn_of_notMem hωN t
  rw [e1, e2, e3, e4]
  exact hp


end Disint

/-! ### Conditional identities under the conditional law -/

section Transfer

variable {Ω : Type*} {𝓔 𝓜 𝓢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **Kernel transfer of a conditional identity.** If `E[X | 𝓜] = Y` almost surely and `𝓔 ≤ 𝓜`, then for every
`𝓜`-event `A`, for `P`-almost every `ω₀`, `∫_A X = ∫_A Y` under the conditional law `condExpKernel P 𝓔 ω₀`. -/
theorem ae_setIntegral_condExpKernel_eq [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (h𝓔𝓜 : 𝓔 ≤ 𝓜) (h𝓜 : 𝓜 ≤ mΩ) {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : Integrable Y P) (hXY : P[X | 𝓜] =ᵐ[P] Y) {A : Set Ω} (hA : MeasurableSet[𝓜] A) :
    ∀ᵐ ω₀ ∂P, ∫ ω in A, X ω ∂(condExpKernel P 𝓔 ω₀) = ∫ ω in A, Y ω ∂(condExpKernel P 𝓔 ω₀) := by
  have hAm : MeasurableSet A := h𝓜 _ hA
  have h1 := condExp_ae_eq_integral_condExpKernel (h𝓔𝓜.trans h𝓜) (hX.indicator hAm)
  have h2 := condExp_ae_eq_integral_condExpKernel (h𝓔𝓜.trans h𝓜) (hY.indicator hAm)
  have t1 : P[P[A.indicator X | 𝓜] | 𝓔] =ᵐ[P] P[A.indicator X | 𝓔] := condExp_condExp_of_le h𝓔𝓜 h𝓜
  have t2 : P[A.indicator X | 𝓜] =ᵐ[P] A.indicator (P[X | 𝓜]) := condExp_indicator hX hA
  have t3 : A.indicator (P[X | 𝓜]) =ᵐ[P] A.indicator Y := hXY.mono fun ω h => by
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, indicator_of_mem hω, h]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  have h3 : P[A.indicator X | 𝓔] =ᵐ[P] P[A.indicator Y | 𝓔] :=
    t1.symm.trans (condExp_congr_ae (t2.trans t3))
  filter_upwards [h1, h2, h3] with ω₀ e1 e2 e3
  rw [← integral_indicator hAm, ← integral_indicator hAm, ← e1, ← e2, e3]

/-- **Kernel transfer, a countable family of events at once.** -/
theorem ae_forall_setIntegral_condExpKernel_eq [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (h𝓔𝓜 : 𝓔 ≤ 𝓜) (h𝓜 : 𝓜 ≤ mΩ) {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : Integrable Y P) (hXY : P[X | 𝓜] =ᵐ[P] Y) {ι : Type*} [Countable ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet[𝓜] (A i)) :
    ∀ᵐ ω₀ ∂P, ∀ i, ∫ ω in A i, X ω ∂(condExpKernel P 𝓔 ω₀) = ∫ ω in A i, Y ω ∂(condExpKernel P 𝓔 ω₀) :=
  ae_all_iff.2 fun i => ae_setIntegral_condExpKernel_eq h𝓔𝓜 h𝓜 hX hY hXY (hA i)

/-- **Dynkin extension of a set-integral identity** under one finite measure: if `∫_A X = ∫_A Y` for every `A` in a
π-system generating `𝓢 ≤ mΩ` and for `A = univ`, then for every `A ∈ 𝓢`. -/
theorem setIntegral_eq_of_isPiSystem {ν : Measure Ω} {X Y : Ω → ℂ} (hX : Integrable X ν)
    (hY : Integrable Y ν) (h𝓢 : 𝓢 ≤ mΩ) {S : Set (Set Ω)}
    (hgen : 𝓢 = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) (huniv : ∫ ω, X ω ∂ν = ∫ ω, Y ω ∂ν)
    (hS : ∀ A ∈ S, ∫ ω in A, X ω ∂ν = ∫ ω in A, Y ω ∂ν) {A : Set Ω} (hA : MeasurableSet[𝓢] A) :
    ∫ ω in A, X ω ∂ν = ∫ ω in A, Y ω ∂ν := by
  induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic t ht => exact hS t ht
  | compl t htm ih =>
    have htm' : MeasurableSet t := h𝓢 _ htm
    have e1 := integral_add_compl htm' hX
    have e2 := integral_add_compl htm' hY
    linear_combination e1 - e2 - ih + huniv
  | iUnion f hfd hfm ih =>
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => h𝓢 _ (hfm i)
    rw [integral_iUnion hfm' hfd hX.integrableOn, integral_iUnion hfm' hfd hY.integrableOn]
    exact tsum_congr ih

end Transfer

/-! ### The named input: Aux. lemma 53 in kernel form -/

section Statement

open Sec5.Markov Sec2.Restart Sec7 LocalExt

universe u

/-- **Named input (not proved here): Aux. lemma 53 in kernel form**, the domain Markov property of the optional hull
specification (specification p. 245: "condition on the recorded driving history and map the active field and future
hulls by the centered map `f_τ = g_τ − W_τ` … Their conditional law again satisfies the original optional hull
specification, with the current force groups as initial data"). For a coupling on a standard Borel space, a finite
stopping time `T` of its driving filtration and a `𝓓_T`-measurable version `K` of the stopped history: for `P`-almost
every `ω₀` with `T ω₀ < ζ ω₀`, under `condExpKernel P 𝓓_T ω₀` some processes equal to the restarted driver and marks
before the restarted lifetime form, with the restarted field `restartField κ (h, K)`, an optional hull coupling of the
word `(V_T − W_T)(ω₀)` with the original weights. -/
def KernelRestartCouplingStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
    ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
      (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
      (K : Ω → DrivingHist nL nR), Measurable[hT.measurableSpace] K →
      (∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
    ∀ᵐ ω₀ ∂P, (T ω₀ : ℝ≥0∞) < ζ ω₀ →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
        IsOptionalHullCoupling κ (fun i => VL i (T ω₀) ω₀ - W (T ω₀) ω₀) (fun j => VR j (T ω₀) ω₀ - W (T ω₀) ω₀)
          ρL ρR (condExpKernel P hT.measurableSpace ω₀) 𝓕' W' VL' VR' B' ζ'
          (fun ω => restartField κ (h ω, K ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ζ' ω = restartLife ζ T ω ∧
          ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → W' t ω = restartDrv W T t ω ∧
            (∀ i, VL' i t ω = restartMark (VL i) W T t ω) ∧ ∀ j, VR' j t ω = restartMark (VR j) W T t ω

end Statement

end DomainMarkov

end Restart

end InteractingSLE
