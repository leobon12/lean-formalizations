/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSel2
import InteractingSLE.Spec.Sec7.ContinuityProb3Lift

/-!
# §7.4, Aux. lemma 122: determining the integer in a coherent pocket word

Packet PROVE-STRIPSYS4. Specification §7.4.1, Aux. lemma 122 and its proof (`source/spec/p385-432.md` L103–L139,
pp. 389–391).

* **Conditioning on a time-zero event.** "Work on the time-zero event `{d = 2πnχ}`. […] The shifted harmonic
  functions are continuous local martingales on this time-zero event." For an event `A ∈ 𝓕₀` of positive probability
  the processes restricted to the subtype `A`, with the conditional law `condSub P A` and the filtration `subFilt 𝓕 A`
  (the trace of `𝓕` on `A`), keep their martingale and local-martingale properties (`martingale_sub`,
  `isLocalMartingaleBefore_sub`).
* **Aux. lemma 122** (`ae_phase_eq_zero`): the phase is constant (`phase_eq_of_pos`), measurable at time `0` by the
  right continuity of the filtration, and every nonzero value is excluded on its time-zero event by
  `false_of_couplingMean_of_opposite` applied on the subtype to the shifted word (PS9.2)–(PS9.3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSel

open Aux117 MartChar

/-! ### Conditioning on an event, as a subtype -/

section Sub

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {A : Set Ω}

/-- The conditional law given `A`, on the subtype `A`: `P(· ∩ A)/P(A)` read on `A`. -/
def condSub (P : Measure Ω) (A : Set Ω) : Measure A := (P A)⁻¹ • P.comap Subtype.val

/-- The trace of the filtration `𝓕` on the subtype `A`. -/
def subFilt (𝓕 : Filtration ℝ≥0 mΩ) (A : Set Ω) : Filtration ℝ≥0 (inferInstance : MeasurableSpace A) :=
  RandRestart.comapFiltration 𝓕 Subtype.val measurable_subtype_coe

theorem condSub_apply (hA : MeasurableSet A) (s : Set A) : condSub P A s = (P A)⁻¹ * P (Subtype.val '' s) := by
  rw [condSub, Measure.smul_apply, smul_eq_mul, comap_subtype_coe_apply hA]

theorem isProbabilityMeasure_condSub [IsFiniteMeasure P] (hA : MeasurableSet A) (h0 : P A ≠ 0) :
    IsProbabilityMeasure (condSub P A) := by
  constructor
  rw [condSub_apply hA, image_univ, Subtype.range_coe]
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top P A)

/-- A `P`-almost sure property holds `condSub P A`-almost surely. -/
theorem ae_condSub_of_ae (hA : MeasurableSet A) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ (ω : A) ∂(condSub P A), p ω := by
  rw [ae_iff] at h ⊢
  rw [condSub_apply hA]
  refine mul_eq_zero_of_right _ (measure_mono_null (μ := P) ?_ h)
  rintro _ ⟨ω, hω, rfl⟩
  exact hω

theorem stronglyAdapted_sub {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓕 X) :
    StronglyAdapted (subFilt 𝓕 A) fun t (ω : A) => X t ω := fun t =>
  (hX t).comp_measurable (Measurable.of_comap_le le_rfl)

theorem isStoppingTime_sub {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) :
    IsStoppingTime (subFilt 𝓕 A) fun ω : A => σ ω := fun i => ⟨_, hσ i, rfl⟩

/-- Set integrals over a trace event under the comapped measure. -/
theorem setIntegral_comap_subtype (hA : MeasurableSet A) {s : Set Ω} (hs : MeasurableSet s) (g : Ω → ℝ) :
    ∫ ω in (Subtype.val ⁻¹' s : Set A), g ↑ω ∂(P.comap Subtype.val) = ∫ ω in s ∩ A, g ω ∂P := by
  rw [← integral_indicator (measurable_subtype_coe hs), ← integral_indicator (hs.inter hA)]
  have e : (Subtype.val ⁻¹' s).indicator (fun ω : A => g (ω : Ω)) = fun ω : A => s.indicator g (ω : Ω) := by
    funext ω
    by_cases h : (ω : Ω) ∈ s <;> simp [h]
  rw [e, integral_subtype_comap hA, ← integral_indicator hA]
  congr 1
  funext ω
  by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ A <;> simp [h1, h2]

/-- **A martingale stays a martingale under the conditional law given an event of `𝓕₀`.** -/
theorem martingale_sub [IsFiniteMeasure P] (hA0 : MeasurableSet[𝓕 0] A) (h0 : P A ≠ 0) {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) : Martingale (fun t (ω : A) => X t ω) (subFilt 𝓕 A) (condSub P A) := by
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  have hint : ∀ t, Integrable (fun ω : A => X t ω) (condSub P A) := fun t => by
    have h := (integrableOn_iff_comap_subtypeVal hA).1 ((hX.integrable t).integrableOn (s := A))
    exact h.smul_measure (ENNReal.inv_ne_top.2 h0)
  refine ⟨stronglyAdapted_sub hX.1, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((subFilt 𝓕 A).le i) (hint j)
    (fun s _ _ => (hint i).integrableOn) (fun s hs _ => ?_)
    ((stronglyAdapted_sub hX.1 i).aestronglyMeasurable)).symm
  obtain ⟨s', hs', rfl⟩ := hs
  have hs'A : MeasurableSet[𝓕 i] (s' ∩ A) := hs'.inter (𝓕.mono (zero_le : (0 : ℝ≥0) ≤ i) _ hA0)
  simp only [condSub, Measure.restrict_smul, integral_smul_measure]
  rw [setIntegral_comap_subtype hA (𝓕.le i _ hs'), setIntegral_comap_subtype hA (𝓕.le i _ hs'),
    hX.setIntegral_eq hij hs'A]


/-- **A local martingale before `ζ` stays one under the conditional law given an event of `𝓕₀`.** -/
theorem isLocalMartingaleBefore_sub [IsFiniteMeasure P] (hA0 : MeasurableSet[𝓕 0] A) (h0 : P A ≠ 0)
    {ζ : Ω → WithTop ℝ≥0} {X : ℝ≥0 → Ω → ℝ} (hX : IsLocalMartingaleBefore 𝓕 P ζ X) :
    IsLocalMartingaleBefore (subFilt 𝓕 A) (condSub P A) (fun ω : A => ζ ω) fun t (ω : A) => X t ω := by
  obtain ⟨σ, hσ, hσζ, hae, hmart⟩ := hX
  exact ⟨fun n (ω : A) => σ n ω, fun n => isStoppingTime_sub (hσ n), fun n ω => hσζ n ω,
    ae_condSub_of_ae (𝓕.le 0 _ hA0) hae, fun n => martingale_sub hA0 h0 (hmart n)⟩

/-- A local martingale minus a constant is a local martingale. -/
theorem isLocalMartingaleBefore_sub_const {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'}
    [IsFiniteMeasure Q] {𝓖 : Filtration ℝ≥0 m'} {ζ : Ω' → WithTop ℝ≥0} {X Y : ℝ≥0 → Ω' → ℝ} (c : ℝ)
    (hX : IsLocalMartingaleBefore 𝓖 Q ζ X) (hY : ∀ t ω, Y t ω = X t ω - c) : IsLocalMartingaleBefore 𝓖 Q ζ Y := by
  obtain ⟨σ, hσ, hσζ, hae, hmart⟩ := hX
  refine ⟨σ, hσ, hσζ, hae, fun n => ?_⟩
  have e : stoppedProcess Y (σ n) = stoppedProcess X (σ n) - fun _ _ => c := by
    funext t ω
    simp only [stoppedProcess, hY, Pi.sub_apply]
  rw [e]
  exact (hmart n).sub (martingale_const 𝓖 Q c)

end Sub


/-! ### Aux. lemma 122 -/

section Main

/-- The lattice spacing `2πχ` of Aux. lemma 122, with `χ = −χ(k) = √k/2 − 2/√k`. -/
def phaseStep (k : ℝ) : ℝ := 2 * Real.pi * -QuantumZipper.chiC k

theorem phaseStep_div {k : ℝ} (hk : 0 < k) : phaseStep k / (Real.pi / Real.sqrt k) = 2 * (k / 2 - 2) := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hss : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk.le
  simp only [phaseStep, QuantumZipper.chiC]
  field_simp
  rw [Real.sq_sqrt hk.le]
  ring

theorem phaseStep_ne_zero {k : ℝ} (hk : 4 < k) : phaseStep k ≠ 0 := by
  have hk0 : 0 < k := by linarith
  intro h
  have := phaseStep_div hk0
  rw [h, zero_div] at this
  linarith

/-- **(PS9.3)**: for a nonzero integer `n` the shifted seed parameters `a = r_L + 2An + 2`, `b = r_R − 2An + 2` have
opposite signs when `r_L, r_R ∈ (−2, 2A − 2)`, `A > 0`. -/
theorem opposite_of_ne_zero {A rL rR : ℝ} (hA : 0 < A) (hrL : -2 < rL) (hrL' : rL < 2 * A - 2) (hrR : -2 < rR)
    (hrR' : rR < 2 * A - 2) {n : ℤ} (hn : n ≠ 0) :
    (0 < rL + n * (2 * A) + 2 ∧ rR - n * (2 * A) + 2 < 0) ∨ (0 < rR - n * (2 * A) + 2 ∧ rL + n * (2 * A) + 2 < 0) := by
  rcases lt_or_gt_of_ne hn with h | h
  · have h' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 h
    right
    constructor <;> nlinarith
  · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    left
    constructor <;> nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

/-- An event measurable at every positive time is measurable at time `0` in a right-continuous filtration. -/
theorem measurableSet_zero_of_forall_pos [𝓕.IsRightContinuous] {A : Set Ω}
    (hA : ∀ j : ℝ≥0, 0 < j → MeasurableSet[𝓕 j] A) : MeasurableSet[𝓕 0] A := by
  refine Filtration.IsRightContinuous.RC (𝓕 := 𝓕) 0 _ ?_
  have hne : (𝓝[>] (0 : ℝ≥0)).NeBot := inferInstance
  rw [Filtration.rightCont_apply, ite_eq_left_of_eq_true _ _ (eq_true hne)]
  exact MeasurableSpace.measurableSet_iInf.2 fun j => MeasurableSpace.measurableSet_iInf.2 fun hj => hA j hj

/-- **Aux. lemma 122 (determining the integer in a coherent pocket word), for globally defined coordinates.** Put
`k > 4`, `Λ = π/√k`, `χ = −χ(k) > 0`, `A = k/2 − 2`. Let the driver `W` and the force coordinates of a finite word
(seeds `0⁻, 0⁺` at index `0`, weights `r_L = ρ^L_0`, `r_R = ρ^R_0 ∈ (−2, 2A − 2)`, other marks separated from `0`)
be continuous adapted processes with the deterministic properties of geometric force images (the hypotheses of the
landed Theorem 2.4 converse), in a right-continuous filtration. Assume the exact boundary description: at every time
the actual mean is the coupling mean (with the parameter-`k` derivative correction) of the bounded harmonic extension of
the word's heights with the exposed interval raised by one common phase `d_t ∈ 2πχℤ` (`phaseData`), adapted in `t`;
these means are local martingales before swallowing and continuous in time before swallowing (stated, like the
landed converse, for every choice of the extensions). Then, almost surely, `d_t = 0` for every `t > 0`. -/
theorem aux122 [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxLd : ∀ i : Fin nL, xL i.succ < 0) (hxRd : ∀ j : Fin nR, 0 < xR j.succ)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ t ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hda : ∀ t, Measurable[𝓕 t] (d t))
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T : ℝ), 0 ≤ T → z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T)) :
    (∀ᵐ ω ∂P, ∀ t, 0 < t → d t ω = 0) ∧ MeasurableSet[𝓕 0] {ω | d 1 ω = 0} ∧ P {ω | d 1 ω = 0} = 1 ∧
      (∀ ω ∈ {ω | d 1 ω = 0}, ∀ t, 0 < t → d t ω = 0) ∧
      IsIntegratedSLEEvolution k xL xR ρL ρR (condSub P {ω | d 1 ω = 0}) (subFilt 𝓕 {ω | d 1 ω = 0})
        (fun t (ω : {ω | d 1 ω = 0}) => W t ω) (fun i t (ω : {ω | d 1 ω = 0}) => VL i t ω)
        (fun j t (ω : {ω | d 1 ω = 0}) => VR j t ω)
        (fun t ω => martProc (jointρ ρL ρR) (fun t (ω : {ω | d 1 ω = 0}) => W t ω)
          (jointV (fun i t (ω : {ω | d 1 ω = 0}) => VL i t ω) fun j t (ω : {ω | d 1 ω = 0}) => VR j t ω) t ω /
            Real.sqrt k)
        (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) := by
  have hk0 : 0 < k := by linarith
  have hA : 0 < k / 2 - 2 := by linarith
  have hvL : ∀ ω t, VL 0 t ω - W t ω ≤ 0 := fun ω t => sub_nonpos.2 (hordL ω t 0)
  have hvR : ∀ ω t, 0 ≤ VR 0 t ω - W t ω := fun ω t => sub_nonneg.2 (hordR ω t 0)
  -- the natural extensions of the phase-shifted data
  set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt k (shiftL k ρL (d t ω)) (shiftR k ρR (d t ω)) (W t ω)
    (fun i => VL i t ω) (fun j => VR j t ω) ξ + d t ω with hU₀def
  have hU₀ : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₀ ω t) := fun ω t =>
    isBoundedHarmonicExtension_unshift hk0 (hvL ω t) (hvR ω t)
      (isBoundedHarmonicExtension_meanExt k _ _ (W t ω) _ _)
  -- the phase is constant on `(0, ∞)`, along every path
  have hconst : ∀ ω (s t : ℝ≥0), 0 < s → 0 < t → d s ω = d t ω := fun ω s t hs ht =>
    phase_eq_of_pos (phaseStep_ne_zero hk) (hWc ω) (fun i => (hpathL ω i).1) (fun j => (hpathR ω j).1)
      (hordL ω) (hordR ω) (hantiL ω 0) (hmonoR ω 0) (hpathL ω 0).2.2.2 (fun t ht => hd t ω ht) (hU₀ ω)
      (hcont U₀ hU₀ ω) hs ht
  -- the time-zero events
  set A : ℤ → Set Ω := fun n => {ω | d 1 ω = n * phaseStep k} with hAdef
  have hA0 : ∀ n, MeasurableSet[𝓕 0] (A n) := fun n => by
    refine measurableSet_zero_of_forall_pos fun j hj => ?_
    have e : A n = d j ⁻¹' {(n : ℝ) * phaseStep k} := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_preimage, mem_singleton_iff, hconst ω 1 j one_pos hj]
    rw [e]
    exact hda j (measurableSet_singleton _)
  -- on each time-zero event of positive probability the shifted explicit means are local martingales
  have hsub : ∀ n : ℤ, P (A n) ≠ 0 → ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 (A n)) (condSub P (A n))
        (fun ω : A n => (QuantumZipper.swallowTime (wpath (fun t (ω : A n) => W t ω) ω) z : WithTop ℝ≥0))
        (coupProc k (shiftL k ρL (n * phaseStep k)) (shiftR k ρR (n * phaseStep k)) (fun t (ω : A n) => W t ω)
          (fun i t (ω : A n) => VL i t ω) (fun j t (ω : A n) => VR j t ω) z) := by
    intro n h0
    have hQ : IsProbabilityMeasure (condSub P (A n)) := isProbabilityMeasure_condSub (𝓕.le 0 _ (hA0 n)) h0
    set c : ℝ := n * phaseStep k with hc
    have hdA : ∀ ω ∈ A n, ∀ t : ℝ≥0, 0 < t → d t ω = c := fun ω hω t ht => by
      rw [← hconst ω 1 t one_pos ht]
      exact hω
    -- an extension equal to the shifted canonical one plus `c` on `A n`
    set U₁ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if ω ∈ A n then (fun ξ => meanExt k (shiftL k ρL c) (shiftR k ρR c)
      (W t ω) (fun i => VL i t ω) (fun j => VR j t ω) ξ + c) else U₀ ω t with hU₁def
    have hU₁ : ∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₁ ω t) := by
      intro ω t
      by_cases hω : ω ∈ A n
      · simp only [hU₁def, hω, ↓reduceIte]
        have hext := isBoundedHarmonicExtension_unshift (c := c) hk0 (hvL ω t) (hvR ω t)
          (isBoundedHarmonicExtension_meanExt k (shiftL k ρL c) (shiftR k ρR c) (W t ω) (fun i => VL i t ω)
            (fun j => VR j t ω))
        rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0t | h0t
        · subst h0t
          refine isBoundedHarmonicExtension_congr_data hext fun x _ => ?_
          simp only [phaseData, hVL0, hVR0, hW0, hxL, hxR, sub_self, Ioo_self, indicator_empty,
            mul_zero]
        · rwa [hdA ω hω t h0t]
      · simp only [hU₁def, hω, ↓reduceIte]
        exact hU₀ ω t
    intro z hz
    have h1 := isLocalMartingaleBefore_sub (hA0 n) h0 (hmart U₁ hU₁ z hz)
    refine isLocalMartingaleBefore_sub_const c h1 fun t ω => ?_
    have hω : (ω : Ω) ∈ A n := ω.2
    simp only [coupProc, hU₁def, hω, ↓reduceIte]
    rw [← couplingMean_sub_const]
    simp only [add_sub_cancel_right]
    rfl
  -- every nonzero phase is excluded (Aux. lemmas 117 and 104 on the subtype)
  have hnull : ∀ n : ℤ, n ≠ 0 → P (A n) = 0 := by
    intro n hn
    by_contra h0
    have hAm : MeasurableSet (A n) := 𝓕.le 0 _ (hA0 n)
    have hQ : IsProbabilityMeasure (condSub P (A n)) := isProbabilityMeasure_condSub hAm h0
    set c : ℝ := n * phaseStep k with hc
    have hcΛ : c / (Real.pi / Real.sqrt k) = n * (2 * (k / 2 - 2)) := by
      rw [hc, mul_div_assoc, phaseStep_div hk0]
    have hab := opposite_of_ne_zero hA hrL hrL' hrR hrR' hn
    rw [← hcΛ] at hab
    refine false_of_couplingMean_of_opposite (P := condSub P (A n)) (𝓕 := subFilt 𝓕 (A n)) hk0
      (ρL := shiftL k ρL c) (ρR := shiftR k ρR c) (W := fun t (ω : A n) => W t ω)
      (VL := fun i t (ω : A n) => VL i t ω) (VR := fun j t (ω : A n) => VR j t ω) hxL hxR hxLd hxRd ?_
      (fun ω => hW0 ω) (fun i ω => hVL0 i ω) (fun i ω => hVR0 i ω) (fun ω => hWc ω) (stronglyAdapted_sub hWa)
      (fun i => stronglyAdapted_sub (hVLa i)) (fun i => stronglyAdapted_sub (hVRa i)) (fun ω => hordL ω)
      (fun ω => hordR ω) (fun ω => hpathL ω) (fun ω => hpathR ω) (fun ω => hantiL ω) (fun ω => hmonoR ω)
      (fun ω => hidxL ω) (fun ω => hidxR ω) (fun ω => hmergeL ω) (fun ω => hmergeR ω) (fun ω => hsep ω)
      (hsub n h0)
    simp only [shiftL_zero, shiftR_zero]
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  -- conclusion
  have hall : ∀ᵐ ω ∂P, ∀ n : ℤ, n ≠ 0 → ω ∉ A n :=
    ae_all_iff.2 fun n => by
      by_cases hn : n = 0
      · exact Eventually.of_forall fun ω h => absurd hn h
      · exact (measure_eq_zero_iff_ae_notMem.1 (hnull n hn)).mono fun ω h _ => h
  have hae : ∀ᵐ ω ∂P, ω ∈ A 0 := by
    filter_upwards [hall] with ω hω
    obtain ⟨n, hn⟩ := hd 1 ω one_pos
    have hn0 : n = 0 := by
      by_contra hne
      exact hω n hne hn
    show d 1 ω = ((0 : ℤ) : ℝ) * phaseStep k
    rw [hn, hn0]
  have eA0 : A 0 = {ω | d 1 ω = 0} := by
    ext ω
    simp only [hAdef, mem_ofPred_eq, Int.cast_zero, zero_mul]
  have hgood : ∀ ω ∈ {ω | d 1 ω = 0}, ∀ t, 0 < t → d t ω = 0 := fun ω hω t ht => by
    rw [hconst ω t 1 ht one_pos]
    exact hω
  have hP1 : P (A 0) = 1 := by
    rw [← prob_compl_eq_zero_iff (𝓕.le 0 _ (hA0 0))]
    exact measure_eq_zero_iff_ae_notMem.2 (hae.mono fun ω h h' => h' h)
  refine ⟨hae.mono fun ω h => hgood ω (eA0 ▸ h), eA0 ▸ hA0 0, eA0 ▸ hP1, hgood, ?_⟩
  -- the canonical evolution on the full-measure time-zero event
  have h0 : P (A 0) ≠ 0 := by rw [hP1]; exact one_ne_zero
  have hQ : IsProbabilityMeasure (condSub P (A 0)) := isProbabilityMeasure_condSub (𝓕.le 0 _ (hA0 0)) h0
  have hs := hsub 0 h0
  simp only [Int.cast_zero, zero_mul, shiftL_zero_eq, shiftR_zero_eq] at hs
  have hE := isIntegratedSLEEvolution_of_coupProc (P := condSub P (A 0)) (𝓕 := subFilt 𝓕 (A 0)) hk0
    (ρL := ρL) (ρR := ρR) (W := fun t (ω : A 0) => W t ω)
    (VL := fun i t (ω : A 0) => VL i t ω) (VR := fun j t (ω : A 0) => VR j t ω)
    (fun ω => hW0 ω) (fun i ω => hVL0 i ω) (fun i ω => hVR0 i ω) (fun ω => hWc ω) (stronglyAdapted_sub hWa)
    (fun i => stronglyAdapted_sub (hVLa i)) (fun i => stronglyAdapted_sub (hVRa i)) (fun ω => hordL ω)
    (fun ω => hordR ω) (fun ω => hpathL ω) (fun ω => hpathR ω) (fun ω => hantiL ω) (fun ω => hmonoR ω)
    (fun ω => hidxL ω) (fun ω => hidxR ω) (fun ω => hmergeL ω) (fun ω => hmergeR ω) (fun ω => hsep ω) hs
  rw [← eA0]
  exact hE

/-- **Aux. lemma 122, the phase is zero**: under the hypotheses of `aux122`, almost surely `d_t = 0` for every
`t > 0`. -/
theorem ae_phase_eq_zero [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxLd : ∀ i : Fin nL, xL i.succ < 0) (hxRd : ∀ j : Fin nR, 0 < xR j.succ)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ t ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hda : ∀ t, Measurable[𝓕 t] (d t))
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T : ℝ), 0 ≤ T → z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t, 0 < t → d t ω = 0 :=
  (aux122 hk hxL hxR hxLd hxRd hrL hrL' hrR hrR' hW0 hVL0 hVR0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hantiL
    hmonoR hidxL hidxR hmergeL hmergeR hsep hd hda hmart hcont).1

end Main

end PhaseSel

end Sec7

end InteractingSLE
