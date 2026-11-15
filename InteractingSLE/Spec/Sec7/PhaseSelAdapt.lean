/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFullMain

/-!
# §7.4, Aux. lemma 122: the phase is adapted (measurability of the explicit means)

Packet PROVE-STRIPSYS6 (specification §7.4, Aux. lemma 122 and its proof, `source/spec/p385-432.md` L104–L131,
p. 390: "Equation (PS9.1) therefore makes `d_t` an adapted continuous function of `t > 0`").

PROVE-STRIPSYS5's `PhaseSelFull.aux122_before` assumes the phase `d` adapted (its extra hypothesis (A2), `hda`). The
source derives it from (PS9.1): `d_t = (M_t(z) − M⁰_t(z))/ω_t(z)` at a point `z` not yet swallowed, where `M` is the
actual mean (adapted before the localizing times of its local-martingale property), `M⁰` the canonical mean and `ω_t`
the harmonic measure of the exposed interval. This file proves the measurability of the explicit parts:

* `measurable_meanExt`: the explicit bounded harmonic extension of a word is jointly measurable in the driver, the
  force positions and the point;
* `measurable_coupProc_alive`, `measurable_phaseWindow_alive`: at a fixed time `j` and a fixed point `z ∈ ℍ`, the
  canonical coupling mean `coupProc` and the harmonic measure `ω_j(z)` of the exposed interval are `𝓕_j`-measurable on
  the alive event (`z` not swallowed by time `j`), for continuous adapted coordinates;
* `mem_aliveSet_iff`: the alive event is `{z ∉ K_j}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelAdapt

open MartChar

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### The explicit extension is measurable -/

theorem measurable_jumpExt_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : α → ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun p => Impl.jumpExt (f p) (g p) := by
  simp_rw [Impl.jumpExt_eq]
  exact measurable_const.sub ((Complex.measurable_arg.comp (hg.sub (Complex.measurable_ofReal.comp hf))).div_const _)

/-- **The explicit bounded harmonic extension of a word is jointly measurable** in the driver value, the force
positions and the point. -/
theorem measurable_meanExt (k : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {α : Type*} [MeasurableSpace α]
    {w : α → ℝ} {vL : α → Fin nL → ℝ} {vR : α → Fin nR → ℝ} {ξ : α → ℂ} (hw : Measurable w)
    (hvL : Measurable vL) (hvR : Measurable vR) (hξ : Measurable ξ) :
    Measurable fun p => meanExt k ρL ρR (w p) (vL p) (vR p) (ξ p) := by
  simp only [meanExt, Impl.forceExt]
  have h0 : Measurable fun p => Impl.jumpExt 0 (ξ p) := measurable_jumpExt_comp measurable_const hξ
  have hL : Measurable fun p => ∑ i, (Ito.weightWord ρL ρR).ρL i *
      (1 - Impl.jumpExt (min 0 (vL p i - w p)) (ξ p)) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_const.sub
      (measurable_jumpExt_comp (measurable_const.min (((measurable_pi_apply i).comp hvL).sub hw)) hξ))
  have hR : Measurable fun p => ∑ i, (Ito.weightWord ρL ρR).ρR i *
      Impl.jumpExt (max 0 (vR p i - w p)) (ξ p) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul
      (measurable_jumpExt_comp (measurable_const.max (((measurable_pi_apply i).comp hvR).sub hw)) hξ)
  exact measurable_const.mul ((((measurable_const.add (measurable_const.mul h0)).sub hL)).add hR)

/-! ### The alive event -/

variable {W : ℝ≥0 → Ω → ℝ}

theorem adaptedBefore_top_of_stronglyAdapted (hWa : StronglyAdapted 𝓕 W) :
    AdaptedBefore 𝓕 (fun _ => ⊤) W := by
  intro t A hA
  have he : {ω | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ W t ω ∈ A} = W t ⁻¹' A := by
    ext ω
    simp
  rw [he]
  exact hWa.adapted t hA

/-- The alive event at time `j` for the point `z ∈ ℍ`: `z` is not swallowed by time `j`. -/
theorem mem_aliveSet_iff (hWc : ∀ ω, Continuous fun t => W t ω) {z : ℂ} (hz : z ∈ H) (j : ℝ≥0) (ω : Ω) :
    ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j ↔ z ∈ H \ QuantumZipper.fwdHull (wpath W ω) j := by
  constructor
  · rintro ⟨-, -, u, hu⟩
    exact ⟨hz, Ito.notMem_fwdHull_of_isForwardSol (continuous_wpath hWc ω) hz j.coe_nonneg hu⟩
  · rintro ⟨-, hK⟩
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull j.coe_nonneg hz hK
    exact ⟨mem_univ _, ENNReal.coe_lt_top, u, hu⟩

theorem measurableSet_aliveSet_top (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, Continuous fun t => W t ω) {z : ℂ}
    (hz : z ∈ H) (j : ℝ≥0) : MeasurableSet[𝓕 j] (Ito.aliveSet W (fun _ => ⊤) univ z j) :=
  Ito.measurableSet_aliveSet (adaptedBefore_top_of_stronglyAdapted hWa) (fun ω _ => (hWc ω).continuousOn)
    (@MeasurableSet.univ Ω (𝓕 0)) hz j

/-! ### The canonical mean and the harmonic measure at a fixed time -/

variable {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

open scoped Classical in
/-- **The canonical coupling mean is adapted on the alive event**: at a fixed time `j` and a fixed `z ∈ ℍ`, the
explicit mean `coupProc` (zero off the alive event) is `𝓕_j`-measurable. -/
theorem measurable_coupProc_alive (k : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hWc : ∀ ω, Continuous fun t => W t ω) {z : ℂ} (hz : z ∈ H) (j : ℝ≥0) :
    Measurable[𝓕 j] fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
      coupProc k ρL ρR W VL VR z j ω else 0 := by
  classical
  have hAB := adaptedBefore_top_of_stronglyAdapted hWa
  have hF := Ito.measurable_fwdMap_alive (𝓖 := 𝓕) hAB (fun ω _ => (hWc ω).continuousOn)
    (@MeasurableSet.univ Ω (𝓕 0)) (z := z) hz j
  have hL := Ito.measurable_logDerivFwd_alive (𝓖 := 𝓕) hAB (fun ω _ => (hWc ω).continuousOn)
    (@MeasurableSet.univ Ω (𝓕 0)) (z := z) hz j
  have h1 : Measurable[𝓕 j] fun ω => W j ω := (hWa j).measurable
  have h2 : Measurable[𝓕 j] fun ω => fun i => VL i j ω :=
    (@measurable_pi_iff Ω (Fin nL) _ (𝓕 j) _ _).2 fun i => (hVLa i j).measurable
  have h3 : Measurable[𝓕 j] fun ω => fun i => VR i j ω :=
    (@measurable_pi_iff Ω (Fin nR) _ (𝓕 j) _ _).2 fun i => (hVRa i j).measurable
  have hM := @measurable_meanExt nL nR k ρL ρR Ω (𝓕 j) _ _ _ _ h1 h2 h3 hF
  have hI : Measurable[𝓕 j] fun ω => QuantumZipper.chiC k * (if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
      QuantumZipper.logDerivFwd (Ito.rpath fun x => W x ω) (j : ℝ) z else 0).im :=
    measurable_const.mul (Complex.measurable_im.comp hL)
  have hG := hM.sub hI
  have e : (fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then coupProc k ρL ρR W VL VR z j ω else 0) =
      fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
        (meanExt k ρL ρR (W j ω) (fun i => VL i j ω) (fun i => VR i j ω)
          (if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
            QuantumZipper.fwdMap (Ito.rpath fun x => W x ω) (j : ℝ) z else 0) -
        QuantumZipper.chiC k * (if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
          QuantumZipper.logDerivFwd (Ito.rpath fun x => W x ω) (j : ℝ) z else 0).im) else 0 := by
    funext ω
    by_cases hω : ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j
    · simp only [hω, ↓reduceIte, coupProc, couplingMean]
      rfl
    · simp only [hω, ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurableSet_aliveSet_top hWa hWc hz j) hG measurable_const

open scoped Classical in
/-- **The harmonic measure of the exposed interval is adapted on the alive event**: at a fixed time `j` and a fixed
`z ∈ ℍ`, `ω_j(z) = phaseWindow (V⁻_j − W_j) (V⁺_j − W_j) (f_j(z))` (zero off the alive event) is
`𝓕_j`-measurable. -/
theorem measurable_phaseWindow_alive {VL0 VR0 : ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓕 W)
    (hVLa : StronglyAdapted 𝓕 VL0) (hVRa : StronglyAdapted 𝓕 VR0)
    (hWc : ∀ ω, Continuous fun t => W t ω) {z : ℂ} (hz : z ∈ H) (j : ℝ≥0) :
    Measurable[𝓕 j] fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
      phaseWindow (VL0 j ω - W j ω) (VR0 j ω - W j ω) (QuantumZipper.fwdMap (wpath W ω) j z) else 0 := by
  classical
  have hAB := adaptedBefore_top_of_stronglyAdapted hWa
  have hF := Ito.measurable_fwdMap_alive (𝓖 := 𝓕) hAB (fun ω _ => (hWc ω).continuousOn)
    (@MeasurableSet.univ Ω (𝓕 0)) (z := z) hz j
  set F : Ω → ℂ := fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
    QuantumZipper.fwdMap (Ito.rpath fun x => W x ω) (j : ℝ) z else 0 with hFdef
  have harg : ∀ {a : Ω → ℝ}, Measurable[𝓕 j] a → Measurable[𝓕 j] fun ω => Complex.arg (F ω - (a ω : ℂ)) :=
    fun {a} ha => Complex.measurable_arg.comp (hF.sub (Complex.measurable_ofReal.comp ha))
  have hG : Measurable[𝓕 j] fun ω => phaseWindow (VL0 j ω - W j ω) (VR0 j ω - W j ω) (F ω) := by
    simp only [phaseWindow]
    exact ((harg ((hVRa j).measurable.sub (hWa j).measurable)).sub
      (harg ((hVLa j).measurable.sub (hWa j).measurable))).div_const _
  have e : (fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
      phaseWindow (VL0 j ω - W j ω) (VR0 j ω - W j ω) (QuantumZipper.fwdMap (wpath W ω) j z) else 0) =
      fun ω => if ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j then
        phaseWindow (VL0 j ω - W j ω) (VR0 j ω - W j ω) (F ω) else 0 := by
    funext ω
    by_cases hω : ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z j
    · simp only [hω, ↓reduceIte, hFdef]
      rfl
    · simp only [hω, ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurableSet_aliveSet_top hWa hWc hz j) hG measurable_const

/-! ### The phase events -/

/-- The far points `i (m + 1)` used to read off the phase. -/
def zpt (m : ℕ) : ℂ := Complex.I * (((m : ℝ) + 1 : ℝ) : ℂ)

theorem zpt_mem (m : ℕ) : zpt m ∈ H := by
  show (0 : ℝ) < (zpt m).im
  simp only [zpt, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re,
    one_mul, zero_add]
  positivity

theorem norm_zpt (m : ℕ) : ‖zpt m‖ = (m : ℝ) + 1 := by
  rw [zpt, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- Every point not far out is eventually beaten by some `zpt m`: for a continuous driver and a time `j`, some far
point is not swallowed by time `j`. -/
theorem exists_zpt_alive {w : ℝ → ℝ} (hw : Continuous w) (j : ℝ≥0) :
    ∃ m : ℕ, zpt m ∈ H \ QuantumZipper.fwdHull w j := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := j)).exists_bound_of_continuousOn hw.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt (|K| + 3 * Real.sqrt j)
  refine ⟨m, mem_diff_fwdHull_of_norm hw j.coe_nonneg
    (fun r hr => (Real.norm_eq_abs _ ▸ hK r hr).trans (le_abs_self K)) (zpt_mem m) ?_⟩
  rw [norm_zpt]
  linarith

open PhaseSel in
/-- **The phase events are adapted (Aux. lemma 122, (A2))**: for continuous adapted coordinates whose phase-shifted
coupling means are local martingales before swallowing and before the stopping time `T`, there are events
`D c j ∈ 𝓕_j` (`j > 0` rational) contained in `{j < T, d_j = c}` and almost surely equal to it ("Equation (PS9.1)
therefore makes `d_t` an adapted continuous function of `t > 0`", p. 390). The events read the phase off (PS9.1) at
the far points `zpt m`, before the localizing times of their means. -/
theorem exists_phaseEvents {P : Measure Ω} {k : ℝ} (hk : 0 < k) {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T) {d : ℝ≥0 → Ω → ℝ}
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z)) :
    ∃ D : ℝ → ℚ → Set Ω,
      (∀ c (j : ℚ), MeasurableSet[𝓕 (j : ℝ).toNNReal] (D c j)) ∧
      (∀ c (j : ℚ) ω, 0 < j → ω ∈ D c j →
        (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω ∧ d (j : ℝ).toNNReal ω = c) ∧
      (∀ᵐ ω ∂P, ∀ c (j : ℚ), 0 < j → (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω →
        d (j : ℝ).toNNReal ω = c → ω ∈ D c j) := by
  classical
  have hvL : ∀ ω t, VL 0 t ω - W t ω ≤ 0 := fun ω t => sub_nonpos.2 (hordL ω t 0)
  have hvR : ∀ ω t, 0 ≤ VR 0 t ω - W t ω := fun ω t => sub_nonneg.2 (hordR ω t 0)
  -- the natural extensions of the phase-shifted data
  set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt k (shiftL k ρL (d t ω)) (shiftR k ρR (d t ω)) (W t ω)
    (fun i => VL i t ω) (fun j => VR j t ω) ξ + d t ω with hU₀def
  have hU₀ : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₀ ω t) := fun ω t =>
    isBoundedHarmonicExtension_unshift hk (hvL ω t) (hvR ω t)
      (isBoundedHarmonicExtension_meanExt k _ _ (W t ω) _ _)
  -- the localizing times at the far points
  set X : ℕ → ℝ≥0 → Ω → ℝ := fun m t ω => couplingMean k (wpath W ω) t (U₀ ω t) (zpt m) with hXdef
  have hloc : ∀ m : ℕ, ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ N, IsStoppingTime 𝓕 (σ N)) ∧
      (∀ N ω, σ N ω ≤ min (QuantumZipper.swallowTime (wpath W ω) (zpt m) : WithTop ℝ≥0) (T ω)) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) <
        min (QuantumZipper.swallowTime (wpath W ω) (zpt m) : WithTop ℝ≥0) (T ω) →
          ∀ᶠ N in atTop, (r : WithTop ℝ≥0) < σ N ω) ∧
      ∀ N, Martingale (stoppedProcess (X m) (σ N)) 𝓕 P := fun m => hmart U₀ hU₀ (zpt m) (zpt_mem m)
  choose σ hσst hσle hσae hσmart using hloc
  -- the explicit parts (zero off the alive event)
  set alive : ℕ → ℝ≥0 → Set Ω := fun m t => Ito.aliveSet W (fun _ => ⊤) univ (zpt m) t with halive
  set X₀ : ℕ → ℝ≥0 → Ω → ℝ := fun m t ω => if ω ∈ alive m t then coupProc k ρL ρR W VL VR (zpt m) t ω
    else 0 with hX₀def
  set pw : ℕ → ℝ≥0 → Ω → ℝ := fun m t ω => if ω ∈ alive m t then
    phaseWindow (VL 0 t ω - W t ω) (VR 0 t ω - W t ω) (QuantumZipper.fwdMap (wpath W ω) t (zpt m)) else 0
    with hpwdef
  set D : ℝ → ℚ → Set Ω := fun c j => {ω | (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω} ∩
    ⋃ m, ⋃ N, (alive m (j : ℝ).toNNReal ∩ {ω | (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < σ m N ω} ∩
      {ω | stoppedProcess (X m) (σ m N) (j : ℝ).toNNReal ω - X₀ m (j : ℝ).toNNReal ω =
        c * pw m (j : ℝ).toNNReal ω}) with hDdef
  -- (PS9.1) at a far point before its localizing time
  have hkey : ∀ m N ω (t : ℝ≥0), 0 < t → ω ∈ alive m t → (t : WithTop ℝ≥0) < σ m N ω →
      stoppedProcess (X m) (σ m N) t ω - X₀ m t ω = d t ω * pw m t ω ∧ 0 < pw m t ω := by
    intro m N ω t ht hal hσ
    have hz := (mem_aliveSet_iff hWc (zpt_mem m) t ω).1 hal
    have hf : QuantumZipper.fwdMap (wpath W ω) t (zpt m) ∈ H :=
      Ito.im_fwdMap_pos (continuous_wpath hWc ω) t.coe_nonneg hz ⟨t.coe_nonneg, le_rfl⟩
    have hsep : VL 0 t ω < VR 0 t ω :=
      seed_lt_seed (hantiL ω 0) (hmonoR ω 0) (fun s => hordL ω s 0) (fun s => hordR ω s 0) (hpathL ω 0).2.2.2 ht
    have hU : IsBoundedHarmonicExtension (phaseData k ρL ρR (fun i => VL i t ω - wpath W ω t)
        (fun j => VR j t ω - wpath W ω t) (d t ω))
        (forceJumpSet (fun i => VL i t ω - wpath W ω t) (fun j => VR j t ω - wpath W ω t)) (U₀ ω t) := by
      rw [wpath_coe]; exact hU₀ ω t
    have h := couplingMean_sub_couplingMean_eq (k := k) (ρL := ρL) (ρR := ρR) (w := wpath W ω) (t := (t : ℝ))
      (vL := fun i => VL i t ω) (vR := fun j => VR j t ω) (d := d t ω) hsep hU hf
    rw [wpath_coe] at h
    have hpw : pw m t ω = phaseWindow (VL 0 t ω - W t ω) (VR 0 t ω - W t ω)
        (QuantumZipper.fwdMap (wpath W ω) t (zpt m)) := by
      simp only [hpwdef, hal, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [stoppedProcess_eq_of_le hσ.le, hpw]
      simp only [hX₀def, hal, ↓reduceIte, hXdef, coupProc]
      exact h
    · rw [hpw]
      exact (phaseWindow_mem_Ioo (by linarith) hf).1
  refine ⟨D, fun c j => ?_, fun c j ω hj hω => ?_, ?_⟩
  · -- measurability
    set jn : ℝ≥0 := (j : ℝ).toNNReal
    have hgt : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 τ →
        MeasurableSet[𝓕 jn] {ω | (jn : WithTop ℝ≥0) < τ ω} := fun τ hτ => by
      have e : {ω | (jn : WithTop ℝ≥0) < τ ω} = {ω | τ ω ≤ jn}ᶜ := by
        ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
      rw [e]; exact (hτ jn).compl
    refine (hgt T hT).inter (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun N =>
      ((measurableSet_aliveSet_top hWa hWc (zpt_mem m) jn).inter (hgt _ (hσst m N))).inter ?_)
    have h1 : Measurable[𝓕 jn] (stoppedProcess (X m) (σ m N) jn) := ((hσmart m N).stronglyAdapted jn).measurable
    have h2 : Measurable[𝓕 jn] (X₀ m jn) :=
      measurable_coupProc_alive k ρL ρR hWa hVLa hVRa hWc (zpt_mem m) jn
    have h3 : Measurable[𝓕 jn] (pw m jn) :=
      measurable_phaseWindow_alive hWa (hVLa 0) (hVRa 0) hWc (zpt_mem m) jn
    exact measurableSet_eq_fun (h1.sub h2) (measurable_const.mul h3)
  · -- the events lie in `{j < T, d_j = c}`
    have hjn : 0 < (j : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hj)
    obtain ⟨hT', hU⟩ := hω
    obtain ⟨m, N, ⟨hal, hσ⟩, heq⟩ := by simpa only [mem_iUnion] using hU
    refine ⟨hT', ?_⟩
    obtain ⟨h1, h2⟩ := hkey m N ω _ hjn hal hσ
    have heq' : stoppedProcess (X m) (σ m N) (j : ℝ).toNNReal ω - X₀ m (j : ℝ).toNNReal ω =
        c * pw m (j : ℝ).toNNReal ω := heq
    rw [h1] at heq'
    exact mul_right_cancel₀ h2.ne' heq'
  · -- almost surely the events are all of `{j < T, d_j = c}`
    filter_upwards [ae_all_iff.2 hσae] with ω hω c j hj hjT hjd
    set jn : ℝ≥0 := (j : ℝ).toNNReal with hjndef
    have hjn : 0 < jn := Real.toNNReal_pos.2 (by exact_mod_cast hj)
    obtain ⟨m, hm⟩ := exists_zpt_alive (continuous_wpath hWc ω) jn
    have hsw : (jn : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) (zpt m) : WithTop ℝ≥0) := by
      have h := hm.2
      simp only [QuantumZipper.fwdHull, mem_ofPred_eq, not_and, not_le] at h
      have h' := h (zpt_mem m)
      rw [ENNReal.ofReal_coe_nnreal] at h'
      exact h'
    obtain ⟨N, hN⟩ := ((hω m jn (lt_min hsw hjT)).exists)
    have hal : ω ∈ alive m jn := (mem_aliveSet_iff hWc (zpt_mem m) jn ω).2 hm
    refine ⟨hjT, mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨N, ⟨hal, hN⟩, ?_⟩⟩⟩
    show stoppedProcess (X m) (σ m N) jn ω - X₀ m jn ω = c * pw m jn ω
    rw [(hkey m N ω jn hjn hal hN).1, hjd]

end PhaseSelAdapt

end Sec7

end InteractingSLE
