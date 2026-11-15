/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71EChart
import InteractingSLE.Spec.Sec7.Lemma71EPrefix
import InteractingSLE.Spec.Sec7.Lemma71DTop

/-!
# Lemma 7.1's pocket curve without measurability requirements on the chart and the prefixes

Packet PROVE-LEMMA71E, item (3) assembled. PROVE-LEMMA71D reduced Lemma 7.1's trace reference to the named input
`Lemma71D.Lemma71PocketCurveConstStatement`, which asks for a filtration `𝓐`, the prefix adaptedness of the mapped
segment and the `𝓐₀`-measurability of the pocket chart (forward map, lift, domain events). This file replaces it by
`Lemma71PocketStatement`, in which none of these is required:

* the filtration is constructed: the **prefix filtration** of `𝓐₀` (the σ-algebra "retaining the complete outer
  curves") and the mapped segment (`prefixFiltrationOf`, `Lemma71EPrefix.lean`);
* the chart is only required **pathwise**: conformal onto `ℍ` from the pocket `C ω`, tending to `0` and `∞` along two
  approach sequences of the marked boundary points, normalized by the scale rule `|ψ(b)| = 1` at a base point `b`
  (the specification's "arbitrary rule", p. 222), with a continuous branch of `arg ψ′` as lift;
* what remains of measurability is primitive data of the outer curves: the pocket observed through closed balls, the
  indices of the approach sequences and of the base point, and the value of the lift at the base point
  (`𝓐₀`-measurable), and the original segment points `seg ω u` (measurable), with `γ ω u` the boundary value of
  `ψ` at `seg ω u`.

**Proof.** The measurable two-point chart `c₀` (`exists_measurable_twoPointChart`) agrees with the given chart up to a
positive factor (uniqueness) which the scale rule identifies as `|c₀.1 (b)|`, and their lifts differ by `2πn(ω)` with
`n` measurable (values at the base point). Hence the given chart is `𝓐₀`-measurable; the mapped positions are
measurable as boundary limits (`Restart.measurable_of_tendsto_nhdsWithin`); the prefix events are measurable
(`measurableSet_prefixEvent`), so the segment is prefix-adapted to the prefix filtration.

## Main results

* `Lemma71PocketStatement` (**named input**);
* **`lemma71PocketCurveConstStatement_of_pocket`**: `Lemma71PocketStatement → Lemma71D.Lemma71PocketCurveConstStatement`;
* `lemma71TraceReferenceStatement_of_pocket`: the composition with PROVE-LEMMA71D, C, B and PROVE-LEMMA71.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.Lemma71E

open MartChar Coupling Lemma71B Lemma71C Lemma71D

/-- The forward map of a conformal chart is a conformal bijection of its domain onto `ℍ`. -/
theorem isConformalBijection_fwd {c : Chart} (hc : c.IsConformal) : IsConformalBijection c.1 (c.dom : Set ℂ) H := by
  refine ⟨hc.differentiableOn_fwd, fun z hz => hc.fwd_mem hz, fun z₁ h₁ z₂ h₂ h => ?_, fun w hw => ?_⟩
  · rw [← hc.inv_fwd h₁, ← hc.inv_fwd h₂, h]
  · exact ⟨c.2.1 w, hc.inv_mem_dom hw, hc.2.2 w hw⟩

/-- A random function read at the point of a countable sequence with a measurable index, where the function is
measurable at each point of the sequence in indicator form and the point lies in the domain. -/
theorem measurable_at_seq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Zero β] {C : Ω → Set ℂ}
    {f : Ω → ℂ → β} {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N) (hNC : ∀ ω, e (N ω) ∈ C ω)
    (hf : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => f ω z)) : Measurable fun ω => f ω (e (N ω)) := by
  have hG : Measurable fun x : Ω × ℕ => {ω | e x.2 ∈ C ω}.indicator (fun ω => f ω (e x.2)) x.1 :=
    measurable_from_prod_countable_left fun j => hf (e j)
  have heq : (fun ω => f ω (e (N ω))) =
      fun ω => ({ω' | e (N ω) ∈ C ω'}.indicator (fun ω' => f ω' (e (N ω))) ω : β) := by
    funext ω
    exact (indicator_of_mem (s := {ω' | e (N ω) ∈ C ω'}) (hNC ω) (fun ω' => f ω' (e (N ω)))).symm
  rw [heq]
  exact hG.comp (measurable_id.prodMk hN)

/-- **Named input: the three-curve pocket data** (Specification §7.1, setup pp. 221–222; proof of Lemma 7.1,
pp. 223–225). Fix `0 < κ < 4` and angles `θ₁ < 0 < θ₂`. On the probability space of the three-curve construction:
* `𝓐₀ ≤ mΩ`, the σ-algebra of the complete outer curves;
* the pocket `C ω ⊆ ℍ` (open, connected, simply connected), with `𝓐₀`-measurable events `{closedBall z r ⊆ C ω}`;
* a dense sequence `e` and `𝓐₀`-measurable indices `Nx m`, `Ny m`, `Nb` of points of `C ω`: approach sequences of the
  marked boundary points `x₀`, `y₀`, and the base point of the scale rule;
* the pocket chart `c ω` (pathwise only): conformal with domain `C ω`, `ψ = (c ω).1 → 0` along the `x₀`-sequence and
  `→ ∞` along the `y₀`-sequence, `|ψ(b)| = 1` at the base point `b = e (Nb ω)`, lift a continuous branch of `arg ψ′`
  (`Im` of a derivative logarithm), whose value at the base point is `𝓐₀`-measurable (the inherited branch);
* the mapped segment `γ` (`IsSegCurve` for every `ω`), with `γ ω u` the boundary value of `ψ` at the original segment
  point `seg ω u ∈ closure (C ω)`, measurable in `ω`;
* the measurable field `h` and constants `a`, `k`;
* the coupling clause at fixed times for the **prefix filtration** of `𝓐₀` and `γ` (Lemma 6.2, Remark 6.7). -/
def Lemma71PocketStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓐₀ : MeasurableSpace Ω) (C : Ω → Set ℂ) (e : ℕ → ℂ) (Nx Ny : ℕ → Ω → ℕ) (Nb : Ω → ℕ)
      (seg γ : Ω → ℝ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ),
      𝓐₀ ≤ mΩ ∧ DenseRange e ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ C ω}) ∧
      (∀ m, Measurable[𝓐₀] (Nx m)) ∧ (∀ m, Measurable[𝓐₀] (Ny m)) ∧ Measurable[𝓐₀] Nb ∧
      (∀ m ω, e (Nx m ω) ∈ C ω) ∧ (∀ m ω, e (Ny m ω) ∈ C ω) ∧ (∀ ω, e (Nb ω) ∈ C ω) ∧
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧
      (∀ ω, Tendsto (fun m => (c ω).1 (e (Nx m ω))) atTop (𝓝 0) ∧
        Tendsto (fun m => ‖(c ω).1 (e (Ny m ω))‖) atTop atTop) ∧
      (∀ ω, ‖(c ω).1 (e (Nb ω))‖ = 1) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im) ∧
      Measurable[𝓐₀] (fun ω => (c ω).2.2 (e (Nb ω))) ∧
      (∀ ω, IsSegCurve (γ ω)) ∧ (∀ u, 0 ≤ u → Measurable[mΩ] fun ω => seg ω u) ∧
      (∀ ω u, 0 ≤ u → seg ω u ∈ closure (C ω) ∧ Tendsto (c ω).1 (𝓝[C ω] (seg ω u)) (𝓝 (γ ω u))) ∧
      Measurable[mΩ] h ∧
      IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
        (prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ) (fun s ω => segDriver (γ ω) s)
        (geomL (fun s ω => segDriver (γ ω) s) LP.twoSeedXL) (geomR (fun s ω => segDriver (γ ω) s) LP.twoSeedXR)
        (fun ω => capLife (γ ω)) c a k h

/-- **The measurability clauses of a pathwise normalized pocket chart.** Under the pocket hypotheses of
`Lemma71PocketStatement`, the given chart has `𝓐₀`-measurable domain events, forward map and lift. -/
theorem measurable_pocketChart {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}
    (hC : ∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) {e : ℕ → ℂ} (he : DenseRange e)
    {Nx Ny : ℕ → Ω → ℕ} {Nb : Ω → ℕ} (hNx : ∀ m, Measurable (Nx m)) (hNy : ∀ m, Measurable (Ny m))
    (hNb : Measurable Nb) (hNxC : ∀ m ω, e (Nx m ω) ∈ C ω) (hNyC : ∀ m ω, e (Ny m ω) ∈ C ω)
    (hNbC : ∀ ω, e (Nb ω) ∈ C ω) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω)
    (hnorm : ∀ ω, Tendsto (fun m => (c ω).1 (e (Nx m ω))) atTop (𝓝 0) ∧
      Tendsto (fun m => ‖(c ω).1 (e (Ny m ω))‖) atTop atTop)
    (hscale : ∀ ω, ‖(c ω).1 (e (Nb ω))‖ = 1)
    (hlift : ∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im)
    (hliftm : Measurable fun ω => (c ω).2.2 (e (Nb ω))) :
    (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) := by
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hbij : ∀ ω, IsConformalBijection (c ω).1 (C ω) H := fun ω => by
    have := isConformalBijection_fwd (hc ω)
    rwa [hdom ω] at this
  obtain ⟨c₀, -, hdom₀, -, -, hfwd₀, hlift₀, -, hL₀, -, huniq⟩ :=
    exists_measurable_twoPointChart hCo (fun ω => (hC ω).2.1) (fun ω => (hC ω).2.2.1) (fun ω => (hC ω).2.2.2)
      hCm he hNx hNy hNxC hNyC fun ω => ⟨(c ω).1, hbij ω, hnorm ω⟩
  have hmem := measurableSet_mem_of_closedBall hCo hCm
  have hset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom ω]
  have hset₀ : ∀ z, {ω | z ∈ (c₀ ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c₀ ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom₀ ω]
  have hfwd₀' : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).1 z) := fun z => by
    rw [← hset₀ z]; exact hfwd₀ z
  have hlift₀' : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).2.2 z) := fun z => by
    rw [← hset₀ z]; exact hlift₀ z
  -- the scale factor
  choose lam hlam hEq using fun ω => huniq ω (c ω).1 (hbij ω) (hnorm ω).1 (hnorm ω).2
  have hlam_eq : ∀ ω, lam ω = ‖(c₀ ω).1 (e (Nb ω))‖ := fun ω => by
    rw [hEq ω (hNbC ω), norm_mul, hscale ω, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hlam ω)]
  have hfwd_eq : ∀ ω, ∀ z ∈ C ω, (c ω).1 z = (c₀ ω).1 z / (‖(c₀ ω).1 (e (Nb ω))‖ : ℂ) := fun ω z hz => by
    rw [hEq ω hz, ← hlam_eq ω]
    have : (lam ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hlam ω).ne'
    field_simp
  have hb₀ : Measurable fun ω => (c₀ ω).1 (e (Nb ω)) := measurable_at_seq hNb hNbC hfwd₀'
  -- the lifts differ by `2πn`
  have hn : ∀ ω, ∃ n : ℤ, ∀ z ∈ C ω, (c ω).2.2 z = (c₀ ω).2.2 z + 2 * Real.pi * n := by
    intro ω
    obtain ⟨L, hL, hLe⟩ := hlift ω
    obtain ⟨L₀, hL₀', hL₀e⟩ := hL₀ ω
    have hL₀c : IsDerivLog (c ω).1 (fun z => L₀ z - ((Real.log (lam ω) : ℝ) : ℂ)) (C ω) := by
      refine ⟨hL₀'.1.sub_const _, fun z hz => ?_⟩
      have hev : (c₀ ω).1 =ᶠ[𝓝 z] fun x => (lam ω : ℂ) * (c ω).1 x :=
        Filter.eventuallyEq_of_mem ((hCo ω).mem_nhds hz) (hEq ω)
      have hd : DifferentiableAt ℂ (c ω).1 z := (hbij ω).1.differentiableAt ((hCo ω).mem_nhds hz)
      have h1 := hL₀'.2 z hz
      rw [hev.deriv_eq, deriv_const_mul _ hd] at h1
      rw [Complex.exp_sub, h1, ← Complex.ofReal_exp, Real.exp_log (hlam ω)]
      have : (lam ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hlam ω).ne'
      field_simp
    obtain ⟨n, hn⟩ := exists_int_eq_lift_add (hCo ω) (hC ω).2.1.isPreconnected hL₀c hL
    refine ⟨n, fun z hz => ?_⟩
    rw [hLe z hz, hn z hz, hL₀e z hz, Complex.sub_im, Complex.ofReal_im, sub_zero]
  choose n hneq using hn
  have hb₀l : Measurable fun ω => (c₀ ω).2.2 (e (Nb ω)) := measurable_at_seq hNb hNbC hlift₀'
  have hnm : Measurable n := measurable_int_of_eq_add hliftm hb₀l fun ω => hneq ω _ (hNbC ω)
  refine ⟨fun z => by rw [hset z]; exact hmem z, fun z => ?_, fun z => ?_, fun ω => ?_⟩
  · rw [hset z]
    have hm : Measurable ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).1 z / (‖(c₀ ω).1 (e (Nb ω))‖ : ℂ)) := by
      have heq : ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).1 z / (‖(c₀ ω).1 (e (Nb ω))‖ : ℂ)) =
          fun ω => ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).1 z) ω / (‖(c₀ ω).1 (e (Nb ω))‖ : ℂ) := by
        funext ω
        by_cases hz : z ∈ C ω
        · simp [indicator_of_mem (show ω ∈ {ω | z ∈ C ω} from hz)]
        · simp [indicator_of_notMem (show ω ∉ {ω | z ∈ C ω} from hz)]
      rw [heq]
      exact (hfwd₀' z).div (Complex.measurable_ofReal.comp hb₀.norm)
    convert hm using 1
    funext ω
    by_cases hz : z ∈ C ω
    · simp only [indicator_of_mem (show ω ∈ {ω | z ∈ C ω} from hz), hfwd_eq ω z hz]
    · simp only [indicator_of_notMem (show ω ∉ {ω | z ∈ C ω} from hz)]
  · rw [hset z]
    have hm : Measurable fun ω => ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).2.2 z) ω +
        {ω | z ∈ C ω}.indicator (fun ω => 2 * Real.pi * (n ω : ℝ)) ω :=
      (hlift₀' z).add (Measurable.indicator (measurable_const.mul
        ((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hnm)) (hmem z))
    convert hm using 1
    funext ω
    by_cases hz : z ∈ C ω
    · simp only [indicator_of_mem (show ω ∈ {ω | z ∈ C ω} from hz), hneq ω z hz]
    · simp only [indicator_of_notMem (show ω ∉ {ω | z ∈ C ω} from hz), add_zero]
  · obtain ⟨L, hL, hLe⟩ := hlift ω
    rw [show ((c ω).dom : Set ℂ) = C ω from hdom ω]
    exact (Complex.continuous_im.comp_continuousOn hL.1.continuousOn).congr fun z hz => hLe z hz

/-- **`Lemma71PocketCurveConstStatement` from the pocket data.** The given chart is measurable
(`measurable_pocketChart`); the mapped positions are measurable as boundary limits of the forward map; the prefix
events are measurable (`measurableSet_prefixEvent`), so the segment is prefix-adapted to the prefix filtration, which
contains `𝓐₀` at time `0`. Conditional helper. -/
theorem lemma71PocketCurveConstStatement_of_pocket (hp : Lemma71PocketStatement.{v}) :
    Lemma71PocketCurveConstStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓐₀, C, e, Nx, Ny, Nb, seg, γ, h, c, a, k, h₀, he, hC, hCm, hNx, hNy, hNb, hNxC, hNyC,
    hNbC, hc, hdom, hnorm, hscale, hlift, hliftm, hγ, hseg, hsegl, hh, hcf⟩ := hp κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨hdm, hfm, hlm, hlc⟩ := @measurable_pocketChart Ω 𝓐₀ C hC hCm e he Nx Ny Nb hNx hNy hNb hNxC hNyC
    hNbC c hc hdom hnorm hscale hlift hliftm
  have hset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom ω]
  -- the mapped positions are measurable
  have hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u := by
    intro u hu
    have hD : ∀ z, MeasurableSet[mΩ] {ω | z ∈ C ω} := fun z => h₀ _ (hset z ▸ hdm z)
    have hF : ∀ z, Measurable[mΩ] ({ω | z ∈ C ω}.indicator fun ω => (c ω).1 z) := fun z =>
      (hset z ▸ hfm z).mono h₀ le_rfl
    exact @Restart.measurable_of_tendsto_nhdsWithin Ω mΩ C (fun ω => (c ω).1) (fun ω => seg ω u)
      (fun ω => γ ω u) (fun ω => (hC ω).1) hD hF (hseg u hu) (fun ω => (hsegl ω u hu).1)
      (fun ω => (hsegl ω u hu).2)
  have hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k) := @measurableSet_prefixEvent Ω mΩ γ hγ hγm
  have hle := le_prefixFiltrationOf h₀ γ 0
  exact ⟨Ω, mΩ, P, hP, prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ, γ, h, c, a, k, hγ,
    isPrefixAdapted_prefixFiltrationOf 𝓐₀ γ hpm, hh, hc, fun z => hle _ (hdm z),
    fun z => (hfm z).mono hle le_rfl, fun z => (hlm z).mono hle le_rfl, hlc, hcf⟩

/-- `Lemma71C.Lemma71PocketCurveStatement` (usual conditions, every stopping time) from the pocket data, through
PROVE-LEMMA71D's transfer. Conditional helper. -/
theorem lemma71PocketCurveStatement_of_pocket (hp : Lemma71PocketStatement.{v}) :
    Lemma71PocketCurveStatement.{v} :=
  lemma71PocketCurveStatement_of_const (lemma71PocketCurveConstStatement_of_pocket hp)

/-- `Lemma71B.Lemma71KilledSegmentStatement` from the pocket data. Conditional helper. -/
theorem lemma71KilledSegmentStatement_of_pocket (hp : Lemma71PocketStatement.{v}) :
    Lemma71KilledSegmentStatement.{v} :=
  lemma71KilledSegmentStatement_of_pocketCurveConst (lemma71PocketCurveConstStatement_of_pocket hp)

/-- **`Sec7.Lemma71TraceReferenceStatement` (Lemma 7.1's transient two-seed reference evolution) from the pocket
data.** Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_pocket (hp : Lemma71PocketStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  lemma71TraceReferenceStatement_of_pocketCurveConst (lemma71PocketCurveConstStatement_of_pocket hp)

end InteractingSLE.Sec7.Lemma71E
