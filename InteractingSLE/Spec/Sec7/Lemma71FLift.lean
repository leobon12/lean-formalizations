/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71ETop
import InteractingSLE.Spec.Restart.ChartMeasLift

/-!
# The inherited lift branch of the pocket chart is `𝓐₀`-measurable

Packet PROVE-LEMMA71F (PROVE-LEMMA71E's "What remains" C: "the inherited branch at the base point must be
`𝓐₀`-measurable: it differs from the canonical chart lift by `2πn(ω)` …, so this is the measurability of `n`, i.e. of
the outer-curve height convention"). Specification §7.1 (p. 222): "The argument lift for `ψ⁻¹` is inherited from the
outer-curve height convention, so the two image boundary heights are those specified below; an unrelated principal
branch is not substituted"; supplement §2.3 (p. 453, `source/spec/p433-480.md` L471–L483), the **deterministic
normalization lemma** that "supplies the branch dependency in Proposition 6.1": for every finite own prefix of a flank,
with hydrodynamic map `g_i` and the logarithm `L_i = log g_i′` tending to zero at infinity, the pocket chart's logarithm
`L_φ = log φ′` satisfies, on the collar of a compact subarc `J` passed by that prefix,
`Im (L_φ − L_i)(z) → 0` as `z → J` (2), and "the logarithm with this property is unique".

So the inherited branch is the branch **pinned** by (2). This file shows that a pinned branch is measurable as soon as
the pins are: along a measurable sequence of points `z_k` of the pocket approaching `J`, the shift `2πn` between the
inherited and the canonical (measurable) lift is the limit of `m_k − ℓ₀(z_k)` with `m_k = Im L_i(z_k)` — measurable by
the dyadic approximation of the canonical logarithm (`Restart.measurable_indicator_canonDerivLog`).

## Main results

* `measurable_branchShift_of_pin`: the abstract principle (branches differing by `2πn`, pinned along measurable points);
* `measurable_lift_base_of_pin`: the lift of a pathwise two-point-normalized pocket chart at the base point is
  measurable, given a pin along measurable dense-sequence indices;
* `measurable_canonDerivLog_im_at_seq`: the pins of (2): `Im log g_K′` of a random compact hull at measurable points;
* `Lemma71PocketPinStatement` (**named input**, strictly weaker than `Lemma71E.Lemma71PocketStatement`): the
  measurability clause of the lift is replaced by the normalization (2) along an `𝓐₀`-measurable approach sequence,
  against the canonical logarithm of an `𝓐₀`-measurable compact prefix hull of a flank;
* **`lemma71PocketStatement_of_pin`**: `Lemma71PocketPinStatement → Lemma71E.Lemma71PocketStatement`, and the
  composition `lemma71TraceReferenceStatement_of_pin`.

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

namespace InteractingSLE.Sec7.Lemma71F

open MartChar Coupling Lemma71B Lemma71C Lemma71D Lemma71E

/-! ### The abstract principle -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A pinned branch shift is measurable.** Let two lifts `ℓ = ℓ₀ + 2πn` differ by an integer multiple of `2π` on a
random set `D`, let `z_k ∈ D` be random points at which the reference lift `ℓ₀` is measurable, and let `m_k` be
measurable pins with `ℓ(z_k) − m_k → 0`. Then `n` is measurable. -/
theorem measurable_branchShift_of_pin {ℓ ℓ₀ : Ω → ℂ → ℝ} {D : Ω → Set ℂ} {n : Ω → ℤ}
    (hn : ∀ ω, ∀ z ∈ D ω, ℓ ω z = ℓ₀ ω z + 2 * Real.pi * n ω)
    {z : ℕ → Ω → ℂ} (hzD : ∀ k ω, z k ω ∈ D ω) (hℓ₀z : ∀ k, Measurable fun ω => ℓ₀ ω (z k ω))
    {m : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (m k))
    (hpin : ∀ ω, Tendsto (fun k => ℓ ω (z k ω) - m k ω) atTop (𝓝 0)) :
    Measurable n := by
  have hlim : ∀ ω, Tendsto (fun k => m k ω - ℓ₀ ω (z k ω)) atTop (𝓝 (2 * Real.pi * n ω)) := by
    intro ω
    have h := ((hpin ω).neg).const_add (2 * Real.pi * (n ω : ℝ))
    rw [neg_zero, add_zero] at h
    refine h.congr fun k => ?_
    rw [hn ω _ (hzD k ω)]
    ring
  have hmeas : Measurable fun ω => 2 * Real.pi * (n ω : ℝ) :=
    measurable_of_tendsto_metrizable (fun k => (hm k).sub (hℓ₀z k)) (tendsto_pi_nhds.2 hlim)
  exact measurable_int_of_eq_add (g := fun _ => (0 : ℝ)) hmeas measurable_const fun ω => by ring

end Abstract

/-! ### The pocket chart -/

/-- **The lift of a pathwise normalized pocket chart at the base point is measurable, given a pin.** Under the
pocket hypotheses of `Lemma71E.measurable_pocketChart` (without the measurability of the lift and without the scale
rule), if the lift is pinned along measurable dense-sequence indices `Nz k` by measurable values `m k`
(`ℓ(e (Nz k ω)) − m k ω → 0`), then `ω ↦ ℓ(e (Nb ω))` is measurable. -/
theorem measurable_lift_base_of_pin {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}
    (hC : ∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) {e : ℕ → ℂ} (he : DenseRange e)
    {Nx Ny : ℕ → Ω → ℕ} {Nb : Ω → ℕ} (hNx : ∀ m, Measurable (Nx m)) (hNy : ∀ m, Measurable (Ny m))
    (hNb : Measurable Nb) (hNxC : ∀ m ω, e (Nx m ω) ∈ C ω) (hNyC : ∀ m ω, e (Ny m ω) ∈ C ω)
    (hNbC : ∀ ω, e (Nb ω) ∈ C ω) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω)
    (hnorm : ∀ ω, Tendsto (fun m => (c ω).1 (e (Nx m ω))) atTop (𝓝 0) ∧
      Tendsto (fun m => ‖(c ω).1 (e (Ny m ω))‖) atTop atTop)
    (hlift : ∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im)
    {Nz : ℕ → Ω → ℕ} (hNz : ∀ k, Measurable (Nz k)) (hNzC : ∀ k ω, e (Nz k ω) ∈ C ω)
    {m : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (m k))
    (hpin : ∀ ω, Tendsto (fun k => (c ω).2.2 (e (Nz k ω)) - m k ω) atTop (𝓝 0)) :
    Measurable fun ω => (c ω).2.2 (e (Nb ω)) := by
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hbij : ∀ ω, IsConformalBijection (c ω).1 (C ω) H := fun ω => by
    have := isConformalBijection_fwd (hc ω)
    rwa [hdom ω] at this
  obtain ⟨c₀, -, hdom₀, -, -, -, hlift₀, -, hL₀, -, huniq⟩ :=
    exists_measurable_twoPointChart hCo (fun ω => (hC ω).2.1) (fun ω => (hC ω).2.2.1) (fun ω => (hC ω).2.2.2)
      hCm he hNx hNy hNxC hNyC fun ω => ⟨(c ω).1, hbij ω, hnorm ω⟩
  have hset₀ : ∀ z, {ω | z ∈ (c₀ ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c₀ ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom₀ ω]
  have hlift₀' : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => (c₀ ω).2.2 z) := fun z => by
    rw [← hset₀ z]; exact hlift₀ z
  -- the scale factor and the shift of the lifts
  choose lam hlam hEq using fun ω => huniq ω (c ω).1 (hbij ω) (hnorm ω).1 (hnorm ω).2
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
  have hnm : Measurable n :=
    measurable_branchShift_of_pin (ℓ := fun ω => (c ω).2.2) (ℓ₀ := fun ω => (c₀ ω).2.2) hneq
      (z := fun k ω => e (Nz k ω)) hNzC (fun k => measurable_at_seq (hNz k) (hNzC k) hlift₀') hm hpin
  have hb₀l : Measurable fun ω => (c₀ ω).2.2 (e (Nb ω)) := measurable_at_seq hNb hNbC hlift₀'
  have heq : (fun ω => (c ω).2.2 (e (Nb ω))) = fun ω => (c₀ ω).2.2 (e (Nb ω)) + 2 * Real.pi * (n ω : ℝ) :=
    funext fun ω => hneq ω _ (hNbC ω)
  rw [heq]
  exact hb₀l.add (measurable_const.mul ((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hnm))

/-! ### The pins of the normalization lemma -/

section Pins

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The pins of (2) are measurable**: `Im log g_K′` (the canonical logarithm, zero at infinity) of a random compact
hull `K` (dyadic-hit measurable), read at measurable points of a dense sequence lying off the filled hull. -/
theorem measurable_canonDerivLog_im_at_seq {K : Ω → Set ℂ} (hK : Restart.IsDyadicHitMeasurable K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {e : ℕ → ℂ}
    {N : Ω → ℕ} (hN : Measurable N) (hNK : ∀ ω, e (N ω) ∈ H \ fillH (K ω)) :
    Measurable fun ω => (Restart.canonDerivLog (fillH (K ω)) (e (N ω))).im := by
  refine measurable_at_seq (C := fun ω => H \ fillH (K ω)) (f := fun ω z => (Restart.canonDerivLog (fillH (K ω)) z).im)
    hN hNK fun z => ?_
  have h := (Complex.measurable_im.comp (Restart.measurable_indicator_canonDerivLog hK hKc hKp z))
  have hcomp : ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => (Restart.canonDerivLog (fillH (K ω)) z).im) =
      Complex.im ∘ ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => Restart.canonDerivLog (fillH (K ω)) z) := by
    funext ω
    by_cases hω : ω ∈ {ω | z ∈ H \ fillH (K ω)}
    · simp only [indicator_of_mem hω, Function.comp_apply]
    · simp only [indicator_of_notMem hω, Function.comp_apply, Complex.zero_im]
  rw [hcomp]
  exact h

end Pins

/-! ### The named input with the pinned branch -/

/-- **Named input: the three-curve pocket data with the inherited branch pinned by the normalization lemma**
(Specification §7.1, p. 222; supplement §2.3, (2)). Exactly `Lemma71E.Lemma71PocketStatement`, except that the clause
"the lift at the base point is `𝓐₀`-measurable" is replaced by the normalization (2) itself: there is a random compact
set `K` (a finite own prefix of a flank, `𝓐₀`-measurable through dyadic squares, with `K ∪ {Im ≤ 0}` preconnected) and
an `𝓐₀`-measurable sequence of points `e (Nz k ω)` of the pocket, off the filled prefix, along which
`ℓ − Im log g_K′ → 0` (`g_K` the hydrodynamic map of `K`, the logarithm zero at infinity). -/
def Lemma71PocketPinStatement : Prop :=
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
      (∃ (K : Ω → Set ℂ) (Nz : ℕ → Ω → ℕ),
        (∀ (n : ℕ) (j : ℤ × ℤ), MeasurableSet[𝓐₀] {ω | (Restart.dyadicSquare n j ∩ K ω).Nonempty}) ∧
        (∀ ω, IsCompact (K ω)) ∧ (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧
        (∀ j, Measurable[𝓐₀] (Nz j)) ∧ (∀ j ω, e (Nz j ω) ∈ C ω) ∧
        (∀ j ω, e (Nz j ω) ∈ H \ fillH (K ω)) ∧
        ∀ ω, Tendsto (fun j => (c ω).2.2 (e (Nz j ω)) -
          (Restart.canonDerivLog (fillH (K ω)) (e (Nz j ω))).im) atTop (𝓝 0)) ∧
      (∀ ω, IsSegCurve (γ ω)) ∧ (∀ u, 0 ≤ u → Measurable[mΩ] fun ω => seg ω u) ∧
      (∀ ω u, 0 ≤ u → seg ω u ∈ closure (C ω) ∧ Tendsto (c ω).1 (𝓝[C ω] (seg ω u)) (𝓝 (γ ω u))) ∧
      Measurable[mΩ] h ∧
      IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
        (prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ) (fun s ω => segDriver (γ ω) s)
        (geomL (fun s ω => segDriver (γ ω) s) LP.twoSeedXL) (geomR (fun s ω => segDriver (γ ω) s) LP.twoSeedXR)
        (fun ω => capLife (γ ω)) c a k h

/-- **`Lemma71E.Lemma71PocketStatement` from the pinned branch.** The pins are measurable
(`measurable_canonDerivLog_im_at_seq`), so the lift at the base point is (`measurable_lift_base_of_pin`).
Conditional helper. -/
theorem lemma71PocketStatement_of_pin (hp : Lemma71PocketPinStatement.{v}) : Lemma71PocketStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓐₀, C, e, Nx, Ny, Nb, seg, γ, h, c, a, k, h₀, he, hC, hCm, hNx, hNy, hNb, hNxC, hNyC,
    hNbC, hc, hdom, hnorm, hscale, hlift, ⟨K, Nz, hKm, hKc, hKp, hNz, hNzC, hNzK, hpin⟩, hγ, hseg, hsegl, hh,
    hcf⟩ := hp κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  have hm : ∀ j, Measurable[𝓐₀] fun ω => (Restart.canonDerivLog (fillH (K ω)) (e (Nz j ω))).im := fun j =>
    @measurable_canonDerivLog_im_at_seq Ω 𝓐₀ K hKm hKc hKp e (Nz j) (hNz j) (hNzK j)
  have hliftm : Measurable[𝓐₀] fun ω => (c ω).2.2 (e (Nb ω)) :=
    @measurable_lift_base_of_pin Ω 𝓐₀ C hC hCm e he Nx Ny Nb hNx hNy hNb hNxC hNyC hNbC c hc hdom hnorm hlift
      Nz hNz hNzC _ hm hpin
  exact ⟨Ω, mΩ, P, hP, 𝓐₀, C, e, Nx, Ny, Nb, seg, γ, h, c, a, k, h₀, he, hC, hCm, hNx, hNy, hNb, hNxC, hNyC,
    hNbC, hc, hdom, hnorm, hscale, hlift, hliftm, hγ, hseg, hsegl, hh, hcf⟩

/-- `Sec7.Lemma71TraceReferenceStatement` (Lemma 7.1's transient two-seed reference evolution) from the pinned pocket
data. Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_pin (hp : Lemma71PocketPinStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  lemma71TraceReferenceStatement_of_pocket (lemma71PocketStatement_of_pin hp)

end InteractingSLE.Sec7.Lemma71F
