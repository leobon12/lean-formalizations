/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Aux. lemma 10: a protected domain change with a different target (statement)

Packet PROVE-T14-BR6. Specification, Aux. lemma 10 (`source/spec/p049-096.md`, anchors `aux-10`, `aux-10-proof`,
pp. 69–71):

> Let `γ : [0, T] → ℍ̄` be a continuous chordal Loewner trace, with filled hulls `K_t`, hydrodynamic maps `g_t`, and
> continuous driver `W_t`. Let `D ⊆ ℍ` be simply connected. Suppose there is a relative-open neighborhood `N` of the
> compact set `K_T` in `ℍ̄` such that `N ∩ ℍ ⊂ D`. Suppose also that an open interval `J ⊂ ℝ` contains `K_T ∩ ℝ` and
> that `D` agrees with `ℍ` in an upper neighborhood of `J`. Let `φ : D → ℍ` be conformal and have a finite analytic
> reflection across `J`, with `φ' > 0` there. Normalize `φ(γ(0)) = 0` and choose the analytic logarithm of `φ'` whose
> imaginary part is zero on `J`.
>
> Then `D \ K_t` is connected and simply connected for every `t ≤ T`, and `K̃_t = φ(K_t)` is a compact half-plane hull
> equal to the filling of `φ(γ([0, t]))`. The mapped path is a continuous Loewner trace after a continuous strictly
> increasing capacity change `a(t) = ½ hcap(K̃_t)`. […] The comparison map `R_t = g̃_{a(t)} ∘ φ ∘ g_t⁻¹` (TD1)
> reflects conformally across the real interval `I_t` representing the old filled hull, and
> `W̃_{a(t)} = R_t(W_t)`, `Im L_t = 0` on `I_t` (TD2), where `L_t` is the logarithm of `R_t'` obtained by the chain
> rule from the chosen `log φ'` and the two hydrodynamically normalized logarithms.

It is the deterministic half of the transport of an optional-hull coupling under a fixed conformal change of target
(Corollary BR4a's retargeting `w ↦ w / (1 + v w)` in inversion coordinates, Lemma BW1's hydrodynamic chart after a
whole piece). It is not formalized in the project; this file states it (`Aux10Statement`) in the frozen conventions:

* hulls are `QuantumZipper.fwdHull` (the points of `ℍ` swallowed by time `t`); the compact filled hull of the source
  is `closure (fwdHull t) ∪ γ [0, t]`;
* maps are centred (`fwdMap W t = g_t − W_t`, `fwdMapInv` its inverse on `ℍ`, `logDerivFwd` the hydrodynamically
  normalized `log f_t'`), so (TD2) `W̃_{a(t)} = R_t(W_t)` reads `R_t(0) = 0` for the centred comparison map
  `R_t = f̃_{a(t)} ∘ φ ∘ f_t⁻¹`;
* "conformal `φ : D → ℍ`" is holomorphic and injective on `D` with image `ℍ` (this makes `D` simply connected); its
  "analytic reflection across `J`" is holomorphy on an open set `V ⊇ J`, real values and positive derivative on `J`;
* "reflects conformally across `I_t`" is a holomorphic extension of `R_t` (and of its chain-rule logarithm `L_t`) to an
  open set containing an open real interval `(y₁, y₂)` around the centred hull interval `I_t` (the real points at which
  `f_t⁻¹` has a limit in the compact hull), real on that interval, with `Im L_t = 0` there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace InteractingSLE

namespace Aux10

open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)

/-- The compact filled hull at time `t` of a trace `γ` of `W`: the swallowed points of `ℍ`, their closure, and the
trace up to `t`. -/
def compactHull (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  closure (fwdHull (fun s : ℝ => W s.toNNReal) t) ∪ γ '' Icc 0 t

/-- **Aux. lemma 10** (statement; spec pp. 69–71). See the module docstring for the reading of each clause. -/
def Aux10Statement : Prop :=
  ∀ (W : ℝ≥0 → ℝ) (T : ℝ≥0) (γ : ℝ≥0 → ℂ), Continuous W → W 0 = 0 → IsGeneratingTrace W T γ →
  ∀ (D U V : Set ℂ) (J : Set ℝ) (φ Lφ : ℂ → ℂ),
    IsOpen D → D ⊆ H →
    -- the protected neighbourhood `N = U ∩ ℍ̄` of `K_T`, with `N ∩ ℍ ⊂ D`
    IsOpen U → compactHull W γ T ⊆ U → U ∩ H ⊆ D →
    -- the open interval `J ⊇ K_T ∩ ℝ`, along which `D` agrees with `ℍ` in an upper neighbourhood
    (∃ x₁ x₂ : ℝ, J = Ioo x₁ x₂) → (∀ x : ℝ, (x : ℂ) ∈ compactHull W γ T → x ∈ J) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z.re ∈ J → 0 < z.im → z.im < ε → z ∈ D) →
    -- `φ : D → ℍ` conformal, with an analytic reflection across `J`, `φ' > 0` on `J`, `φ(γ(0)) = 0`
    IsOpen V → (∀ x ∈ J, (x : ℂ) ∈ V) → DifferentiableOn ℂ φ (D ∪ V) → InjOn φ D → φ '' D = H →
    (∀ x ∈ J, (φ x).im = 0 ∧ (deriv φ x).im = 0 ∧ 0 < (deriv φ x).re) → φ (γ 0) = 0 →
    -- the logarithm of `φ'` with imaginary part zero on `J`
    DifferentiableOn ℂ Lφ (D ∪ V) → (∀ z ∈ D ∪ V, Complex.exp (Lφ z) = deriv φ z) →
    (∀ x ∈ J, (Lφ x).im = 0) →
    -- `D \ K_t` is connected
    (∀ t ≤ T, IsConnected (D \ compactHull W γ t)) ∧
    -- the mapped path is a Loewner trace after a continuous strictly increasing capacity change `a`, with hulls
    -- `φ(K_t)`
    ∃ (a : ℝ≥0 → ℝ≥0) (Wm : ℝ≥0 → ℝ) (γm : ℝ≥0 → ℂ),
      a 0 = 0 ∧ StrictMonoOn a (Iic T) ∧ ContinuousOn a (Iic T) ∧
      ContinuousOn Wm (Iic (a T)) ∧ Wm 0 = 0 ∧ IsGeneratingTrace Wm (a T) γm ∧
      ∀ t ≤ T, γm (a t) = φ (γ t) ∧ compactHull Wm γm (a t) = φ '' compactHull W γ t ∧
        -- (TD1)–(TD2): the centred comparison map and its chain-rule logarithm reflect across a real interval
        -- around the centred hull interval, with `R_t(0) = 0` and `Im L_t = 0` there
        ∃ (y₁ y₂ : ℝ) (O : Set ℂ) (R L : ℂ → ℂ),
          y₁ < 0 ∧ 0 < y₂ ∧ IsOpen O ∧ (∀ y ∈ Ioo y₁ y₂, (y : ℂ) ∈ O) ∧
          (∀ y : ℝ, (∃ p ∈ compactHull W γ t,
            Tendsto (fwdMapInv (fun s : ℝ => W s.toNNReal) t) (𝓝[H] (y : ℂ)) (𝓝 p)) → y ∈ Ioo y₁ y₂) ∧
          DifferentiableOn ℂ R (O ∪ fwdMap (fun s : ℝ => W s.toNNReal) t '' (D \ compactHull W γ t)) ∧
          DifferentiableOn ℂ L (O ∪ fwdMap (fun s : ℝ => W s.toNNReal) t '' (D \ compactHull W γ t)) ∧
          (∀ w ∈ fwdMap (fun s : ℝ => W s.toNNReal) t '' (D \ compactHull W γ t),
            R w = fwdMap (fun s : ℝ => Wm s.toNNReal) (a t) (φ (fwdMapInv (fun s : ℝ => W s.toNNReal) t w)) ∧
            L w = logDerivFwd (fun s : ℝ => Wm s.toNNReal) (a t)
                (φ (fwdMapInv (fun s : ℝ => W s.toNNReal) t w)) +
              Lφ (fwdMapInv (fun s : ℝ => W s.toNNReal) t w) -
              logDerivFwd (fun s : ℝ => W s.toNNReal) t (fwdMapInv (fun s : ℝ => W s.toNNReal) t w)) ∧
          (∀ w ∈ O, Complex.exp (L w) = deriv R w) ∧
          R 0 = 0 ∧ ∀ y ∈ Ioo y₁ y₂, (R y).im = 0 ∧ (L y).im = 0

end Aux10

end InteractingSLE
