/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CutoffUniqueness
import InteractingSLE.Foundations.Topology.PathComplement.Basic

/-!
# Carathéodory's continuous extension on the disk, and Aux. lemma 29 in the source's form

Packet PROVE-SEC6-A3 (specification §6.1, `source/spec/p145-192.md`, `#aux-29`, p. 164).

**Carathéodory's continuity theorem** ([Pom] C. Pommerenke, *Boundary Behaviour of Conformal Maps*,
Thm 2.1, (iv) ⇒ (i), pp. 20–22), disk form: a conformal map `f` of the unit disk onto a bounded
domain `O` with locally connected boundary extends continuously to the closed disk, and the
boundary values lie on `∂O`. The extension is Mathlib's `extendFrom (ball 0 1) f` (the limit of
`f` from inside the disk), so "f denotes also its continuous extension" (Aux. 29) has a canonical
meaning.

Proof: `∂O` is compact and locally connected, hence uniformly locally connected
(`ulc_of_locallyConnectedSpace`); QuantumZipper's half-plane theorem
(`QuantumZipper.CA.Car.continuousOn_extension`, with `D = O`, `E = ∂O`) applies to `f ∘ cayley`
on `ℍ`, and gives a continuous extension to `ℍ̄` and a limit at `∞`. Pulling back by `cayleyInv`
gives the limit of `f` at every point of the closed disk (at `1` it is the limit at `∞`).

## Main results

* `tendsto_nhdsWithin_ball_of_isConformalBijection`: the limit of `f` at every point of the closed
  disk;
* `continuousOn_extendFrom_ball`: Carathéodory's extension theorem on the disk;
* `aux29_eqOn_zero_of_locallyConnected`, `aux29_eqOn_of_tendsto_of_locallyConnected`: Aux. lemma
  29 with the source's hypotheses on `O` (bounded, locally connected boundary) and the boundary
  condition stated for the continuous extension `extendFrom (ball 0 1) f`. Simple connectivity of
  `O` is not needed as a separate hypothesis (it follows from the conformal bijection).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Metric Set

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Sec6

/-- The composition `f ∘ cayley : ℍ → O` satisfies QuantumZipper's standing Carathéodory
hypotheses with `E = ∂O`. -/
theorem carHyp_comp_cayley {O : Set ℂ} (hOo : IsOpen O) {R₀ : ℝ} (hOR : O ⊆ ball 0 R₀)
    {f : ℂ → ℂ} (hf : IsConformalBijection f (ball 0 1) O) :
    QuantumZipper.CA.Car.CarHyp (f ∘ cayley) O (frontier O) R₀ := by
  refine ⟨hf.1.comp (QuantumZipper.CA.differentiableOn_cayley_Hbar.mono
      QuantumZipper.H_subset_Hbar) (fun z hz => QuantumZipper.CA.cayley_mem_ball hz),
    hf.2.comp QuantumZipper.CA.bijOn_cayley_H, hOo, hOR, isClosed_frontier, subset_rfl, ?_, ?_⟩
  · intro z hz hzO
    have : z ∈ O ∩ frontier O := ⟨hzO, hz⟩
    rw [hOo.inter_frontier_eq] at this
    exact this
  · calc frontier O ⊆ closure O := frontier_subset_closure
      _ ⊆ closure (ball 0 R₀) := closure_mono hOR
      _ ⊆ closedBall 0 R₀ := closure_ball_subset_closedBall

/-- `cayleyInv` sends the punctured approach to `1` from inside the disk to `∞` within `ℍ`. -/
theorem tendsto_cayleyInv_nhdsWithin_ball_one :
    Tendsto cayleyInv (𝓝[ball 0 1] 1) (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
  · refine QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.mono_left (nhdsWithin_mono _ ?_)
    intro w hw h1
    rw [mem_singleton_iff] at h1
    rw [h1, mem_ball, dist_zero_right, norm_one] at hw
    exact lt_irrefl _ hw
  · exact eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.CA.cayleyInv_mem_H hw

/-- `cayleyInv` sends the approach to a point `q ≠ 1` of the closed disk from inside the disk to
the approach to `cayleyInv q` within `ℍ`. -/
theorem tendsto_cayleyInv_nhdsWithin_ball {q : ℂ} (hq : q ≠ 1) :
    Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (cayleyInv q)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact ((QuantumZipper.CA.continuousOn_cayleyInv q hq).continuousAt
      (isOpen_ne.mem_nhds hq)).tendsto.mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.CA.cayleyInv_mem_H hw

theorem cayley_cayleyInv_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    cayley (cayleyInv w) = w := by
  refine QuantumZipper.CA.cayley_cayleyInv fun h1 => ?_
  rw [h1, mem_ball, dist_zero_right, norm_one] at hw
  exact lt_irrefl _ hw

/-- **Carathéodory, limits at the boundary.** A conformal map `f` of the unit disk onto a bounded
open set `O` whose boundary is locally connected has a limit, lying on `∂O`, at every point of the
unit circle (from inside the disk). -/
theorem tendsto_nhdsWithin_ball_of_isConformalBijection {O : Set ℂ} (hOo : IsOpen O)
    (hOb : Bornology.IsBounded O) (hOl : LocallyConnectedSpace (frontier O)) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) :
    ∃ y ∈ frontier O, Tendsto f (𝓝[ball 0 1] q) (𝓝 y) := by
  obtain ⟨R₀, hR₀⟩ := hOb.subset_ball 0
  have hcar := carHyp_comp_cayley hOo hR₀ hf
  have hEc : IsCompact (frontier O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hOb.closure.subset frontier_subset_closure)
  obtain ⟨F, hFeq, hFc, hFfr, wInf, hwInf, hInf⟩ :=
    QuantumZipper.CA.Car.continuousOn_extension hcar (ulc_of_locallyConnectedSpace hEc)
  -- `f = (f ∘ cayley) ∘ cayleyInv` on the disk
  have hfeq : f =ᶠ[𝓝[ball 0 1] q] (f ∘ cayley) ∘ cayleyInv :=
    eventually_nhdsWithin_of_forall fun w hw => by
      simp only [Function.comp_apply, cayley_cayleyInv_of_mem_ball hw]
  by_cases hq1 : q = 1
  · subst hq1
    exact ⟨wInf, hwInf, (hInf.comp tendsto_cayleyInv_nhdsWithin_ball_one).congr' hfeq.symm⟩
  · set p := cayleyInv q with hp
    have hpH : p ∈ Hbar := QuantumZipper.CA.cayleyInv_mem_Hbar (sphere_subset_closedBall hq)
    have hpim : p.im = 0 := by
      rw [hp, QuantumZipper.CA.im_cayleyInv, mem_sphere_zero_iff_norm.1 hq]
      norm_num
    have hpre : p = ((p.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hpim]
    have hlim : Tendsto (f ∘ cayley) (𝓝[H] p) (𝓝 (F p)) := by
      have h1 : Tendsto F (𝓝[H] p) (𝓝 (F p)) :=
        ((hFc p hpH).mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar))
      exact h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hFeq hz)
    refine ⟨F p, ?_, (hlim.comp (tendsto_cayleyInv_nhdsWithin_ball hq1)).congr' hfeq.symm⟩
    rw [hpre]
    exact hFfr p.re

/-- **Carathéodory's continuous extension on the disk** ([Pom] Thm 2.1). A conformal map `f` of the
unit disk onto a bounded open set `O` with locally connected boundary extends continuously to the
closed disk: `extendFrom (ball 0 1) f` agrees with `f` on the disk, is continuous on the closed disk,
and maps the unit circle into `∂O`. -/
theorem continuousOn_extendFrom_ball {O : Set ℂ} (hOo : IsOpen O) (hOb : Bornology.IsBounded O)
    (hOl : LocallyConnectedSpace (frontier O)) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) :
    EqOn (extendFrom (ball 0 1) f) f (ball 0 1) ∧
      ContinuousOn (extendFrom (ball 0 1) f) (closedBall 0 1) ∧
      MapsTo (extendFrom (ball 0 1) f) (sphere 0 1) (frontier O) := by
  have hcl : closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
  have hlim : ∀ q ∈ closedBall (0 : ℂ) 1, ∃ y, Tendsto f (𝓝[ball 0 1] q) (𝓝 y) := by
    intro q hq
    by_cases hqb : q ∈ ball (0 : ℂ) 1
    · exact ⟨f q, ((hf.1.continuousOn q hqb).mono_left le_rfl)⟩
    · have hqs : q ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        rw [mem_closedBall_zero_iff] at hq
        rw [mem_ball_zero_iff, not_lt] at hqb
        exact le_antisymm hq hqb
      obtain ⟨y, -, hy⟩ := tendsto_nhdsWithin_ball_of_isConformalBijection hOo hOb hOl hf hqs
      exact ⟨y, hy⟩
  refine ⟨extendFrom_extends hf.1.continuousOn, continuousOn_extendFrom hcl hlim, ?_⟩
  intro q hq
  obtain ⟨y, hy, hT⟩ := tendsto_nhdsWithin_ball_of_isConformalBijection hOo hOb hOl hf hq
  rw [extendFrom_eq (hcl (sphere_subset_closedBall hq)) hT]
  exact hy

/-- The continuous extension of a conformal map of the disk onto a bounded open set with locally
connected boundary is again a conformal bijection of the disk onto the set. -/
theorem isConformalBijection_extendFrom_ball {O : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) :
    IsConformalBijection (extendFrom (ball 0 1) f) (ball 0 1) O := by
  have heq : EqOn (extendFrom (ball 0 1) f) f (ball 0 1) := extendFrom_extends hf.1.continuousOn
  exact ⟨hf.1.congr heq, hf.2.congr heq.symm⟩

/-- **Aux. lemma 29** (first part), with the source's hypotheses. Let `O` be a bounded domain with
locally connected boundary, `f : 𝔻 → O` conformal, and `P ⊆ ∂O` finite. If `u` is harmonic in
`𝔻`, `u ∈ L²(𝔻)`, and `u` has continuous boundary value zero at every point `q` of the unit circle
with `f(q) ∉ P`, where `f(q)` is the value of the continuous extension of `f` (Carathéodory), then
`u = 0`. (Simple connectivity of `O` follows from the conformal bijection; it is not needed as a
separate hypothesis.) -/
theorem aux29_eqOn_zero_of_locallyConnected {O : Set ℂ} (hOo : IsOpen O)
    (hOb : Bornology.IsBounded O) (hOl : LocallyConnectedSpace (frontier O)) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) {P : Set ℂ} (hP : P.Finite)
    (hPO : P ⊆ frontier O) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    (hL2 : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≠ ⊤)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, extendFrom (ball 0 1) f q ∉ P →
      Tendsto u (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, u z = 0 :=
  aux29_eqOn_zero hOo (isConformalBijection_extendFrom_ball hf)
    (continuousOn_extendFrom_ball hOo hOb hOl hf).2.1 hP hPO hu hL2 hbd

/-- **Aux. lemma 29** (final assertion), with the source's hypotheses. Let `O` be a bounded domain
with locally connected boundary, `f : 𝔻 → O` conformal, `P ⊆ ∂O` finite. Let `H` be harmonic in `O`
with `|H(z)| ≤ C_ε (1 + dist(z, ∂O)^{−ε})` for every `ε > 0`, `φ : O → ℍ` conformal, `g` bounded
harmonic in `ℍ`, `χ` real, and `A` a continuous branch of `arg φ'` on `O`; put `F = g ∘ φ − χ A`.
If `(H − F) ∘ f` has continuous boundary value zero at every point `q` of the unit circle with
`f(q) ∉ P` (`f(q)` the value of the continuous extension), then `H = F` on `O`. -/
theorem aux29_eqOn_of_tendsto_of_locallyConnected {O : Set ℂ} (hOo : IsOpen O)
    (hOb : Bornology.IsBounded O) (hOl : LocallyConnectedSpace (frontier O)) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) {P : Set ℂ} (hP : P.Finite)
    (hPO : P ⊆ frontier O) {Hh : ℂ → ℝ} (hH : InnerProductSpace.HarmonicOnNhd Hh O)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ O,
      |Hh z| ≤ Cε * (1 + infDist z (frontier O) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ O {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A O)
    (hA : ∀ z ∈ O, deriv φ z = ‖deriv φ z‖ * exp (A z * I))
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, extendFrom (ball 0 1) f q ∉ P →
      Tendsto (fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ O, Hh z = g (φ z) - χ * A z := by
  have heq : EqOn (extendFrom (ball 0 1) f) f (ball 0 1) := extendFrom_extends hf.1.continuousOn
  refine aux29_eqOn_of_tendsto hOo (isConformalBijection_extendFrom_ball hf)
    (continuousOn_extendFrom_ball hOo hOb hOl hf).2.1 hP hPO hH hgrowth hφ hg hgb χ hAc hA
    fun q hq hqP => (hbd q hq hqP).congr' (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
  simp only [heq hζ]

end InteractingSLE.Sec6
