/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixedInf
import InteractingSLE.Spec.Sec7.PocketWordAssembly

/-!
# Theorem R.7's mixed and outer pockets: the relative traversal and `Good`

Packet PROVE-R7-STOPIN. Supplement §5.4 and the proof of Theorem R.7 (`source/spec/p433-480.md` L990–L1018,
L1058–L1068, pp. 474, 477): "The traversal argument above gives a complete continuous relative trace […] the complete
erased physical traversal ends at the pocket target, whose Jordan uniformization is infinity; its relative trace is
unbounded as completion is approached. […] The same endpoint convergence gives transience."

For the selected change pocket of a mixed or outer pair, in the landed notation of the contained case
(`PocketJordan.cfTraversal R L r η ψ`, `cfTraversalInf`: the erased counterflow traversal read in a Jordan coordinate
`ψ`, `x₀ ↦ ∞`, `y₀ ↦ 0`, on `[0, ∞)`):

* `RelLoewner ζ L` (**named input**: Aux. lemma 41's Loewner conclusion for the erased path on every `[0, S']`,
  `S' < L` — §5.4: "There is strict relative hull growth […] The same Loewner criterion used in Aux. 41 now gives a
  continuous relative driver");
* **`cfTraversal_props_of_erasure`** (bounded pocket) and **`cfTraversalInf_props_of_erasure`** (pocket opening at
  the flow seed, transient counterflow): from the erasure facts (`IsErasurePocket(Inf)`, proved for every mixed and
  outer pocket in `R7StopInMixed(Inf)` from the source's stochastic inputs), a Jordan coordinate and `RelLoewner`: the
  traversal is a driven curve with points of `ℍ` of arbitrarily large modulus (the hypotheses `hγ`, `hunb` of the stop
  level), it tends to `∞`, and with infinite capacity lifetime it satisfies **`GoodR7`** (Theorem R.7's transience,
  the `hGood` of `R7Pocket.R7PocketStopStatement`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7StopIn

open Sec6 PocketTraversal Lemma71C PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen R7Aux131

/-- **Aux. lemma 41's Loewner conclusion** for an erased path `ζ` with terminal clock `L` (named input): on every
`[0, S']`, `0 < S' < L`, the fillings of `ζ` are the hulls of a continuous driver after a continuous strictly increasing
capacity change. -/
def RelLoewner (ζ : ℝ → ℂ) (L : ℝ) : Prop :=
  ∀ S' : ℝ, 0 < S' → S' < L → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧
    StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
    ∀ t ∈ Icc 0 S', QuantumZipper.fwdHull W (σ' t) = fillH (ζ '' Icc 0 t)

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ} {ψ : ℂ → ℂ}

/-- **The relative traversal of a bounded mixed or outer pocket** (§5.4, Theorem R.7): a driven curve with points of
`ℍ` of arbitrarily large modulus, tending to `∞`, and `GoodR7` when its capacity lifetime is infinite. -/
theorem cfTraversal_props_of_erasure
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)))
    (hψ : IsCfJordan R L r ψ)
    (hloc : RelLoewner (fun v => ψ (erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) v)) (pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) (firstHit η (cfArcR R L r 0)))) :
    IsDrivenCurve (cfTraversal R L r η ψ) ∧
      (∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversal R L r η ψ u ∈ H ∧ M < ‖cfTraversal R L r η ψ u‖) ∧
      Tendsto (fun u => ‖cfTraversal R L r η ψ u‖) atTop atTop ∧
      (capLife (cfTraversal R L r η ψ) = ⊤ → GoodR7 (fun t => segDriver (cfTraversal R L r η ψ) t) ⊤) := by
  have hψ' : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]
    exact hψ
  have hγ : IsDrivenCurve (cfTraversal R L r η ψ) :=
    hP.isDrivenCurve_relTrav hψ'.1 hψ'.2.2.2.2.2.1 hloc
  exact ⟨hγ, hP.exists_relTrav_mem_H_lt_norm (fun z hz => hψ'.2.2.2.1.2.mapsTo hz) hψ'.2.2.2.2.2.2,
    hP.tendsto_norm_relTrav hψ'.2.2.2.2.2.2, fun hL => hP.goodR7_relTrav hγ hψ'.2.2.2.2.2.2 hL⟩

/-- **The relative traversal of a mixed or outer pocket opening at the flow seed** (transient counterflow): a driven
curve with points of `ℍ` of arbitrarily large modulus, tending to `∞`, and `GoodR7` when its capacity lifetime is
infinite. -/
theorem cfTraversalInf_props_of_erasure
    (hP : IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)))
    (hψ : IsCfJordanInf R L r ψ) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    (hloc : RelLoewner (fun v => ψ (erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
      (clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))) :
    IsDrivenCurve (cfTraversalInf R L r η ψ) ∧
      (∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversalInf R L r η ψ u ∈ H ∧ M < ‖cfTraversalInf R L r η ψ u‖) ∧
      Tendsto (fun u => ‖cfTraversalInf R L r η ψ u‖) atTop atTop ∧
      (capLife (cfTraversalInf R L r η ψ) = ⊤ → GoodR7 (fun t => segDriver (cfTraversalInf R L r η ψ) t) ⊤) := by
  have hψ' : IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  have hγ : IsDrivenCurve (cfTraversalInf R L r η ψ) :=
    hP.isDrivenCurve_relTravInf hψ'.1 hψ'.2.2.2.2.2.1 hloc
  exact ⟨hγ, hP.exists_relTravInf_mem_H_lt_norm (fun z hz => hψ'.2.2.2.1.2.mapsTo hz) hψ'.2.2.2.2.2.2 htr,
    hP.tendsto_norm_relTravInf hψ'.2.2.2.2.2.2 htr, fun hL => hP.goodR7_relTravInf hγ hψ'.2.2.2.2.2.2 htr hL⟩

end InteractingSLE.Sec7.R7StopIn
