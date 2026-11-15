/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketLife
import InteractingSLE.Spec.Sec7.PocketLifeOsc
import InteractingSLE.Spec.Sec2.MartingaleCoupling
import InteractingSLE.Spec.Sec7.PocketTraversalMeas
import InteractingSLE.Spec.Sec7.RelClockAnnounce

/-!
# Aux. lemma 125's infinite relative lifetime, almost surely, from the driving equation before the lifetime

Packet PROVE-STRIPSYS13. Proof of Aux. lemma 125 (`source/spec/p385-432.md` L224–L232, p. 397): "Stop before a fixed
coordinate bound or at `ζ`, whichever occurs first. On the latter event […] the Brownian driver has its continuous
limit. […] If `ζ` were finite, […] `|X_C(s)| → ∞` as `s ↑ ζ`. The preceding bound makes the driver bounded on that
finite interval. The elementary Loewner rectangle bound then bounds the whole trace prefix, a contradiction. Thus
`ζ = ∞`."

For a random driven curve `γ ω` (`PocketTraversal.IsDrivenCurve`) whose curve has points of `ℍ` of arbitrarily large
modulus (for the erased pocket traversal: `PocketLife.exists_relCurve_mem_H_lt_norm_of_isReversePocket(Inf)`), whose
canonical driver solves the path equations of Definition 2.1 **before** the terminal capacity time `capLife (γ ω)`
with a noise `b` (Aux. lemma 122's conclusion at announced lifetimes), and whose noise is, along announcing stopping
times, a bounded martingale with bounded second moments (the Brownian property before the lifetime):

* **`ae_capLife_eq_top_of_announcing`**: almost surely `capLife (γ ω) = ∞`;
* `ae_capLife_eq_top_of_announcing_sq`: the same with the second moments from the quadratic variation `t`;
* `driverEq_martValue`: before the lifetime, the path equations already give the driving equation with the explicit
  noise `martValue/√a` (the process `MartChar.martProc` of Theorem 2.4's converse, whose stopped martingale property
  `PhaseSelFull.martingale_martProc_lifeLoc` proves); **`ae_capLife_eq_top_of_martProc`**: the a.s. statement with
  this noise;
* **`exists_announcing_capLife`**: for a random driven curve with adapted filled prefixes in a right-continuous
  filtration, the times `σₙ = n ∧ inf {s < capLife : |W_s| > n}` are stopping times, strictly before `capLife`,
  nondecreasing and exhausting `[0, capLife)` ("the complete Jordan traversal announces its own lifetime", p. 396).

The proof: the noise has a left limit at a finite `capLife` (`ae_exists_tendsto_of_announcing`), so it extends
continuously (`continuous_extend_of_tendsto`); the path equations before `capLife` are unchanged, and the pathwise
Aux. lemma 125 (`capLife_eq_top_of_driverEq`) gives `capLife = ∞`, contradicting finiteness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketLife

open Lemma71C PocketTraversal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Aux. lemma 125: the relative lifetime is infinite almost surely** (see the module docstring). -/
theorem ae_capLife_eq_top_of_announcing [IsProbabilityMeasure P] {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {a : ℝ} {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Ω → Fin nL → ℝ≥0 → ℝ} {vR : Ω → Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ ω, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω)) (vL ω) (vR ω) (capLife (γ ω)))
    (hw : ∀ ω, Sec2.DriverEq a ρL ρR (segDriver (γ ω)) (vL ω) (vR ω) (b · ω) (capLife (γ ω)))
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσT : ∀ n ω, (σ n ω : ℝ≥0∞) < capLife (γ ω)) (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσex : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < capLife (γ ω) → ∃ n, t ≤ σ n ω)
    (hbc : ∀ ω, ContinuousOn (b · ω) {t | (t : ℝ≥0∞) < capLife (γ ω)})
    (hbb : ∀ n, ∃ C, ∀ ω t, t ≤ σ n ω → |b t ω| ≤ C)
    (hbm : ∀ n, Martingale (fun t ω => b (min t (σ n ω)) ω) 𝓕 P)
    (hL2 : ∀ N : ℝ≥0, BddAbove (range fun n => ∫ ω, b (min N (σ n ω)) ω ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  classical
  filter_upwards [ae_exists_tendsto_of_announcing hσ hσT hσm hσex hbc hbb hbm hL2] with ω hω
  by_contra hne
  obtain ⟨Lim, hLim⟩ := hω hne
  set T : ℝ≥0 := (capLife (γ ω)).toNNReal with hTdef
  have hTe : (T : ℝ≥0∞) = capLife (γ ω) := ENNReal.coe_toNNReal hne
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (γ ω) ↔ t < T := fun t => by
    rw [← hTe]; exact ENNReal.coe_lt_coe
  have hc : ContinuousOn (b · ω) (Iio T) := (hbc ω).mono fun t ht => (hlt t).2 ht
  have hb'c := continuous_extend_of_tendsto hc hLim
  have hw' : Sec2.DriverEq a ρL ρR (segDriver (γ ω)) (vL ω) (vR ω) (fun t => if t < T then b t ω else Lim)
      (capLife (γ ω)) := fun t ht => by
    rw [hw ω t ht]
    simp only [(hlt t).1 ht, ↓reduceIte]
  exact hne (capLife_eq_top_of_driverEq (hγ ω) (hunb ω) (hpath ω) hw' hb'c hL hR)

/-- **Aux. lemma 125, with the second moments from the quadratic variation**: as `ae_capLife_eq_top_of_announcing`,
with the `L²` bound replaced by the martingale property of `(b^{σₙ})² − (t ∧ σₙ)` (the noise is a Brownian motion
before the lifetime). -/
theorem ae_capLife_eq_top_of_announcing_sq [IsProbabilityMeasure P] {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {a : ℝ} {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Ω → Fin nL → ℝ≥0 → ℝ} {vR : Ω → Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ ω, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω)) (vL ω) (vR ω) (capLife (γ ω)))
    (hw : ∀ ω, Sec2.DriverEq a ρL ρR (segDriver (γ ω)) (vL ω) (vR ω) (b · ω) (capLife (γ ω)))
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσT : ∀ n ω, (σ n ω : ℝ≥0∞) < capLife (γ ω)) (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσex : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < capLife (γ ω) → ∃ n, t ≤ σ n ω)
    (hbc : ∀ ω, ContinuousOn (b · ω) {t | (t : ℝ≥0∞) < capLife (γ ω)})
    (hbb : ∀ n, ∃ C, ∀ ω t, t ≤ σ n ω → |b t ω| ≤ C)
    (hbm : ∀ n, Martingale (fun t ω => b (min t (σ n ω)) ω) 𝓕 P)
    (hQ : ∀ n, Martingale (fun t ω => b (min t (σ n ω)) ω ^ 2 - ((min t (σ n ω) : ℝ≥0) : ℝ)) 𝓕 P) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  refine ae_capLife_eq_top_of_announcing hγ hunb hpath hw hL hR hσ hσT hσm hσex hbc hbb hbm fun N => ?_
  have hint : ∀ n (N : ℝ≥0), Integrable (fun ω => b (min N (σ n ω)) ω ^ 2) P := fun n N => by
    obtain ⟨C, hC⟩ := hbb n
    refine Integrable.of_bound ((((hbm n).1 N).mono (Filtration.le _ N)).aestronglyMeasurable.pow 2) (C ^ 2)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC ω _ (min_le_right _ _)) 2
  exact bddAbove_integral_sq_of_martingale_sq_sub (κ := 1) zero_le_one hint
    (fun n => by simpa only [one_mul] using hQ n) N

/-! ### The noise is the explicit martingale part -/

section MartValue

open MartChar

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- One force point: `ρ (v_t − v_0) = −2 ∫₀ᵗ ρ/(w − v)` when `v_t = v_0 + ∫₀ᵗ 2/(v − w)`. -/
theorem mul_sub_eq_neg_two_mul_integral {ρ x : ℝ} {v : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hv : v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)) (hv0 : v 0 = x) :
    ρ * (v t - v 0) = -2 * ∫ s in (0 : ℝ)..t, ρ / (w s.toNNReal - v s.toNNReal) := by
  rw [hv, hv0, add_sub_cancel_left, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show w s.toNNReal - v s.toNNReal = -(v s.toNNReal - w s.toNNReal) by ring, div_neg]
  ring

/-- **The driving equation with the explicit martingale part** (Theorem 2.4's converse, before the lifetime): the path
equations before `ζ` give `w_t = √a · (M_t/√a) + Σ ∫ ρL/(w − vL) + Σ ∫ ρR/(w − vR)` with
`M_t = martValue (jointρ ρL ρR) w₀ v₀ w_t v_t` (`MartChar.martProc` of the coordinates). -/
theorem driverEq_martValue (h : Aux125.IsForcePathPre xL xR ρL ρR w vL vR ζ) {a : ℝ} (ha : 0 < a) :
    Sec2.DriverEq a ρL ρR w vL vR
      (fun t => martValue (jointρ ρL ρR) (w 0) (jointV (fun i => vL i 0) (fun j => vR j 0)) (w t)
        (jointV (fun i => vL i t) (fun j => vR j t)) / Real.sqrt a) ζ := by
  intro t ht
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  rw [mul_div_cancel₀ _ hsa]
  simp only [martValue, Fintype.sum_sum_type, jointρ, jointV, Sum.elim_inl, Sum.elim_inr, h.w_zero, sub_zero]
  have hL : ∀ i, ρL i * (vL i t - vL i 0) =
      -2 * ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) := fun i =>
    mul_sub_eq_neg_two_mul_integral (h.vL_eq ht i) (h.vL_zero i)
  have hR : ∀ j, ρR j * (vR j t - vR j 0) =
      -2 * ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) := fun j =>
    mul_sub_eq_neg_two_mul_integral (h.vR_eq ht j) (h.vR_zero j)
  simp only [hL, hR, ← Finset.mul_sum]
  ring

/-- The process `martProc` of the joint coordinates is `martValue` of the joint coordinates at each `ω`. -/
theorem martProc_jointV_apply {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    martProc (jointρ ρL ρR) W (jointV VL VR) t ω =
      martValue (jointρ ρL ρR) (W 0 ω) (jointV (fun i => VL i 0 ω) (fun j => VR j 0 ω)) (W t ω)
        (jointV (fun i => VL i t ω) (fun j => VR j t ω)) := by
  have e : ∀ s : ℝ≥0, (fun j => jointV VL VR j s ω) = jointV (fun i => VL i s ω) (fun j => VR j s ω) :=
    fun s => funext fun j => by cases j <;> rfl
  simp only [martProc, e]

end MartValue

section AeMart

open MartChar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Aux. lemma 125: the relative lifetime is infinite almost surely, with the explicit noise** (see the module
docstring): for a random driven curve with points of `ℍ` of arbitrarily large modulus, whose canonical driver
`W t ω = segDriver (γ ω) t` and force paths `VL`, `VR` satisfy the path equations of Definition 2.1 before
`capLife (γ ω)`, and whose martingale part `B = martProc/√a` is, along announcing stopping times, a bounded martingale
with `(B^{σₙ})² − (t ∧ σₙ)` a martingale (Theorem 2.4's converse before the lifetime), `capLife (γ ω) = ∞` almost
surely. -/
theorem ae_capLife_eq_top_of_martProc [IsProbabilityMeasure P] {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {a : ℝ} (ha : 0 < a) {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hpath : ∀ ω, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω)) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (capLife (γ ω)))
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσT : ∀ n ω, (σ n ω : ℝ≥0∞) < capLife (γ ω)) (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσex : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < capLife (γ ω) → ∃ n, t ≤ σ n ω)
    (hbc : ∀ ω, ContinuousOn (fun t => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω /
      Real.sqrt a) {t | (t : ℝ≥0∞) < capLife (γ ω)})
    (hbb : ∀ n, ∃ C, ∀ ω t, t ≤ σ n ω →
      |martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω / Real.sqrt a| ≤ C)
    (hbm : ∀ n, Martingale (fun t ω => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR)
      (min t (σ n ω)) ω / Real.sqrt a) 𝓕 P)
    (hQ : ∀ n, Martingale (fun t ω => (martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR)
      (min t (σ n ω)) ω / Real.sqrt a) ^ 2 - ((min t (σ n ω) : ℝ≥0) : ℝ)) 𝓕 P) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  refine ae_capLife_eq_top_of_announcing_sq (a := a) (xL := xL) (xR := xR)
    (vL := fun ω i t => VL i t ω) (vR := fun ω j t => VR j t ω)
    (b := fun t ω => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω / Real.sqrt a)
    hγ hunb hpath (fun ω => ?_) hL hR hσ hσT hσm hσex hbc hbb hbm hQ
  have h := driverEq_martValue (hpath ω) ha
  have e : (fun t => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω / Real.sqrt a) =
      fun t => martValue (jointρ ρL ρR) (segDriver (γ ω) 0) (jointV (fun i => VL i 0 ω) (fun j => VR j 0 ω))
        (segDriver (γ ω) t) (jointV (fun i => VL i t ω) (fun j => VR j t ω)) / Real.sqrt a :=
    funext fun t => by rw [martProc_jointV_apply]
  simpa only [e] using h

end AeMart

section Announce

open RelClock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The relative lifetime announces itself** (proof of Aux. lemma 125, p. 396: "`ζₙ = n ∧ inf {s < ζ : |X_C(s)| ≥ n}`
[…] If `ζ` is finite […] `ζₙ < ζ` and `ζₙ ↑ ζ`. […] These are genuine stopping times in the relative history"), with the
driver in place of the coordinate: for a random driven curve with points of `ℍ` of arbitrarily large modulus and filled
prefixes adapted to a right-continuous filtration, `σₙ = n ∧ inf {s < capLife : |segDriver s| > n}` are stopping times
strictly before `capLife`, nondecreasing, and every time before `capLife` lies below some `σₙ`. -/
theorem exists_announcing_capLife [𝓕.IsRightContinuous] {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) (hpre : IsPrefixAdapted 𝓕 γ) :
    ∃ σ : ℕ → Ω → ℝ≥0, (∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, (σ n ω : ℝ≥0∞) < capLife (γ ω)) ∧ (∀ ω, Monotone fun n => σ n ω) ∧
      ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < capLife (γ ω) → ∃ n, t ≤ σ n ω := by
  set X : ℝ≥0 → Ω → ℝ := fun t ω => |segDriver (γ ω) t| with hX
  set ζ : Ω → WithTop ℝ≥0 := fun ω => capLife (γ ω) with hζ
  have hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := fun ω =>
    (hγ ω).segDriver_spec.2.1.abs
  have hA := adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓕 t] {ω | (t : WithTop ℝ≥0) < ζ ω ∧ c < X t ω} := fun t c =>
    hA t {x : ℝ | c < |x|} (measurableSet_lt measurable_const measurable_abs)
  have hunb' : ∀ ω, ζ ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : WithTop ℝ≥0) < ζ ω ∧ M < X s ω := fun ω hfin M =>
    exists_lt_abs_segDriver (hγ ω) (hunb ω) hfin M
  exact ⟨announce X ζ, isStoppingTime_announce hXa hXc, fun n ω => announce_lt (hunb' ω) n,
    monotone_announce, fun ω t ht => exists_le_announce hXc ht⟩

end Announce

end InteractingSLE.Sec7.PocketLife
