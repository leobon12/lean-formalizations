/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelBHLand
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# The tip identity of a relative exploration (Schramm–Wilson: `W̃_{a(t)} = Φ_t(W_t)`)

Packet PROVE-Q3-REL2, item (A)3 of `planning/handoffs/PROVE-Q3-REL.md` §4.1. `IsRelConfigOff` asks for the **tip
identity**: the transition `τ = g_t ∘ Ψi ∘ f̃_u` (explored chain `w` at time `t`, relative chain `Wr` at time
`u`, retained chart `(Ψ, Ψi)`) tends to `0` at `0`. The route through Aux. lemma 8's driver identity is not needed: the
transition already has a real limit `v` at `0` (`Q3Rel.exists_tendsto_transition`, PROVE-Q3-REL), and `v = 0` because
the later hull increments are matched by `Ψ` and shrink to `0` in both centred planes:

* `exists_norm_fwdMap_diff_lt` (Lawler's hull-radius bound for the shifted driver): for every `ε > 0`, the centred
  images `g_t(K_{t+s} \ K_t)` lie in `B(0, ε)` for all small `s ≥ 0`;
* `tendsto_tip_of_cluster`: if `0` is a cluster value of `τ` at `0` (points `y → 0` of `ℍ` with `τ(y) → 0`), then
  `τ → 0` at `0` (the limit is unique);
* **`tendsto_tip_of_later`**: if arbitrarily close later explored times `t'` are matched with arbitrarily close later
  relative times `u' > u` (`Ψ(K_{t'}) = K̃_{u'}`, `K_{t'}` off `A`), the tip identity holds: take a trace point
  `z ∈ K_{t'} \ K_t`; `y = g̃_u(Ψ z)` is small (the relative increment) and `τ(y) = g_t(z)` is small (the explored
  increment).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Supp8.Q3Kernel

open BHMean (jointInv)
open Q3Rel (IsRetainedChartOff IsGoodPt)

/-! ### Hull increments in the centred plane -/

/-- **Centred hull increments are small** (Lawler's hull-radius bound for the shifted driver): for a continuous driver
`W` and `t ≥ 0`, for every `ε > 0` there is `δ > 0` such that `‖g_t(z)‖ < ε` for every `z ∈ K_{t+s} \ K_t`,
`0 ≤ s < δ`. -/
theorem exists_norm_fwdMap_diff_lt {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ z ∈ fwdHull W (t + s) \ fwdHull W t, ‖fwdMap W t z‖ < ε := by
  have hWt : ContinuousAt (fun s : ℝ => W (t + s) - W t) 0 := by fun_prop
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.continuousAt_iff.1 hWt (ε / 3) (by positivity)
  set δ : ℝ := min δ₁ ((ε / 9) ^ 2) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (by positivity)
  refine ⟨δ, hδ0, fun s hs hsδ z hz => ?_⟩
  rcases hs.eq_or_lt with rfl | hs0
  · rw [add_zero, sdiff_self] at hz; exact absurd hz (notMem_empty z)
  rw [QuantumZipper.fwdHull_add_diff hW ht hs] at hz
  obtain ⟨-, hzK⟩ := hz
  have hbound : ∀ q ∈ Icc (0 : ℝ) s, |W (t + q) - W t| ≤ ε / 3 := by
    intro q hq
    have hq' : dist q 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.1]
      exact lt_of_le_of_lt hq.2 (lt_of_lt_of_le hsδ (min_le_left _ _))
    have := hδ₁b hq'
    rw [Real.dist_eq, add_zero, sub_self, sub_zero] at this
    exact this.le
  have hK := QuantumZipper.CaraR.fwdHull_subset_closedBall (A := fun q => W (t + q) - W t) (by fun_prop) hs0
    hbound hzK
  rw [mem_closedBall, dist_zero_right] at hK
  have hsq : 3 * Real.sqrt s < ε / 3 := by
    have h1 : Real.sqrt s < ε / 9 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact lt_of_lt_of_le hsδ (min_le_right _ _)
    linarith
  linarith

/-- **The trace at a positive time lies on the closed hull**: `η(u) ∈ cl K_u` for `u > 0` (trace points of the
increments `K_u \ K_{a}`, `a ↑ u`, converge to `η(u)`). -/
theorem trace_mem_closure_fwdHull {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {u : ℝ} (hu : 0 < u) : η u ∈ closure (fwdHull W u) := by
  have hex : ∀ n : ℕ, ∃ v ∈ Ioc (u - u / ((n : ℝ) + 1)) u,
      η v ∈ fwdHull W u \ fwdHull W (u - u / ((n : ℝ) + 1)) := fun n => by
    have h1 : u / ((n : ℝ) + 1) ≤ u := div_le_self hu.le (by linarith [n.cast_nonneg (α := ℝ)])
    have h2 : 0 < u / ((n : ℝ) + 1) := by positivity
    exact hη.exists_mem_diff hW hW0 (by linarith) (by linarith)
  choose v hv hmem using hex
  have hδ : Tendsto (fun n : ℕ => u - u / ((n : ℝ) + 1)) atTop (𝓝 u) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul u
    rw [mul_zero] at h1
    have h2 := (tendsto_const_nhds (x := u)).sub h1
    rw [sub_zero] at h2
    exact h2.congr fun n => by rw [mul_one_div]
  have hvt : Tendsto v atTop (𝓝 u) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hδ tendsto_const_nhds (fun n => (hv n).1.le) fun n => (hv n).2
  have hv0 : ∀ n, v n ∈ Ici (0 : ℝ) := fun n => by
    have h1 : u / ((n : ℝ) + 1) ≤ u := div_le_self hu.le (by linarith [n.cast_nonneg (α := ℝ)])
    exact le_trans (by linarith) (hv n).1.le
  have hc : Tendsto (fun n => η (v n)) atTop (𝓝 (η u)) :=
    ((hη.2.1 u (show (0 : ℝ) ≤ u from hu.le)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hvt, Eventually.of_forall hv0⟩)
  exact mem_closure_of_tendsto hc (Eventually.of_forall fun n => (hmem n).1)

/-! ### The tip identity -/

section Tip

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The tip identity from a cluster value.** If the transition `τ = g_t ∘ Ψi ∘ f̃_u` has `0` as a cluster value at
`0` (there are `y ∈ ℍ` arbitrarily close to `0` with `τ(y)` arbitrarily close to `0`), and `0` is a good point landing
off the closed retained set, then `τ → 0` at `0`. -/
theorem tendsto_tip_of_cluster (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hg : IsGoodPt Sb Wr u 0) (hA0 : extendFrom H (jointInv Ψi Wr u) 0 ∉ closure A)
    (hcl : ∀ ε > 0, ∃ y ∈ H, ‖y‖ < ε ∧ ‖fwdMap w t (Ψi (fwdMapInv Wr u y))‖ < ε) :
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) := by
  obtain ⟨v, -, -, hT⟩ := Q3Rel.exists_tendsto_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd
    (z := 0) Complex.zero_im hg hA0
  have hT' : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 v) := hT
  have hv : v = 0 := by
    have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose y hyH hy hτ using fun n : ℕ => hcl (1 / ((n : ℝ) + 1)) (hpos n)
    have hlim0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hy0 : Tendsto y atTop (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hyH⟩
      exact squeeze_zero_norm (fun n => (hy n).le) hlim0
    have h1 := hT'.comp hy0
    have h2 : Tendsto (fun n => fwdMap w t (Ψi (fwdMapInv Wr u (y n)))) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hτ n).le) hlim0
    exact tendsto_nhds_unique h1 h2
  rwa [hv] at hT'

/-- **The tip identity from matched later times.** Suppose that for every `δ > 0` there are an explored time
`t' ∈ (t, t + δ)` and a relative time `u' ∈ (u, u + δ)` with `Ψ(K_{t'}) = K̃_{u'}` and `K_{t'}` disjoint from `A`.
Then the transition `τ = g_t ∘ Ψi ∘ f̃_u` tends to `0` at `0` (given that `0` is a good point landing off the closed
retained set). -/
theorem tendsto_tip_of_later (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hg : IsGoodPt Sb Wr u 0) (hA0 : extendFrom H (jointInv Ψi Wr u) 0 ∉ closure A)
    (hlater : ∀ δ > 0, ∃ t' u', t < t' ∧ t' < t + δ ∧ u < u' ∧ u' < u + δ ∧
      Ψ '' fwdHull w t' = fwdHull Wr u' ∧ Disjoint (fwdHull w t') A) :
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) := by
  refine tendsto_tip_of_cluster hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hg hA0 fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_norm_fwdMap_diff_lt hw ht hε
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_norm_fwdMap_diff_lt hWr hu hε
  obtain ⟨t', u', htt', ht'δ, huu', hu'δ, hK', hdA⟩ := hlater (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨r, -, hr⟩ := hη.exists_mem_diff hw hw0 ht htt'
  set z := η r with hz
  have hzK' : z ∈ fwdHull w t' := hr.1
  have hzK : z ∉ fwdHull w t := hr.2
  have hzH : z ∈ H := hzK'.1
  have hzA : z ∉ A := Set.disjoint_left.1 hdA hzK'
  have hzD : z ∈ H \ A := ⟨hzH, hzA⟩
  set zt : ℂ := Ψ z with hzt
  have hztK' : zt ∈ fwdHull Wr u' := hK' ▸ mem_image_of_mem Ψ hzK'
  have hztK : zt ∉ fwdHull Wr u := by
    rw [← hK]
    rintro ⟨z₀, hz₀, hz₀e⟩
    have hz₀D : z₀ ∈ H \ A :=
      ⟨hz₀.1, fun h => Set.disjoint_left.1 hd (subset_closure hz₀) (subset_closure h)⟩
    have : z₀ = z := hΨ.conf.2.injOn hz₀D hzD hz₀e
    exact hzK (this ▸ hz₀)
  have hztH : zt ∈ H := hΨ.conf.2.mapsTo hzD
  refine ⟨fwdMap Wr u zt, QuantumZipper.FwdHolo.mapsTo_fwdMap hWr hu ⟨hztH, hztK⟩, ?_, ?_⟩
  · have hs : u' - u < δ₂ := by linarith [min_le_right δ₁ δ₂]
    exact hb₂ (u' - u) (by linarith) hs zt ⟨by rwa [add_sub_cancel], hztK⟩
  · rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 hu ⟨hztH, hztK⟩, hΨ.inv_fwd hzD]
    have hs : t' - t < δ₁ := by linarith [min_le_left δ₁ δ₂]
    exact hb₁ (t' - t) (by linarith) hs z ⟨by rwa [add_sub_cancel], hzK⟩

/-- **The good-point and landing conditions at `0` for a positive relative time.** If `u > 0`, the relative tip lands on
the closed relative hull, so `0` is a good point (the exceptional points are off the closed relative hull) and its joint
landing point lies on the closed explored hull, hence off the closed retained set. -/
theorem goodPt_zero_and_notMem (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 < u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)) :
    IsGoodPt Sb Wr u 0 ∧ extendFrom H (jointInv Ψi Wr u) 0 ∉ closure A := by
  have h0b : (0 : ℂ) ∈ Hbar := by simpa using RelTrans.ofReal_mem_Hbar 0
  have htip : Tendsto (fwdMapInv Wr u) (𝓝[H] 0) (𝓝 (ηr u)) := hηr.tendsto_fwdMapInv_tip hWr hWr0 hu.le
  have he : extendFrom H (fwdMapInv Wr u) 0 = ηr u := extendFrom_eq (by rw [closure_H]; exact h0b) htip
  have hmem : extendFrom H (fwdMapInv Wr u) 0 ∈ closure (fwdHull Wr u) := by
    rw [he]
    exact trace_mem_closure_fwdHull hηr hWr hWr0 hu
  have hg : IsGoodPt Sb Wr u 0 := Q3Rel.goodPt_of_mem_closure hSbK hmem
  refine ⟨hg, fun hA => ?_⟩
  have hK0 := Q3Rel.extendFrom_jointInv_mem_closure hΨ hw ht hWr hWr0 hηr hu.le hK hd hSbK h0b hmem
  exact Set.disjoint_left.1 hd hK0 hA

end Tip

end InteractingSLE.Supp8.Q3Kernel
