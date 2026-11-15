/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmTrace
import InteractingSLE.Spec.Supplement.GB6

/-!
# GW2's open lines: no contact in the launch frame from no physical contact

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* `tipAt_infinitySourceChart_of_trace`: the tip of a driver read through the inversion is `−1/γ(v)`;
* **`lt_firstContactTime_launch`**: if the explored trace after the launch is the boundary extension of the launch
  chart's inverse at the current piece's trace, the conditional counterflow's tips correspond to the original
  counterflow's through the clock `ℓ`, and the explored curve up to `T + t` misses the original counterflow up to
  `s = ℓ t₀`, then the current piece misses the conditional counterflow's trace up to `t₀` in the launch frame
  until after `t` (the contact premise of the kernel union mean, `UnionFormAt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Psm

open Supp8.GB6 (firstContactTime sphereInv)

/-- **The tip of a driver read through the inversion.** -/
theorem tipAt_infinitySourceChart_of_trace {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) {v : ℝ≥0} (hv0 : γ v ≠ 0) :
    infinitySourceChart.tipAt W v (-(γ v)⁻¹) := by
  have hrad : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((0 : ℝ) * Complex.I)) :=
        ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact QuantumZipper.RS.mul_I_mem_H hy
  have h1 : Tendsto (fwdMapInv (fun s : ℝ => W s.toNNReal) v) (𝓝[H] 0) (𝓝 (γ v)) :=
    hγ.tendsto_fwdMapInv_tip hW.continuousOn hW0 ENNReal.coe_lt_top
  have h2 : Tendsto (fun w : ℂ => -w⁻¹) (𝓝 (γ v)) (𝓝 (-(γ v)⁻¹)) :=
    ((continuousAt_inv₀ hv0).neg).tendsto
  exact h2.comp (h1.comp hrad)

/-- **No contact in the launch frame from no physical contact.** -/
theorem lt_firstContactTime_launch {cL : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto cL.2.1 (𝓝[H] p) (𝓝 (f p)))
    {Wk : ℝ≥0 → ℝ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) {γk : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hγk0 : ∀ q : ℝ≥0, 0 < q → γk q ≠ 0) {W' : ℝ≥0 → ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0)
    {γ' : ℝ≥0 → ℂ} (hγ' : IsGeneratingTrace W' ⊤ γ') (hγ'0 : ∀ v : ℝ≥0, 0 < v → γ' v ≠ 0) {ℓ : ℝ≥0 → ℝ≥0}
    (hℓm : StrictMono ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt W' (ℓ q) z) {t₀ s : ℝ≥0} (ht₀ : ℓ t₀ = s) {α : ℝ≥0 → ℂ} {t t' : ℝ≥0}
    (htt' : t < t') (hαc : ContinuousOn α (Icc 0 t')) {ηe : ℝ≥0 → ℂ} {T : ℝ≥0}
    (htr : ∀ u ≤ t, ηe (T + u) = f (α u))
    (hphys : ∀ u ≤ t, ∀ v ≤ s, 0 < v → ηe (T + u) ≠ -(γ' v)⁻¹) :
    (t : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
      ((fun q => sphereInv (γk q : OnePoint ℂ)) '' Icc 0 t₀) := by
  have hγkc : Continuous γk := continuousOn_univ.1 (hγk.2.1.mono fun q _ => show (q : ℝ≥0∞) ≤ ⊤ from le_top)
  have hA : IsClosed ((fun q => sphereInv (γk q : OnePoint ℂ)) '' Icc 0 t₀) :=
    (isCompact_Icc.image (Supp8.GB6.continuous_sphereInv.comp
      (OnePoint.continuous_coe.comp hγkc))).isClosed
  refine lt_firstContactTime_of_forall hA htt' (OnePoint.continuous_coe.comp_continuousOn hαc) ?_
  rintro u hu ⟨q, hq, hqe⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hq0
  · subst hq0
    have h0 : γk 0 = 0 := hγk.1
    simp only at hqe
    rw [h0, Supp8.GB6.sphereInv_coe] at hqe
    simp only [ite_true] at hqe
    exact OnePoint.infty_ne_coe _ hqe
  · have hγq := hγk0 q hq0
    simp only at hqe
    rw [Supp8.GB6.sphereInv_coe_of_ne hγq] at hqe
    have hαu : α u = -(γk q)⁻¹ := (OnePoint.coe_injective hqe).symm
    have hv : 0 < ℓ q := by rw [← hℓ0]; exact hℓm hq0
    have hvs : ℓ q ≤ s := by rw [← ht₀]; exact hℓm.monotone hq.2
    have htip := tipAt_infinitySourceChart_of_trace hW' hW'0 hγ' (hγ'0 _ hv)
    have hz := eq_ext_of_tipAt hf hWk hWk0 hγk hγq ((hiff q _).2 htip)
    exact hphys u hu (ℓ q) hvs hv (by rw [htr u hu, hαu, ← hz])
