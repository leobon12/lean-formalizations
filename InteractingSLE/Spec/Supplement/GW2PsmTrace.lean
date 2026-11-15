/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Supplement.GW1PieceChart
import InteractingSLE.Spec.Supplement.BR4a
import QuantumZipper.Proofs.RS.TraceShift

/-!
# GW2's open lines: traces through the launch chart, and contact before a time

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* **`trace_join_eq_ext`**: the explored trace at `T + u` is the boundary extension of the launch chart's inverse at
  the current piece's own trace at `u` (the restart of a Loewner chain, `RS.fwdMapInv_add_shift`, with boundary
  limits);
* **`eq_ext_of_tipAt`**: a tip of a driver read through `c.trans infinitySourceChart` is the boundary extension of
  `c`'s inverse at `−1/γ(q)`;
* **`lt_firstContactTime_of_forall`**: a curve continuous a little past `t` that misses a closed set on `[0, t]`
  contacts it only after `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Psm

open Supp8.GB6 (firstContactTime)

/-- **The explored trace at `T + u` through the launch chart's boundary extension.** -/
theorem trace_join_eq_ext {Jn : ℝ≥0 → ℝ} (hJn : Continuous Jn) (hJn0 : Jn 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace Jn ⊤ η) (T : ℝ≥0) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {u : ℝ≥0}
    (huζ : (u : ℝ≥0∞) < ζ) {t₂ : ℝ} (hut₂ : (u : ℝ) < t₂)
    (hshift : ∀ r ∈ Icc (0 : ℝ) t₂,
      QuantumZipper.RS.shiftDrive (fun s : ℝ => Jn s.toNNReal) (T : ℝ) r = w r.toNNReal)
    {f : ℂ → ℂ} (hf : Tendsto (fwdMapInv (fun s : ℝ => Jn s.toNNReal) (T : ℝ)) (𝓝[H] (α u)) (𝓝 (f (α u)))) :
    η (T + u) = f (α u) := by
  set J : ℝ → ℝ := fun s : ℝ => Jn s.toNNReal with hJ
  have hJc : Continuous J := hJn.comp continuous_real_toNNReal
  have hJ0 : J 0 = 0 := by simp [hJ, hJn0]
  set Sh : ℝ → ℝ := QuantumZipper.RS.shiftDrive J (T : ℝ) with hSh
  have hShc : Continuous Sh := QuantumZipper.RS.continuous_shiftDrive hJc _
  have hSh0 : Sh 0 = 0 := by rw [hSh]; simp [QuantumZipper.RS.shiftDrive]
  have h1 : Tendsto (fwdMapInv J ((T + u : ℝ≥0) : ℝ)) (𝓝[H] 0) (𝓝 (η (T + u))) :=
    hη.tendsto_fwdMapInv_tip hJn.continuousOn hJn0 ENNReal.coe_lt_top
  have hcongr : fwdMapInv Sh u = fwdMapInv (fun s : ℝ => w s.toNNReal) u :=
    InteractingSLE.fwdMapInv_eq_of_eqOn u.coe_nonneg hut₂ hshift
  have h2 : Tendsto (fwdMapInv Sh u) (𝓝[H] 0) (𝓝 (α u)) := by
    rw [hcongr]
    exact hα.tendsto_fwdMapInv_tip hw hw0 huζ
  have h2' : Tendsto (fwdMapInv Sh u) (𝓝[H] 0) (𝓝[H] (α u)) :=
    tendsto_nhdsWithin_iff.2 ⟨h2, eventually_mem_nhdsWithin.mono fun z hz =>
      QuantumZipper.RS.fwdMapInv_mem_H hShc hSh0 u.coe_nonneg hz⟩
  have h3 : Tendsto (fun z => fwdMapInv J T (fwdMapInv Sh u z)) (𝓝[H] 0) (𝓝 (f (α u))) := hf.comp h2'
  have h4 : Tendsto (fwdMapInv J ((T + u : ℝ≥0) : ℝ)) (𝓝[H] 0) (𝓝 (f (α u))) := by
    refine h3.congr' (eventually_mem_nhdsWithin.mono fun z hz => ?_)
    rw [NNReal.coe_add, QuantumZipper.RS.fwdMapInv_add_shift hJc hJ0 T.coe_nonneg u.coe_nonneg hz]
  have hne : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℂ) ∈ Hbar by simp [QuantumZipper.Hbar])
  exact tendsto_nhds_unique h1 h4

/-- **A tip read through `c.trans infinitySourceChart` is the boundary extension of `c`'s inverse at `−1/γ(q)`.** -/
theorem eq_ext_of_tipAt {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) {q : ℝ≥0}
    (hq0 : γ q ≠ 0) {z : ℂ} (htip : (c.trans infinitySourceChart).tipAt W q z) : z = f (-(γ q)⁻¹) := by
  have hWc : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
  have hrad : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((0 : ℝ) * Complex.I)) :=
        ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact QuantumZipper.RS.mul_I_mem_H hy
  have h1 : Tendsto (fwdMapInv (fun s : ℝ => W s.toNNReal) q) (𝓝[H] 0) (𝓝 (γ q)) :=
    hγ.tendsto_fwdMapInv_tip hW.continuousOn hW0 ENNReal.coe_lt_top
  have h1' : Tendsto (fwdMapInv (fun s : ℝ => W s.toNNReal) q) (𝓝[H] 0) (𝓝[H] (γ q)) :=
    tendsto_nhdsWithin_iff.2 ⟨h1, eventually_mem_nhdsWithin.mono fun w hw =>
      QuantumZipper.RS.fwdMapInv_mem_H hWc hW0' q.coe_nonneg hw⟩
  have hinv : Tendsto (fun v : ℂ => -v⁻¹) (𝓝[H] (γ q)) (𝓝[H] (-(γ q)⁻¹)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun v hv => ?_⟩
    · exact ((continuousAt_inv₀ hq0).neg).tendsto.mono_left nhdsWithin_le_nhds
    · show 0 < (-v⁻¹).im
      have hv' : 0 < v.im := hv
      have hv0 : v ≠ 0 := fun h => by rw [h] at hv'; simp at hv'
      rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
      exact div_pos hv' (Complex.normSq_pos.2 hv0)
  have hγbar : γ q ∈ Hbar := by
    have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℂ) ∈ Hbar by simp [QuantumZipper.Hbar])
    have hcl : γ q ∈ closure {z : ℂ | 0 < z.im} :=
      mem_closure_of_tendsto h1 (eventually_mem_nhdsWithin.mono fun w hw =>
        QuantumZipper.RS.fwdMapInv_mem_H hWc hW0' q.coe_nonneg hw)
    rw [Complex.closure_setOfPred_lt_im] at hcl
    exact hcl
  have hpbar : -(γ q)⁻¹ ∈ Hbar := by
    show 0 ≤ (-(γ q)⁻¹).im
    have hg : 0 ≤ (γ q).im := hγbar
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_nonneg hg (Complex.normSq_nonneg _)
  have h2 : Tendsto (fun y : ℝ => (c.trans infinitySourceChart).2.1
      (fwdMapInv (fun s : ℝ => W s.toNNReal) q ((y : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 (f (-(γ q)⁻¹))) :=
    ((hf _ hpbar).comp hinv).comp (h1'.comp hrad)
  exact tendsto_nhds_unique htip h2

/-- **A curve continuous a little past `t` that misses a closed set on `[0, t]` contacts it only after `t`.** -/
theorem lt_firstContactTime_of_forall {X : Type*} [TopologicalSpace X] {η : ℝ≥0 → X} {A : Set X}
    (hA : IsClosed A) {t t' : ℝ≥0} (htt' : t < t') (hη : ContinuousOn η (Icc 0 t'))
    (hmiss : ∀ u ≤ t, η u ∉ A) : (t : ℝ≥0∞) < firstContactTime η A := by
  classical
  set K : Set ℝ≥0 := Icc 0 t' ∩ η ⁻¹' A with hK
  have hKc : IsClosed K := hη.preimage_isClosed_of_isClosed isClosed_Icc hA
  have hKcpt : IsCompact K := isCompact_Icc.of_isClosed_subset hKc inter_subset_left
  have hKt : ∀ u ∈ K, t < u := fun u hu => lt_of_not_ge fun h => hmiss u h hu.2
  -- a lower bound `b > t` for every contact time
  obtain ⟨b, hbt, hb⟩ : ∃ b : ℝ≥0, t < b ∧ ∀ u : ℝ≥0, η u ∈ A → b ≤ u := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨t', htt', fun u hu => le_of_not_gt fun hlt => ?_⟩
      have : u ∈ K := ⟨⟨zero_le, hlt.le⟩, hu⟩
      rw [hKe] at this
      exact this
    · set m := sInf K with hm
      have hmK : m ∈ K := hKcpt.sInf_mem hKne
      refine ⟨min m t', lt_min (hKt m hmK) htt', fun u hu => ?_⟩
      by_cases hut : u ≤ t'
      · exact (min_le_left _ _).trans (csInf_le hKcpt.bddBelow ⟨⟨zero_le, hut⟩, hu⟩)
      · exact (min_le_right _ _).trans (le_of_not_ge hut)
  have hle : ((b : ℝ≥0) : ℝ≥0∞) ≤ firstContactTime η A :=
    le_iInf₂ fun u hu => ENNReal.coe_le_coe.2 (hb u hu)
  exact (ENNReal.coe_lt_coe.2 hbt).trans_le hle

end InteractingSLE.Theorem14.GW2Psm
