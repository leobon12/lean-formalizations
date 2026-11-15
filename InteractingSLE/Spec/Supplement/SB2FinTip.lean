/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCollar
import InteractingSLE.Spec.Supplement.SB2UnionLift
import InteractingSLE.Spec.Supplement.R1RefFreshTip

/-!
# SB2(1)'s tip identity

Packet PROVE-T14-SB2FIN. The field `tip` of `SB.Union.IsRelConfigJ` / `IsRelConfigJC`: the transition map
`f_t ∘ Ψ⁻¹ ∘ F̃_u` tends to `0` at `0` (the relative tip is read at the physical tip; SB2, p. 632: "the same untouched
real interval through its individual driver continues this lift to its other germ").

* **`tip_of_isCutTime`** (generic): if the joint parametrization lands at the physical tip `η(t)` from `0` and `t` is a
  cut time of the physical trace (a fresh interior visit, `YuanSimpleApprox.IsCutTime`), the transition tends to `0` —
  the landed transition limit `Union.exists_tendsto_transition_rel` lands in the fibre of `η(t)`, which is `{0}` by the
  fresh-tip uniqueness (R41's Lemma 1.1, `IsLoewnerTrace.eq_zero_of_extendFrom_eq_of_isCutTime`);
* `extendFrom_jointInv_zero_of_isSB2RelChain`: for SB2's relative chain the joint parametrization lands at `g(γ s)`
  from `0`, i.e. at the physical point `β'(t_L + s)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C

/-- **The tip identity at a fresh interior tip.** -/
theorem tip_of_isCutTime {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}
    (hΨ : Supp8.Q3Rel.IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 < t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    (hg0 : Supp8.Q3Rel.IsGoodPt Sb Wr u 0) (hcut : YuanSimpleApprox.IsCutTime η t)
    (hland : extendFrom H (Supp8.BHMean.jointInv Ψi Wr u) 0 = η t) :
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) := by
  have htK : η t ∈ fwdHull w t := by
    rw [hη.2.2 t ht.le]
    exact ⟨hcut.1, Or.inl (subset_closure ⟨t, ⟨ht.le, le_rfl⟩, rfl⟩)⟩
  obtain ⟨v, hv, hFv, hT⟩ := Union.exists_tendsto_transition_rel hΨ hw hw0 hη ht.le hWr hWr0 hηr hu hKin
    (z := 0) (by simp) hg0 (by rw [hland]; exact fun h => h.2 htK)
  have hvr : v = (v.re : ℂ) := Complex.ext (by simp) (by simp [hv])
  rw [hland, hvr] at hFv
  have hv0 := hη.eq_zero_of_extendFrom_eq_of_isCutTime hw hw0 ht hcut hFv
  rw [hvr, hv0, Complex.ofReal_zero] at hT
  exact hT

/-- **For SB2's relative chain the joint parametrization lands at `β'(t_L + s)` from `0`.** -/
theorem extendFrom_jointInv_zero_of_isSB2RelChain {A : Set ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ}
    {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hlift : ∀ s, g (γ s) = β' (tL + s)) (hch : IsSB2RelChain A c β' γ tL S₀ Wr ηr) {s : ℝ} (hs : s ∈ Icc 0 S₀) :
    extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) 0 =
      β' (tL + s.toNNReal) := by
  obtain ⟨hWr, hWr0, hηr, -, -, -, hK⟩ := hch
  obtain ⟨hu, hηa, -, -, -⟩ := hK s hs
  rw [extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu (show (0 : ℝ) ≤ (0 : ℂ).im by simp)]
  have h0 : (0 : ℂ) ∈ closure H := by rw [closure_H]; exact show (0 : ℝ) ≤ (0 : ℂ).im by simp
  rw [extendFrom_eq h0 (hηr.tendsto_fwdMapInv_tip hWr hWr0 hu), hηa, hlift]

/-- **The physical tip is fresh when the relative tip is in `ℍ`**: if the physical trace is the injective witness `β'`
on `[0, t_L + s]` and the lift point `γ s` lies in `ℍ`, then `t_L + s` is a cut time — the tip `β'(t_L + s) = g(γ s)` is
in `D_A ⊆ ℍ`, and it was not visited before (injectivity of `β'`). -/
theorem isCutTime_of_lift_mem_H {A : Set ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {η : ℝ → ℂ}
    (hD : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H) (hβ' : Supp9B.IsProperCurve β')
    (hlift : ∀ s, g (γ s) = β' (tL + s)) {s : ℝ} (hs : 0 ≤ s)
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H) :
    YuanSimpleApprox.IsCutTime η ((tL : ℝ) + s) := by
  have ht0 : (0 : ℝ) ≤ (tL : ℝ) + s := by have := tL.coe_nonneg; linarith
  have hte : ((tL : ℝ) + s).toNNReal = tL + s.toNNReal := by
    rw [Real.toNNReal_add tL.coe_nonneg hs, Real.toNNReal_coe]
  have htip : η ((tL : ℝ) + s) = β' (tL + s.toNNReal) := by
    rw [hηβ _ ⟨ht0, le_rfl⟩, hte]
  refine ⟨?_, ?_⟩
  · rw [htip, ← hlift, hgi hγH]
    exact (hD.inv_mem hγH).1
  · rintro ⟨r, hr, hre⟩
    rw [hηβ r ⟨hr.1, hr.2.le⟩, htip] at hre
    have := hβ'.2.1 hre
    have h2 : ((r.toNNReal : ℝ≥0) : ℝ) = ((tL + s.toNNReal : ℝ≥0) : ℝ) := by rw [this]
    rw [Real.coe_toNNReal _ hr.1, NNReal.coe_add, Real.coe_toNNReal _ hs] at h2
    linarith [hr.2]

end InteractingSLE.Theorem14.SB.FinRel
