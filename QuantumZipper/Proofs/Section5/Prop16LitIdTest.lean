import QuantumZipper.Proofs.Section5.Prop16LitChartInv
import QuantumZipper.Proofs.Section5.Prop16LitExAQ
import QuantumZipper.Proofs.Complex.BasicsUnivalent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: pulled-back test functions through the charts (D98)

For a test function `F x` supported in the chart domain `U_x = B(0, r₀ x) ∩ ℍ`, the function
`w ↦ F x (ψ_x⁻¹ w)` on `ψ_x(U_x)`, `0` elsewhere (`Prop16Lit.pullT`), is jointly measurable in
`(x, w)` (through `chartInv`), agrees for each `x` with `SWCore.pullTest (ψ x) R (F x)` for every
`R ⊆ ℍ` containing the support (`pullT_eq_pullTest`), and is therefore a continuous test function
with compact support in `ψ_x(U_x)` (`continuous_pullT`, SW's equicontinuity `pullTest_equicont`)
whose integrals are the integrals of `F x` against the pullback (`integral_pullT`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open SWCore G1Side

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

open Classical in
/-- The test function `F x ∘ ψ_x⁻¹`, extended by `0`. -/
def pullT (ψ : ℝ → ℂ → ℂ) (a b : ℝ) (r₀ : ℝ → ℝ) (F : ℝ → ℂ → ℝ) (x : ℝ) (w : ℂ) : ℝ :=
  if (x, w) ∈ range (chartPair ψ a b r₀) then F x (chartInv ψ a b r₀ x w) else 0

open Classical in
theorem measurable_pullT (hfam : LitFamily D a b ψ r₀) {F : ℝ → ℂ → ℝ}
    (hF : Measurable fun q : ℝ × ℂ => F q.1 q.2) :
    Measurable fun q : ℝ × ℂ => pullT ψ a b r₀ F q.1 q.2 := by
  unfold pullT
  exact Measurable.ite (measurableEmbedding_chartPair hfam).measurableSet_range
    (hF.comp (measurable_fst.prodMk (measurable_chartInv hfam))) measurable_const

theorem mem_range_chartPair_iff {x : ℝ} (hx : x ∈ Ioo a b) {w : ℂ} :
    (x, w) ∈ range (chartPair ψ a b r₀) ↔ w ∈ ψ x '' (ball 0 (r₀ x) ∩ H) := by
  constructor
  · rintro ⟨⟨⟨x', u⟩, hx', hu⟩, h⟩
    simp only [chartPair, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨(x, u), hx, hu⟩, rfl⟩

/-- **Pointwise identification with `pullTest`.** -/
theorem pullT_eq_pullTest (hfam : LitFamily D a b ψ r₀) {x : ℝ} (hx : x ∈ Ioo a b)
    {F : ℝ → ℂ → ℝ} (hFU : tsupport (F x) ⊆ ball 0 (r₀ x) ∩ H) {R : Set ℂ} (hRH : R ⊆ H)
    (hFR : tsupport (F x) ⊆ R) : pullT ψ a b r₀ F x = pullTest (ψ x) R (F x) := by
  classical
  have hinj : InjOn (ψ x) H := (hfam.2.2 x hx).2.1
  funext w
  unfold pullT pullTest
  by_cases hw : (x, w) ∈ range (chartPair ψ a b r₀)
  · rw [if_pos hw]
    obtain ⟨u, hu, rfl⟩ := (mem_range_chartPair_iff hx).1 hw
    rw [chartInv_apply hfam hx hu]
    by_cases hR : ψ x u ∈ ψ x '' R
    · rw [if_pos hR]
      have h1 := Function.invFunOn_mem hR
      have h2 := Function.invFunOn_eq hR
      rw [hinj (hRH h1) hu.2 h2]
    · rw [if_neg hR]
      exact image_eq_zero_of_notMem_tsupport fun h => hR ⟨u, hFR h, rfl⟩
  · rw [if_neg hw]
    split_ifs with hR
    · symm
      refine image_eq_zero_of_notMem_tsupport fun h => hw ?_
      exact (mem_range_chartPair_iff hx).2 ⟨_, hFU h, Function.invFunOn_eq hR⟩
    · rfl

/-- The support of the pulled-back test function. -/
theorem tsupport_pullT_subset (hfam : LitFamily D a b ψ r₀) {x : ℝ} (hx : x ∈ Ioo a b)
    {F : ℝ → ℂ → ℝ} (hFs : HasCompactSupport (F x)) (hFU : tsupport (F x) ⊆ ball 0 (r₀ x) ∩ H) :
    tsupport (pullT ψ a b r₀ F x) ⊆ ψ x '' tsupport (F x) := by
  have hcont : ContinuousOn (ψ x) (tsupport (F x)) :=
    (hfam.2.2 x hx).1.continuousOn.mono (hFU.trans inter_subset_right)
  refine closure_minimal (fun w hw => ?_) (hFs.isCompact.image_of_continuousOn hcont).isClosed
  classical
  unfold pullT at hw
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hw
  obtain ⟨hr, hne⟩ := hw
  obtain ⟨u, hu, rfl⟩ := (mem_range_chartPair_iff hx).1 hr
  rw [chartInv_apply hfam hx hu] at hne
  exact ⟨u, subset_tsupport _ hne, rfl⟩

/-- **Continuity of the pulled-back test function.** -/
theorem continuous_pullT (hfam : LitFamily D a b ψ r₀) (hDH : D ⊆ H) {x : ℝ} (hx : x ∈ Ioo a b)
    {F : ℝ → ℂ → ℝ} (hFc : Continuous (F x)) (hFs : HasCompactSupport (F x))
    (hFU : tsupport (F x) ⊆ ball 0 (r₀ x) ∩ H) : Continuous (pullT ψ a b r₀ F x) := by
  obtain ⟨hψd, hψi, hψim, -⟩ := hfam.2.2 x hx
  have hψH : MapsTo (ψ x) H H := fun w hw =>
    Prop16Asm.zoomDomain_subset_H hDH x (hψim ▸ mem_image_of_mem (ψ x) hw)
  have hψ0 : ∀ z ∈ H, deriv (ψ x) z ≠ 0 := fun z hz =>
    CA.deriv_ne_zero_of_injOn isOpen_H hψd hψi hz
  obtain ⟨n, hn⟩ := exists_recR hFs (hFU.trans inter_subset_right)
  set a' : ℚ := -(n : ℚ) with ha
  set b' : ℚ := (n : ℚ) with hb
  set c' : ℚ := 1 / ((n : ℚ) + 1) with hcq
  set d' : ℚ := (n : ℚ) with hd
  have hrect : rectC (a' : ℝ) b' c' d' = recR n := by
    simp only [recR, ha, hb, hcq, hd]; push_cast; rfl
  have hc0 : (0 : ℝ) < c' := by rw [hcq]; push_cast; positivity
  obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := exists_areaClass (a := a') (b := b') (d := d')
    hψd hψi hψH hψ0 hc0
  have hFK : tsupport (F x) ⊆ interior (rectC (a' : ℝ) b' c' d') := by rw [hrect]; exact hn
  rw [pullT_eq_pullTest hfam hx hFU (hrect ▸ recR_subset_H n)
    (hFK.trans interior_subset)]
  refine Metric.continuous_iff.2 fun w ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hFc hFs hFK (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun w' hw' => ?_⟩
  rw [Real.dist_eq]
  exact (h _ hcl w' w hw').trans_lt (half_lt_self hε)

/-- **Integrals of the pulled-back test function against a measure = integrals of the test
function against the pullback.** -/
theorem integral_pullT (hfam : LitFamily D a b ψ r₀) {x : ℝ} (hx : x ∈ Ioo a b)
    {F : ℝ → ℂ → ℝ} (hFc : Continuous (F x)) (hFU : tsupport (F x) ⊆ ball 0 (r₀ x) ∩ H)
    (ν : Measure ℂ) : ∫ w, pullT ψ a b r₀ F x w ∂ν = ∫ z, F x z ∂pullMu ν (ψ x) := by
  obtain ⟨hψd, hψi, -⟩ := hfam.2.2 x hx
  rw [integral_pullMu hψd.continuousOn hψi inter_subset_right hFc hFU,
    pullT_eq_pullTest hfam hx hFU inter_subset_right hFU]

end Prop16Lit
end QuantumZipper
