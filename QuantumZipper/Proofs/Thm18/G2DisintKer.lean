import QuantumZipper.Proofs.Thm18.G2DisintCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the (untruncated) root kernel is s-finite

`g2FinKer ν M e = ν(e)|_M` when `ν(e)(M) < ∞` (else `0`) is an s-finite kernel: it is the sum over
`n` of the finite kernels on `{⌊ν(e)(M)⌋ = n}` (`g2FinKer_apply`). With it, the product form
`g2_core_transfer'` holds without truncating the root mass. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

section Ker

variable {E : Type*} [MeasurableSpace E]

/-- The `n`-th piece: `ν(e)|_M` on `{ν(e)(M) < ∞, ⌊ν(e)(M)⌋ = n}`. -/
def g2Piece (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ} (hM : MeasurableSet M)
    (n : ℕ) : Kernel E ℝ where
  toFun e := if ν e M < ⊤ ∧ ⌊(ν e M).toReal⌋₊ = n then (ν e).restrict M else 0
  measurable' := by
    have hm : Measurable fun e => ν e M := (Measure.measurable_coe hM).comp hν
    refine Measurable.ite ((measurableSet_lt hm measurable_const).inter
      (measurableSet_eq_fun (Nat.measurable_floor.comp hm.ennreal_toReal) measurable_const))
      ?_ measurable_const
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter hM)).comp hν

instance g2Piece_finite (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ}
    (hM : MeasurableSet M) (n : ℕ) : IsFiniteKernel (g2Piece ν hν hM n) := by
  refine ⟨⟨(n : ℝ≥0∞) + 1, by simp, fun e => ?_⟩⟩
  show (if ν e M < ⊤ ∧ ⌊(ν e M).toReal⌋₊ = n then (ν e).restrict M else 0) univ ≤ _
  split_ifs with h
  · rw [Measure.restrict_apply_univ, ← ENNReal.ofReal_toReal h.1.ne]
    have := Nat.lt_floor_add_one (ν e M).toReal
    rw [h.2] at this
    calc ENNReal.ofReal (ν e M).toReal ≤ ENNReal.ofReal ((n : ℝ) + 1) :=
          ENNReal.ofReal_le_ofReal this.le
      _ = (n : ℝ≥0∞) + 1 := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp
  · simp

/-- The root kernel `ν(e)|_M` (finite masses only). -/
def g2FinKer (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ} (hM : MeasurableSet M) :
    Kernel E ℝ :=
  Kernel.sum (g2Piece ν hν hM)

instance g2FinKer_sfinite (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ}
    (hM : MeasurableSet M) : IsSFiniteKernel (g2FinKer ν hν hM) :=
  ⟨⟨_, fun n => g2Piece_finite ν hν hM n, rfl⟩⟩

theorem g2FinKer_apply (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ}
    (hM : MeasurableSet M) (e : E) :
    g2FinKer ν hν hM e = if ν e M < ⊤ then (ν e).restrict M else 0 := by
  ext s hs
  rw [g2FinKer, Kernel.sum_apply' _ _ hs]
  have hp : ∀ n, g2Piece ν hν hM n e s =
      if ν e M < ⊤ ∧ ⌊(ν e M).toReal⌋₊ = n then (ν e).restrict M s else 0 := fun n => by
    show (if ν e M < ⊤ ∧ ⌊(ν e M).toReal⌋₊ = n then (ν e).restrict M else 0) s = _
    split_ifs <;> simp
  simp_rw [hp]
  split_ifs with h
  · rw [tsum_eq_single ⌊(ν e M).toReal⌋₊ fun n hn => if_neg fun h' => hn h'.2.symm,
      if_pos ⟨h, rfl⟩]
  · simp [h]

/-- **Product form of the rooted integral**, for any s-finite root kernel. -/
theorem g2_core_transfer' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → E} {α : Ω → ℝ} (hY : Measurable Y) (hα : Measurable α)
    (hind : IndepFun Y α P) (κ : Kernel E ℝ) [IsSFiniteKernel κ] {H : E × ℝ × ℝ → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ ω, ∫⁻ x, H (Y ω, x, α ω) ∂(κ (Y ω)) ∂P =
      ∫⁻ e, ∫⁻ x, ∫⁻ a, H (e, x, a) ∂(P.map α) ∂(κ e) ∂(P.map Y) := by
  set κ' : Kernel (E × ℝ) ℝ := κ.comap Prod.fst measurable_fst with hκ'
  have hΦ : Measurable fun p : E × ℝ => ∫⁻ x, H (p.1, x, p.2) ∂(κ p.1) := by
    have hf : Measurable fun q : (E × ℝ) × ℝ => H (q.1.1, q.2, q.1.2) :=
      hH.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact hf.lintegral_kernel_prod_right' (κ := κ')
  have h1 := lintegral_indep_transfer hY hα hind hΦ
  simp only at h1
  rw [h1, ← lintegral_map (f := fun e => ∫⁻ a, ∫⁻ x, H (e, x, a) ∂(κ e) ∂(P.map α))
    hΦ.lintegral_prod_right' hY]
  refine lintegral_congr fun e => ?_
  have hHe : Measurable fun q : ℝ × ℝ => H (e, q.2, q.1) :=
    hH.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap (μ := P.map α) (ν := κ e) (f := fun a x => H (e, x, a))
    hHe.aemeasurable

/-- The product measure `(law Y ⊗ κ) ⊗ N` in iterated form. -/
theorem g2_prod_compProd_apply (μ : Measure E) [SFinite μ] (κ : Kernel E ℝ) [IsSFiniteKernel κ]
    (N : Measure ℝ) [SFinite N] {T : Set ((E × ℝ) × ℝ)} (hT : MeasurableSet T) :
    ((μ ⊗ₘ κ).prod N) T = ∫⁻ e, ∫⁻ x, ∫⁻ a, T.indicator 1 ((e, x), a) ∂N ∂(κ e) ∂μ := by
  rw [← lintegral_indicator_one hT, lintegral_prod _ ((measurable_one.indicator hT).aemeasurable),
    Measure.lintegral_compProd]
  exact (measurable_one.indicator hT).lintegral_prod_right'

end Ker

end Thm18Asm
end QuantumZipper
