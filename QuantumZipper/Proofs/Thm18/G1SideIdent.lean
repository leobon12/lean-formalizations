import QuantumZipper.Proofs.Thm18.G1SideOff2
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1RegRepRed
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (9): the transported limit is the pullback of the canonical boundary measure

For the dilation-family member with boundary values `t ↦ s Φ(c t)` on `[a,b]` (`s` the canonical
scale, `c ∈ [1,2]` the offset), the limit functional of the uniform transport, applied to the
dilated test function `f(c ·)`, is `∫ f d(Φ⁻¹_*(ν|_S))` with `ν` the boundary measure of the
rescaled field `rescale w Q s` (`limit_ident`). Ingredients: `GoodTransforms.qBoundaryMeasure_rescale`
(M4-T3, `ν_{rescale w Q s} = (·/s)_* ν_w`) and the change of variables `u = s Φ(c t)`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open Thm18Asm

theorem symm_notMem_side {left : Bool} {Φ : ℝ ≃o ℝ} (hΦ0 : Φ 0 = 0) {v : ℝ}
    (hv : v ∉ g1SideHalf left) : Φ.symm v ∉ g1SideHalf left := by
  have h0 : Φ.symm 0 = 0 := Φ.symm_apply_eq.2 hΦ0.symm
  cases left
  · simp only [g1SideHalf, Bool.false_eq_true, ↓reduceIte, mem_Ioi, not_lt] at hv ⊢
    calc Φ.symm v ≤ Φ.symm 0 := Φ.symm.monotone hv
      _ = 0 := h0
  · simp only [g1SideHalf, ↓reduceIte, mem_Iio, not_lt] at hv ⊢
    calc (0 : ℝ) = Φ.symm 0 := h0.symm
      _ ≤ Φ.symm v := Φ.symm.monotone hv

/-- **Identification of the limit functional.** -/
theorem limit_ident {γ : ℝ} (hγ : 0 < γ) {w : FieldSample} (hw : IsLQGGood γ w) {s c : ℝ}
    (hs : 0 < s) (hc : c ∈ Icc (1 : ℝ) 2) {left : Bool} {Φ : ℝ ≃o ℝ} (hΦ0 : Φ 0 = 0)
    {Ψq : ℂ → ℂ} {a b a' b' : ℝ} (hab : a ≤ b) (hsub : Icc a' b' ⊆ Icc a b)
    (hS : Icc a' b' ⊆ g1SideHalf left)
    (hbv : ∀ t ∈ Icc a b, Ψq t = ((s * Φ (c * t) : ℝ) : ℂ)) {f : ℝ → ℝ} (hf : Continuous f)
    (hvan : ∀ u, u ∉ Icc a' b' → f (c * u) = 0) (hvan1 : ∀ u, u ∉ Icc a' b' → f u = 0) :
    ∫ u in Icc (Ψq a).re (Ψq b).re,
        f (c * Function.invFunOn (fun t : ℝ => (Ψq t).re) (Icc a b) u) ∂qBoundaryMeasure γ w =
      ∫ v, f v ∂(((qBoundaryMeasure γ (rescale w (Qc γ) s)).restrict (g1SideHalf left)).map
        Φ.symm) := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hre : ∀ t ∈ Icc a b, (Ψq t).re = s * Φ (c * t) := fun t ht => by
    rw [hbv t ht]; simp
  set g : ℝ → ℝ := fun u => f (Φ.symm (u / s)) with hg
  have hΦc : Continuous Φ.symm := Φ.symm.continuous
  have hgc : Continuous g := hf.comp (hΦc.comp (continuous_id.div_const s))
  -- the boundary values are strictly increasing on `[a,b]`
  have hmono : StrictMonoOn (fun t : ℝ => (Ψq t).re) (Icc a b) := fun x hx y hy hxy => by
    simp only [hre x hx, hre y hy]
    exact mul_lt_mul_of_pos_left (Φ.strictMono (mul_lt_mul_of_pos_left hxy hc0)) hs
  -- the integrand on the image interval
  have hEq : EqOn (fun u => f (c * Function.invFunOn (fun t : ℝ => (Ψq t).re) (Icc a b) u)) g
      (Icc (Ψq a).re (Ψq b).re) := by
    intro u hu
    set t := Φ.symm (u / s) / c with ht
    have hua : u / s ∈ Icc (Φ (c * a)) (Φ (c * b)) := by
      rw [hre a ⟨le_rfl, hab⟩, hre b ⟨hab, le_rfl⟩] at hu
      constructor
      · rw [le_div_iff₀ hs]; linarith [hu.1]
      · rw [div_le_iff₀ hs]; linarith [hu.2]
    have htI : t ∈ Icc a b := by
      have h1 : c * a ≤ Φ.symm (u / s) := by
        rw [← Φ.le_iff_le, Φ.apply_symm_apply]; exact hua.1
      have h2 : Φ.symm (u / s) ≤ c * b := by
        rw [← Φ.le_iff_le, Φ.apply_symm_apply]; exact hua.2
      constructor
      · rw [ht, le_div_iff₀ hc0]; linarith
      · rw [ht, div_le_iff₀ hc0]; linarith
    have hct : c * t = Φ.symm (u / s) := by rw [ht]; field_simp
    have hut : (Ψq t).re = u := by
      rw [hre t htI, hct, Φ.apply_symm_apply]; field_simp
    have hmem : u ∈ (fun t : ℝ => (Ψq t).re) '' Icc a b := ⟨t, htI, hut⟩
    have hinv : Function.invFunOn (fun t : ℝ => (Ψq t).re) (Icc a b) u = t :=
      hmono.injOn (Function.invFunOn_mem hmem) htI ((Function.invFunOn_eq hmem).trans hut.symm)
    simp only [hinv, hct, hg]
  rw [setIntegral_congr_fun measurableSet_Icc hEq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := qBoundaryMeasure γ w) (f := g)
    (s := Icc (Ψq a).re (Ψq b).re) (fun u hu => by
      by_contra hne
      set y := Φ.symm (u / s) / c with hy
      have hcy : c * y = Φ.symm (u / s) := by rw [hy]; field_simp
      have hy1 : y ∈ Icc a' b' := by
        by_contra hn; exact hne (by simp only [hg, ← hcy]; exact hvan y hn)
      have hyI := hsub hy1
      apply hu
      rw [hre a ⟨le_rfl, hab⟩, hre b ⟨hab, le_rfl⟩]
      have hu' : u = s * Φ (c * y) := by rw [hcy, Φ.apply_symm_apply]; field_simp
      rw [hu']
      exact ⟨mul_le_mul_of_nonneg_left (Φ.monotone (mul_le_mul_of_nonneg_left hyI.1 hc0.le))
          hs.le,
        mul_le_mul_of_nonneg_left (Φ.monotone (mul_le_mul_of_nonneg_left hyI.2 hc0.le)) hs.le⟩)]
  -- the right side
  rw [integral_map hΦc.measurable.aemeasurable hf.aestronglyMeasurable,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => hvan1 _ fun h =>
      symm_notMem_side hΦ0 hv (hS h)),
    GoodTransforms.qBoundaryMeasure_rescale hw hγ hs,
    integral_map (φ := fun u : ℝ => u / s) (f := fun v => f (Φ.symm v))
      (by fun_prop) (hf.comp hΦc).aestronglyMeasurable]

end G1Side
end QuantumZipper
