import QuantumZipper.Proofs.Zipper.SWCoreB5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (2): dilated class maps stay in a class, Lipschitz in the dilation

For `ψ ∈ BdryClass a b ρ M m`, a sub-segment `[α, β]` with `c [α, β] ⊂ [a, b]` for all
`c ∈ [1,2]`, and `4ρ' ≤ ρ`, the dilated maps `z ↦ ψ(c z)`, `c ∈ [1,2]`, lie in
`BdryClass α β ρ' M m` (`dil_mem_class`) and depend Lipschitz-continuously on `c` on the
`ρ'`-thickening (`dil_lipschitz`, constant `(4M/ρ)(|α| + |β| + ρ')`). This is the family input
(the dilation as one more parameter) of the offset form of the boundary transport, SWC-B8.
Own elementary proof (chain rule, Cauchy estimate `norm_deriv_le_of_class`).
-/

noncomputable section

open Set Metric

namespace QuantumZipper
namespace SWCore

variable {a b ρ M m : ℝ} {ψ : ℂ → ℂ}

theorem dil_mem_thick {α β ρ' c : ℝ} (hc : c ∈ Icc (1 : ℝ) 2)
    (hin : ∀ t ∈ Icc α β, c * t ∈ Icc a b) {z : ℂ} (hz : z ∈ thickening ρ' (segC α β)) :
    (c : ℂ) * z ∈ thickening (2 * ρ') (segC a b) := by
  obtain ⟨_, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.1 hz
  refine mem_thickening_iff.2 ⟨((c * t : ℝ) : ℂ), ⟨c * t, hin t ht, rfl⟩, ?_⟩
  have hc0 : 0 < c := by linarith [hc.1]
  rw [dist_eq_norm, show (c : ℂ) * z - ((c * t : ℝ) : ℂ) = (c : ℂ) * (z - t) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, ← dist_eq_norm]
  nlinarith [hc.2, dist_nonneg (x := z) (y := (t : ℂ))]

theorem dil_mem_class (hψ : ψ ∈ BdryClass a b ρ M m) {α β ρ' : ℝ} (hρ' : 0 < ρ')
    (hρ'ρ : 2 * ρ' ≤ ρ) {c : ℝ} (hc : c ∈ Icc (1 : ℝ) 2)
    (hin : ∀ t ∈ Icc α β, c * t ∈ Icc a b) (hm : 0 ≤ m) :
    (fun z => ψ ((c : ℂ) * z)) ∈ BdryClass α β ρ' M m := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hthick : ∀ z ∈ thickening ρ' (segC α β), (c : ℂ) * z ∈ thickening ρ (segC a b) :=
    fun z hz => thickening_mono hρ'ρ _ (dil_mem_thick hc hin hz)
  have hdiff : DifferentiableOn ℂ (fun z => ψ ((c : ℂ) * z)) (thickening ρ' (segC α β)) :=
    hψ.1.comp ((differentiable_id.const_mul _).differentiableOn) hthick
  refine ⟨hdiff, fun z hz => hψ.2.1 _ (hthick z hz), fun t ht => ?_, ?_, fun t ht => ?_⟩
  · have := hψ.2.2.1 (c * t) (hin t ht)
    simpa [Complex.ofReal_mul] using this
  · intro t ht s hs hts
    have h := hψ.2.2.2.1 (hin t ht) (hin s hs) (mul_lt_mul_of_pos_left hts hc0)
    simpa [Complex.ofReal_mul] using h
  · have hct : ((c * t : ℝ) : ℂ) ∈ thickening ρ (segC a b) :=
      self_subset_thickening (by linarith) _ ⟨c * t, hin t ht, rfl⟩
    have hdψ : DifferentiableAt ℂ ψ ((c : ℂ) * t) := by
      have := hψ.1.differentiableAt (isOpen_thickening.mem_nhds hct)
      simpa [Complex.ofReal_mul] using this
    have hder : deriv (fun z => ψ ((c : ℂ) * z)) (t : ℂ) = (c : ℂ) * deriv ψ ((c : ℂ) * t) := by
      have h1 : HasDerivAt (fun z : ℂ => (c : ℂ) * z) (c : ℂ) (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).const_mul (c : ℂ)
      exact (hdψ.hasDerivAt.comp (t : ℂ) h1).deriv.trans (mul_comm _ _)
    rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have hm' := hψ.2.2.2.2 (c * t) (hin t ht)
    have e : (((c * t : ℝ)) : ℂ) = (c : ℂ) * t := by push_cast; ring
    rw [e] at hm'
    nlinarith [hc.1, norm_nonneg (deriv ψ ((c : ℂ) * t))]

/-- **Lipschitz dependence on the dilation.** -/
theorem dil_lipschitz (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {α β ρ' : ℝ} (hρ' : 0 < ρ')
    (hρ'ρ : 4 * ρ' ≤ ρ) (hin : ∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc α β, c * t ∈ Icc a b)
    {c c' : ℝ} (hc : c ∈ Icc (1 : ℝ) 2) (hc' : c' ∈ Icc (1 : ℝ) 2) {z : ℂ}
    (hz : z ∈ thickening ρ' (segC α β)) :
    ‖ψ ((c : ℂ) * z) - ψ ((c' : ℂ) * z)‖ ≤ 4 * M / ρ * ‖z‖ * |c - c'| := by
  set S : Set ℂ := segment ℝ ((c' : ℂ) * z) ((c : ℂ) * z) with hS
  have hSsub : S ⊆ thickening (ρ / 2) (segC a b) := by
    intro w hw
    obtain ⟨θ, η, hθ, hη, hθη, rfl⟩ := hw
    have hcθ : θ * c' + η * c ∈ Icc (1 : ℝ) 2 := by
      constructor <;> nlinarith [hc.1, hc.2, hc'.1, hc'.2]
    have := dil_mem_thick hcθ (hin _ hcθ) hz
    have e : θ • ((c' : ℂ) * z) + η • ((c : ℂ) * z) = ((θ * c' + η * c : ℝ) : ℂ) * z := by
      simp only [Complex.real_smul]; push_cast; ring
    rw [e]
    exact thickening_mono (by linarith) _ this
  have hdS : ∀ w ∈ S, DifferentiableAt ℂ ψ w := fun w hw =>
    hψ.1.differentiableAt (isOpen_thickening.mem_nhds
      (thickening_mono (by linarith) _ (hSsub hw)))
  have hb : ∀ w ∈ S, ‖deriv ψ w‖ ≤ 4 * M / ρ := fun w hw =>
    norm_deriv_le_of_class hψ hρ (hSsub hw)
  have key := (convex_segment _ _).norm_image_sub_le_of_norm_deriv_le hdS hb
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have e2 : ‖(c : ℂ) * z - (c' : ℂ) * z‖ = ‖z‖ * |c - c'| := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  rw [e2] at key
  calc _ ≤ 4 * M / ρ * (‖z‖ * |c - c'|) := key
    _ = _ := by ring

end SWCore
end QuantumZipper
