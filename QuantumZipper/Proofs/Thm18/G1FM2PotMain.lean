import QuantumZipper.Proofs.Thm18.G1FM2Pot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2 (energy), part 4: `PushPotLip` for the selected maps

Assembly of `G1FM2.pushPot_comp_lip` with uniform constants (`G1FM2.psi_consts`) and the Koebe
`1/4` covering theorem (`CA.Koebe.ball_subset_image_koebe`). Main result:
`G1FM2.pushPotLip_holds : ∀ ψ, PsiGood ψ → PushPotLip ψ`. Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ComplexConjugate Real

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

open G1RC CA.Koebe

/-- **`PushPotLip` holds for every selected map.** -/
theorem pushPotLip_holds (ψ : ℂ → ℂ) (hψ : PsiGood ψ) : PushPotLip ψ := by
  intro m
  have hd := hψ.2.1
  have hinj := hψ.2.2.1
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set h : ℝ := 1 / ((m : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨M₀, M₁, M₂, a₀, c₀, hM₀, hM₁, hM₂, ha₀, hc₀, hK⟩ :=
    psi_consts hψ (2 * ((m : ℝ) + 1) + 1) (h / 2) (by positivity)
  set rD : ℝ := min (h / 4) (min 1 (a₀ / (4 * (M₂ + 1)))) with hrD
  have hrD0 : 0 < rD := lt_min (by positivity) (lt_min one_pos (by positivity))
  have hrD1 : rD ≤ h / 4 := min_le_left _ _
  have hrD2 : rD ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrD3 : rD ≤ a₀ / (4 * (M₂ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hM₂rD : M₂ * rD ≤ a₀ / 4 := by
    have h1 : (M₂ + 1) * rD ≤ a₀ / 4 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M₂ + 1))] at hrD3
      nlinarith
    nlinarith
  set α : ℝ := a₀ / 2 with hαdef
  have hα : 0 < α := by positivity
  set LE : ℝ := M₂ / α + 1 / h + M₁ / (2 * c₀) with hLEdef
  set B₀ : ℝ := D3Plus.fmBase.real univ with hB₀
  have hB₀0 : 0 ≤ B₀ := measureReal_nonneg
  have hLE0 : 0 ≤ LE := by positivity
  set L : ℝ := (2 * π + 2 * (B₀ * LE)) * (((m : ℝ) + 1) / α) with hLdef
  set ρ₁ : ℝ := koebeCovConst * rD * (a₀ * h) with hρ₁
  set τ₁ : ℝ := min (rD / 2) (min (h / 3) 1) with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (lt_min (by positivity) one_pos)
  have hτ₁a : τ₁ ≤ rD / 2 := min_le_left _ _
  have hτ₁b : τ₁ ≤ h / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁c : τ₁ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hκ := koebeCovConst_pos
  refine ⟨M₀, M₁, rD, L, ρ₁, τ₁, hM₀, hM₁, hrD0, by positivity, by positivity, hτ₁0,
    by linarith, fun w hw1 hw2 => ?_⟩
  have hr : rD < w.im := by linarith
  have hDreg : ∀ z ∈ closedBall w rD, z ∈ reg (2 * ((m : ℝ) + 1) + 1) (h / 2) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := norm_le_norm_add_norm_sub' z w
      rw [← dist_eq_norm] at this
      linarith [mem_closedBall.1 hz]
    · linarith [im_ge_of_mem hz]
  have hDH := closedBall_subset_H hr
  have hψlip : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD, ‖ψ x - ψ x'‖ ≤ M₁ * ‖x - x'‖ :=
    fun x hx x' hx' => norm_sub_le_of_deriv hd hr (fun z hz => (hK z (hDreg z hz)).2.1) hx hx'
  have hψ'lip : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
      ‖deriv ψ x - deriv ψ x'‖ ≤ M₂ * ‖x - x'‖ :=
    fun x hx x' hx' => norm_sub_le_of_deriv (hd.deriv isOpen_H) hr
      (fun z hz => (hK z (hDreg z hz)).2.2.2.1) hx hx'
  refine ⟨hr, fun x hx => (hK x (hDreg x hx)).1, hψlip, fun u hu S hS τ s hτ hττ₁ hs hsτ => ?_⟩
  have hSh : h ≤ S := hS.1
  have hS0 : 0 < S := hh0.trans_le hSh
  set f : ℂ → ℂ := fun z => (S : ℂ) * ψ z with hf
  have hfd : DifferentiableOn ℂ f H := (differentiableOn_const _).mul hd
  have hfinj : InjOn f H := fun a ha b hb hab => hinj ha hb
    (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hS0.ne') hab)
  have hder : ∀ x ∈ H, deriv f x = (S : ℂ) * deriv ψ x := fun x hx =>
    deriv_const_mul _ (hd.differentiableAt (isOpen_H.mem_nhds hx))
  have hnS : ‖(S : ℂ)‖ = S := by rw [Complex.norm_real, Real.norm_of_nonneg hS0.le]
  have hL : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
      ‖deriv f x - deriv f x'‖ ≤ S * M₂ * ‖x - x'‖ := by
    intro x hx x' hx'
    rw [hder x (hDH hx), hder x' (hDH hx'), ← mul_sub, norm_mul, hnS, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hψ'lip x hx x' hx') hS0.le
  have hwD : w ∈ closedBall w rD := mem_closedBall_self hrD0.le
  have hdw : S * a₀ ≤ ‖deriv f w‖ := by
    rw [hder w (hDH hwD), norm_mul, hnS]
    exact mul_le_mul_of_nonneg_left (hK w (hDreg w hwD)).2.2.1 hS0.le
  have hq : ∀ x ∈ closedBall w rD, ∀ y ∈ closedBall w rD, S * α ≤ ‖fmQ f x y‖ := by
    intro x hx y hy
    have h1 := norm_fmQ_sub_le (M₂ := S * M₂) hfd hr (fun z hz => by
      refine (hL z hz w hwD).trans ?_
      exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz)
        (by positivity)) hx hy
    have h2 := norm_sub_norm_le (deriv f w) (deriv f w - fmQ f x y)
    rw [sub_sub_cancel] at h2
    rw [norm_sub_rev] at h1
    have h3 : S * M₂ * rD ≤ S * (a₀ / 4) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hM₂rD hS0.le
    rw [hαdef]
    nlinarith
  have him : ∀ x ∈ closedBall w rD, S * c₀ ≤ ((S : ℂ) * ψ x).im := by
    intro x hx
    rw [Complex.im_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (hK x (hDreg x hx)).2.2.2.2 hS0.le
  have hM₁f : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
      ‖(S : ℂ) * ψ x - (S : ℂ) * ψ x'‖ ≤ S * M₁ * ‖x - x'‖ := by
    intro x hx x' hx'
    rw [← mul_sub, norm_mul, hnS, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hψlip x hx x' hx') hS0.le
  have hLE : S * M₂ / (S * α) + 1 / (2 * (w.im - rD)) + S * M₁ / (2 * (S * c₀)) ≤ LE := by
    have e1 : S * M₂ / (S * α) = M₂ / α := by field_simp
    have e2 : S * M₁ / (2 * (S * c₀)) = M₁ / (2 * c₀) := by field_simp
    rw [e1, e2, hLEdef]
    have : 1 / (2 * (w.im - rD)) ≤ 1 / h := by
      apply one_div_le_one_div_of_le hh0
      linarith
    linarith
  have hτ3 : 3 * τ ≤ w.im := by linarith
  have key := fun x hx x' hx' => pushPot_comp_lip (x := x) (x' := x') hψ hS0 hu hr hτ hs hsτ
    (by linarith) hτ3 (by positivity) (by positivity) (by positivity) hL hq him hM₁f hLE hx hx'
  -- Koebe covering
  have hball : ball w rD ⊆ H := ball_subset_closedBall.trans hDH
  have hcov := ball_subset_image_koebe (hfd.mono hball) (hfinj.mono hball)
  have hρ : ρ₁ ≤ koebeCovConst * rD * ‖deriv f w‖ := by
    rw [hρ₁]
    refine mul_le_mul_of_nonneg_left (hdw.trans' ?_) (by positivity)
    rw [mul_comm a₀ h]; exact mul_le_mul_of_nonneg_right hSh ha₀.le
  intro p hp p' hp'
  obtain ⟨x, hx, rfl⟩ := hcov (ball_subset_ball hρ hp)
  obtain ⟨x', hx', rfl⟩ := hcov (ball_subset_ball hρ hp')
  have hxD := ball_subset_closedBall hx
  have hx'D := ball_subset_closedBall hx'
  have k1 := key x hxD x' hx'D
  have hpp : S * α * ‖x - x'‖ ≤ ‖f x - f x'‖ := by
    rw [fmQ_spec hfd hr hxD hx'D, norm_mul]
    exact mul_le_mul_of_nonneg_right (hq x hxD x' hx'D) (norm_nonneg _)
  have hxx : ‖x - x'‖ ≤ ((m : ℝ) + 1) / α * ‖f x - f x'‖ := by
    have h1 : h * α * ‖x - x'‖ ≤ ‖f x - f x'‖ :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hα.le)
        (norm_nonneg _)) hpp
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    rw [hh] at h1
    have e : 1 / ((m : ℝ) + 1) * α * ‖x - x'‖ * ((m : ℝ) + 1) = α * ‖x - x'‖ := by
      field_simp
    have := mul_le_mul_of_nonneg_right h1 hm1.le
    linarith
  have hK1 : 2 * π / τ + 2 * (B₀ * LE) ≤ (2 * π + 2 * (B₀ * LE)) / τ := by
    rw [add_div]
    have : 2 * (B₀ * LE) ≤ 2 * (B₀ * LE) / τ :=
      le_div_self (by positivity) hτ (hττ₁.trans hτ₁c)
    exact add_le_add le_rfl this
  show |pushPot ψ S w ((τ : ℂ) * u) s (f x) - pushPot ψ S w ((τ : ℂ) * u) s (f x')| ≤
    L / τ * ‖f x - f x'‖
  calc _ ≤ (2 * π / τ + 2 * (B₀ * LE)) * ‖x - x'‖ := k1
    _ ≤ (2 * π + 2 * (B₀ * LE)) / τ * (((m : ℝ) + 1) / α * ‖f x - f x'‖) :=
        mul_le_mul hK1 hxx (norm_nonneg _) (by positivity)
    _ = L / τ * ‖f x - f x'‖ := by rw [hLdef]; ring

end G1FM2
end Thm18Asm
end QuantumZipper
