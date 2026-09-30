import QuantumZipper.Proofs.Zipper.CfgFMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (6): uniform-in-time Lipschitz bound of the pushed potentials

`CfgFM.tPushPotLip_holds : TPushPotLip W T` for a continuous driver with `W 0 = 0`: the unzipping
maps `ψ_t` (`tpsi`) have local constants (bounds of `ψ_t`, `ψ_t'`, `1/ψ_t'`, `ψ_t''`, `1/Im ψ_t`)
uniform in `t ∈ [0,T]` on compact regions of `ℍ` (`CfgFM.tpsi_consts`: joint continuity of
`(t, z) ↦ ψ_t(z)` and of `log |ψ_t'(z)|`, `RegUnif.continuousOn_fwdMapInv_joint`,
`RegUnif.continuousOn_log_deriv_fwdMapInv_joint`, and the Cauchy estimate for `ψ_t''`), and the
proof of `Thm18Asm.G1FM2.pushPotLip_holds` depends on the map only through these constants
(`CfgFM.pushPotLip_core`, a verbatim generalization). Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ComplexConjugate Real

namespace QuantumZipper.E6
namespace CfgFM

open Thm18Asm Thm18Asm.G1FM2 Thm18Asm.G1RC CA.Koebe

theorem pushPotLip_core (m : ℕ) {M₀ M₁ M₂ a₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (ha₀ : 0 < a₀) (hc₀ : 0 < c₀) :
    ∃ rD L ρ₁ τ₁ : ℝ, 0 < rD ∧ 0 ≤ L ∧ 0 < ρ₁ ∧ 0 < τ₁ ∧ 2 * τ₁ ≤ rD ∧
      rD < 1 / ((m : ℝ) + 1) ∧ ∀ ψ : ℂ → ℂ, PsiGood ψ → (∀ z ∈ reg (2 * ((m : ℝ) + 1) + 1) (1 / ((m : ℝ) + 1) / 2),
        ‖ψ z‖ ≤ M₀ ∧ ‖deriv ψ z‖ ≤ M₁ ∧ a₀ ≤ ‖deriv ψ z‖ ∧ ‖deriv (deriv ψ) z‖ ≤ M₂ ∧
          c₀ ≤ (ψ z).im) →
      ∀ w : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → 1 / ((m : ℝ) + 1) ≤ w.im →
        rD < w.im ∧ (∀ x ∈ closedBall w rD, ‖ψ x‖ ≤ M₀) ∧
        (∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD, ‖ψ x - ψ x'‖ ≤ M₁ * ‖x - x'‖) ∧
        ∀ u : ℂ, ‖u‖ = 1 → ∀ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
          ∀ τ s : ℝ, 0 < τ → τ ≤ τ₁ → 0 ≤ s → s ≤ τ →
            ∀ p ∈ ball ((S : ℂ) * ψ w) ρ₁, ∀ p' ∈ ball ((S : ℂ) * ψ w) ρ₁,
              |pushPot ψ S w ((τ : ℂ) * u) s p - pushPot ψ S w ((τ : ℂ) * u) s p'| ≤
                L / τ * ‖p - p'‖ := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set h : ℝ := 1 / ((m : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
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
  refine ⟨rD, L, ρ₁, τ₁, hrD0, by positivity, by positivity, hτ₁0,
    by linarith, by linarith, fun ψ hψ hK w hw1 hw2 => ?_⟩
  have hd := hψ.2.1
  have hinj := hψ.2.2.1
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

variable {W : ℝ → ℝ}

theorem deriv_tpsi_eq (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H) : deriv (tpsi W t) z = deriv (fwdMapInv W t) z :=
  ((tpsi_eqOn hW hW0 ht).eventuallyEq_of_mem (isOpen_H.mem_nhds hz)).deriv_eq

/-- **Uniform constants of the unzipping maps** on a compact region, for `t ∈ [0,T]`. -/
theorem tpsi_consts (hW : Continuous W) (hW0 : W 0 = 0) (T R h : ℝ) (hh : 0 < h) :
    ∃ M₀ M₁ M₂ a₀ c₀ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 < a₀ ∧ 0 < c₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ reg R h, ‖tpsi W t z‖ ≤ M₀ ∧ ‖deriv (tpsi W t) z‖ ≤ M₁ ∧
        a₀ ≤ ‖deriv (tpsi W t) z‖ ∧ ‖deriv (deriv (tpsi W t)) z‖ ≤ M₂ ∧
          c₀ ≤ (tpsi W t z).im := by
  set K1 : Set (ℝ × ℂ) := Icc (0 : ℝ) T ×ˢ reg (R + h) (h / 2) with hK1
  have hK1c : IsCompact K1 := isCompact_Icc.prod (isCompact_reg _ _)
  have hK1H : K1 ⊆ Icc 0 T ×ˢ H := prod_mono le_rfl (reg_subset_H (by positivity))
  have hc0 := RegUnif.continuousOn_fwdMapInv_joint hW hW0 T
  have hcL := RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T
  obtain ⟨M₀, hM₀⟩ := hK1c.exists_bound_of_continuousOn ((hc0.mono hK1H).norm)
  obtain ⟨Λ, hΛ⟩ := hK1c.exists_bound_of_continuousOn (hcL.mono hK1H)
  -- lower bound of the imaginary part
  obtain ⟨c₀, hc₀, hcmin⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ p ∈ K1, c₀ ≤ (fwdMapInv W p.1 p.2).im := by
    rcases K1.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by rw [he] at hp; exact absurd hp (notMem_empty p)⟩
    obtain ⟨p₀, hp₀, hmin⟩ := hK1c.exists_isMinOn hne
      (Complex.continuous_im.comp_continuousOn (hc0.mono hK1H))
    exact ⟨_, RS.fwdMapInv_mem_H hW hW0 (hK1H hp₀).1.1 (hK1H hp₀).2, fun p hp => hmin hp⟩
  have hsub : ∀ z ∈ reg R h, closedBall z (h / 2) ⊆ reg (R + h) (h / 2) := by
    intro z hz x hx
    refine ⟨?_, ?_⟩
    · have := norm_le_norm_add_norm_sub' x z
      rw [← dist_eq_norm] at this
      linarith [mem_closedBall.1 hx, hz.1]
    · have h2 : |(x - z).im| ≤ ‖x - z‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im, ← dist_eq_norm] at h2
      linarith [neg_abs_le (x.im - z.im), mem_closedBall.1 hx, hz.2]
  have hreg1 : ∀ z ∈ reg R h, z ∈ reg (R + h) (h / 2) := fun z hz =>
    hsub z hz (mem_closedBall_self (by positivity))
  have hderb : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ reg (R + h) (h / 2),
      Real.exp (-|Λ|) ≤ ‖deriv (tpsi W t) z‖ ∧ ‖deriv (tpsi W t) z‖ ≤ Real.exp |Λ| := by
    intro t ht z hz
    have hzH : z ∈ H := reg_subset_H (by positivity) hz
    rw [deriv_tpsi_eq hW hW0 ht.1 hzH]
    have hpos : 0 < ‖deriv (fwdMapInv W t) z‖ := by
      rw [← deriv_tpsi_eq hW hW0 ht.1 hzH]
      exact norm_pos_iff.2 (CA.Koebe.deriv_ne_zero_of_injOn isOpen_H
        (tpsi_psiGood hW hW0 ht.1).2.1 (tpsi_psiGood hW hW0 ht.1).2.2.1 hzH)
    have hl := (hΛ (t, z) ⟨ht, hz⟩).trans (le_abs_self _)
    rw [Real.norm_eq_abs] at hl
    obtain ⟨hl1, hl2⟩ := abs_le.1 hl
    constructor
    · rw [← Real.exp_log hpos]; exact Real.exp_le_exp.2 hl1
    · rw [← Real.exp_log hpos]; exact Real.exp_le_exp.2 hl2
  refine ⟨|M₀|, Real.exp |Λ|, Real.exp |Λ| / (h / 2), Real.exp (-|Λ|), c₀, abs_nonneg _,
    (Real.exp_pos _).le, by positivity, Real.exp_pos _, hc₀, fun t ht z hz => ?_⟩
  have hzH : z ∈ H := reg_subset_H (by positivity) (hreg1 z hz)
  have hz1 := hreg1 z hz
  refine ⟨?_, (hderb t ht z hz1).2, (hderb t ht z hz1).1, ?_, ?_⟩
  · rw [tpsi_eq hW hW0 ht.1 hzH]
    have := hM₀ (t, z) ⟨ht, hz1⟩
    rw [norm_norm] at this
    exact this.trans (le_abs_self _)
  · have hdd : DifferentiableOn ℂ (deriv (tpsi W t)) H :=
      (tpsi_psiGood hW hW0 ht.1).2.1.deriv isOpen_H
    have hball : closedBall z (h / 2) ⊆ H :=
      (hsub z hz).trans (reg_subset_H (by positivity))
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hdd.diffContOnCl_ball hball) fun x hx =>
        (hderb t ht x (hsub z hz (sphere_subset_closedBall hx))).2
  · rw [tpsi_eq hW hW0 ht.1 hzH]
    exact hcmin (t, z) ⟨ht, hz1⟩

/-- **`TPushPotLip` holds** for every continuous driver with `W 0 = 0`. -/
theorem tPushPotLip_holds (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) : TPushPotLip W T := by
  intro m
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  obtain ⟨M₀, M₁, M₂, a₀, c₀, hM₀, hM₁, hM₂, ha₀, hc₀, hK⟩ :=
    tpsi_consts hW hW0 T (2 * ((m : ℝ) + 1) + 1) (1 / ((m : ℝ) + 1) / 2) (by positivity)
  obtain ⟨rD, L, ρ₁, τ₁, hrD, hL, hρ₁, hτ₁, h2τ, hrDh, hcore⟩ :=
    pushPotLip_core m hM₀ hM₁ hM₂ ha₀ hc₀
  refine ⟨M₀, M₁, rD, L, ρ₁, τ₁, hM₀, hM₁, hrD, hL, hρ₁, hτ₁, h2τ, fun w hw1 hw2 => ?_⟩
  have hw := fun t (ht : t ∈ Icc (0 : ℝ) T) =>
    hcore (tpsi W t) (tpsi_psiGood hW hW0 ht.1) (hK t ht) w hw1 hw2
  have hrw : rD < w.im := lt_of_lt_of_le hrDh hw2
  refine ⟨hrw, fun t ht => ⟨(hw t ht).2.1, (hw t ht).2.2.1, fun u hu τ s hτ hττ hs hsτ p hp p' hp' => ?_⟩⟩
  have hS1 : (1 : ℝ) ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) := by
    constructor
    · rw [div_le_one hm1]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have e : ((1 : ℝ) : ℂ) * tpsi W t w = tpsi W t w := by simp
  exact (hw t ht).2.2.2 u hu 1 hS1 τ s hτ hττ hs hsτ p (by rw [e]; exact hp) p' (by rw [e]; exact hp')

end CfgFM
end QuantumZipper.E6
