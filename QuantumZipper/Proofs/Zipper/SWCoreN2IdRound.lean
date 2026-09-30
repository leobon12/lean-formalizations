import QuantumZipper.Proofs.Zipper.SWCoreN2IdPush

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2-ID (3): the round semicircle family and the round comparison term

Task SWC-N2-ID. The two-parameter family `(s, ρ') ↦ fc(s, ρ')` (`ρ' ≥ ε₀ > 0`) satisfies the box
bounds of `swcN2_ae_evalReg`, so a.s. `(s, ρ') ↦ evalReg x (fc(s,ρ'))` is continuous on
`ℝ × [ε₀, ∞)` and equals the raw value `X(fc(s,ρ'))` for each fixed `(s,ρ')`
(`swcN2_round_ae`). Composed with the continuous map `(q,t) ↦ (Re Ψ_q(t), r ‖Ψ_q'(t)‖)` (Cauchy's
estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` for the Lipschitz dependence of
`Ψ_q'` on `q`), this gives the round half of (ii) (`swcN2_round_family_ae`). Sources as in
`SWCoreN2IdFam.lean`; own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- The round family `(s, ρ') ↦ fc(s, max ε₀ ρ')`, parametrized by the angle. -/
def swcN2RoundΦ (ε₀ : ℝ) : (Fin 2 → ℝ) → ℝ → ℂ := fun p θ =>
  foldH (circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ)

theorem swcN2_isFrostman_mono {ν : Measure ℂ} {α C C' : ℝ} (h : TwoPoint.IsFrostman ν α C)
    (hC : C ≤ C') : TwoPoint.IsFrostman ν α C' := fun w s hs =>
  (h w s hs).trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hs.le α))

theorem swcN2_round_bounds {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Continuous (uncurry (swcN2RoundΦ ε₀)) ∧ (∀ p θ, swcN2RoundΦ ε₀ p θ ∈ Hbar) ∧
      ∀ R : ℕ, ∃ B C H : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ H ∧ ∀ p ∈ KolmD.boxD (d := 2) R,
        (∀ θ, ‖swcN2RoundΦ ε₀ p θ‖ ≤ B) ∧
        TwoPoint.IsFrostman (circM.map (swcN2RoundΦ ε₀ p)) 1 C ∧
        ∀ p' ∈ KolmD.boxD (d := 2) R, ∀ θ,
          ‖swcN2RoundΦ ε₀ p θ - swcN2RoundΦ ε₀ p' θ‖ ≤ H * ‖p - p'‖ ^ (1 : ℝ) := by
  have hcont : Continuous (uncurry (swcN2RoundΦ ε₀)) := by
    refine CircleFubini.continuous_foldH'.comp ?_
    simp only [circleMap]
    exact (Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_fst)).add
      ((Complex.continuous_ofReal.comp (continuous_const.max
        ((continuous_apply 1).comp continuous_fst))).mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
  have hpos : ∀ p : Fin 2 → ℝ, 0 < max ε₀ (p 1) := fun p => lt_max_of_lt_left hε₀
  refine ⟨hcont, fun p θ => CircleFubini.foldH_mem_Hbar' _, fun R => ?_⟩
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  refine ⟨R + (ε₀ + R), 12 / ε₀, 2, by positivity, by positivity, by norm_num,
    fun p hp => ⟨fun θ => ?_, ?_, fun p' hp' θ => ?_⟩⟩
  · have h0 := swcN2_norm_foldH_sub_real (circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ) 0
    simp only [Complex.ofReal_zero, sub_zero] at h0
    simp only [swcN2RoundΦ]
    rw [h0]
    have e := circleMap_sub_center ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ
    have hn : ‖circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ‖ ≤
        ‖((p 0 : ℝ) : ℂ)‖ + ‖circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ - (p 0 : ℂ)‖ := by
      calc ‖circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ‖ =
            ‖((p 0 : ℝ) : ℂ) + (circleMap ((p 0 : ℝ) : ℂ) (max ε₀ (p 1)) θ - (p 0 : ℂ))‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [e, norm_circleMap_zero, abs_of_pos (hpos p), Complex.norm_real, Real.norm_eq_abs] at hn
    have h1 : |p 0| ≤ R := hp 0
    have h2 : p 1 ≤ R := (abs_le.1 (hp 1)).2
    have h3 : max ε₀ (p 1) ≤ ε₀ + R := max_le (by linarith) (by linarith)
    linarith
  · refine swcN2_isFrostman_mono (swcN2_frostman (y := ((p 0 : ℝ) : ℂ)) (hpos p) one_pos
      (hcont.comp (continuous_const.prodMk continuous_id)).measurable fun θ θ' => ?_) ?_
    · rw [one_mul]; exact le_rfl
    · rw [one_mul]
      exact div_le_div_of_nonneg_left (by norm_num) hε₀ (le_max_left _ _)
  · refine (swcN2_norm_fold_circle_sub (hpos p) (hpos p') θ).trans ?_
    have h0 : |p 0 - p' 0| ≤ ‖p - p'‖ := by
      have := norm_le_pi_norm (p - p') 0; simpa using this
    have h1 : |p 1 - p' 1| ≤ ‖p - p'‖ := by
      have := norm_le_pi_norm (p - p') 1; simpa using this
    have h2 : |max ε₀ (p 1) - max ε₀ (p' 1)| ≤ |p 1 - p' 1| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero]
      exact max_le (abs_nonneg _) le_rfl
    rw [Real.rpow_one]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Round semicircles**: a.s. `(s, ρ') ↦ evalReg x (fc(s,ρ'))` is continuous on
`ℝ × [ε₀, ∞)`, and equals the raw value for each fixed `(s, ρ')`, `ρ' ≥ ε₀`. -/
theorem swcN2_round_ae {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hX : IsFreeGFFModConstH X P) :
    (∀ᵐ ω ∂P, ContinuousOn (fun x : ℝ × ℝ => evalReg (X ω) (foldedCircle (x.1 : ℂ) x.2))
      (univ ×ˢ Ici ε₀)) ∧
    ∀ s ρ' : ℝ, ε₀ ≤ ρ' → ∀ᵐ ω ∂P,
      evalReg (X ω) (foldedCircle (s : ℂ) ρ') = X ω (foldedCircle (s : ℂ) ρ') := by
  obtain ⟨hc, hH, hb⟩ := swcN2_round_bounds hε₀
  obtain ⟨hae, hpt⟩ := swcN2_ae_evalReg hc hH hb hX
  have heq : ∀ s ρ' : ℝ, ε₀ ≤ ρ' →
      circM.map (swcN2RoundΦ ε₀ ![s, ρ']) = foldedCircle (s : ℂ) ρ' := by
    intro s ρ' h
    rw [swcN2_fc_eq_map]
    congr 1
    funext θ
    simp [swcN2RoundΦ, max_eq_right h]
  have hv : Continuous fun x : ℝ × ℝ => (![x.1, x.2] : Fin 2 → ℝ) :=
    continuous_fst.matrixVecCons (continuous_snd.matrixVecCons continuous_const)
  refine ⟨?_, fun s ρ' h => ?_⟩
  · filter_upwards [hae] with ω hω
    refine ((hω.comp hv).continuousOn).congr fun x hx => ?_
    simp only [comp_apply]
    rw [heq x.1 x.2 hx.2]
  · filter_upwards [hpt ![s, ρ']] with ω hω
    rwa [heq s ρ' h] at hω

variable {n : ℕ}

/-- Cauchy's estimate for the difference of two holomorphic maps. -/
theorem swcN2_deriv_sub_le {ψ φ : ℂ → ℂ} {T : Set ℂ} (hT : IsOpen T)
    (hψ : DifferentiableOn ℂ ψ T) (hφ : DifferentiableOn ℂ φ T) {z : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hball : closedBall z R ⊆ T) (hδ : ∀ w ∈ T, ‖ψ w - φ w‖ ≤ δ) :
    ‖deriv ψ z - deriv φ z‖ ≤ δ / R := by
  have hz : z ∈ T := hball (mem_closedBall_self hR.le)
  have e : deriv ψ z - deriv φ z = deriv (fun w => ψ w - φ w) z :=
    (deriv_sub (hψ.differentiableAt (hT.mem_nhds hz))
      (hφ.differentiableAt (hT.mem_nhds hz))).symm
  rw [e]
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR ?_
    fun w hw => hδ w (hball (sphere_subset_closedBall hw))
  exact ((hψ.sub hφ).mono (by rw [closure_ball z hR.ne']; exact hball)).diffContOnCl

section Round

variable {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}

theorem swcN2_continuousOn_deriv (hρ : 0 < ρ) (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖) :
    ContinuousOn (fun x : (Fin n → ℝ) × ℝ => deriv (Ψ x.1) (x.2 : ℂ)) (K ×ˢ Icc a b) := by
  have hsub : segC a b ⊆ thickening ρ (segC a b) := self_subset_thickening hρ _
  have h := swcN2_continuousOn_family (Ψ := fun q => deriv (Ψ q)) (K := K) (T := segC a b)
    (L := L / (ρ / 2))
    (fun q hq => (((hΨ q hq).1.deriv isOpen_thickening).continuousOn).mono hsub)
    (fun q hq q' hq' z hz => by
      obtain ⟨t, ht, rfl⟩ := hz
      refine (swcN2_deriv_sub_le isOpen_thickening (hΨ q hq).1 (hΨ q' hq').1 (half_pos hρ)
        (swcN2_ball_sub_thick ht (by linarith)) (hL q hq q' hq')).trans (le_of_eq ?_)
      ring)
  exact h.comp (continuousOn_fst.prodMk
    (Complex.continuous_ofReal.comp_continuousOn continuousOn_snd))
    (fun x hx => ⟨hx.1, ⟨x.2, hx.2, rfl⟩⟩)

theorem swcN2_round_map_cont (hρ : 0 < ρ) (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (r : ℝ) :
    ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
      ((Ψ x.1 (x.2 : ℂ)).re, r * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)) (K ×ˢ Icc a b) := by
  have hΨc : ContinuousOn (fun x : (Fin n → ℝ) × ℝ => Ψ x.1 (x.2 : ℂ)) (K ×ˢ Icc a b) :=
    (swcN2_continuousOn_family (T := thickening ρ (segC a b))
      (fun q hq => (hΨ q hq).1.continuousOn) hL).comp
      (continuousOn_fst.prodMk (Complex.continuous_ofReal.comp_continuousOn continuousOn_snd))
      (fun x hx => ⟨hx.1, self_subset_thickening hρ _ ⟨x.2, hx.2, rfl⟩⟩)
  exact (Complex.continuous_re.comp_continuousOn hΨc).prodMk
    (continuousOn_const.mul (swcN2_continuousOn_deriv hρ hΨ hL).norm)

/-- **(ii), round half**: a.s. `(q,t) ↦ evalReg x (fc(Re Ψ_q(t), r ‖Ψ_q'(t)‖))` is continuous
on `K × [a,b]`. -/
theorem swcN2_round_family_ae (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ContinuousOn (fun x : (Fin n → ℝ) × ℝ => evalReg (X ω)
      (foldedCircle (((Ψ x.1 (x.2 : ℂ)).re : ℝ) : ℂ) (r * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)))
      (K ×ˢ Icc a b) := by
  obtain ⟨hae, -⟩ := swcN2_round_ae (mul_pos hr hm) hX
  have hmaps : MapsTo (fun x : (Fin n → ℝ) × ℝ =>
      ((Ψ x.1 (x.2 : ℂ)).re, r * ‖deriv (Ψ x.1) (x.2 : ℂ)‖)) (K ×ˢ Icc a b)
      (univ ×ˢ Ici (r * m)) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h5 : m ≤ ‖deriv (Ψ x.1) (x.2 : ℂ)‖ := (hΨ x.1 hx1).2.2.2.2 x.2 hx2
    exact ⟨mem_univ _, mul_le_mul_of_nonneg_left h5 hr.le⟩
  have hh := swcN2_round_map_cont hρ hΨ hL r
  filter_upwards [hae] with ω hω
  have key : ContinuousOn ((fun y : ℝ × ℝ => evalReg (X ω) (foldedCircle (y.1 : ℂ) y.2)) ∘
      fun x : (Fin n → ℝ) × ℝ => ((Ψ x.1 (x.2 : ℂ)).re, r * ‖deriv (Ψ x.1) (x.2 : ℂ)‖))
      (K ×ˢ Icc a b) := ContinuousOn.comp hω hh hmaps
  exact key

end Round

end SWCore
end QuantumZipper
