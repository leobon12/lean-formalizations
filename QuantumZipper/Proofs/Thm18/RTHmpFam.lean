import QuantumZipper.Proofs.Thm18.RTHmpBC
import QuantumZipper.Proofs.Zipper.XAreaPCModI
import QuantumZipper.Proofs.Zipper.SWCoreN2Apply
import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.LQG.WedgeToolkit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-HMP (3): the circle-average family of the free field at scale `2^{-k}`

For `θ = (x, y, ρ)` with rational coordinates, `|x| ≤ N`, `0 ≤ y ≤ N`, `ρ ∈ [2^{-k-1}, 2^{-k}]`,
the balanced pair differences `X(fc(x + iy, ρ)) − X(fc(0, 1))` of a free field satisfy

* `Var ≤ V_N (k + 1)`: the Neumann energy of `fc(c, ρ) − fc(0, 1)` is a sum of four integrals of
  the potentials `−log max(ρ, |c − ·|) − log max(ρ, |c − ·̄|)`, each `O(|log ρ| + 1)`;
* `Var(difference) ≤ 5² ‖θ − θ'‖ / 2^{-k}` (`E6.XAreaPC.abs_kernelCov2_fc_fc_le`).

Hence (`RTHmp.hmp_ae_eventually_le`) a.s., eventually in `k`, all of them are `≤ a (k + 1)`:
Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 and the proof of Lemma 3.1 (variance
`log(1/ε) + O(1)` of `h_ε(z)`, grid union bound, Borel–Cantelli). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real ComplexConjugate

namespace QuantumZipper
namespace R18
namespace RTHmp

open RegUnif SWCore

/-! ## Potential and energy bounds -/

theorem hmp_abs_log_max_le {ρ t R : ℝ} (hρ : 0 < ρ) (hle : max ρ t ≤ R) :
    |Real.log (max ρ t)| ≤ |Real.log ρ| + |Real.log R| := by
  have h1 : Real.log ρ ≤ Real.log (max ρ t) := Real.log_le_log hρ (le_max_left _ _)
  have h2 : Real.log (max ρ t) ≤ Real.log R :=
    Real.log_le_log (lt_of_lt_of_le hρ (le_max_left _ _)) hle
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log ρ), le_abs_self (Real.log R),
    abs_nonneg (Real.log ρ), abs_nonneg (Real.log R)]

theorem hmp_abs_hfc_le {c x : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) (hcx : ‖c‖ + ‖x‖ ≤ R) :
    |E6.XAreaPC.hfc c ρ x| ≤ 2 * (|Real.log ρ| + |Real.log R|) := by
  unfold E6.XAreaPC.hfc
  have e1 : max ρ ‖c - x‖ ≤ R := max_le hρR ((norm_sub_le _ _).trans hcx)
  have e2 : max ρ ‖c - conj x‖ ≤ R :=
    max_le hρR ((norm_sub_le _ _).trans (by rw [Complex.norm_conj]; exact hcx))
  have a1 := hmp_abs_log_max_le hρ e1
  have a2 := hmp_abs_log_max_le hρ e2
  have := abs_sub (-Real.log (max ρ ‖c - x‖)) (Real.log (max ρ ‖c - conj x‖))
  rw [abs_neg] at this
  linarith

/-- Energy of a pair of folded circles from a uniform bound on the potentials. -/
theorem hmp_abs_kernelCov2_le {c c' : ℂ} {ρ ρ' Rb B : ℝ} (hc : c ∈ Hbar) (hc' : c' ∈ Hbar)
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (h1 : ‖c‖ + ρ ≤ Rb) (h2 : ‖c'‖ + ρ' ≤ Rb)
    (hB : ∀ x : ℂ, ‖x‖ ≤ Rb → |E6.XAreaPC.hfc c ρ x| ≤ B ∧ |E6.XAreaPC.hfc c' ρ' x| ≤ B) :
    |kernelCov2 neumannH (foldedCircle c ρ, foldedCircle c' ρ')
        (foldedCircle c ρ, foldedCircle c' ρ')| ≤ 4 * B := by
  have hin : ∀ (d : ℂ) (r : ℝ), 0 < r →
      (fun x => ∫ y, neumannH x y ∂foldedCircle d r) = E6.XAreaPC.hfc d r := fun d r hr =>
    funext fun x => E6.XAreaPC.xpc_inner_fc d x hr
  simp only [kernelCov2, kernelCov]
  rw [hin c ρ hρ, hin c' ρ' hρ']
  have hbd : ∀ (e : ℂ) (s : ℝ), e ∈ Hbar → 0 ≤ s → ‖e‖ + s ≤ Rb → ∀ f : ℂ → ℝ,
      (∀ x, ‖x‖ ≤ Rb → |f x| ≤ B) → |∫ x, f x ∂foldedCircle e s| ≤ B := by
    intro e s he hs hes f hf
    have h := norm_integral_le_of_norm_le_const (μ := foldedCircle e s) (f := f) (C := B) ?_
    · rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
    · filter_upwards [E6.foldedCircle_ae_dist_le_pc he hs] with u hu
      rw [Real.norm_eq_abs]
      apply hf
      have := norm_sub_norm_le u e
      rw [dist_eq_norm] at hu
      linarith
  obtain ⟨a1, b1⟩ := abs_le.1 (hbd c ρ hc hρ.le h1 _ fun x hx => (hB x hx).1)
  obtain ⟨a2, b2⟩ := abs_le.1 (hbd c ρ hc hρ.le h1 _ fun x hx => (hB x hx).2)
  obtain ⟨a3, b3⟩ := abs_le.1 (hbd c' ρ' hc' hρ'.le h2 _ fun x hx => (hB x hx).1)
  obtain ⟨a4, b4⟩ := abs_le.1 (hbd c' ρ' hc' hρ'.le h2 _ fun x hx => (hB x hx).2)
  rw [abs_le]
  constructor <;> linarith

/-! ## The family -/

/-- Lower corners of the parameter box at scale `k`. -/
def hmpLo (N : ℝ) (k : ℕ) : Fin 3 → ℝ := ![-N, 0, radius (k + 1)]

/-- Upper corners of the parameter box at scale `k`. -/
def hmpHi (N : ℝ) (k : ℕ) : Fin 3 → ℝ := ![N, N, radius k]

/-- Rational parameters in the box at scale `k`. -/
def hmpD (N : ℝ) (k : ℕ) : Set (Fin 3 → ℝ) :=
  Set.pi univ fun i => Icc (hmpLo N k i) (hmpHi N k i) ∩ range ((↑) : ℚ → ℝ)

/-- The centre of the parameter `θ`. -/
def hmpC (θ : Fin 3 → ℝ) : ℂ := ⟨θ 0, θ 1⟩

theorem hmpD_countable (N : ℝ) (k : ℕ) : (hmpD N k).Countable :=
  Set.countable_univ_pi fun _ => (Set.countable_range _).mono inter_subset_right

theorem hmpD_mem {N : ℝ} {k : ℕ} {θ : Fin 3 → ℝ} (h : θ ∈ hmpD N k) :
    θ 0 ∈ Icc (-N) N ∧ θ 1 ∈ Icc 0 N ∧ θ 2 ∈ Icc (radius (k + 1)) (radius k) := by
  have h0 := (h 0 (mem_univ _)).1
  have h1 := (h 1 (mem_univ _)).1
  have h2 := (h 2 (mem_univ _)).1
  simp only [hmpLo, hmpHi] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem radius_succ_eq (k : ℕ) : radius (k + 1) = radius k / 2 := by
  unfold radius; rw [pow_succ]; ring

theorem hmpC_mem_Hbar {θ : Fin 3 → ℝ} (h : 0 ≤ θ 1) : hmpC θ ∈ Hbar := h

theorem norm_hmpC_le (θ : Fin 3 → ℝ) : ‖hmpC θ‖ ≤ |θ 0| + |θ 1| :=
  Complex.norm_le_abs_re_add_abs_im _

/-- Log bound for radii in `[2^{-k-1}, 2^{-k}]`. -/
theorem abs_log_le_of_mem {ρ : ℝ} {k : ℕ} (h : ρ ∈ Icc (radius (k + 1)) (radius k)) :
    |Real.log ρ| ≤ k + 1 := by
  have hpos : 0 < radius (k + 1) := radius_pos _
  have hρ : 0 < ρ := lt_of_lt_of_le hpos h.1
  have hρ1 : ρ ≤ 1 := h.2.trans (swcn2_radius_le_one k)
  have hl0 : Real.log ρ ≤ 0 := Real.log_nonpos hρ.le hρ1
  have hl1 : Real.log (radius (k + 1)) ≤ Real.log ρ := Real.log_le_log hpos h.1
  have e : Real.log (radius (k + 1)) = -((k + 1 : ℕ) * Real.log 2) := by
    simp [radius, Real.log_pow, Real.log_inv]
  have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_nonpos hl0]
  push_cast at e
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

end RTHmp
end R18
end QuantumZipper
