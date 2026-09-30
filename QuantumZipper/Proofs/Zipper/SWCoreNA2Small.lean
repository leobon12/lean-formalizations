import QuantumZipper.Proofs.Thm18.G1FMKolm5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2 (N2, probabilistic core): uniform smallness of a sequence of continuous processes

Task SWC-NA (`handoff/SW-CORE.md` §5), step N2. Generic Kolmogorov–Borel–Cantelli step: if
`Z_k(q)` (`q ∈ ℝⁿ`) are processes continuous in `q` for every `ω`, whose `p`-th moments and
Kolmogorov increment moments (exponent `a > n`) on every box are bounded by `K_k` with
`Σ_k K_k < ∞`, then almost surely, for every box and every `η > 0`, eventually in `k`,
`sup_{q ∈ box} |Z_k(q)| ≤ η` (`swcNA2_ae_eventually_sup_le`).

Applied with `Z_k(q) = X(ψ_* fc(z, 2^{-k})) − X(fc(ψ z, 2^{-k}‖ψ'(z)‖))` (continuous modifications,
variance `O(2^{-k})` by `swcVA_variance_push_round`, increments by the VA moduli, interpolated),
this is the distortion smallness of SW Lemma 3.5 / (3.20)–(3.23) (p. 16) pathwise, the SW proof
replacing Borell–TIS by the Kolmogorov tail of the repository (`G1FM.kolm_sup_tail_N`) and
Borel–Cantelli (mathlib `ae_eventually_notMem`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace QuantumZipper
namespace SWCore

open KolmD KolmG

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- One box and one threshold. -/
theorem swcNA2_ae_eventually_sup_le_box {Z : ℕ → (Fin n → ℝ) → Ω → ℝ}
    (hZc : ∀ k ω, Continuous fun q => Z k q ω) (hZm : ∀ k q, AEMeasurable (Z k q) P)
    {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : (n : ℝ) < a) (R : ℕ) {K : ℕ → ℝ} (hK0 : ∀ k, 0 ≤ K k)
    (hKs : Summable K) (hmom : ∀ k, MomentBoundG (Z k) P p a (K k) (R + 1))
    (hpt : ∀ k, ∀ q ∈ boxD (d := n) R, ∫⁻ ω, ENNReal.ofReal (|Z k q ω| ^ p) ∂P ≤
      ENNReal.ofReal (K k)) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R, |Z k q ω| ≤ η := by
  obtain ⟨θ, hθ0, hθ1, hρ⟩ := KolmN.exists_theta_N (d := n) hp ha
  have ha0 : 0 ≤ a := (Nat.cast_nonneg n).trans ha.le
  set c : ℝ := (n : ℝ) / (1 - θ) + 1 with hc
  have hc0 : 0 < c := by
    have : 0 ≤ (n : ℝ) / (1 - θ) := div_nonneg (Nat.cast_nonneg n) (by linarith)
    linarith
  set l : ℝ := η / c with hl
  have hl0 : 0 < l := div_pos hη hc0
  set Cst : ℝ := (2 * R + 1) ^ n + n * (2 * R + 1) ^ n /
    (1 - (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ a / θ ^ p)) with hCst
  have hCst0 : 0 ≤ Cst := by
    have h1 : 0 < 1 - (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ a / θ ^ p) := by linarith
    positivity
  set s : ℕ → Set Ω := fun k => {ω | ∃ q ∈ boxD (d := n) R, c * l < |Z k q ω|} with hs
  have hbound : ∀ k, P (s k) ≤ ENNReal.ofReal (K k / l ^ p * Cst) := fun k =>
    Thm18Asm.G1FM.kolm_sup_tail_N hθ0 hθ1 (hZc k) (hZm k) ha0 (hK0 k) hρ (hmom k) (hpt k) hl0
  have hsum : ∑' k, P (s k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by have := hK0 k; positivity)
      ((hKs.div_const (l ^ p)).mul_right Cst)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk q hq
  by_contra h
  push Not at h
  refine hk ⟨q, hq, ?_⟩
  have : c * l = η := by rw [hl]; field_simp
  rw [this]; exact h

/-- **Uniform smallness, all boxes and thresholds at once.** -/
theorem swcNA2_ae_eventually_sup_le {Z : ℕ → (Fin n → ℝ) → Ω → ℝ}
    (hZc : ∀ k ω, Continuous fun q => Z k q ω) (hZm : ∀ k q, AEMeasurable (Z k q) P)
    {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : (n : ℝ) < a)
    (hK : ∀ R : ℕ, ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧ Summable K ∧
      (∀ k, MomentBoundG (Z k) P p a (K k) (R + 1)) ∧
      ∀ k, ∀ q ∈ boxD (d := n) R, ∫⁻ ω, ENNReal.ofReal (|Z k q ω| ^ p) ∂P ≤
        ENNReal.ofReal (K k)) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R, |Z k q ω| ≤ η := by
  have h : ∀ R i : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R,
      |Z k q ω| ≤ 1 / ((i : ℝ) + 1) := fun R i => by
    obtain ⟨K, hK0, hKs, hmom, hpt⟩ := hK R
    exact swcNA2_ae_eventually_sup_le_box hZc hZm hp ha R hK0 hKs hmom hpt (by positivity)
  have h' : ∀ᵐ ω ∂P, ∀ R i : ℕ, ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R,
      |Z k q ω| ≤ 1 / ((i : ℝ) + 1) := by
    rw [ae_all_iff]; intro R; rw [ae_all_iff]; exact h R
  filter_upwards [h'] with ω hω R η hη
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω R i] with k hk q hq
  exact (hk q hq).trans hi.le

end SWCore
end QuantumZipper
