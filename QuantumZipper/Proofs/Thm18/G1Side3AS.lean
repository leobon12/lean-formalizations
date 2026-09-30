import QuantumZipper.Proofs.Thm18.G1Side3Err

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (10): the free-field inputs of `pushErrR_small`, a.s., for all scales at once

For the free field and a map `ψ` in an area class of a rectangle `R`, almost surely, for every
scale `s ∈ [1/N, N]`: the regularizations on the pushed circles `(sψ)_* fc(z, α 2^{-k})` converge,
and the pushed-versus-round distortion is eventually small uniformly in `α ∈ [1,2]`, `z ∈ R`
(`ae_scale_family`). This is the repository's finite-parameter primed area core
(`SWCore.swcNA2I_primed`, Sheffield–Wang arXiv:1605.06171 Lemmas 3.4–3.5, pathwise) for the scale
family `G1Side.famF` (`G1Side.scaleFam_unif`), read at the parameters `(s, α, Re z, Im z)`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

theorem eventually_shift {p : ℕ → Prop} (k₀ : ℕ) (h : ∀ᶠ k in atTop, p (k + k₀)) :
    ∀ᶠ k in atTop, p k := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨K + k₀, fun k hk => ?_⟩
  have := hK (k - k₀) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The parameter vector of `(s, α, z)`. -/
def parQ (s α : ℝ) (z : ℂ) : Fin 4 → ℝ := ![s, α, z.re, z.im]

theorem famF_parQ {ψ : ℂ → ℂ} {N : ℕ} {s α : ℝ} (hs : s ∈ Icc (1 / (N : ℝ)) N) (z : ℂ) :
    famF ψ N (parQ s α z) = fun u => (s : ℂ) * ψ u := by
  funext u
  simp only [famF, famS, parQ, Matrix.cons_val_zero, swcN2Clamp_of_mem hs]

theorem famA_parQ {s α : ℝ} (hα : α ∈ Icc (1 : ℝ) 2) (z : ℂ) : famA (parQ s α z) = α := by
  simp only [famA, parQ, Matrix.cons_val_one, Matrix.cons_val_zero, swcN2Clamp_of_mem hα]

theorem famZ_parQ {a b c d s α : ℝ} {z : ℂ} (hz : z ∈ rectC a b c d) :
    famZ a b c d (parQ s α z) = z := by
  apply Complex.ext
  · simp [famZ, parQ, swcN2Clamp_of_mem hz.1]
  · simp [famZ, parQ, swcN2Clamp_of_mem hz.2]

/-- **The free-field inputs, a.s., for all scales.** -/
theorem ae_scale_family [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ψ : ℂ → ℂ}
    {a b c d ρ M m : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m)
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc (1 / (N : ℝ)) N,
      (∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
        Tendsto (fun j => ∫ u, avgReg (X ω) j u
            ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
          (𝓝 (evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)))) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
        |evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
          evalReg (X ω) (foldedCircle ((s : ℂ) * ψ z)
            (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η) := by
  have h := scaleFam_unif hab hcd hc hρ hm hψ hN
  obtain ⟨k₀, hae⟩ := swcNA2I_primed (P := P) hX h
  filter_upwards [hae] with ω hω s hs
  obtain ⟨h1, _, h3⟩ := hω
  refine ⟨eventually_shift k₀ (Eventually.of_forall fun k α hα z hz => ?_), fun η hη => ?_⟩
  · have ht := (h1 k {parQ s α z} isCompact_singleton).tendsto_at (mem_singleton _)
    rw [famF_parQ hs, famA_parQ hα, famZ_parQ hz] at ht
    exact ht
  · set R : ℕ := N + 2 + ⌈|a| + |b| + |c| + |d|⌉₊ with hR
    refine eventually_shift k₀ ((h3 R η hη).mono fun k hk α hα z hz => ?_)
    have hq : parQ s α z ∈ KolmD.boxD (d := 4) R := by
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hceil : |a| + |b| + |c| + |d| ≤ (⌈|a| + |b| + |c| + |d|⌉₊ : ℝ) := Nat.le_ceil _
      have hRr : (R : ℝ) = N + 2 + ⌈|a| + |b| + |c| + |d|⌉₊ := by rw [hR]; push_cast; ring
      have habs : ∀ t lo hi : ℝ, t ∈ Icc lo hi → |t| ≤ |lo| + |hi| := fun t lo hi ht => by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2, le_abs_self lo, neg_abs_le lo,
          le_abs_self hi, neg_abs_le hi, abs_nonneg lo, abs_nonneg hi]
      intro i
      fin_cases i
      · show |s| ≤ R
        rw [abs_of_pos (lt_of_lt_of_le (by positivity) hs.1), hRr]
        linarith [hs.2, Nat.cast_nonneg (α := ℝ) ⌈|a| + |b| + |c| + |d|⌉₊]
      · show |α| ≤ R
        rw [abs_of_pos (by linarith [hα.1]), hRr]
        linarith [hα.2, Nat.cast_nonneg (α := ℝ) ⌈|a| + |b| + |c| + |d|⌉₊]
      · show |z.re| ≤ R
        have := habs _ _ _ hz.1
        rw [hRr]; linarith [abs_nonneg c, abs_nonneg d]
      · show |z.im| ≤ R
        have := habs _ _ _ hz.2
        rw [hRr]; linarith [abs_nonneg a, abs_nonneg b]
    have := hk _ hq
    rw [famF_parQ hs, famA_parQ hα, famZ_parQ hz] at this
    exact this

end G1Side
end QuantumZipper
