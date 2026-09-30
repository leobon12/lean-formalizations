import QuantumZipper.Proofs.Zipper.SWCoreA8Meas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (2): the fixed-path fibre of the countable event

`a8_fibre`: for every good continuous path `f` (`RegCont.GoodP`), almost surely in the free field,
the countable event `a8Ev` holds for `(f, X ω)`. Proof: the finite-parameter primed core
`swcNA2I_primed` (D64) for the Lipschitz family `a7Map (Wof f)` (`a7_unif`), read on the compact
image of `[0,T] × [A,B] × [C,D]` under the diagonal `a7Diag`: uniform convergence in `j` gives the
uniform Cauchy property, and the distortion bound plus uniform convergence give the closeness
of the smoothed pairing to the round value. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem continuous_a7Diag_joint (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous fun p : ℝ × ℂ => a7Diag W p.1 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [a7Diag] <;> fun_prop

/-- **The fixed-path fibre.** -/
theorem a8_fibre [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (κ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) {A B C D : ℚ} (hAB : (A : ℝ) ≤ B) (hC : (0 : ℝ) < C) (hCD : (C : ℝ) ≤ D)
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT (1 / 3)) :
    ∀ᵐ ω ∂P, a8Ev κ hT A B C D (f, X ω) := by
  set W := Wof κ T hT f with hWdef
  have hW : Continuous W := continuous_Wof κ T hT f
  have hW0 : W 0 = 0 := Wof_zero_of_GoodP hT κ hf
  obtain ⟨S, ρ, M, m, HL, hS, h⟩ := a7_unif hW hW0 hT (x₁ := A) (x₂ := B) (y₁ := C) (y₂ := D)
    hAB hC hCD
  have hdiag : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D,
      a7Map W T S (a7Diag W t w) = fwdMapInv W t ∧
        a7Cen A B C D (a7Diag W t w) = w ∧ a7Rad (a7Diag W t w) = 1 := by
    intro t ht w hw
    refine ⟨a7Map_diag ht (hS t ht) (by simp [a7Diag]) (by simp [a7Diag]), ?_, ?_⟩
    · apply Complex.ext
      · simp only [a7Cen, a7Diag]
        exact clampI_eq hw.1
      · simp only [a7Cen, a7Diag]
        exact clampI_eq hw.2
    · simp only [a7Rad, a7Diag]
      exact clampI_eq ⟨le_rfl, by norm_num⟩
  set R : ℕ := ⌈|T| + |S| + |(A : ℝ)| + |(B : ℝ)| + |(D : ℝ)| + 2⌉₊ with hRdef
  have hRle : |T| + |S| + |(A : ℝ)| + |(B : ℝ)| + |(D : ℝ)| + 2 ≤ R := Nat.le_ceil _
  have hR : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D,
      a7Diag W t w ∈ KolmD.boxD (d := 5) R := by
    intro t ht w hw i
    have h0 := abs_nonneg T; have h1 := abs_nonneg S; have h2 := abs_nonneg (A : ℝ)
    have h3 := abs_nonneg (B : ℝ); have h4 := abs_nonneg (D : ℝ)
    fin_cases i
    · simp only [a7Diag]
      show |t| ≤ R
      rw [abs_of_nonneg ht.1]
      linarith [le_abs_self T, ht.2]
    · simp only [a7Diag]
      show |W t| ≤ R
      linarith [hS t ht, le_abs_self S]
    · simp only [a7Diag]
      show |w.re| ≤ R
      rw [abs_le]
      constructor <;> linarith [hw.1.1, hw.1.2, neg_abs_le (A : ℝ), le_abs_self (B : ℝ)]
    · simp only [a7Diag]
      show |w.im| ≤ R
      rw [abs_le]
      constructor <;> linarith [hw.2.1, hw.2.2, le_abs_self (D : ℝ)]
    · simp only [a7Diag]
      show |(1 : ℝ)| ≤ R
      rw [abs_one]
      linarith
  set Kc : Set (Fin 5 → ℝ) := (fun p : ℝ × ℂ => a7Diag W p.1 p.2) ''
    (Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D) with hKcdef
  have hKc : IsCompact Kc := (isCompact_Icc.prod (swA6_isCompact_rectC _ _ _ _)).image
    (continuous_a7Diag_joint W hW)
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX h
  filter_upwards [hae] with ω hω
  obtain ⟨hi, -, hiii⟩ := hω
  -- reading the family at a rational point
  have hread : ∀ k' j : ℕ, ∀ t (ht : t ∈ Icc (0 : ℝ) T), ∀ w ∈ rectC (A : ℝ) B C D,
      (∫ u, avgReg (X ω) j u ∂((foldedCircle (a7Cen A B C D (a7Diag W t w))
        (a7Rad (a7Diag W t w) * radius (k' + k₀))).map (a7Map W T S (a7Diag W t w)))) =
        a8Phi κ hT j (k' + k₀) t ht.1 w (f, X ω) := by
    intro k' j t ht w hw
    obtain ⟨e1, e2, e3⟩ := hdiag t ht w hw
    rw [e1, e2, e3, one_mul, a8Phi_eq hW0 ht]
  have hmemK : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D, a7Diag W t w ∈ Kc :=
    fun t ht w hw => ⟨(t, w), ⟨ht, hw⟩, rfl⟩
  have hunif : ∀ k' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∀ t (ht : t ∈ Icc (0 : ℝ) T), ∀ w ∈ rectC (A : ℝ) B C D,
        dist (evalReg (X ω) ((foldedCircle w (radius (k' + k₀))).map (fwdMapInv W t)))
          (a8Phi κ hT j (k' + k₀) t ht.1 w (f, X ω)) < ε := by
    intro k' ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 (hi k' Kc hKc)) ε hε)
    refine ⟨J, fun j hj t ht w hw => ?_⟩
    have := hJ j hj _ (hmemK t ht w hw)
    obtain ⟨e1, e2, e3⟩ := hdiag t ht w hw
    rw [hread k' j t ht w hw] at this
    rw [e1, e2, e3, one_mul] at this
    exact this
  have hzH : ∀ z : ℚ × ℚ, zQ z ∈ rectC (A : ℝ) B C D → zQ z ∈ H := fun z hz =>
    show 0 < (zQ z).im from lt_of_lt_of_le hC hz.2.1
  refine ⟨⟨k₀, fun k hk m => ?_⟩, fun n => ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + k₀ := ⟨k - k₀, (Nat.sub_add_cancel hk).symm⟩
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) / 2 := by positivity
    obtain ⟨J, hJ⟩ := hunif k' _ hε
    refine ⟨J, fun j hj j' hj' q hq z hz => ?_⟩
    have h1 := hJ j hj q hq (zQ z) hz
    have h2 := hJ j' hj' q hq (zQ z) hz
    rw [Real.dist_eq] at h1 h2
    rw [abs_sub_comm] at h1
    calc _ ≤ |a8Phi κ hT j (k' + k₀) q hq.1 (zQ z) (f, X ω) -
          evalReg (X ω) ((foldedCircle (zQ z) (radius (k' + k₀))).map (fwdMapInv W q))| +
          |evalReg (X ω) ((foldedCircle (zQ z) (radius (k' + k₀))).map (fwdMapInv W q)) -
          a8Phi κ hT j' (k' + k₀) q hq.1 (zQ z) (f, X ω)| := abs_sub_le _ _ _
      _ ≤ 1 / ((m : ℝ) + 1) := by linarith
  · have hη : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
    obtain ⟨K', hK'⟩ := eventually_atTop.1 (hiii R _ hη)
    refine ⟨K' + k₀, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + k₀ := ⟨k - k₀, (Nat.sub_add_cancel (by omega)).symm⟩
    obtain ⟨J, hJ⟩ := hunif k' _ hη
    refine ⟨J, fun j hj q hq z hz => ?_⟩
    have h1 := hJ j hj q hq (zQ z) hz
    rw [Real.dist_eq, abs_sub_comm] at h1
    have h2 := hK' k' (by omega) _ (hR q hq (zQ z) hz)
    obtain ⟨e1, e2, e3⟩ := hdiag q hq (zQ z) hz
    rw [e1, e2, e3, one_mul] at h2
    rw [a8Rd_eq hW0 hq (k' + k₀) (hzH z hz)]
    calc _ ≤ |a8Phi κ hT j (k' + k₀) q hq.1 (zQ z) (f, X ω) -
          evalReg (X ω) ((foldedCircle (zQ z) (radius (k' + k₀))).map (fwdMapInv W q))| +
          |evalReg (X ω) ((foldedCircle (zQ z) (radius (k' + k₀))).map (fwdMapInv W q)) -
          evalReg (X ω) (foldedCircle (fwdMapInv W q (zQ z))
            (radius (k' + k₀) * ‖deriv (fwdMapInv W q) (zQ z)‖))| := abs_sub_le _ _ _
      _ ≤ 1 / ((n : ℝ) + 1) := by linarith

end SWCore
end QuantumZipper
