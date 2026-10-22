import HigherDimLQGMetric.ShellDec.Translate

/-!
# Functional shell decoupling for initial segments at centre zero
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem shellDecouplingFun_zero {d : ℕ} (hd : 1 ≤ d)
    (a b q : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsWholeSpaceLGF h P →
        ∀ (ρ : ℕ → ℝ), (∀ i, 0 < ρ i) →
          (∀ i, ρ (i + 1) ≤ q * ρ i) →
          ∀ (n : ℕ) (F : Fin n → Ω → ℝ),
            (∀ (i : Fin n), Measurable[fieldSigma0 h
              (ann 0 (a * ρ i) (b * ρ i))] (F i)) →
            (∀ i ω, 0 ≤ F i ω ∧ F i ω ≤ 1) →
            ∫ ω, ∏ i, F i ω ∂P ≤
              ∏ i, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹ := by
  have hab : a < b := lt_trans ha1 hb1
  obtain ⟨C, ε₀, hC, hε₀, hbound⟩ :=
    shellUniformCoordinateBound hd ha hab
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε₀ hq1
  let k₀ : ℕ := max 1 k
  have hk₀ : 1 ≤ k₀ := Nat.le_max_left _ _
  have hqk : q ^ k₀ ≤ ε₀ := by
    calc
      q ^ k₀ ≤ q ^ k := pow_le_pow_of_le_one hq.le hq1.le (Nat.le_max_right _ _)
      _ ≤ ε₀ := hk.le
  let K : ℝ := (2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)
  have hK : 1 ≤ K := by
    have hk' : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
    have hterm : 0 ≤ 2 * C * q ^ k₀ / (1 - q) := by positivity
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ h hh ρ hpos hstep n F hFm hF01
  let Y : Fin n → ℕ → Ω → ℝ :=
    fun i k ω => h ω (shellCountableTest hd ha ha1 hb1
      (hpos i) 0 (Nat.unpair k)).1.1
  let X : Fin n → ℕ → Lp ℝ 2 P :=
    fun i k => lgfPairLp hh (shellCountableTest hd ha ha1 hb1
      (hpos i) 0 (Nat.unpair k)).1
  have hYm : ∀ i k, Measurable (Y i k) :=
    fun i k => (measurable_distOn_apply _).comp hh.measurable
  have hXY : ∀ i k, (X i k : Ω → ℝ) =ᵐ[P] Y i k := by
    intro i k
    exact ((hh.gaussian.hasGaussianLaw_eval
      (shellCountableTest hd ha ha1 hb1 (hpos i) 0 (Nat.unpair k)).1).memLp_two).coeFn_toLp
  have hX : ∀ (i : Fin n) (k : ℕ),
      X i k ∈ annularBlock hh a b (ρ i) :=
    fun i k => lgfPairLp_mem_annularBlock hh _ (shellCountableTest hd ha ha1 hb1
      (hpos i) 0 (Nat.unpair k)).2
  have hFm' : ∀ i, Measurable[MeasurableSpace.comap
      (fun ω (k : ℕ) => Y i k ω) MeasurableSpace.pi] (F i) := by
    intro i
    simpa only [Y] using
      (show Measurable[MeasurableSpace.comap
        (fun ω (k : ℕ) => h ω (shellCountableTest hd ha ha1 hb1
          (hpos i) 0 (Nat.unpair k)).1.1) MeasurableSpace.pi] (F i) by
        rw [← fieldSigma0_ann_eq_comap_shellNat hd h ha ha1 hb1 (hpos i) 0]
        exact hFm i)
  exact shellCountableHolder hh hC.le (hbound hh) hq hq1 hk₀ hqk
    ρ hpos hstep n Y hYm X hXY hX F hFm'
    (fun i ω => (hF01 i ω).1) (fun i ω => (hF01 i ω).2)

end HigherDimLQGMetric
