import HigherDimLQGMetric.ShellDec.Zero
import HigherDimLQGMetric.ShellDec.Defs

/-!
# Functional Gaussian shell decoupling
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private theorem shellProdPad {M : Type*} [CommMonoid M]
    (I : Finset ℕ) (n : ℕ) (hI : ∀ i ∈ I, i < n) (f : ℕ → M) :
    (∏ j : Fin n, if (j : ℕ) ∈ I then f j else 1) = ∏ i ∈ I, f i := by
  classical
  rw [Fin.prod_univ_eq_prod_range (fun i => if i ∈ I then f i else 1) n]
  rw [← Finset.prod_filter]
  have heq : (Finset.range n).filter (· ∈ I) = I := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hi
      exact ⟨hI i hi, hi⟩
  rw [heq]

private theorem shellBoundedRepresentative {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (F : Ω → ℝ) (hF : ∃ G : Ω → ℝ, Measurable[m] G ∧ F =ᵐ[P] G)
    (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1) :
    ∃ H : Ω → ℝ, Measurable[m] H ∧
      (∀ ω, 0 ≤ H ω ∧ H ω ≤ 1) ∧ F =ᵐ[P] H := by
  obtain ⟨G, hGm, hFG⟩ := hF
  let H : Ω → ℝ := fun ω => max 0 (min 1 (G ω))
  refine ⟨H, measurable_const.max (measurable_const.min hGm), ?_, ?_⟩
  · intro ω
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · filter_upwards [hFG] with ω hω
    simp [H, ← hω, min_eq_right (hF1 ω), max_eq_right (hF0 ω)]

private theorem shellDecouplingFun_initial {d : ℕ} (hd : 1 ≤ d)
    (a b q : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsWholeSpaceLGF h P →
        ∀ (z : Rd d) (ρ : ℕ → ℝ), (∀ i, 0 < ρ i) →
          (∀ i, ρ (i + 1) ≤ q * ρ i) →
          ∀ (n : ℕ) (F : Fin n → Ω → ℝ),
            (∀ (i : Fin n), Measurable[fieldSigma0 h
              (ann z (a * ρ i) (b * ρ i))] (F i)) →
            (∀ i ω, 0 ≤ F i ω ∧ F i ω ≤ 1) →
            ∫ ω, ∏ i, F i ω ∂P ≤
              ∏ i, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹ := by
  obtain ⟨K, hK, hzero⟩ :=
    shellDecouplingFun_zero hd a b q ha ha1 hb1 hq hq1
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ h hh z ρ hpos hstep n F hFm hF01
  let h' : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hh' : IsWholeSpaceLGF h' P := hh.affineComp one_pos z
  have hFm' : ∀ (i : Fin n), Measurable[fieldSigma0 h'
      (ann 0 (a * ρ i) (b * ρ i))] (F i) := by
    intro i
    rw [show fieldSigma0 h' (ann 0 (a * ρ i) (b * ρ i)) =
      fieldSigma0 h (ann z (a * ρ i) (b * ρ i)) from
        fieldSigma0_ann_translate h z _ _]
    exact hFm i
  exact hzero P h' hh' ρ hpos hstep n F hFm' hF01

/-- Functional shell decoupling, with a constant uniform in the law and centre. -/
theorem shellDecouplingFun {d : ℕ} (hd : 1 ≤ d) : ShellDecouplingFun0 d := by
  classical
  intro a b q ha ha1 hb1 hq hq1
  obtain ⟨K, hK, hinit⟩ :=
    shellDecouplingFun_initial hd a b q ha ha1 hb1 hq hq1
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ h hh z r hpos hstep I F hFm hF01
  have hex (i : ℕ) : ∃ H : Ω → ℝ,
      Measurable[fieldSigma0 h (ann z (a * r i) (b * r i))] H ∧
      (∀ ω, 0 ≤ H ω ∧ H ω ≤ 1) ∧ F i =ᵐ[P] H :=
    shellBoundedRepresentative P _ (F i) (hFm i)
      (fun ω => (hF01 i ω).1) (fun ω => (hF01 i ω).2)
  choose H hHm hH01 hFH using hex
  let n : ℕ := I.sup id + 1
  have hI : ∀ i ∈ I, i < n := by
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  let Fpad : Fin n → Ω → ℝ :=
    fun j ω => if (j : ℕ) ∈ I then H j ω else 1
  have hpadM : ∀ (j : Fin n),
      Measurable[fieldSigma0 h (ann z (a * r j) (b * r j))] (Fpad j) := by
    intro j
    by_cases hj : (j : ℕ) ∈ I
    · simp [Fpad, hj, hHm (j : ℕ)]
    · simp [Fpad, hj]
  have hpad01 : ∀ (j : Fin n) ω,
      0 ≤ Fpad j ω ∧ Fpad j ω ≤ 1 := by
    intro j ω
    by_cases hj : (j : ℕ) ∈ I
    · simpa [Fpad, hj] using hH01 (j : ℕ) ω
    · simp [Fpad, hj]
  have hbound := hinit P h hh z r hpos hstep n Fpad hpadM hpad01
  have hLω (ω : Ω) :
      (∏ j : Fin n, Fpad j ω) = ∏ i ∈ I, H i ω := by
    simpa only [Fpad] using
      shellProdPad I n hI (fun i => H i ω)
  have hL : (∫ ω, ∏ j : Fin n, Fpad j ω ∂P) =
      ∫ ω, ∏ i ∈ I, H i ω ∂P :=
    integral_congr_ae (ae_of_all _ hLω)
  have hRj (j : Fin n) :
      (∫ ω, Fpad j ω ^ K ∂P) ^ K⁻¹ =
        if (j : ℕ) ∈ I then
          (∫ ω, H j ω ^ K ∂P) ^ K⁻¹ else 1 := by
    by_cases hj : (j : ℕ) ∈ I
    · simp [Fpad, hj]
    · simp [Fpad, hj]
  have hR : (∏ j : Fin n, (∫ ω, Fpad j ω ^ K ∂P) ^ K⁻¹) =
      ∏ i ∈ I, (∫ ω, H i ω ^ K ∂P) ^ K⁻¹ := by
    simp_rw [hRj]
    exact shellProdPad I n hI
      (fun i => (∫ ω, H i ω ^ K ∂P) ^ K⁻¹)
  have hLH : (∫ ω, ∏ i ∈ I, F i ω ∂P) =
      ∫ ω, ∏ i ∈ I, H i ω ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hFH] with ω hω
    exact Finset.prod_congr rfl fun i _ => hω i
  have hRH : (∏ i ∈ I, (∫ ω, H i ω ^ K ∂P) ^ K⁻¹) =
      ∏ i ∈ I, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹ := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply integral_congr_ae
    filter_upwards [hFH i] with ω hω
    exact congrArg (fun x : ℝ => x ^ K) hω.symm
  calc
    (∫ ω, ∏ i ∈ I, F i ω ∂P) =
        ∫ ω, ∏ i ∈ I, H i ω ∂P := hLH
    _ = ∫ ω, ∏ j : Fin n, Fpad j ω ∂P := hL.symm
    _ ≤ ∏ j : Fin n, (∫ ω, Fpad j ω ^ K ∂P) ^ K⁻¹ := hbound
    _ = ∏ i ∈ I, (∫ ω, H i ω ^ K ∂P) ^ K⁻¹ := hR
    _ = ∏ i ∈ I, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹ := hRH

end HigherDimLQGMetric
