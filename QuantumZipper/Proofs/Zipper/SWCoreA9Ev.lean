import QuantumZipper.Proofs.Zipper.SWCoreA8Rand

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (1): offset radii — measurable proxies, countable event, fixed-path fibre

Offset-radius analogue of SWC-A8 (radius `α 2^{-k}` with a rational factor `α ∈ [1,2]`, the
radius factor `a7Rad` of the D64 family `a7Map`), at rational times, factors and centres.
In Sheffield–Wang (arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7)) the radius `ε` is a
continuous parameter, so the offsets are part of the paper's statement.

* `a9Phi`, `a9Rd`: measurable proxies of the smoothed pushed pairing at radius `α 2^{-k}` and of
  the round value at radius `α 2^{-k} |(f_t⁻¹)'(z)|`;
* `a9Ev`: the countable event (rational `t`, `α`, centres);
* `a9_fibre`: for every good path, almost surely in the free field, `a9Ev` holds (primed core
  `swcNA2I_primed` for the family `a7Map`, read on the diagonal `a9Diag`).

Own bookkeeping, mirrors `SWCoreA8Meas`/`SWCoreA8Fib` with the radius factor of the D64 family
`a7Rad`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

section Meas

variable (κ : ℝ) {T : ℝ} (hT : 0 ≤ T)

/-- Proxy of the smoothed pushed pairing at radius `α 2^{-k}`. -/
def a9Phi (j k : ℕ) (α : ℝ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ)
    (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  PsiKm hT κ z (α * radius k) s hs j p

/-- Proxy of the round value at radius `α 2^{-k} |(f_t⁻¹)'(z)|`. -/
def a9Rd (k : ℕ) (α : ℝ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ)
    (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  evalReg p.2 (foldedCircle (Fm κ s hs (revPath hT s hs p.1, z))
    (α * radius k * ‖Dm κ s hs (revPath hT s hs p.1, z)‖))

theorem measurable_a9Phi (j k : ℕ) (α s : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    Measurable (a9Phi κ hT j k α s hs z) :=
  measurable_PsiKm hT κ z (α * radius k) s hs j

set_option maxHeartbeats 1000000 in
-- the proxies unfold through `revPath` and `Fm`
theorem measurable_a9Rd (k : ℕ) (α s : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    Measurable (a9Rd κ hT k α s hs z) := by
  unfold a9Rd
  have hG : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      (revPath hT s hs p.1, z) := ((measurable_revPath hT s hs).comp measurable_fst).prodMk
        measurable_const
  have h1 : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      (p.2, (Fm κ s hs (revPath hT s hs p.1, z),
        α * radius k * ‖Dm κ s hs (revPath hT s hs p.1, z)‖)) :=
    measurable_snd.prodMk (((measurable_Fm κ s hs).comp hG).prodMk
      (measurable_const.mul ((measurable_Dm κ s hs).comp hG).norm))
  exact (IndepParams.measurable_evalReg_fc₂.comp h1 :)

/-- The countable event on `C([0,T]) × FieldSample` for the rectangle `[A,B] × [C,D]`. -/
def a9Ev (A B C D : ℚ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : Prop :=
  (∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ j' : ℕ, J ≤ j' →
    ∀ q : ℚ, ∀ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 →
      ∀ z : ℚ × ℚ, zQ z ∈ rectC A B C D →
      |a9Phi κ hT j k α q hq.1 (zQ z) p - a9Phi κ hT j' k α q hq.1 (zQ z) p| ≤
        1 / ((m : ℝ) + 1)) ∧
  ∀ n : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
    ∀ q : ℚ, ∀ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 →
      ∀ z : ℚ × ℚ, zQ z ∈ rectC A B C D →
      |a9Phi κ hT j k α q hq.1 (zQ z) p - a9Rd κ hT k α q hq.1 (zQ z) p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_a9Ev (A B C D : ℚ) : MeasurableSet {p | a9Ev κ hT A B C D p} := by
  refine measurableSet_setOfPred.2 ?_
  unfold a9Ev
  refine Measurable.and ?_ ?_
  · refine Measurable.exists fun K₀ => Measurable.forall fun k => Measurable.forall fun _ =>
      Measurable.forall fun m => Measurable.exists fun J => Measurable.forall fun j =>
      Measurable.forall fun _ => Measurable.forall fun j' => Measurable.forall fun _ =>
      Measurable.forall fun q => Measurable.forall fun hq => Measurable.forall fun α =>
      Measurable.forall fun _ => Measurable.forall fun z => Measurable.forall fun _ => ?_
    exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_a9Phi κ hT _ _ _ _ _ _).sub (measurable_a9Phi κ hT _ _ _ _ _ _)))
      measurable_const)
  · refine Measurable.forall fun n => Measurable.exists fun K => Measurable.forall fun k =>
      Measurable.forall fun _ => Measurable.exists fun J => Measurable.forall fun j =>
      Measurable.forall fun _ => Measurable.forall fun q => Measurable.forall fun hq =>
      Measurable.forall fun α => Measurable.forall fun _ =>
      Measurable.forall fun z => Measurable.forall fun _ => ?_
    exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_a9Phi κ hT _ _ _ _ _ _).sub (measurable_a9Rd κ hT _ _ _ _ _)))
      measurable_const)

variable {κ hT}

theorem a9Phi_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (j k : ℕ) {α : ℝ} (hα : 0 < α) (z : ℂ) (x : FieldSample) :
    a9Phi κ hT j k α s hs.1 z (f, x) =
      ∫ u, avgReg x j u ∂((foldedCircle z (α * radius k)).map (fwdMapInv (Wof κ T hT f) s)) :=
  PsiKm_eq hT κ z (mul_pos hα (radius_pos k)) hs j f hf0 x

theorem a9Rd_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (k : ℕ) (α : ℝ) {z : ℂ} (hz : z ∈ H) (x : FieldSample) :
    a9Rd κ hT k α s hs.1 z (f, x) = evalReg x (foldedCircle (fwdMapInv (Wof κ T hT f) s z)
      (α * radius k * ‖deriv (fwdMapInv (Wof κ T hT f) s) z‖)) := by
  unfold a9Rd
  rw [a8_Fm_eq hf0 hs hz, a8_Dm_eq hf0 hs hz]

end Meas

/-! ## The fixed-path fibre -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The diagonal with radius factor `α`. -/
def a9Diag (V : ℝ → ℝ) (t : ℝ) (w : ℂ) (α : ℝ) : Fin 5 → ℝ := ![t, V t, w.re, w.im, α]

theorem continuous_a9Diag_joint (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous fun p : ℝ × ℂ × ℝ => a9Diag W p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [a9Diag] <;> fun_prop

/-- **The fixed-path fibre** (offset radii). -/
theorem a9_fibre [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (κ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) {A B C D : ℚ} (hAB : (A : ℝ) ≤ B) (hC : (0 : ℝ) < C) (hCD : (C : ℝ) ≤ D)
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT (1 / 3)) :
    ∀ᵐ ω ∂P, a9Ev κ hT A B C D (f, X ω) := by
  set W := Wof κ T hT f with hWdef
  have hW : Continuous W := continuous_Wof κ T hT f
  have hW0 : W 0 = 0 := Wof_zero_of_GoodP hT κ hf
  obtain ⟨S, ρ, M, m, HL, hS, h⟩ := a7_unif hW hW0 hT (x₁ := A) (x₂ := B) (y₁ := C) (y₂ := D)
    hAB hC hCD
  have hdiag : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D, ∀ α ∈ Icc (1 : ℝ) 2,
      a7Map W T S (a9Diag W t w α) = fwdMapInv W t ∧
        a7Cen A B C D (a9Diag W t w α) = w ∧ a7Rad (a9Diag W t w α) = α := by
    intro t ht w hw α hα
    refine ⟨a7Map_diag ht (hS t ht) (by simp [a9Diag]) (by simp [a9Diag]), ?_, ?_⟩
    · apply Complex.ext
      · simp only [a7Cen, a9Diag]
        exact clampI_eq hw.1
      · simp only [a7Cen, a9Diag]
        exact clampI_eq hw.2
    · simp only [a7Rad, a9Diag]
      exact clampI_eq hα
  set R : ℕ := ⌈|T| + |S| + |(A : ℝ)| + |(B : ℝ)| + |(D : ℝ)| + 2⌉₊ with hRdef
  have hRle : |T| + |S| + |(A : ℝ)| + |(B : ℝ)| + |(D : ℝ)| + 2 ≤ R := Nat.le_ceil _
  have hR : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D, ∀ α ∈ Icc (1 : ℝ) 2,
      a9Diag W t w α ∈ KolmD.boxD (d := 5) R := by
    intro t ht w hw α hα i
    have h0 := abs_nonneg T; have h1 := abs_nonneg S; have h2 := abs_nonneg (A : ℝ)
    have h3 := abs_nonneg (B : ℝ); have h4 := abs_nonneg (D : ℝ)
    fin_cases i
    · simp only [a9Diag]
      show |t| ≤ R
      rw [abs_of_nonneg ht.1]
      linarith [le_abs_self T, ht.2]
    · simp only [a9Diag]
      show |W t| ≤ R
      linarith [hS t ht, le_abs_self S]
    · simp only [a9Diag]
      show |w.re| ≤ R
      rw [abs_le]
      constructor <;> linarith [hw.1.1, hw.1.2, neg_abs_le (A : ℝ), le_abs_self (B : ℝ)]
    · simp only [a9Diag]
      show |w.im| ≤ R
      rw [abs_le]
      constructor <;> linarith [hw.2.1, hw.2.2, le_abs_self (D : ℝ)]
    · simp only [a9Diag]
      show |α| ≤ R
      rw [abs_le]
      constructor <;> linarith [hα.1, hα.2]
  set Kc : Set (Fin 5 → ℝ) := (fun p : ℝ × ℂ × ℝ => a9Diag W p.1 p.2.1 p.2.2) ''
    (Icc (0 : ℝ) T ×ˢ (rectC (A : ℝ) B C D ×ˢ Icc (1 : ℝ) 2)) with hKcdef
  have hKc : IsCompact Kc :=
    (isCompact_Icc.prod ((swA6_isCompact_rectC _ _ _ _).prod isCompact_Icc)).image
      (continuous_a9Diag_joint W hW)
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX h
  filter_upwards [hae] with ω hω
  obtain ⟨hi, -, hiii⟩ := hω
  have hread : ∀ k' j : ℕ, ∀ t (ht : t ∈ Icc (0 : ℝ) T), ∀ w ∈ rectC (A : ℝ) B C D,
      ∀ α ∈ Icc (1 : ℝ) 2,
      (∫ u, avgReg (X ω) j u ∂((foldedCircle (a7Cen A B C D (a9Diag W t w α))
        (a7Rad (a9Diag W t w α) * radius (k' + k₀))).map (a7Map W T S (a9Diag W t w α)))) =
        a9Phi κ hT j (k' + k₀) α t ht.1 w (f, X ω) := by
    intro k' j t ht w hw α hα
    obtain ⟨e1, e2, e3⟩ := hdiag t ht w hw α hα
    rw [e1, e2, e3, a9Phi_eq hW0 ht j (k' + k₀) (by linarith [hα.1])]
  have hmemK : ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ rectC (A : ℝ) B C D, ∀ α ∈ Icc (1 : ℝ) 2,
      a9Diag W t w α ∈ Kc :=
    fun t ht w hw α hα => ⟨(t, w, α), ⟨ht, hw, hα⟩, rfl⟩
  have hunif : ∀ k' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∀ t (ht : t ∈ Icc (0 : ℝ) T), ∀ w ∈ rectC (A : ℝ) B C D, ∀ α ∈ Icc (1 : ℝ) 2,
        dist (evalReg (X ω) ((foldedCircle w (α * radius (k' + k₀))).map (fwdMapInv W t)))
          (a9Phi κ hT j (k' + k₀) α t ht.1 w (f, X ω)) < ε := by
    intro k' ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 (hi k' Kc hKc)) ε hε)
    refine ⟨J, fun j hj t ht w hw α hα => ?_⟩
    have := hJ j hj _ (hmemK t ht w hw α hα)
    obtain ⟨e1, e2, e3⟩ := hdiag t ht w hw α hα
    rw [hread k' j t ht w hw α hα] at this
    rw [e1, e2, e3] at this
    exact this
  have hzH : ∀ z : ℚ × ℚ, zQ z ∈ rectC (A : ℝ) B C D → zQ z ∈ H := fun z hz =>
    show 0 < (zQ z).im from lt_of_lt_of_le hC hz.2.1
  refine ⟨⟨k₀, fun k hk m => ?_⟩, fun n => ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + k₀ := ⟨k - k₀, (Nat.sub_add_cancel hk).symm⟩
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) / 2 := by positivity
    obtain ⟨J, hJ⟩ := hunif k' _ hε
    refine ⟨J, fun j hj j' hj' q hq α hα z hz => ?_⟩
    have h1 := hJ j hj q hq (zQ z) hz α hα
    have h2 := hJ j' hj' q hq (zQ z) hz α hα
    rw [Real.dist_eq] at h1 h2
    rw [abs_sub_comm] at h1
    calc _ ≤ |a9Phi κ hT j (k' + k₀) α q hq.1 (zQ z) (f, X ω) -
          evalReg (X ω) ((foldedCircle (zQ z) (α * radius (k' + k₀))).map (fwdMapInv W q))| +
          |evalReg (X ω) ((foldedCircle (zQ z) (α * radius (k' + k₀))).map (fwdMapInv W q)) -
          a9Phi κ hT j' (k' + k₀) α q hq.1 (zQ z) (f, X ω)| := abs_sub_le _ _ _
      _ ≤ 1 / ((m : ℝ) + 1) := by linarith
  · have hη : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
    obtain ⟨K', hK'⟩ := eventually_atTop.1 (hiii R _ hη)
    refine ⟨K' + k₀, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + k₀ := ⟨k - k₀, (Nat.sub_add_cancel (by omega)).symm⟩
    obtain ⟨J, hJ⟩ := hunif k' _ hη
    refine ⟨J, fun j hj q hq α hα z hz => ?_⟩
    have h1 := hJ j hj q hq (zQ z) hz α hα
    rw [Real.dist_eq, abs_sub_comm] at h1
    have h2 := hK' k' (by omega) _ (hR q hq (zQ z) hz α hα)
    obtain ⟨e1, e2, e3⟩ := hdiag q hq (zQ z) hz α hα
    rw [e1, e2, e3] at h2
    rw [a9Rd_eq hW0 hq (k' + k₀) α (hzH z hz)]
    calc _ ≤ |a9Phi κ hT j (k' + k₀) α q hq.1 (zQ z) (f, X ω) -
          evalReg (X ω) ((foldedCircle (zQ z) (α * radius (k' + k₀))).map (fwdMapInv W q))| +
          |evalReg (X ω) ((foldedCircle (zQ z) (α * radius (k' + k₀))).map (fwdMapInv W q)) -
          evalReg (X ω) (foldedCircle (fwdMapInv W q (zQ z))
            (α * radius (k' + k₀) * ‖deriv (fwdMapInv W q) (zQ z)‖))| := abs_sub_le _ _ _
      _ ≤ 1 / ((n : ℝ) + 1) := by linarith

end SWCore
end QuantumZipper
