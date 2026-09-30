import QuantumZipper.Proofs.Zipper.BaseFin2UL
import QuantumZipper.Proofs.LQG.RevCouplingReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL-N: `BaseULNrmStmt` from a first moment of the `Γ⁰` approximations

Proves `baseULNrm_of_gamma0 : BaseULGamma0MomStmt → BaseULNrmStmt` (with `p = 1`).

* Pathwise, for every field `y`: `ν_y([−n,n]) ≤ liminf_k ∫ φ_n dν^k_y` (`ul_qbm_le_liminf`), where
  `ν^k_y = bdryApprox` and `φ_n` is the tent function equal to `1` on `[−n,n]`, supported in
  `[−n−1, n+1]` (vague convergence when the limit exists; `ν_y = 0` otherwise).
* The functional `y ↦ liminf_k ∫ φ_n dν^k_{y − y(ϖ₀)}` is a measurable function of the circle
  coordinates of `nrm y` (`ulPsi`, via `RevCouplingReg.recF`; `ϖ₀ = fc(0,1)` is one of the
  enumerated circles), so its law under the chart-`1` field equals its law under the `Γ⁰` field
  (Theorem 1.2 at the level of circle coordinates, `B1Full.b1_full`).
* Fatou reduces the `Γ⁰` side to the first moments of the approximations (`BaseULGamma0MomStmt`),
  a statement about the free field alone.

Own elementary bookkeeping (no published proof of X1, see `BaseFin2Defs.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

/-- **(X1-UL-G)** Uniform first moments of the approximate boundary measures of the `Γ⁰` field
normalized on `ϖ₀`, growing at most exponentially in the window. -/
def BaseULGamma0MomStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ A : ℝ, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → RegUnif.IsNrmSample X → ∀ k n : ℕ,
    ∫⁻ ω, bdryApprox (Real.sqrt κ) (ulShift (ofFun (h0rev κ) + X ω)) k
        (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) ∂P ≤ K * ENNReal.ofReal (Real.exp (A * n))

/-! ## The tent function -/

/-- `φ_n = 1` on `[−n,n]`, `0` off `[−n−1, n+1]`, linear in between. -/
def ulPhi (n : ℕ) (t : ℝ) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - |t|))

theorem ulPhi_cont (n : ℕ) : Continuous (ulPhi n) := by
  unfold ulPhi; fun_prop

theorem ulPhi_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ulPhi n t := le_max_left _ _

theorem ulPhi_le_one (n : ℕ) (t : ℝ) : ulPhi n t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ulPhi_eq_one {n : ℕ} {t : ℝ} (ht : t ∈ Icc (-(n : ℝ)) n) : ulPhi n t = 1 := by
  unfold ulPhi
  have : |t| ≤ n := abs_le.2 ⟨ht.1, ht.2⟩
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ulPhi_eq_zero {n : ℕ} {t : ℝ} (ht : t ∉ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :
    ulPhi n t = 0 := by
  unfold ulPhi
  have : (n : ℝ) + 1 < |t| := by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact lt_abs.2 (Or.inr (by linarith))
    · exact lt_abs.2 (Or.inl h)
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem ulPhi_hcs (n : ℕ) : HasCompactSupport (ulPhi n) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => ulPhi_eq_zero ht

theorem ul_ofReal_integral_le {μ : Measure ℝ} {f : ℝ → ℝ} (hf : 0 ≤ f) :
    ENNReal.ofReal (∫ t, f t ∂μ) ≤ ∫⁻ t, ENNReal.ofReal (f t) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf)]
  · rw [integral_undef hi]; simp

/-- **Pathwise lower semicontinuity**: `ν_y([−n,n]) ≤ liminf_k ∫ φ_n dν^k_y`, for every `y`. -/
theorem ul_qbm_le_liminf (γ : ℝ) (y : FieldSample) (n : ℕ) :
    qBoundaryMeasure γ y (Icc (-(n : ℝ)) n) ≤
      liminf (fun k => ∫⁻ t, ENNReal.ofReal (ulPhi n t) ∂bdryApprox γ y k) atTop := by
  by_cases hex : ∃ ν, IsVagueLimitR (bdryApprox γ y) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [qBoundaryMeasure_eq hν]
    have := hν.1
    have hint : Integrable (ulPhi n) ν :=
      (ulPhi_cont n).integrable_of_hasCompactSupport (ulPhi_hcs n)
    have h1 : ν (Icc (-(n : ℝ)) n) ≤ ENNReal.ofReal (∫ t, ulPhi n t ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (ulPhi_nonneg n))]
      calc ν (Icc (-(n : ℝ)) n) = ∫⁻ t, (Icc (-(n : ℝ)) n).indicator 1 t ∂ν :=
            (lintegral_indicator_one measurableSet_Icc).symm
        _ ≤ _ := lintegral_mono fun t => by
            by_cases ht : t ∈ Icc (-(n : ℝ)) n
            · simp [ht, ulPhi_eq_one ht]
            · simp [ht]
    have h2 : Tendsto (fun k => ENNReal.ofReal (∫ t, ulPhi n t ∂bdryApprox γ y k)) atTop
        (𝓝 (ENNReal.ofReal (∫ t, ulPhi n t ∂ν))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hν.2 _ (ulPhi_cont n) (ulPhi_hcs n))
    rw [← h2.liminf_eq] at h1
    exact h1.trans (liminf_le_liminf (Eventually.of_forall fun k =>
      ul_ofReal_integral_le (ulPhi_nonneg n)))
  · unfold qBoundaryMeasure
    simp [hex]

/-! ## The coordinate functional -/

theorem ulNorm_univ : (ulNorm univ).toReal = 1 := by
  unfold ulNorm; simp

theorem ulShift_nrm (y : FieldSample) : ulShift (B1Full.nrm y) = ulShift y := by
  funext μ
  simp only [ulShift, B1Full.nrm, addConst, ulNorm_univ]
  ring

theorem measurable_ulShift : Measurable ulShift := by
  refine measurable_pi_iff.2 fun μ => ?_
  simp only [ulShift, addConst]
  exact (measurable_pi_apply μ).add ((measurable_pi_apply ulNorm).neg.mul_const _)

theorem ulNorm_mem :
    ∃ i, foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = ulNorm := by
  refine ⟨Encodable.encode ((0 : ℤ), (0 : ℤ), (0 : ℕ), (0 : ℕ), (0 : ℕ)), ?_⟩
  unfold CoordsFull.fullIndex ulNorm
  rw [Denumerable.ofNat_encode]
  congr 1
  · apply Complex.ext <;> simp
  · norm_num

/-- `∫ φ_n dν^k` of the `ϖ₀`-normalized field reconstructed from circle coordinates. -/
def ulPsiK (γ : ℝ) (n k : ℕ) (c : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (ulPhi n t) ∂bdryApprox γ (ulShift (RevCouplingReg.recF c)) k

/-- The liminf functional. -/
def ulPsi (γ : ℝ) (n : ℕ) (c : ℕ → ℝ) : ℝ≥0∞ := liminf (fun k => ulPsiK γ n k c) atTop

theorem measurable_ulPsiK (γ : ℝ) (n k : ℕ) : Measurable (ulPsiK γ n k) :=
  (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (ulPhi_cont n).measurable)).comp
    ((measurable_bdryApprox γ k).comp (measurable_ulShift.comp RevCouplingReg.measurable_recF))

theorem measurable_ulPsi (γ : ℝ) (n : ℕ) : Measurable (ulPsi γ n) :=
  Measurable.liminf fun k => measurable_ulPsiK γ n k

theorem ulPsiK_coords (γ : ℝ) (n k : ℕ) (z : FieldSample) :
    ulPsiK γ n k (CoordsFull.coordsFull z) =
      ∫⁻ t, ENNReal.ofReal (ulPhi n t) ∂bdryApprox γ (ulShift z) k := by
  obtain ⟨i₀, hi₀⟩ := ulNorm_mem
  have hc : CoordsFull.coordsFull (ulShift (RevCouplingReg.recF (CoordsFull.coordsFull z))) =
      CoordsFull.coordsFull (ulShift z) := by
    have h := RevCouplingReg.coordsFull_recF z
    have h0 : RevCouplingReg.recF (CoordsFull.coordsFull z) ulNorm = z ulNorm := by
      have := congrFun h i₀
      simp only [CoordsFull.coordsFull, hi₀] at this
      exact this
    funext i
    have hi := congrFun h i
    simp only [CoordsFull.coordsFull] at hi
    simp only [CoordsFull.coordsFull, ulShift, addConst, hi, h0]
  have ha := CoordsFull.avgReg_congr_full hc
  unfold ulPsiK
  unfold bdryApprox
  rw [ha]

/-- **`BaseULNrmStmt` from the `Γ⁰` first moments.** -/
theorem baseULNrm_of_gamma0 (hG : BaseULGamma0MomStmt) : BaseULNrmStmt := by
  intro κ hκ hκ4
  obtain ⟨A, K, hK, hG'⟩ := hG κ hκ hκ4
  refine ⟨1, one_pos, A, K, hK, ?_⟩
  intro Ω _ P _ B X hB hX hind hNrm n
  have hF1 := B2.aemeasurable_data_unzip (κ := κ) hB hX hind zero_le_one
  have hF0 := B2.aemeasurable_data0 (κ := κ) hB hX
  have hlaw := B1Full.b1_full κ hκ P B X hB hX hind one_pos
  refine ⟨fun ω => ulPsi (Real.sqrt κ) n (CoordsFull.coordsFull (B1Full.nrm
    (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) 1))),
    (measurable_ulPsi _ n).comp_aemeasurable hF1.fst.fst, ?_, ?_⟩
  · simp only [ENNReal.rpow_one]
    have hm : Measurable fun p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) =>
        ulPsi (Real.sqrt κ) n p.1.1 :=
      (measurable_ulPsi _ n).comp (measurable_fst.comp measurable_fst)
    calc ∫⁻ ω, ulPsi (Real.sqrt κ) n (CoordsFull.coordsFull (B1Full.nrm
          (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) 1))) ∂P
        = ∫⁻ ω, ulPsi (Real.sqrt κ) n (CoordsFull.coordsFull
            (B1Full.nrm (ofFun (h0rev κ) + X ω))) ∂P := by
          have e1 := lintegral_map' hm.aemeasurable hF1
          have e0 := lintegral_map' hm.aemeasurable hF0
          rw [hlaw] at e1
          exact e1.symm.trans e0
      _ ≤ liminf (fun k => ∫⁻ ω, ulPsiK (Real.sqrt κ) n k (CoordsFull.coordsFull
            (B1Full.nrm (ofFun (h0rev κ) + X ω))) ∂P) atTop :=
          lintegral_liminf_le' fun k => (measurable_ulPsiK _ n k).comp_aemeasurable hF0.fst.fst
      _ ≤ K * ENNReal.ofReal (Real.exp (A * n)) := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          refine le_trans (lintegral_mono fun ω => ?_) (hG' P X hX hNrm k n)
          rw [ulPsiK_coords, ulShift_nrm]
          calc ∫⁻ t, ENNReal.ofReal (ulPhi n t) ∂bdryApprox (Real.sqrt κ)
                (ulShift (ofFun (h0rev κ) + X ω)) k
              ≤ ∫⁻ t, (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)).indicator 1 t ∂bdryApprox
                (Real.sqrt κ) (ulShift (ofFun (h0rev κ) + X ω)) k := by
                refine lintegral_mono fun t => ?_
                by_cases ht : t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
                · simp only [ht, indicator_of_mem, Pi.one_apply]
                  rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (ulPhi_le_one n t)
                · simp [ulPhi_eq_zero ht]
            _ = _ := lintegral_indicator_one measurableSet_Icc
  · refine Eventually.of_forall fun ω => ?_
    rw [B2.h0f_eq_unzippedField]
    simp only [ulPsi, ulPsiK_coords, ulShift_nrm]
    exact ul_qbm_le_liminf _ _ n

end BaseFin2
end QuantumZipper
