import QuantumZipper.Proofs.Zipper.E1WindowAE
import QuantumZipper.Proofs.Zipper.E1Fixed

/-!
# E1-FIX: the Palm formula on the whole live window `[−δ, 0] ∩ liveNeg` (fixed driver)

`handoff/E1-PLAN.md`, sub-node **E1-FIX** (assembly (R3) of `handoff/E1-PW.md`). For a fixed
driver `v`, a normalizer `ϖ` and a free field `X'`,

```
∫⁻ ω', ∫⁻ x in [−δ,0], G x (coordsFull (addConst (𝔥₀ + X') (−m)))
    ∂qBoundaryMeasureOn √κ (addConst (hFix κ v t X') (−m)) (liveNeg v t) ∂P'
  = ∫⁻ x in [−δ,0], 1_{live}(x) · ρ_t(x) · ∫⁻ ω', G x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P'.
```

Proof. The open set `U = liveNeg v t` is the disjoint union of the pieces `D_n ⊆ W_n` of its
rational windows (`E1Glue`). Pathwise, the measure on `U` restricted to `W_n` is the measure on
`W_n` (uniqueness of local limits, `E1Fixed`), so the left integrand is `Σ_n T_n(ω)` with `T_n`
the E1-PW window term for the weight `1_{D_n ∩ [−δ,0]} G`. Each `T_n` is a.e. measurable
(`E1WindowAE`), so `∫⁻` and `Σ` commute; E1-PW (`lintegral_palm_window`) on each window and
re-summation give the right side (`Icc_inter_isLive_eq`).

Paper: Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68) and Thm 4.5 (p. 51); the
decomposition into windows is own bookkeeping (countable additivity).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open PalmNorm B2 CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E1-FIX** (`handoff/E1-PLAN.md`): the Palm formula of the fixed-driver field on the live part
of `[−δ, 0]`. (The plan's hypothesis `0 < δ` is not needed.) -/
theorem lintegral_palm_liveNeg [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ) (hv : Continuous v) (hv0 : v 0 = 0)
    (ht : 0 ≤ t) (δ : ℝ) {G : ℝ → (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, G x (coordsFull (addConst (ofFun (h0rev κ) + X' ω')
        (-(mFix κ v t ϖ (X' ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ v t (X' ω'))
          (-(mFix κ v t ϖ (X' ω')))) (liveNeg v t) ∂P' =
      ∫⁻ x in Icc (-δ) 0, {x | IsLive v t x}.indicator (fun x => ENNReal.ofReal (rhoT κ v t ϖ x) *
        ∫⁻ ω', G x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P') x := by
  set γ := Real.sqrt κ with hγdef
  set U := liveNeg v t with hUdef
  set S : Set ℝ := Icc (-δ) 0 with hSdef
  have hU : IsOpen U := isOpen_liveNeg hv t
  have hUD : ⋃ n, winD U n = U := (iUnion_winD U).trans (iUnion_winW hU)
  set Gn : ℕ → ℝ → (ℕ → ℝ) → ℝ≥0∞ := fun n x c => (winD U n ∩ S).indicator (fun x => G x c) x
    with hGndef
  have hGn : ∀ n, Measurable (Function.uncurry (Gn n)) := fun n =>
    hG.indicator (((measurableSet_winD U n).inter measurableSet_Icc).preimage measurable_fst)
  set c : Ω → ℕ → ℝ := fun ω => coordsFull (addConst (ofFun (h0rev κ) + X' ω)
    (-(mFix κ v t ϖ (X' ω)))) with hc
  set μ : Ω → Set ℝ → Measure ℝ := fun ω => qBoundaryMeasureOn γ (addConst (hFix κ v t (X' ω))
    (-(mFix κ v t ϖ (X' ω)))) with hμ
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => ∫⁻ x, Gn n x (c ω) ∂μ ω (winW U n) with hT
  set R : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (rhoT κ v t ϖ x) *
    ∫⁻ ω', G x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P' with hR
  -- pathwise decomposition of the left integrand
  have hpath : ∀ᵐ ω ∂P', ∫⁻ x in S, G x (c ω) ∂μ ω U = ∑' n, T n ω := by
    filter_upwards [ae_exists_isVagueLimitOnR_hFix_liveNeg hκ hκ4 hX hv hv0 ht,
      CoordReg.ae_isRegularSample_coordChange_h0rev' hv ht hX κ (Qc γ)] with ω hex hreg
    have hres : ∀ n, (μ ω U).restrict (winW U n) = μ ω (winW U n) := fun n => by
      simp only [hμ]
      rw [LocalRule.qBoundaryMeasureOn_addConst (x := hFix κ v t (X' ω)) hreg.rawConverges γ _ hU,
        LocalRule.qBoundaryMeasureOn_addConst (x := hFix κ v t (X' ω)) hreg.rawConverges γ _
          (isOpen_winW U n), Measure.restrict_smul,
        qBoundaryMeasureOn_restrict_of_subset hU (isOpen_winW U n) (winW_subset U n) hex]
    have hself : (μ ω U).restrict U = μ ω U :=
      Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (qBoundaryMeasureOn_compl γ _ U))
    calc ∫⁻ x in S, G x (c ω) ∂μ ω U
        = ∫⁻ x in U, S.indicator (fun x => G x (c ω)) x ∂μ ω U := by
          rw [lintegral_indicator measurableSet_Icc, hself]
      _ = ∑' n, ∫⁻ x in winD U n, S.indicator (fun x => G x (c ω)) x ∂μ ω U := by
          rw [← lintegral_iUnion (measurableSet_winD U) (pairwise_disjoint_winD U), hUD]
      _ = ∑' n, T n ω := tsum_congr fun n => by
          simp only [hT]
          rw [← hres n, ← lintegral_indicator (isOpen_winW U n).measurableSet,
            ← lintegral_indicator (measurableSet_winD U n)]
          refine lintegral_congr fun x => ?_
          simp only [hGndef, indicator_indicator]
          rw [inter_eq_right.2 (inter_subset_left.trans (winD_subset U n))]
  -- the bad windows
  have hbad : ∀ n, ¬(((winPQ n).1 : ℝ) < (winPQ n).2 ∧ Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U) →
      winD U n = ∅ := fun n hgood => by
    have hWe : winW U n = ∅ := by
      unfold winW; split_ifs with h
      · exact Ioo_eq_empty fun hlt => hgood ⟨hlt, h⟩
      · rfl
    exact subset_empty_iff.1 (hWe ▸ winD_subset U n)
  have hTz : ∀ n, winD U n = ∅ → T n = 0 := fun n hD => funext fun ω => by
    simp [hT, hGndef, hD]
  have hgoodW : ∀ n, ((winPQ n).1 : ℝ) < (winPQ n).2 ∧ Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U →
      winW U n = Ioo ((winPQ n).1 : ℝ) (winPQ n).2 := fun n hgood => by
    unfold winW; simp only [hgood.2, ↓reduceIte]
  have hTm : ∀ n, AEMeasurable (T n) P' := fun n => by
    by_cases hgood : ((winPQ n).1 : ℝ) < (winPQ n).2 ∧ Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U
    · simp only [hT, hgoodW n hgood]
      exact aemeasurable_window_lhs hκ hκ4 hX hϖ hv hv0 ht hgood.1 (fun x hx => hgood.2 hx)
        (hGn n)
    · rw [hTz n (hbad n hgood)]; exact aemeasurable_const
  -- each window by E1-PW
  have hwin : ∀ n, ∫⁻ ω, T n ω ∂P' = ∫⁻ x in winD U n ∩ S, R x := fun n => by
    by_cases hgood : ((winPQ n).1 : ℝ) < (winPQ n).2 ∧ Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U
    · have hW := hgoodW n hgood
      simp only [hT, hW]
      rw [lintegral_palm_window hκ hκ4 hX hϖ hv hv0 ht hgood.1 (fun x hx => hgood.2 hx) (hGn n)]
      have hpt : ∀ x, ENNReal.ofReal (rhoT κ v t ϖ x) *
          ∫⁻ ω', Gn n x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P' =
          (winD U n ∩ S).indicator R x := fun x => by
        by_cases hx : x ∈ winD U n ∩ S
        · simp [hGndef, hR, hx]
        · simp [hGndef, hx]
      simp_rw [hpt]
      have hm : MeasurableSet (winD U n ∩ S) := (measurableSet_winD U n).inter measurableSet_Icc
      rw [lintegral_indicator hm, Measure.restrict_restrict hm,
        inter_eq_left.2 (inter_subset_left.trans ((winD_subset U n).trans hW.le))]
    · have hD := hbad n hgood
      rw [hTz n hD, hD]; simp
  calc ∫⁻ ω', ∫⁻ x in S, G x (c ω') ∂μ ω' U ∂P'
      = ∫⁻ ω, ∑' n, T n ω ∂P' := lintegral_congr_ae hpath
    _ = ∑' n, ∫⁻ ω, T n ω ∂P' := lintegral_tsum hTm
    _ = ∑' n, ∫⁻ x in winD U n ∩ S, R x := tsum_congr hwin
    _ = ∫⁻ x in ⋃ n, winD U n ∩ S, R x :=
        (lintegral_iUnion (fun n => (measurableSet_winD U n).inter measurableSet_Icc)
          ((pairwise_disjoint_winD U).mono fun i j h =>
            Disjoint.mono inter_subset_left inter_subset_left h) R).symm
    _ = ∫⁻ x in S, {x | IsLive v t x}.indicator R x := by
        rw [lintegral_indicator (isOpen_setOf_isLive hv).measurableSet,
          Measure.restrict_restrict (isOpen_setOf_isLive hv).measurableSet, inter_comm,
          Icc_inter_isLive_eq hv0 δ, ← iUnion_inter, hUD, inter_comm]

end E1
end QuantumZipper
