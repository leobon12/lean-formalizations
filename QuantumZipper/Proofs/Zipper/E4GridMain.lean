import QuantumZipper.Proofs.Zipper.E4Grid

/-!
# E4-GRID: main statement

`handoff/E-PLAN-2.md`, node E4-GRID (`E4GridStmt` of `handoff/E-PLAN-2-statements.lean.txt`, with
`s ω x = dyUp n (sigEps (Vr κ T B ω) T ε x)` written `sG κ T T B ε n ω x`; the plan's `0 < ε` is not
needed). `e4_grid_cap`: the same with the entrance time capped at any `T₀ ∈ (0, T]` (for E4-LIM). Unconditional: `hReg` is `RevCouplingReg.revCouplingBoundaryMeasureRegular`, E1-TR is
`E1.e1_tr`.

Proof: `E4Grid.grid_lintegral` on both sides (G1 `gridSet`, G2 measurability), then E1-NU
(`E1Nu.e1_nu_of_tr`) at each grid time `t_k < T` with `Ψ_k = Ψ · 1_{gridSet}`. On the right side
the inner expectation is the measurable `H_k(x, V^{t_k}, W⁰)` of E4-MEAS on live points.
Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E4-GRID, capped form.** E1-NU at the `x`-dependent grid time `s = dyUp n σ_ε(x)` (entrance
time capped at `T₀ ≤ T`), on `{s < T₀, x live at s}`. -/
theorem e4_grid_cap {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    (hX' : IsFreeGFFModConstH X' P') {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (δ ε : ℝ) (n : ℕ)
    {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} {Φ : (ℕ → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
          (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
            Φ (coordsFull (addConst (Yf κ T (sG κ T T₀ B ε n ω x) B X ω)
              (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
          (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
            ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (sG κ T T₀ B ε n ω x) ϖ x
              (X' ω'))) ∂P') x
        ∂nuPalm κ T B X ϖ ω ∂P := by
  have hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular
  have hν := NuMeas.aemeasurable_nuPalm hReg hκ hκ4 hT hB hX hind hϖ
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have htk : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, tk n k < T := fun k hk =>
    ((tk_lt_iff n k T₀).1 (Finset.mem_range.1 hk)).trans_le hT₀T
  have hD : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊,
      AEMeasurable (fun ω => (Vstop κ T (tk n k) B ω, W0p κ T B ω)) P := fun k hk =>
    (aemeasurable_data (κ := κ) hB hX hind (tk_nonneg n k) (htk k hk).le).snd
  choose H hHm hH using fun k => E4Meas.e4_meas (tk_nonneg n k) κ ϖ hϖ hX' hΦ
  have key : ∀ᵐ ω ∂P, ∀ k x, IsLive (Vr κ T B ω) (tk n k) x →
      ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P' =
        H k (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) := by
    filter_upwards [hB.cont] with ω hc k x hx
    have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
    have hS : Continuous (stopDrive (Vstop κ T (tk n k) B ω, W0p κ T B ω)) := by
      unfold stopDrive Vstop
      exact hV.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).min continuous_const)
    have hD1 : Continuous (Vstop κ T (tk n k) B ω) :=
      hV.comp (NNReal.continuous_coe.min continuous_const)
    have heq := E1Nu.eqOn_Vr_stopDrive (κ := κ) (T := T) (t := tk n k) (B := B) ω
    rw [hH k x _ hD1 ((isLive_congr_drive hV hS (tk_nonneg n k) heq).1 hx)]
    exact lintegral_congr fun ω' => by rw [E1Nu.targetField_congr_drive κ heq]
  have hR : ∀ᵐ ω ∂P, ∀ k x,
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P' =
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        H k (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) := by
    filter_upwards [hB.cont, key] with ω hc hk k x
    by_cases h : (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) ∈ gridSet T₀ ε n k
    · rw [hk k x ((mem_gridSet_Vr hc hT.le hT₀.le (fst_neg_of_mem_gridSet h).le k).1 h).2.2]
    · simp only [PsiK, indicator_of_notMem h, zero_mul]
  have mL : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω)))) :=
    Eventually.of_forall fun ω k _ => (measurable_PsiK hΨ).of_uncurry_right.mul_const _
  have aL : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω) P := by
    intro k hk
    refine (aemeasurable_setLIntegral_family hν hfin ((hD k hk).prodMk
      (aemeasurable_field (κ := κ) hB hX hind hϖ (tk_nonneg n k) (htk k hk)))
      (g := fun p => PsiK T₀ ε n k Ψ p.1 p.2.1 * Φ p.2.2) ?_).congr ?_
    · exact ((measurable_PsiK hΨ).comp (measurable_fst.prodMk
        (measurable_fst.comp measurable_snd))).mul (hΦ.comp (measurable_snd.comp measurable_snd))
    · filter_upwards [hB.cont] with ω hc
      exact setLIntegral_congr_fun measurableSet_Icc fun x _ => (liveInd_eq hc hT.le hT₀.le k
        (fun _ => Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω))))) x).symm
  have mR : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P' := by
    filter_upwards [hR] with ω h k _
    simp_rw [h k]
    exact (measurable_PsiK hΨ).of_uncurry_right.mul
      ((hHm k).comp (measurable_id.prodMk measurable_const))
  have aR : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
          ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P') x
        ∂nuPalm κ T B X ϖ ω) P := by
    intro k hk
    refine (aemeasurable_setLIntegral_family hν hfin (hD k hk)
      (g := fun p => PsiK T₀ ε n k Ψ p.1 p.2 * H k p) ((measurable_PsiK hΨ).mul (hHm k))).congr ?_
    filter_upwards [hB.cont, hR] with ω hc h
    refine setLIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    rw [liveInd_eq hc hT.le hT₀.le k _ x, h k x]
  rw [grid_lintegral (Z := fun ω x s => Φ (coordsFull (addConst (Yf κ T s B X ω)
      (-(mReg κ T B X ϖ ω))))) hT.le hT₀ hB δ mL aL,
    grid_lintegral (Z := fun ω x s => ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) s ϖ x
      (X' ω'))) ∂P') hT.le hT₀ hB δ mR aR]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact E1Nu.e1_nu_of_tr hκ hκ4 (tk_nonneg n k) (htk k hk) hB hX hX' hϖ δ
    (fun Ψ Φ hΨ hΦ => e1_tr hReg hκ hκ4 (tk_nonneg n k) (htk k hk) hB hX hind hϖ δ hΨ hΦ)
    (measurable_PsiK hΨ) hΦ

end E4Grid
end QuantumZipper
