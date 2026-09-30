import QuantumZipper.Proofs.Zipper.E4LimStep
import QuantumZipper.Proofs.Zipper.E4L3

/-!
# E4-LIM: E4 with collision before a cap `T₀ < T`, for continuous cylinder test functions

`handoff/E4.md`, item E4-LIM. For `Ψ = g(x, d.1(u_1..u_m), d.2(u_1..u_m))` and
`Φ = f(c_{I_1}, …, c_{I_{m'}})` with `g, f` continuous and `≤ 1` (`cylPsi`, `cylPhi`), and
`0 < T₀ < T`, `δ > 0`:

  `∫⁻ ω ∫⁻_{[−δ,0]} 1{τ_x ≤ T₀} Ψ(x, V^{τ_x}, W⁰) Φ(Y_{τ_x} − m) dν dP
     = ∫⁻ ω ∫⁻_{[−δ,0]} 1{τ_x ≤ T₀} Ψ(x, V^{τ_x}, W⁰) E'[Φ(targetColl κ V τ_x ϖ X')] dν dP`

(`e4_lim`), from E4-GRID (`e4_grid_cap`) by dominated convergence (`e4_lim_side`): `n → ∞`
(dyadic grid), then `ε = 1/(j+1) → 0`. Left side: REG-CONT (L2). Right side: the two explicit
hypotheses `hL3` (L3 of `handoff/E4.md`, the law of the target field as `s ↑ τ_x`; discharged in
`e4_cyl` by `E4Grid.tendsto_lintegral_targetField_coll`, `E4L3.lean`) and `hL3i` (right-continuity of the same law at live times `s < T₀`, needed for
the `n → ∞` step at fixed `ε`; not listed in the handoff).

`targetColl` (from `E4L3Terms`): the collision target field = `targetField` with the tip value
`F x` replaced by `0` (explicit; never through the junk value `realRevMap V τ_x x = 0`).

Own argument filling in the limiting step of Sheffield, arXiv:1012.4797, proof of Lemma 5.6
(pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

/-- Continuous cylinder test function of `(x, (V^t, W⁰))`. -/
def cylPsi {m : ℕ} (u : Fin m → ℝ≥0) (g : ℝ × (Fin m → ℝ) × (Fin m → ℝ) → ℝ≥0∞) :
    ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  fun x d => g (x, fun j => d.1 (u j), fun j => d.2 (u j))

/-- Continuous cylinder test function of the `coordsFull` coordinates. -/
def cylPhi {m : ℕ} (I : Fin m → ℕ) (f : (Fin m → ℝ) → ℝ≥0∞) : (ℕ → ℝ) → ℝ≥0∞ :=
  fun c => f (fun j => c (I j))

theorem measurable_cylPsi {m : ℕ} {u : Fin m → ℝ≥0} {g : ℝ × (Fin m → ℝ) × (Fin m → ℝ) → ℝ≥0∞}
    (hg : Continuous g) : Measurable (Function.uncurry (cylPsi u g)) :=
  hg.measurable.comp (measurable_fst.prodMk ((measurable_pi_iff.2 fun j =>
    (measurable_pi_apply (u j)).comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_iff.2 fun j =>
      (measurable_pi_apply (u j)).comp (measurable_snd.comp measurable_snd))))

theorem measurable_cylPhi {m : ℕ} {I : Fin m → ℕ} {f : (Fin m → ℝ) → ℝ≥0∞}
    (hf : Continuous f) : Measurable (cylPhi I f) :=
  hf.measurable.comp (measurable_pi_iff.2 fun j => measurable_pi_apply (I j))

theorem lintegral_le_one_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : α → ℝ≥0∞} (h : ∀ a, F a ≤ 1) : ∫⁻ a, F a ∂μ ≤ 1 :=
  (lintegral_mono h).trans_eq (by rw [lintegral_one, measure_univ])

/-- The left integrand of E4 on the event `A ω` (`τ = τ_x`). -/
def lhsInt {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (A : Ω → Set ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) (ω : Ω)
    (x : ℝ) : ℝ≥0∞ :=
  (A ω).indicator (fun x =>
    Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
      Φ (coordsFull (addConst (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω)
        (-(mReg κ T B X ϖ ω))))) x

/-- The right integrand of E4 on the event `A ω` (`τ = τ_x`). -/
def rhsInt {Ω Ω' : Type*} [MeasurableSpace Ω'] (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ϖ : Measure ℂ)
    (P' : Measure Ω') (X' : Ω' → FieldSample)
    (A : Ω → Set ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) (ω : Ω)
    (x : ℝ) : ℝ≥0∞ :=
  (A ω).indicator (fun x =>
    Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
      ∫⁻ ω', Φ (coordsFull (targetColl κ (Vr κ T B ω) (realHitTime (Vr κ T B ω) x).toReal ϖ
        (X' ω'))) ∂P') x

/-- Both integrands are a.e.-measurable, in `x` for a.e. `ω` and, after the `x`-integration,
in `ω` (bookkeeping for the monotone-class step). -/
def GoodPair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Ω → Measure ℝ) (S : Set ℝ)
    (F G : Ω → ℝ → ℝ≥0∞) : Prop :=
  AEMeasurable (fun ω => ∫⁻ x in S, F ω x ∂ν ω) P ∧ (∀ᵐ ω ∂P, AEMeasurable (F ω) ((ν ω).restrict S)) ∧
    AEMeasurable (fun ω => ∫⁻ x in S, G ω x ∂ν ω) P ∧ (∀ᵐ ω ∂P, AEMeasurable (G ω) ((ν ω).restrict S))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- Grid measurability, left side (as in `e4_grid_cap`). -/
theorem grid_meas_L (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T) (δ ε : ℝ) (n : ℕ)
    {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} {Φ : (ℕ → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    (∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω))))) ∧
    ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω) P := by
  have hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular
  have hν := NuMeas.aemeasurable_nuPalm hReg hκ hκ4 hT hB hX hind hϖ
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have htk : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, tk n k < T := fun k hk =>
    ((tk_lt_iff n k T₀).1 (Finset.mem_range.1 hk)).trans_le hT₀T
  have hD : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊,
      AEMeasurable (fun ω => (Vstop κ T (tk n k) B ω, W0p κ T B ω)) P := fun k hk =>
    (aemeasurable_data (κ := κ) hB hX hind (tk_nonneg n k) (htk k hk).le).snd
  refine ⟨Eventually.of_forall fun ω k _ => (measurable_PsiK hΨ).of_uncurry_right.mul_const _,
    fun k hk => ?_⟩
  refine (aemeasurable_setLIntegral_family hν hfin ((hD k hk).prodMk
    (aemeasurable_field (κ := κ) hB hX hind hϖ (tk_nonneg n k) (htk k hk)))
    (g := fun p => PsiK T₀ ε n k Ψ p.1 p.2.1 * Φ p.2.2) ?_).congr ?_
  · exact ((measurable_PsiK hΨ).comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).mul (hΦ.comp (measurable_snd.comp measurable_snd))
  · filter_upwards [hB.cont] with ω hc
    exact setLIntegral_congr_fun measurableSet_Icc fun x _ => (liveInd_eq hc hT.le hT₀.le k
      (fun _ => Φ (coordsFull (addConst (Yf κ T (tk n k) B X ω) (-(mReg κ T B X ϖ ω))))) x).symm

/-- Grid measurability, right side (as in `e4_grid_cap`, via E4-MEAS). -/
theorem grid_meas_R (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P')
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T) (δ ε : ℝ) (n : ℕ)
    {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} {Φ : (ℕ → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    (∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
        ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P') ∧
    ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) *
          ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) (tk n k) ϖ x (X' ω'))) ∂P') x
        ∂nuPalm κ T B X ϖ ω) P := by
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
  refine ⟨?_, fun k hk => ?_⟩
  · filter_upwards [hR] with ω h k _
    simp_rw [h k]
    exact (measurable_PsiK hΨ).of_uncurry_right.mul
      ((hHm k).comp (measurable_id.prodMk measurable_const))
  · refine (aemeasurable_setLIntegral_family hν hfin (hD k hk)
      (g := fun p => PsiK T₀ ε n k Ψ p.1 p.2 * H k p) ((measurable_PsiK hΨ).mul (hHm k))).congr ?_
    filter_upwards [hB.cont, hR] with ω hc h
    refine setLIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    rw [liveInd_eq hc hT.le hT₀.le k _ x, h k x]

/-- **E4-LIM.** E4 with collision before `T₀ < T`, for continuous cylinder test functions, given
L3 (`hL3`, law of the target field as `s ↑ τ_x`) and its interior form `hL3i`. -/
theorem e4_lim (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P')
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ < T) {δ : ℝ} (hδ : 0 < δ)
    {m : ℕ} {u : Fin m → ℝ≥0} {g : ℝ × (Fin m → ℝ) × (Fin m → ℝ) → ℝ≥0∞}
    (hg : Continuous g) (hg1 : ∀ p, g p ≤ 1)
    {m' : ℕ} {I : Fin m' → ℕ} {f : (Fin m' → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ c, f c ≤ 1)
    (hL3 : ∀ᵐ ω ∂P, ∀ x < 0, ∀ τ, realHitTime (Vr κ T B ω) x = ENNReal.ofReal τ → τ ≤ T₀ →
      Tendsto (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (𝓝[<] τ)
        (𝓝 (∫⁻ ω', cylPhi I f (coordsFull (targetColl κ (Vr κ T B ω) τ ϖ (X' ω'))) ∂P')))
    (hL3i : ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T₀ → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (Ici s) s) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, lhsInt κ T B X ϖ
        (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}) (cylPsi u g) (cylPhi I f)
        ω x ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, rhsInt κ T B ϖ P' X'
        (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}) (cylPsi u g) (cylPhi I f)
        ω x ∂nuPalm κ T B X ϖ ω ∂P ∧
    GoodPair P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0) (lhsInt κ T B X ϖ
        (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}) (cylPsi u g) (cylPhi I f))
      (rhsInt κ T B ϖ P' X'
        (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}) (cylPsi u g) (cylPhi I f))
      := by
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hεdef
  have hε0 : ∀ j, 0 < ε j := fun j => by positivity
  have hεt : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun j => hε0 j⟩
  have hΨm := measurable_cylPsi (u := u) hg
  have hΦm := measurable_cylPhi (I := I) hf
  have hΨ1 : ∀ x d, cylPsi u g x d ≤ 1 := fun x d => hg1 _
  have hΦ1 : ∀ c, cylPhi I f c ≤ 1 := fun c => hf1 _
  have hVω : ∀ᵐ ω ∂P, Continuous (Vr κ T B ω) ∧ Vr κ T B ω 0 = 0 := by
    filter_upwards [hB.cont] with ω hc
    exact ⟨continuous_vrev (drive_continuous hc) T, vrev_zero hT.le⟩
  have hΨc : ∀ᵐ ω ∂P, ∀ x, Continuous fun s =>
      cylPsi u g x (Vstop κ T s B ω, W0p κ T B ω) := by
    filter_upwards [hVω] with ω hV x
    exact hg.comp (continuous_const.prodMk ((continuous_pi fun j =>
      hV.1.comp (continuous_const.min continuous_id)).prodMk
        (continuous_const : Continuous fun _ : ℝ => fun j => W0p κ T B ω (u j))))
  have hτpos : ∀ᵐ ω ∂P, ∀ x < 0, ∀ τ, realHitTime (Vr κ T B ω) x = ENNReal.ofReal τ → 0 < τ := by
    filter_upwards [hVω] with ω hV x hx τ hτ
    have := RealLine.realHitTime_pos hV.1 (x := x) (by rw [hV.2]; exact hx.ne)
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  -- left side: continuity of the field coordinates (L2)
  have hcL : ∀ᵐ ω ∂P, ContinuousOn (fun s => cylPhi I f (coordsFull
      (addConst (Yf κ T s B X ω) (-(mReg κ T B X ϖ ω))))) (Icc 0 T) := by
    filter_upwards [ae_continuousOn_coordsFull_Yf (κ := κ) hB hX hind hT] with ω h
    refine hf.comp_continuousOn (continuousOn_pi.2 fun j => ?_)
    simp only [E1.coordsFull_addConst]
    exact (h (I j)).add continuousOn_const
  obtain ⟨hL1, hL2, hL3m, hL4m⟩ := e4_lim_side (P := P) hκ hκ4 hT hB hX hind hϖ hT₀ hδ hε0 hεt hΨ1 hΨc
    (Z := fun ω _ s => cylPhi I f (coordsFull
      (addConst (Yf κ T s B X ω) (-(mReg κ T B X ϖ ω)))))
    (Zc := fun ω x => cylPhi I f (coordsFull (addConst
      (Yf κ T (realHitTime (Vr κ T B ω) x).toReal B X ω) (-(mReg κ T B X ϖ ω)))))
    (fun _ _ _ => hΦ1 _) (fun _ _ => hΦ1 _)
    (fun j n => (grid_meas_L hκ hκ4 hT hB hX hind hϖ hT₀ hT₀T.le δ (ε j) n hΨm hΦm).1)
    (fun j n => (grid_meas_L hκ hκ4 hT hB hX hind hϖ hT₀ hT₀T.le δ (ε j) n hΨm hΦm).2)
    (by
      filter_upwards [hcL] with ω hc x _ s hs0 hsT _
      exact (hc s ⟨hs0, (hsT.trans hT₀T).le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE (hsT.trans hT₀T)) (Icc_subset_Icc_left hs0)))
    (by
      filter_upwards [hcL, hτpos] with ω hc hp x hx τ hτ hτT
      have h0 := hp x hx τ hτ
      simp only [hτ, ENNReal.toReal_ofReal h0.le]
      exact (hc τ ⟨h0.le, hτT.trans hT₀T.le⟩).tendsto.mono_left (nhdsWithin_le_of_mem
        (mem_of_superset (Ioo_mem_nhdsLT h0)
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right (hτT.trans hT₀T.le))))))
  obtain ⟨hR1, hR2, hR3m, hR4m⟩ := e4_lim_side (P := P) hκ hκ4 hT hB hX hind hϖ hT₀ hδ hε0 hεt hΨ1 hΨc
    (Z := fun ω x s => ∫⁻ ω', cylPhi I f (coordsFull
      (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P')
    (Zc := fun ω x => ∫⁻ ω', cylPhi I f (coordsFull (targetColl κ (Vr κ T B ω)
      (realHitTime (Vr κ T B ω) x).toReal ϖ (X' ω'))) ∂P')
    (fun _ _ _ => lintegral_le_one_of_le_one fun _ => hΦ1 _)
    (fun _ _ => lintegral_le_one_of_le_one fun _ => hΦ1 _)
    (fun j n => (grid_meas_R hκ hκ4 hT hB hX hind hϖ hX' hT₀ hT₀T.le δ (ε j) n hΨm hΦm).1)
    (fun j n => (grid_meas_R hκ hκ4 hT hB hX hind hϖ hX' hT₀ hT₀T.le δ (ε j) n hΨm hΦm).2)
    hL3i
    (by
      filter_upwards [hL3, hτpos] with ω h hp x hx τ hτ hτT
      simp only [hτ, ENNReal.toReal_ofReal (hp x hx τ hτ).le]
      exact h x hx τ hτ hτT)
  have heq := fun j => tendsto_nhds_unique (hL1 j) ((hR1 j).congr fun n =>
    (e4_grid_cap hκ hκ4 hT hB hX hind hϖ hX' hT₀ hT₀T.le δ (ε j) n hΨm hΦm).symm)
  exact ⟨tendsto_nhds_unique hL2 (hR2.congr fun j => (heq j).symm), hL3m, hL4m, hR3m, hR4m⟩

end E4Grid
end QuantumZipper
