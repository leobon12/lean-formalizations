import QuantumZipper.Proofs.Zipper.E4Meas

/-!
# E1-NU: the Palm-zip field clause with both sides integrated against `ν`

`handoff/E-PLAN-2.md`, node E1-NU. Conditional on E1-TR (hypothesis `hTR : E1TRHolds …`, the
conclusion of E1-TR for all measurable `Ψ, Φ`, exactly as `E1.e1_main_of_tr` takes it for one pair):

`e1_nu_of_tr`: for measurable `Ψ, Φ` and any free field `X'` on `(Ω', P')`,
`E ∫_{[−δ,0]} 1_{live} Ψ(x, V^t, W⁰) Φ(coords (Y_t − m)) dν
   = E ∫_{[−δ,0]} 1_{live} Ψ(x, V^t, W⁰) E'[Φ(coords (targetField … x X'))] dν`.

Proof (Sheffield arXiv:1012.4797, Lemma 5.6, pp. 66–68: the conditional law of the field given
the Palm point is read off the Palm formula; here "E1 twice"): by E1 both sides equal the same
Lebesgue integral `E ∫ 1_{live} ρ_t Ψ H dx`, where `H(x, V^t, W⁰)` is the measurable version of the
inner expectation (E4-MEAS, `E4Meas.e4_meas`); for the right side apply E1 to `Ψ' = Ψ·H`, `Φ' = 1`.
Own bookkeeping.

* `realRevMap_congr_drive`, `targetField_congr_drive`: `targetField κ v t ϖ x` depends on `v` only
  on `[0,t]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1Nu

open B2 E1 CoordsFull PalmNorm

theorem realRevMap_congr_drive {v v' : ℝ → ℝ} {t : ℝ} (h : EqOn v v' (Icc 0 t)) (x : ℝ) :
    realRevMap v t x = realRevMap v' t x := by
  have hP : IsRealRevSol v x t = IsRealRevSol v' x t :=
    funext fun u => propext (isRealRevSol_congr_drive h)
  unfold realRevMap
  rw [hP]

theorem targetField_congr_drive (κ : ℝ) {v v' : ℝ → ℝ} {t : ℝ} (h : EqOn v v' (Icc 0 t))
    (ϖ : Measure ℂ) (x : ℝ) (Y : FieldSample) :
    targetField κ v t ϖ x Y = targetField κ v' t ϖ x Y := by
  have hrev : revMap v t = revMap v' t := funext fun z => ReverseFlow.revMap_congr_drive z h
  simp only [targetField, varpiT, qt, hrev, realRevMap_congr_drive h x]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- The conclusion of E1-TR (`handoff/E1-PLAN.md`) for all measurable `Ψ, Φ`. -/
def E1TRHolds (κ T t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (ϖ : Measure ℂ) (δ : ℝ) : Prop :=
  ∀ (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞),
    Measurable (Function.uncurry Ψ) → Measurable Φ →
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (ofFun (h0rev κ) + X ω')
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) t (X ω'))
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))) (liveNeg (Vr κ T B ω) t) ∂P ∂P

/-- On `[0,t]` the reversed driver is the driver read off `V^t`. -/
theorem eqOn_Vr_stopDrive (ω : Ω) :
    EqOn (Vr κ T B ω) (stopDrive (Vstop κ T t B ω, W0p κ T B ω)) (Icc 0 t) := fun s hs => by
  simp only [stopDrive, Vstop, Real.coe_toNNReal _ hs.1, min_eq_left hs.2]

/-- **E1-NU, conditional on E1-TR.** -/
theorem e1_nu_of_tr {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X' : Ω' → FieldSample}
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hX' : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ)
    (δ : ℝ) (hTR : E1TRHolds κ T t P B X ϖ δ) {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    {Φ : (ℕ → ℝ) → ℝ≥0∞} (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) t ϖ x (X' ω'))) ∂P') x
        ∂nuPalm κ T B X ϖ ω ∂P := by
  obtain ⟨H, hHm, hH⟩ := E4Meas.e4_meas ht κ ϖ hϖ hX' hΦ
  set Ψ' : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun x d => Ψ x d * H (x, d) with hΨ'
  have hΨ'm : Measurable (Function.uncurry Ψ') := hΨ.mul hHm
  have h1c : Measurable fun _ : ℕ → ℝ => (1 : ℝ≥0∞) := measurable_const
  have h1 := e1_main_of_tr (P' := P') (X' := X') hκ hκ4 ht htT hB hX hX' hϖ δ hΨ hΦ
    (hTR Ψ Φ hΨ hΦ)
  have h2 := e1_main_of_tr (P' := P') (X' := X') hκ hκ4 ht htT hB hX hX' hϖ δ hΨ'm h1c
    (hTR Ψ' _ hΨ'm h1c)
  -- the inner expectation is `H` on live points
  have key : ∀ᵐ ω ∂P, ∀ x, IsLive (Vr κ T B ω) t x →
      ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) t ϖ x (X' ω'))) ∂P' =
        H (x, (Vstop κ T t B ω, W0p κ T B ω)) := by
    filter_upwards [hB.cont] with ω hc x hx
    have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
    have hS : Continuous (stopDrive (Vstop κ T t B ω, W0p κ T B ω)) := by
      unfold stopDrive Vstop
      exact hV.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).min continuous_const)
    have hD1 : Continuous (Vstop κ T t B ω) :=
      hV.comp (NNReal.continuous_coe.min continuous_const)
    have heq := eqOn_Vr_stopDrive (κ := κ) (T := T) (t := t) (B := B) ω
    rw [hH x _ hD1 ((isLive_congr_drive hV hS ht heq).1 hx)]
    exact lintegral_congr fun ω' => by rw [targetField_congr_drive κ heq]
  rw [h1]
  calc _ = ∫⁻ ω, (∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        ENNReal.ofReal (rhoT κ (Vr κ T B ω) t ϖ x) * Ψ' x (Vstop κ T t B ω, W0p κ T B ω) *
          ∫⁻ ω', (fun _ : ℕ → ℝ => (1 : ℝ≥0∞))
            (coordsFull (targetField κ (Vr κ T B ω) t ϖ x (X' ω'))) ∂P') x) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [key] with ω hω
        refine lintegral_congr fun x => ?_
        refine congrFun (indicator_congr fun x hx => ?_) x
        simp only [hΨ', lintegral_const, measure_univ, mul_one, hω x hx, mul_assoc]
    _ = _ := h2.symm
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [key] with ω hω
        refine lintegral_congr fun x => ?_
        refine congrFun (indicator_congr fun x hx => ?_) x
        simp only [hΨ', mul_one, hω x hx]

end E1Nu
end QuantumZipper
