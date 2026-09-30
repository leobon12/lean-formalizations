import QuantumZipper.Proofs.Zipper.E1Fixed2

/-!
# E1: the Palm-zip field clause (assembly, conditional on E1-TR)

`handoff/E1-PLAN.md`, node **E1**. From the transfer identity E1-TR (taken here as the hypothesis
`hTR`, exactly its conclusion for the given `δ, Ψ, Φ`), E1-FIX per `ω` (`lintegral_palm_liveNeg`
with the driver `v = Vr κ T B ω` and the auxiliary free field `(P, X)`), and the law swap of the
auxiliary free field to an arbitrary free field `X'` on `(Ω', P')`:

* `measurable_coordsFull_targetField`, `lintegral_targetField_eq`: the coordinates of
  `targetField κ v t ϖ x Y` are `a + (Y(fc_j) − Y(ϖ_t))_j` for a deterministic `a`, so their law
  under a free field does not depend on the field (`WedgeRes.map_gaussFam_eq₂`);
* `e1_main_of_tr`: the statement of E1 given E1-TR.

Paper: Sheffield, arXiv:1012.4797, Theorem 4.5 (p. 51) and Lemma 5.6 with its proof
(pp. 66–68). The assembly is own bookkeeping (Tonelli, law of a Gaussian family).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open PalmNorm B2 CoordsFull WedgeTK

section Law

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → FieldSample} {X' : Ω' → FieldSample}
  {κ t : ℝ} {v : ℝ → ℝ} {ϖ : Measure ℂ}

/-- The coordinates of `targetField κ v t ϖ x Y`: a deterministic shift plus the differences
`Y(fc_j) − Y(ϖ_t)`. -/
theorem coordsFull_targetField (x : ℝ) (Y : FieldSample) :
    coordsFull (targetField κ v t ϖ x Y) = fun j =>
      (ofFun (shiftFun (Real.sqrt κ) (h0rev κ) (varpiT v t ϖ) (realRevMap v t x))
          (foldedCircle (fullIndex j).1 (fullIndex j).2) -
        ofFun (shiftFun (Real.sqrt κ) (h0rev κ) (varpiT v t ϖ) (realRevMap v t x))
          (varpiT v t ϖ) - qt κ v t ϖ) +
      (Y (foldedCircle (fullIndex j).1 (fullIndex j).2) - Y (varpiT v t ϖ)) := by
  funext j
  simp only [coordsFull, targetField, normAt, addConst, Pi.add_apply, measure_univ,
    ENNReal.toReal_one, mul_one]
  ring

theorem measurable_coordsFull_targetField (hX : IsFreeGFFModConstH X P) (x : ℝ) :
    Measurable fun ω => coordsFull (targetField κ v t ϖ x (X ω)) := by
  simp_rw [coordsFull_targetField]
  exact measurable_pi_iff.2 fun j => measurable_const.add
    ((hX.measurable_coord _).sub (hX.measurable_coord _))

/-- **Law swap.** The integral of a functional of the coordinates of `targetField` does not
depend on the free field. -/
theorem lintegral_targetField_eq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hX : IsFreeGFFModConstH X P) (hX' : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ)
    (hv : Continuous v) (ht : 0 ≤ t) (x : ℝ) {Φ : (ℕ → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (coordsFull (targetField κ v t ϖ x (X ω))) ∂P =
      ∫⁻ ω', Φ (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P' := by
  set ϖ' := varpiT v t ϖ with hϖ'def
  have := hϖ.prob
  have hm := TwoPoint.measurable_revMap hv ht
  have : IsProbabilityMeasure ϖ' := by simp only [hϖ'def, varpiT]; infer_instance
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hfr⟩ := hϖ.frost
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hv ht hKc hKH hK0
  obtain ⟨C', hC'⟩ := B2.isFrostman_map_revMap_of_compact hv ht hKc hKH hK0 hα.le hfr
  have hadm : IsAdmissibleH ϖ' := FrostmanReg.isAdmissibleH_of_frostman hR hC' hα
  have hμ : ∀ j, IsAdmissibleH (foldedCircle (fullIndex j).1 (fullIndex j).2) := fun j => by
    rw [← CoordReg.foldedCircle_foldH]
    refine isAdmissibleH_foldedCircle (CircleFubini.foldH_mem_Hbar' _) ?_
    have key : ∀ p : ℤ × ℤ × ℕ × ℕ × ℕ, (0 : ℝ) < ((p.2.2.2.1 : ℝ) + 1) / (2 : ℝ) ^ p.2.2.2.2 :=
      fun p => by positivity
    exact key (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) j)
  set p : ℕ → BPair := fun j => ⟨(foldedCircle (fullIndex j).1 (fullIndex j).2, ϖ'),
    hμ j, hadm, by simp only [measure_univ]⟩ with hp
  set a : ℕ → ℝ := fun j =>
    ofFun (shiftFun (Real.sqrt κ) (h0rev κ) ϖ' (realRevMap v t x))
        (foldedCircle (fullIndex j).1 (fullIndex j).2) -
      ofFun (shiftFun (Real.sqrt κ) (h0rev κ) ϖ' (realRevMap v t x)) ϖ' - qt κ v t ϖ with ha
  set A : (ℕ → ℝ) → (ℕ → ℝ) := fun w j => a j + w j with hA
  have hAm : Measurable A := measurable_pi_iff.2 fun j => measurable_const.add
    (measurable_pi_apply j)
  have hrepX : (fun ω => coordsFull (targetField κ v t ϖ x (X ω))) =
      A ∘ fun ω j => gaussFam X p j ω := by
    funext ω; rw [coordsFull_targetField]; rfl
  have hrepX' : (fun ω => coordsFull (targetField κ v t ϖ x (X' ω))) =
      A ∘ fun ω j => gaussFam X' p j ω := by
    funext ω; rw [coordsFull_targetField]; rfl
  rw [← lintegral_map hΦ (measurable_coordsFull_targetField hX x),
    ← lintegral_map hΦ (measurable_coordsFull_targetField hX' x), hrepX, hrepX',
    ← Measure.map_map hAm (measurable_gaussFam_pi hX p),
    ← Measure.map_map hAm (measurable_gaussFam_pi hX' p), WedgeRes.map_gaussFam_eq₂ hX hX' p]

end Law

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E1, conditional on E1-TR** (`handoff/E1-PLAN.md`, node E1). Given the conclusion `hTR` of
E1-TR for `δ, Ψ, Φ`, the left side of E1-TR equals the Palm-zip right side, for any free field
`X'` on any probability space `(Ω', P')`. -/
theorem e1_main_of_tr {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X' : Ω' → FieldSample}
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hX' : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ)
    (δ : ℝ) {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} {Φ : (ℕ → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ)
    (hTR : ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (ofFun (h0rev κ) + X ω')
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) t (X ω'))
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))) (liveNeg (Vr κ T B ω) t) ∂P ∂P) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, (∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        ENNReal.ofReal (rhoT κ (Vr κ T B ω) t ϖ x) * Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          ∫⁻ ω', Φ (coordsFull (targetField κ (Vr κ T B ω) t ϖ x (X' ω'))) ∂P') x) ∂P := by
  rw [hTR]
  refine lintegral_congr_ae ?_
  filter_upwards [hB.cont] with ω hc
  have hv : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hv0 : Vr κ T B ω 0 = 0 := vrev_zero (ht.trans htT.le)
  set d := (Vstop κ T t B ω, W0p κ T B ω) with hd
  have hG : Measurable (Function.uncurry fun (x : ℝ) (c : ℕ → ℝ) => Ψ x d * Φ c) :=
    (hΨ.comp (measurable_fst.prodMk measurable_const)).mul (hΦ.comp measurable_snd)
  refine (lintegral_palm_liveNeg (P' := P) hκ hκ4 hX hϖ hv hv0 ht δ hG).trans ?_
  refine lintegral_congr fun x => congrArg (fun f => indicator _ f x) (funext fun y => ?_)
  show ENNReal.ofReal (rhoT κ (Vr κ T B ω) t ϖ y) *
      ∫⁻ ω', Ψ y d * Φ (coordsFull (targetField κ (Vr κ T B ω) t ϖ y (X ω'))) ∂P = _
  rw [lintegral_const_mul (Ψ y d)
      (f := fun ω' => Φ (coordsFull (targetField κ (Vr κ T B ω) t ϖ y (X ω'))))
      (hΦ.comp (measurable_coordsFull_targetField hX y)),
    lintegral_targetField_eq hX hX' hϖ hv ht y hΦ, mul_assoc]

end Main

end E1
end QuantumZipper
