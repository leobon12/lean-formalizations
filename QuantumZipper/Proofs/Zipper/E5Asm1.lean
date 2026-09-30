import QuantumZipper.Proofs.Zipper.E5HW0Ver
import QuantumZipper.Proofs.Zipper.E5Palm2Good
import QuantumZipper.Proofs.Zipper.E5Palm2Read
import QuantumZipper.Proofs.Zipper.E5IncField

/-!
# E5-ASM, part 1: the E-SM model package without `hw0`, and the model integrand

Task E5-ASM (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of
Lemma 5.6).

* `e5_esm_model_good`: `E5.e5_esm_model` with `hw0` discharged (`measurable_w0_level_good`), for a
  continuous version of `B` that is good at every sample (`exists_goodVersion`).
* `measurable_drvMap_esmGerm`: the germ driver `(z, u) ↦ drvMap κ (esmGerm z.1) u` is jointly
  measurable.
* **`measurable_modelInt_of_coords`**: the level-space model integrand
  `z ↦ Γ (locRich R (zcfgTL … C z))` of `e5_esm_model` is measurable, given
  (a) `X' ω' + α(−log|·|)` is `IsLQGGood (√κ)` at **every** `ω'` and
  (b) joint measurability of `coordsFull` of the collision target field at the level point
  (collision time `T − T_ℓ`, `palmTau_xL_eq_of`).
  With (a), the target field is good at every point (`isLQGGood_targetColl`: `k_{ϖ_τ}` is
  continuous for every continuous `V`, `continuous_kPot_varpiT`), so `canonical` reads only the
  circle coordinates (`locG_canonConfig_addConst_eq`), a measurable function of `coordsFull`.
* `measurable_coords_target_of_level`: input (b) with the collision time replaced by the
  measurable level time `T − T_ℓ`.
* `exists_base_regField_good`: input (a) for `X' = regField ϖ ρ₀ ∘ X₁`, `X₁` a modification of
  the base free field `X₀` on a null set (again a free field).

Remaining for the model integrand: input (b), i.e. joint measurability in `(ℓ, ω, ω')` of
`coordsFull (targetColl κ (Vr κ T B ω) (T − T_ℓ) ϖ (X' ω'))` — the value of `X'` at the random
measure `ϖ_{T−T_ℓ}` (`measurable_regField_varpiT_prod`, which needs measurability of
`z ↦ varpiT … A`), the circle averages of `k_{ϖ_{T−T_ℓ}}`, and `q_{T−T_ℓ}`; all three need joint
measurability of `(ω, t, u) ↦ revMap (Vr κ T B ω) t u` (and of its derivative).

Own elementary measure-theoretic bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 CoordsFull E4Grid

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

omit [IsProbabilityMeasure P'] in
/-- The germ driver is jointly measurable in (level point, time). -/
theorem measurable_drvMap_esmGerm (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω') × ℝ =>
      drvMap κ (esmGerm κ T B X P p.1.1) p.2 := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  have hG := measurable_esmGerm hκ hκ4 hT hB hX hind hBc
  have hU : Measurable fun p : ℝ≥0 × (ℝ≥0 × NullMeasurableSpace Ω P) =>
      esmGerm κ T B X P p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (s : ℝ≥0) (q : ℝ≥0 × NullMeasurableSpace Ω P) => esmGerm κ T B X P q s)
      (fun q => continuous_esmGerm hBc q) (fun s => (measurable_pi_apply s).comp hG)
  have hpair : Measurable fun p : ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω') × ℝ =>
      ((p.2.toNNReal, p.1.1) : ℝ≥0 × (ℝ≥0 × NullMeasurableSpace Ω P)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst)
  have h2 : Measurable fun p : ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω') × ℝ =>
      esmGerm κ T B X P p.1.1 p.2.toNNReal :=
    Measurable.comp
      (g := fun p : ℝ≥0 × (ℝ≥0 × NullMeasurableSpace Ω P) => esmGerm κ T B X P p.2 p.1)
      (f := fun p : ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω') × ℝ =>
        ((p.2.toNNReal, p.1.1) : ℝ≥0 × (ℝ≥0 × NullMeasurableSpace Ω P))) hU hpair
  show Measurable fun p : ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω') × ℝ =>
    Real.sqrt κ * esmGerm κ T B X P p.1.1 p.2.toNNReal
  exact h2.const_mul _

/-- **The level-space model integrand is measurable**, given goodness of `X' + α(−log)` at every
sample and joint measurability of the circle coordinates of the collision target field. -/
theorem measurable_modelInt_of_coords (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω))
    (hX'g : ∀ ω', IsLQGGood (Real.sqrt κ)
      (X' ω' + ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖))
    (hcm : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (palmTau κ T B (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2))) ϖ (X' z.2)))
    (R : ℕ) (C : ℝ) {Γ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hΓ : Measurable Γ) :
    Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      Γ (locG D3Plus.locFieldFull R (zcfgTL κ T B X P ϖ X' C z)) := by
  have hϖ := hS.2.2.2.2.2.2
  set γ := Real.sqrt κ
  set c := C / Real.sqrt κ
  set y : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' → ℕ → ℝ := fun z =>
    coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
      (palmTau κ T B (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2))) ϖ (X' z.2)) with hy
  set F : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' → ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
    fun z => (D3Plus.locFieldFull R (rdField γ c (y z)),
      fun s : ℝ≥0 => drvMap κ (esmGerm κ T B X P z.1) (rdScale γ c (y z) ^ 2 *
        max (min (s : ℝ) R) 0) / rdScale γ c (y z)) with hF
  have heq : (fun z => Γ (locG D3Plus.locFieldFull R (zcfgTL κ T B X P ϖ X' C z))) =
      fun z => Γ (F z) := by
    funext z
    have hk := continuous_kPot_varpiT hϖ (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P z.1.2))) (ENNReal.toReal_nonneg
        (a := realHitTime (Vr κ T B (ofCompl P z.1.2)) (xL κ T B X z.1.1 (ofCompl P z.1.2))))
    have hgood := (isLQGGood_targetColl hk (hX'g z.2)).addConst c
    have h := locG_canonConfig_addConst_eq hgood R
      (d := drvMap κ (esmGerm κ T B X P z.1)) (D := drvMap κ (esmGerm κ T B X P z.1))
      (fun _ _ => rfl)
    exact congrArg Γ h
  rw [heq]
  refine hΓ.comp (Measurable.prodMk ?_ (measurable_pi_iff.2 fun s => ?_))
  · exact (measurable_locOfData R).comp ((WedgeMeas.measurable_dataFull_resc H (Qc γ)).comp
      ((measurable_rdCoords c).prodMk (measurable_rdScale γ c))) |>.comp hcm
  · have ha : Measurable fun z => rdScale γ c (y z) := (measurable_rdScale γ c).comp hcm
    have hD := measurable_drvMap_esmGerm (Ω' := Ω') hS hBc
    exact (hD.comp (measurable_id.prodMk ((ha.pow_const 2).mul measurable_const))).div ha

/-- The coordinate input of `measurable_modelInt_of_coords` with the collision time written as
the level time `T − T_ℓ` (`palmTau_xL_eq_of`), for a version good at every sample. -/
theorem measurable_coords_target_of_level (hBc : ∀ ω, Continuous (B · ω)) (hT : 0 < T)
    (hG : ∀ ω, GoodVr κ T (Vr κ T B ω))
    (hcm : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1.1 (ofCompl P z.1.2) : ℝ≥0) : ℝ)) ϖ
          (X' z.2))) :
    Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (palmTau κ T B (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2))) ϖ (X' z.2)) := by
  have e : (fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (palmTau κ T B (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2))) ϖ (X' z.2))) =
      fun z => coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1.1 (ofCompl P z.1.2) : ℝ≥0) : ℝ)) ϖ
          (X' z.2)) := by
    funext z
    rw [palmTau_xL_eq_of hT (hBc (ofCompl P z.1.2)) (hG (ofCompl P z.1.2)).1
      (hG (ofCompl P z.1.2)).2 z.1.1]
  rw [e]; exact hcm

omit [IsProbabilityMeasure P'] in
/-- **A base field whose regular version is good at every sample.** Given a free field `X₀`, a
modification `X₁` (equal to `X₀` a.s., again a free field) such that
`regField ϖ ρ₀ (X₁ ω') + α(−log|·|)` is `IsLQGGood (√κ)` at **every** `ω'` (it is a.s. by the
log-singularity goodness `LogSingGood.logSingGoodAS_holds`; redefine `X₀` on the measurable null
bad set by one good sample). This supplies `hX'g` of `measurable_modelInt_of_coords` for
`X' = regField ϖ ρ₀ ∘ X₁`. -/
theorem exists_base_regField_good [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    {X₀ : Ω' → FieldSample} (hX₀ : IsFreeGFFModConstH X₀ P') (hϖ : IsNormalizer ϖ)
    {ρ₀ : Measure ℂ} (hρ₀ : IsAdmissibleH ρ₀) :
    ∃ X₁ : Ω' → FieldSample, IsFreeGFFModConstH X₁ P' ∧ (∀ᵐ ω' ∂P', X₁ ω' = X₀ ω') ∧
      ∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
        ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖) := by
  classical
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by linarith)
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := by
    unfold Qc
    have h : 1 < 2 / Real.sqrt κ := (one_lt_div hγ).2 hγ2
    linarith
  set f : FieldSample := ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖
  have hY := isFreeGFFModConstH_regField hX₀ hϖ hρ₀
  have hLS := LogSingGood.logSingGoodAS_holds hγ hγ2 hα Ω' _ P'
    (fun ω' => regField ϖ ρ₀ (X₀ ω')) inferInstance hY
  have hYm : Measurable fun ω' => regField ϖ ρ₀ (X₀ ω') + f :=
    measurable_pi_iff.2 fun μ => by
      simp only [Pi.add_apply]
      exact (measurable_regField_coord hX₀.measurable_coord ϖ ρ₀ μ).add measurable_const
  set G : Set Ω' := {ω' | IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₀ ω') + f)} with hGdef
  have hGm : MeasurableSet G := (GoodMeas.measurableSet_isLQGGood _).preimage hYm
  have hGae : ∀ᵐ ω' ∂P', ω' ∈ G := hLS
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, ω₀ ∈ G := by
    by_contra h
    push Not at h
    have h0 : ∀ᵐ ω' ∂P', False := hGae.mono fun ω' hω' => h ω' hω'
    rw [ae_iff] at h0
    simp at h0
  set X₁ : Ω' → FieldSample := fun ω' => if ω' ∈ G then X₀ ω' else X₀ ω₀ with hX₁def
  have hX₁m : ∀ μ, Measurable fun ω' => X₁ ω' μ := fun μ => by
    have e : (fun ω' => X₁ ω' μ) = fun ω' => if ω' ∈ G then X₀ ω' μ else X₀ ω₀ μ := by
      funext ω'; simp only [hX₁def]; split_ifs <;> rfl
    rw [e]
    exact Measurable.ite hGm (hX₀.measurable_coord μ) measurable_const
  have hae : ∀ᵐ ω' ∂P', X₁ ω' = X₀ ω' := hGae.mono fun ω' h => by simp only [hX₁def, if_pos h]
  refine ⟨X₁, isFreeGFFModConstH_of_ae_shift hX₀ 0 hX₁m fun μ _ => hae.mono fun ω' h => by
    simp [h], hae, fun ω' => ?_⟩
  by_cases h : ω' ∈ G
  · simp only [hX₁def, if_pos h]; exact h
  · simp only [hX₁def, if_neg h]; exact hω₀

end E5
end QuantumZipper
