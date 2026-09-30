import QuantumZipper.Proofs.Zipper.BaseFin2ULRad
import QuantumZipper.Proofs.Zipper.UnzipExpMom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL-C: the unzipped constant at `fc(0,1)` has exponential moments, uniformly in law

`bf2_unzipConstExpMom_lawUnif`: for `r ≥ 0` there is `K < ∞` such that for every gauge-pinned `Γ⁰` pair
(on any probability space) `exp(r · h⁰_1(fc(0,1)))` has an a.e.-measurable majorant `M` with
`∫ M ≤ K`. This is `RegUnif.unzipConstExpMomStmt_holds` (UnzipExpMom.lean) made uniform:
the same pointwise split `h⁰_1(fc(0,1)) = Z + D` (Gaussian part, conditionally on the driver, with
variance `O(log(1 + sup|B|))`; deterministic part `e^{√κ D} ≤ C (1 + sup|B|)²`), where the
Brownian running maximum is bounded by the oscillation, whose Gaussian tail
(`BMOsc.bmOsc_tail`) gives exponential moments with explicit constants (`ul_expMom_of_tail`),
using `(1 + x)^a ≤ e^{a x}`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont KolmD RegSample B2

/-- `(1 + ofReal O)^a ≤ ofReal (e^{a O})` for `O, a ≥ 0`. -/
theorem ulc_one_add_rpow_le {O a : ℝ} (hO : 0 ≤ O) (ha : 0 ≤ a) :
    (1 + ENNReal.ofReal O) ^ a ≤ ENNReal.ofReal (Real.exp (a * O)) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hO,
    ENNReal.ofReal_rpow_of_nonneg (by linarith) ha]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (1 + O) ^ a ≤ (Real.exp O) ^ a :=
        Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp O]) ha
    _ = Real.exp (a * O) := by rw [← Real.exp_mul, mul_comm]

/-- The explicit exponential-moment constant of the oscillation. -/
def ulcK (l : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp l) + ENNReal.ofReal (2 * Real.exp ((l + 1) ^ 2 / 2 + l)) *
    ∑' m : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ m

theorem ulcK_ne_top (l : ℝ) : ulcK l ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top BaseFin2.ul_geom_ne_top⟩

/-- **Uniform exponential moments of the unzipped constant at `fc(0,1)`, time `1`.** -/
theorem bf2_unzipConstExpMom_lawUnif {κ : ℝ} (hκ : 0 < κ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      (∀ ω, B1Full.nrm (X ω) = X ω) →
      ∃ M : Ω → ℝ≥0∞, AEMeasurable M P ∧ ∫⁻ ω, M ω ∂P ≤ K ∧
        ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (r * h0f κ 1 B X ω (foldedCircle 0 1))) ≤ M ω := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set a : ℝ := 2 * r / Real.sqrt κ with ha
  have ha0 : 0 ≤ a := by positivity
  set b : ℝ := 4 * (2 * r) ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  set K : ℝ := Real.exp (12 * (2 * r) ^ 2 * frostC 1 1 1) *
    (40 * Real.sqrt κ + 21) ^ (4 * (2 * r) ^ 2) with hK
  set Cd : ℝ≥0∞ := ENNReal.ofReal (detConst κ) ^ a with hCd
  have hCd' : Cd ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha0 ENNReal.ofReal_ne_top
  refine ⟨ENNReal.ofReal K * ulcK b + Cd * ulcK (2 * a),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ulcK_ne_top _),
      ENNReal.mul_ne_top hCd' (ulcK_ne_top _)⟩, ?_⟩
  intro Ω _ P _ B X hB hX hind hN
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hpre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hOm : Measurable (bmOsc B' 0 1) := measurable_bmOsc hB'm hB'c 0 1
  have hO0 : ∀ ω, 0 ≤ bmOsc B' 0 1 ω := fun ω =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have htail : ∀ a : ℝ, 0 < a → P {ω | a < bmOsc B' 0 1 ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / 2)) := fun a ha => by
    have := BMOsc.bmOsc_tail hpre hB'm hB'c 0 1 one_pos ha
    simpa using this
  -- `bmSup B ≤ osc` a.s.
  have hsup : ∀ᵐ ω ∂P, bmSup B ω ≤ ENNReal.ofReal (bmOsc B' 0 1 ω) := by
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω heq h0
    have hbdd : BddAbove (range fun x : Icc (0 : ℝ≥0) (0 + 1) => |B' x ω - B' 0 ω|) := by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := 0 + 1)).image
        (f := fun r => |B' r ω - B' 0 ω|) (by have := hB'c ω; fun_prop) |>.bddAbove
      exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC ⟨x, x.2, rfl⟩⟩
    refine iSup₂_le fun s hs' => ENNReal.ofReal_le_ofReal ?_
    have hmem : s.toNNReal ∈ Icc (0 : ℝ≥0) (0 + 1) :=
      ⟨s.toNNReal.2, by rw [zero_add]; exact Real.toNNReal_le_one.2 hs'.2⟩
    have h1 : |B' s.toNNReal ω - B' 0 ω| ≤ bmOsc B' 0 1 ω := by
      rw [bmOsc_eq_iSup_subtype (hB'c ω)]
      exact le_ciSup hbdd ⟨s.toNNReal, hmem⟩
    have hB0 : B' 0 ω = 0 := by rw [heq 0]; exact h0
    rw [hB0, sub_zero, heq] at h1
    exact h1
  have hmomO : ∀ l : ℝ, 0 ≤ l →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * bmOsc B' 0 1 ω)) ∂P ≤ ulcK l := fun l hl =>
    BaseFin2.ul_expMom_of_tail hOm htail hl
  have hsupPow : ∀ c : ℝ, 0 ≤ c → ∀ᵐ ω ∂P,
      (1 + bmSup B ω) ^ c ≤ ENNReal.ofReal (Real.exp (c * bmOsc B' 0 1 ω)) := fun c hc => by
    filter_upwards [hsup] with ω h
    exact (ENNReal.rpow_le_rpow (add_le_add le_rfl h) hc).trans
      (ulc_one_add_rpow_le (hO0 ω) hc)
  -- the pieces of `unzipConstExpMomStmt_holds` at `t = 1`
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC 1 B' hB'c) X P :=
    indepFun_pathC 1 (hind.congr hpath (ae_eq_refl _)) hB'c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hN0 : ∀ ω, X ω (foldedCircle 0 1) = 0 := fun ω => by
    have h := congrFun (hN ω) (foldedCircle 0 1)
    simp only [B1Full.nrm, addConst, measure_univ, ENNReal.toReal_one, mul_one] at h
    linarith
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp : ((1 : ℝ), ((0 : ℂ), (1 : ℝ))) ∈ parSet 1 :=
    ⟨ht, show (0 : ℝ) ≤ (0 : ℂ).im by simp, show (0 : ℝ) < 1 from one_pos⟩
  set q := pr4 ((1 : ℝ), ((0 : ℂ), (1 : ℝ))) with hq
  set Z : Ω → ℝ := fun ω => ZE zero_le_one κ (pathC 1 B' hB'c ω, X ω) q with hZ
  have hraw := ae_raw_eq κ (Real.sqrt κ) hB hX (T := 1)
    (Zr := fun q ω => ZE zero_le_one κ (pathC 1 B' hB'c ω, X ω) q)
    (fun q => ae_tendsto_ZE κ hB hX hB'm hB'c hB'eq hind' one_pos q) hp
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (r * h0f κ 1 B X ω (foldedCircle 0 1))) ≤
      ENNReal.ofReal (Real.exp (2 * r * Z ω)) + Cd * (1 + bmSup B ω) ^ (2 * a) := by
    filter_upwards [hraw, ae_drive_good hB κ] with ω hω hd
    set D := Ddet κ (Real.sqrt κ) (drive κ B ω) ((1 : ℝ), ((0 : ℂ), (1 : ℝ))) with hDdef
    have e1 : h0f κ 1 B X ω (foldedCircle 0 1) = Z ω + D := by
      rw [B2.h0f_eq_unzippedField]; exact hω
    rw [e1, show r * (Z ω + D) = (2 * r) / 2 * (Z ω + D) by ring]
    refine (ofReal_exp_half_add_le (2 * r) _ _).trans (add_le_add le_rfl ?_)
    have hD := ofReal_exp_Ddet_le hκ hd ht (t := 0) (by norm_num)
    rw [Complex.ofReal_zero] at hD
    have e3 : ENNReal.ofReal (Real.exp (2 * r * D)) =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * D)) ^ a := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha0, ← Real.exp_mul]
      congr 2
      rw [ha, mul_div_assoc', eq_div_iff hs.ne']
      ring
    rw [e3]
    calc _ ≤ (ENNReal.ofReal (detConst κ) * (1 + bmSup B ω) ^ (2 : ℝ)) ^ a :=
          ENNReal.rpow_le_rpow hD ha0
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ ha0, ← ENNReal.rpow_mul]
  have hF : Measurable fun p : C(Icc (0 : ℝ) 1, ℝ) × FieldSample =>
      ENNReal.ofReal (Real.exp (2 * r * ZE zero_le_one κ p q)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_ZE _ κ q)))
  have hsplit : ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * r * Z ω)) ∂P =
      ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (Real.exp
        (2 * r * ZE zero_le_one κ (pathC 1 B' hB'c ω, X ω') q)) ∂P ∂P :=
    unzipExpMom_lintegral_indep (measurable_pathC 1 hB'm hB'c) hXm hind' hF
  have hgauss : ∀ᵐ ω ∂P, ∫⁻ ω', ENNReal.ofReal (Real.exp
      (2 * r * ZE zero_le_one κ (pathC 1 B' hB'c ω, X ω') q)) ∂P ≤
        ENNReal.ofReal K * (1 + bmSup B ω) ^ b := by
    filter_upwards [ae_pathC_good hB hB'c hB'eq one_pos, hB'eq] with ω hgood heq
    obtain ⟨hfin, hW⟩ := unzipExpMom_Wof_pathC_le κ hB'c heq
    refine (unzipExpMom_fixed_le hX hN0 κ ht (2 * r) hgood hW).trans ?_
    have h := unzipExpMom_exp_varC_le hs.le (ENNReal.toReal_nonneg (a := bmSup B ω)) (2 * r)
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hfin]
  have hZm : Measurable fun ω => ENNReal.ofReal (Real.exp (2 * r * Z ω)) :=
    hF.comp ((measurable_pathC 1 hB'm hB'c).prodMk hXm)
  have hEm : Measurable fun ω => ENNReal.ofReal (Real.exp (2 * a * bmOsc B' 0 1 ω)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hOm.const_mul _))
  refine ⟨fun ω => ENNReal.ofReal (Real.exp (2 * r * Z ω)) +
      Cd * ENNReal.ofReal (Real.exp (2 * a * bmOsc B' 0 1 ω)),
    (hZm.add (hEm.const_mul _)).aemeasurable, ?_, ?_⟩
  · rw [lintegral_add_left hZm, lintegral_const_mul' _ _ hCd']
    refine add_le_add ?_ (mul_le_mul' le_rfl (hmomO _ (by positivity)))
    rw [hsplit]
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal K * (1 + bmSup B ω) ^ b ∂P := lintegral_mono_ae hgauss
      _ ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (Real.exp (b * bmOsc B' 0 1 ω)) ∂P :=
          lintegral_mono_ae ((hsupPow b hb0).mono fun ω h => mul_le_mul' le_rfl h)
      _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (Real.exp (b * bmOsc B' 0 1 ω)) ∂P :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (hOm.const_mul _)))
      _ ≤ ENNReal.ofReal K * ulcK b := mul_le_mul' le_rfl (hmomO b hb0)
  · filter_upwards [hpt, hsupPow (2 * a) (by positivity)] with ω h1 h2
    exact h1.trans (add_le_add le_rfl (mul_le_mul' le_rfl h2))

end RegUnif

namespace BaseFin2

/-- **`BaseULConstStmt` holds** (normalizer `ulNorm = fc(0,1)`). -/
theorem baseULConstStmt_holds : BaseULConstStmt := by
  intro κ hκ _
  obtain ⟨K, hK, h⟩ := RegUnif.bf2_unzipConstExpMom_lawUnif hκ (r := 1) zero_le_one
  refine ⟨1, one_pos, K, hK, fun P _ B X hB hX hind hN => ?_⟩
  obtain ⟨M, hM, hMi, hMd⟩ := h P B X hB hX hind hN
  exact ⟨M, hM, hMi, by simpa [ulConst, ulNorm] using hMd⟩

end BaseFin2
end QuantumZipper
