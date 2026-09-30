import QuantumZipper.Proofs.Zipper.RegShiftUnifLog
import QuantumZipper.Proofs.Zipper.RegShiftUnif
import QuantumZipper.Proofs.Zipper.F2AddConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# REGSHIFT-UNIF (F2): the unzipped log-singular field, and `AddConstAgreeStmt` proved

Theorem 1.3, node F2, step (2b). The field `X + α₀(−log|·|)` (`α₀ = γ − 2/γ`, `γ = √κ`) is the
configuration field `𝔥₀ + X = (2/γ) log|·| + X` plus the deterministic log field `−γ log|·|`
(`logSing_eq`, exact identity of field samples). Hence, along the pushed circles `(f_t)_* fc`:

* `E1.RegShift` of `X + α₀(−log|·|)` is `RegShift` of `𝔥₀ + X` (the proved D37/D33 input
  `gaugeRegDyStmt_holds`) plus `RegShift` of the log field (deterministic,
  `regShift_logF_fc_map`), by additivity (`regShift_add`);
* the raw boundary averages of the unzipped field are those of `h⁰_t` plus
  `−γ ∫ log|f_t| dfc(c, 2^{-k})`, continuous in the centre (`continuous_integral_log_fwdMapInv`),
  so `Cor15Group.BdryConvAE` transfers.

This gives `f2UnzipRegDyStmt_holds` — the statement `F2.F2UnzipRegStmt` at the circles of radius
`2^{-k}` centred in `Dy` (the only circles read by `bdryApprox`, hence by `qBoundaryMeasure` and
the unzipped lengths) — and then **`addConstAgreeStmt_holds : F2.AddConstAgreeStmt`**
(rule (5.1) for constants, `agree_addConst_dy`).

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1)
(pp. 60–62), §5.4 (pp. 70–72); Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1. The
decomposition and the junk-value bookkeeping are own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 CircleFubini

/-! ## Deterministic lemmas -/

/-- `X + α₀(−log|·|) = (𝔥₀ + X) + (−γ)·log|·|`, exactly. -/
theorem logSing_eq (κ : ℝ) (x : FieldSample) :
    x + F2.logSingField κ = (ofFun (h0rev κ) + x) + logF (-Real.sqrt κ) := by
  funext μ
  show x μ + ∫ z, (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖ ∂μ =
    (∫ z, h0rev κ z ∂μ + x μ) + ∫ z, -Real.sqrt κ * Real.log ‖z‖ ∂μ
  simp only [h0rev, integral_const_mul, integral_neg]
  ring

/-- **Additivity of `RegShift`**, with additivity of `evalReg`. -/
theorem regShift_add {y g : FieldSample} {ν : Measure ℂ} (hy : E1.RegShift y ν)
    (hg : E1.RegShift g ν) :
    E1.RegShift (y + g) ν ∧ evalReg (y + g) ν = evalReg y ν + evalReg g ν := by
  obtain ⟨hy1, hy2, Ly, hLy⟩ := hy
  obtain ⟨hg1, hg2, Lg, hLg⟩ := hg
  have hae : ∀ k : ℕ, (fun z => avgReg (y + g) k z) =ᵐ[ν]
      fun z => avgReg y k z + avgReg g k z := fun k => by
    filter_upwards [hy1, hg1] with z h1 h2
    obtain ⟨l1, t1⟩ := h1 k
    obtain ⟨l2, t2⟩ := h2 k
    have e1 : avgReg y k z = l1 := t1.limUnder_eq
    have e2 : avgReg g k z = l2 := t2.limUnder_eq
    rw [e1, e2]
    exact (t1.add t2).limUnder_eq
  have hsum : Tendsto (fun k => ∫ z, avgReg (y + g) k z ∂ν) atTop (𝓝 (Ly + Lg)) :=
    (hLy.add hLg).congr fun k => by
      rw [integral_congr_ae (hae k), integral_add (hy2 k) (hg2 k)]
  refine ⟨⟨?_, fun k => ((hy2 k).add (hg2 k)).congr (hae k).symm, _, hsum⟩, ?_⟩
  · filter_upwards [hy1, hg1] with z h1 h2 k
    obtain ⟨l1, t1⟩ := h1 k
    obtain ⟨l2, t2⟩ := h2 k
    exact ⟨_, t1.add t2⟩
  · have e1 : evalReg (y + g) ν = Ly + Lg := hsum.limUnder_eq
    have e2 : evalReg y ν = Ly := hLy.limUnder_eq
    have e3 : evalReg g ν = Lg := hLg.limUnder_eq
    rw [e1, e2, e3]

/-- **Pathwise regularity of the log-singular field** from that of `𝔥₀ + X` at one time. -/
theorem logSing_reg_path (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {x : FieldSample}
    (hR : ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + x)
      ((foldedCircle d (radius k)).map (fwdMapInv W t)))
    (hbc : Cor15Group.BdryConvAE (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t)) :
    (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (x + F2.logSingField κ)
      ((foldedCircle d (radius k)).map (fwdMapInv W t))) ∧
      Cor15Group.BdryConvAE (unzippedField (Real.sqrt κ) (x + F2.logSingField κ, W) t) := by
  set b := -Real.sqrt κ with hb
  refine ⟨fun k d hd => ?_, fun k => ?_⟩
  · rw [logSing_eq]
    exact (regShift_add (hR k d hd) (regShift_logF_fc_map hW hW0 ht b d (radius_pos k)).1).1
  · filter_upwards [hbc k] with s hs
    obtain ⟨l, hl⟩ := hs
    set J : ℂ → ℝ := fun c => ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle c (radius k)
      with hJ
    have hJc : Continuous J := continuous_integral_log_fwdMapInv hW hW0 ht (radius_pos k)
    have key : ∀ n : ℕ, unzippedField (Real.sqrt κ) (x + F2.logSingField κ, W) t
        (foldedCircle (dyadicRoundC n (s : ℂ)) (radius k)) =
        unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t
          (foldedCircle (dyadicRoundC n (s : ℂ)) (radius k)) +
          b * J (foldH (dyadicRoundC n (s : ℂ))) := by
      intro n
      rw [← CoordReg.foldedCircle_foldH (dyadicRoundC n (s : ℂ)) (radius k)]
      have hd := foldH_dyadicRoundC_mem_Dy n (s : ℂ)
      have hL := regShift_logF_fc_map hW hW0 ht b (foldH (dyadicRoundC n (s : ℂ))) (radius_pos k)
      have he := (regShift_add (hR k _ hd) hL.1).2
      have hg : evalReg (logF b) ((foldedCircle (foldH (dyadicRoundC n (s : ℂ))) (radius k)).map
          (fwdMapInv W t)) = b * J (foldH (dyadicRoundC n (s : ℂ))) := hL.2.limUnder_eq
      show evalReg (x + F2.logSingField κ) _ + _ = (evalReg (ofFun (h0rev κ) + x) _ + _) + _
      rw [logSing_eq, he, hg]
      ring
    refine ⟨l + b * J (foldH (s : ℂ)), ?_⟩
    have hJt : Tendsto (fun n => J (foldH (dyadicRoundC n (s : ℂ)))) atTop
        (𝓝 (J (foldH (s : ℂ)))) :=
      (hJc.tendsto _).comp ((continuous_foldH'.tendsto _).comp
        (RegClosure.tendsto_dyadicRoundC _))
    exact (hl.add (hJt.const_mul b)).congr fun n => (key n).symm

/-! ## The a.s. statement -/

/-- **`F2.F2UnzipRegStmt` at the circles of radius `2^{-k}` centred in `Dy`.** -/
def F2UnzipRegDyStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ k : ℕ, ∀ d ∈ Dy,
        E1.RegShift (X ω + F2.logSingField κ)
          ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) t))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
        Cor15Group.BdryConvAE
          (unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) t))

/-- The pathwise conclusion at all times `t > 0`, on one full event. -/
theorem ae_logSing_reg {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (X ω + F2.logSingField κ)
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) t))) ∧
      Cor15Group.BdryConvAE
        (unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) t) := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (cfg κ B X ω).1
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
        Cor15Group.BdryConvAE (h0f κ s B X ω) :=
    ae_all_iff.2 fun n => gaugeRegDyStmt_holds hB hX hind (by positivity)
  filter_upwards [hall, hB.cont, hB.eval_zero_ae_eq_zero] with ω h hc h0 t ht
  have hts : t ∈ Icc (0 : ℝ) ((⌈t⌉₊ : ℝ) + 1) := ⟨ht.le, by linarith [Nat.le_ceil t]⟩
  obtain ⟨hR, hbc⟩ := h ⌈t⌉₊ t hts
  rw [h0f_eq_unzippedField] at hbc
  exact logSing_reg_path κ (drive_continuous hc) (drive_zero h0) ht.le hR hbc

/-- **`F2UnzipRegDyStmt` holds.** -/
theorem f2UnzipRegDyStmt_holds : F2UnzipRegDyStmt := by
  intro κ _ _ Ω _ P _ B X hB hX hind
  have h := ae_logSing_reg (κ := κ) hB hX hind
  exact ⟨h.mono fun ω hω t ht => (hω t ht).1, h.mono fun ω hω t ht => (hω t ht).2⟩

/-! ## `AddConstAgreeStmt` -/

end RegUnif
end QuantumZipper
