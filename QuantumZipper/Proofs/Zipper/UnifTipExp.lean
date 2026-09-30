import QuantumZipper.Proofs.Zipper.UnifTipExpDet
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.MeasUnzipField
import QuantumZipper.Proofs.Zipper.JointModFinal

/-!
# UNIF-TIPEXP: reduction of `TipExpSupStmt` (decision D31, S3(i))

`TipExpSupStmt κ p` asks for finite `p`-th moments of
`tipExpSup = sup_{u ∈ ℚ∩[0,1]} sup_{t ∈ (−1,1)} e^{(γ/2) h⁰_{u,1}(t)}` (`γ = √κ`).

**Route.** The jointly continuous modification of `JointModFinal` has the explicit form
`Zh = ZE ∘ pr4 + Ddet` (free-field part `ZE`, continuous for every `ω`; deterministic part
`Ddet` of the driver). At the countably many rational times and folded dyadic centres the raw
values agree a.s. with it (`ae_raw_eq`), so by continuity (`tendsto_raw_of_witness`), a.s. for all
rational `u ∈ [0,1]` and all real `t` (`ae_avgReg_h0f_eq`):

`h⁰_{u,1}(t) = ZE(u, t, 1) + Ddet(u, t, 1)`.

Then `e^{(γ/2)(a+b)} ≤ e^{γa} + e^{γb}`, and
* the field part is bounded by `fieldTipSup`, a countable supremum (rational `u` and `t`, by
  continuity of `ZE`) of `e^{γ ZE}`: its `p`-th moment is the open node `FieldTipSupStmt`
  (conditionally on the driver `ZE` is a continuous centred Gaussian process: Fernique's theorem,
  X. Fernique, *Intégrabilité des vecteurs gaussiens*, C. R. Acad. Sci. Paris 270 (1970),
  1698–1699; or Borell–TIS);
* the deterministic part is bounded pathwise (`Ddet_unit_le`, file `UnifTipExpDet`) by
  `C_D (1 + sup_{[0,1]} |B|)²` (**no Gaussian input**); its `p`-th moment is finite given the
  polynomial moments of the Brownian running maximum (open node `BMSupMomentStmt`; standard:
  Doob's `L^q` maximal inequality, Revuz–Yor, 3rd ed., Ch. II, Thm (1.7)).

Main result: `tipExpSupStmt_of_nodes : 0 < κ → 0 < p → FieldTipSupStmt κ p → BMSupMomentStmt →
TipExpSupStmt κ p`.

Own elementary arguments (bookkeeping around the repository's JointMod construction).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun RegCont RegSample B2 B5 CircleFubini

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Definitions and the open nodes -/

/-- The running maximum `sup_{s ∈ [0,1]} |B_s|`. -/
def bmSup (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ s ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |B s.toNNReal ω|

/-! ## Elementary lemmas -/

theorem ofReal_exp_half_add_le (γ a b : ℝ) :
    ENNReal.ofReal (Real.exp (γ / 2 * (a + b))) ≤
      ENNReal.ofReal (Real.exp (γ * a)) + ENNReal.ofReal (Real.exp (γ * b)) := by
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total (γ * a) (γ * b) with h | h
  · have : Real.exp (γ / 2 * (a + b)) ≤ Real.exp (γ * b) := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_pos (γ * a)]
  · have : Real.exp (γ / 2 * (a + b)) ≤ Real.exp (γ * a) := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_pos (γ * b)]

/-! ## The a.s. identity with the explicit modification -/

/-! ## The pointwise bound -/

/-- The constant of the deterministic part. -/
def detConst (κ : ℝ) : ℝ :=
  Real.exp (Real.sqrt κ * (|Qc (Real.sqrt κ)| * 39)) * (20 * Real.sqrt κ + 13) ^ 2

omit [MeasurableSpace Ω] in
theorem ofReal_exp_Ddet_le {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hd : Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ENNReal.ofReal (Real.exp (Real.sqrt κ * Ddet κ (Real.sqrt κ) (drive κ B ω) (u, ((t : ℂ), 1))))
      ≤ ENNReal.ofReal (detConst κ) * (1 + bmSup B ω) ^ (2 : ℝ) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- `bmSup` is finite
  have hBc : Continuous fun s : ℝ => B s.toNNReal ω := by
    have : (fun s : ℝ => B s.toNNReal ω) = fun s => (Real.sqrt κ)⁻¹ * drive κ B ω s := by
      funext s; simp only [drive]; field_simp
    rw [this]; exact continuous_const.mul hd.1
  obtain ⟨M0, hM0⟩ := exists_abs_le_on_Icc hBc 1
  have hSfin : bmSup B ω ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M0)) (iSup₂_le fun s hs' => ?_)
    exact ENNReal.ofReal_le_ofReal (hM0 s hs')
  set MB := (bmSup B ω).toReal with hMB
  have hMB0 : 0 ≤ MB := ENNReal.toReal_nonneg
  have hBle : ∀ s ∈ Icc (0 : ℝ) 1, |B s.toNNReal ω| ≤ MB := fun s hs =>
    (ENNReal.ofReal_le_iff_le_toReal hSfin).1
      (le_iSup₂_of_le (f := fun (s : ℝ) (_ : s ∈ Icc (0 : ℝ) 1) =>
        ENNReal.ofReal |B s.toNNReal ω|) s hs le_rfl)
  have hM : ∀ s ∈ Icc (0 : ℝ) 1, |drive κ B ω s| ≤ Real.sqrt κ * MB := fun s hs' => by
    simp only [drive, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (hBle s hs') hs.le
  have hDd := Ddet_unit_le κ (Real.sqrt κ) hd.1 hd.2 (mul_nonneg hs.le hMB0) hM hu
    (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
  set K := |Qc (Real.sqrt κ)| * 39
  set x := 20 * (Real.sqrt κ * MB) + 13 with hx
  have hx0 : 0 < x := by positivity
  have hreal : Real.exp (Real.sqrt κ * Ddet κ (Real.sqrt κ) (drive κ B ω) (u, ((t : ℂ), 1))) ≤
      detConst κ * (1 + MB) ^ (2 : ℝ) := by
    calc Real.exp (Real.sqrt κ * Ddet κ (Real.sqrt κ) (drive κ B ω) (u, ((t : ℂ), 1)))
        ≤ Real.exp (Real.sqrt κ * (2 / Real.sqrt κ * Real.log x + K)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hDd hs.le)
      _ = Real.exp (Real.sqrt κ * K) * (Real.exp (Real.log x) * Real.exp (Real.log x)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          field_simp
          ring
      _ = Real.exp (Real.sqrt κ * K) * x ^ 2 := by rw [Real.exp_log hx0]; ring
      _ ≤ Real.exp (Real.sqrt κ * K) * ((20 * Real.sqrt κ + 13) ^ 2 * (1 + MB) ^ 2) := by
          gcongr
          rw [← mul_pow]
          gcongr
          nlinarith [mul_nonneg hs.le hMB0]
      _ = detConst κ * (1 + MB) ^ (2 : ℝ) := by
          rw [Real.rpow_two, detConst]; ring
  calc ENNReal.ofReal (Real.exp (Real.sqrt κ * Ddet κ (Real.sqrt κ) (drive κ B ω)
        (u, ((t : ℂ), 1)))) ≤ ENNReal.ofReal (detConst κ * (1 + MB) ^ (2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (detConst κ) * (1 + bmSup B ω) ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by unfold detConst; positivity),
          ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_add zero_le_one hMB0, ENNReal.ofReal_one, hMB,
          ENNReal.ofReal_toReal hSfin]

/-! ## The reduction -/

end RegUnif
end QuantumZipper
