import QuantumZipper.Proofs.Thm18.R18RTCore
import QuantumZipper.Proofs.Thm18.R18UnzipArea
import QuantumZipper.Proofs.Zipper.T13Hard3Realize
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegDet
import QuantumZipper.Proofs.Zipper.AreaPCReduce
import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-HMP (1): log growth of the wedge circle averages from that of the free field

Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1
and its standard consequence `sup_{|z| ≤ R} |h_ε(z)| = O(log 1/ε)` (the proof of their Lemma 3.1
/ Thm 1.2 upper bound: union bound over a grid plus the modulus of Prop. 2.1).

This file proves `CircAvgLogGrowthStmt` from the free-field statement
`FreeCircLogGrowthStmt` (a.s., the regularized circle averages `evalReg X (fc(c, ρ))` of a free
field are `O(1 + |log ρ|)` on bounded sets), by the transfer used throughout the project:

* realization of the wedge (`WedgeUnzip.pStarRealizeStmt_holds`): `avgReg Y = avgReg (canonical Z)`
  with `Z` the unscaled wedge field and `b = scaleParam γ Z > 0`;
* the decomposition `Z = X'' + α₀(−log|·|) + G` on every folded circle
  (`WedgeUnzip.WDec.wedgeDecompStmt_holds`), `G` continuous;
* a dyadic raw value of the regular `Y` is its regularized value, which is
  `evalReg Z (fc(b d, b 2^{-k})) + Q log b` (`F1.evalReg_fc_of_avgReg_rescale`);
* the averages of `α₀(−log|·|)` are `−2α₀ log max(ρ, |c|)` and those of `G` are bounded.

Own bookkeeping on top of the cited project results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace RTHmp

open Thm18Asm

/-- **Free-field log growth of circle averages** (Hu–Miller–Peres, Ann. Probab. 38 (2010),
Prop. 2.1 and the grid argument of §3): a.s., on every bounded set, the regularized folded-circle
averages of a free field are `O(1 + |log ρ|)`. -/
def FreeCircLogGrowthStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Hbar, ‖c‖ ≤ R → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      |evalReg (X ω) (foldedCircle c ρ)| ≤ C * (1 + |Real.log ρ|)

/-! ## Dyadic bookkeeping -/

theorem dyadicRound_intDiv {n m : ℕ} (hnm : n ≤ m) (z : ℤ) :
    dyadicRound m ((z : ℝ) / 2 ^ n) = (z : ℝ) / 2 ^ n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold dyadicRound
  have e : (2 : ℝ) ^ (n + j) * ((z : ℝ) / 2 ^ n) = ((z * 2 ^ j : ℤ) : ℝ) := by
    push_cast; rw [pow_add]; field_simp
  rw [e, Int.floor_intCast]
  push_cast
  rw [pow_add]
  field_simp

theorem dyadicRoundC_fixed {n m : ℕ} (hnm : n ≤ m) {d : ℂ} {a b : ℤ}
    (ha : d.re = a / 2 ^ n) (hb : d.im = b / 2 ^ n) : dyadicRoundC m d = d := by
  apply Complex.ext
  · show dyadicRound m d.re = d.re
    rw [ha, dyadicRound_intDiv hnm]
  · show dyadicRound m d.im = d.im
    rw [hb, dyadicRound_intDiv hnm]

theorem foldH_dyadicRoundC_fixed (n : ℕ) (w : ℂ) {m : ℕ} (hnm : n ≤ m) :
    dyadicRoundC m (foldH (dyadicRoundC n w)) = foldH (dyadicRoundC n w) := by
  unfold foldH
  split_ifs
  · exact dyadicRoundC_fixed hnm (a := ⌊(2 : ℝ) ^ n * w.re⌋) (b := ⌊(2 : ℝ) ^ n * w.im⌋) rfl rfl
  · refine dyadicRoundC_fixed hnm (a := ⌊(2 : ℝ) ^ n * w.re⌋) (b := -⌊(2 : ℝ) ^ n * w.im⌋) ?_ ?_
    · simp [dyadicRoundC, dyadicRound]
    · simp [dyadicRoundC, dyadicRound]
      ring

/-- A dyadic raw value of a regular sample is its regularized value. -/
theorem raw_dyadic_eq_evalReg {y : FieldSample} {F : ℂ × ℝ → ℝ} (hy : IsRegularWith y F)
    (n k : ℕ) (w : ℂ) :
    y (foldedCircle (dyadicRoundC n w) (radius k)) =
      evalReg y (foldedCircle (foldH (dyadicRoundC n w)) (radius k)) := by
  set d := foldH (dyadicRoundC n w) with hd
  have hdH : d ∈ Hbar := CircleFubini.foldH_mem_Hbar' _
  rw [← CoordReg.foldedCircle_foldH (dyadicRoundC n w), hy.evalReg_fc_of_mem hdH (radius_pos k)]
  have h2 : Tendsto (fun m => y (foldedCircle (dyadicRoundC m d) (radius k))) atTop
      (𝓝 (y (foldedCircle d (radius k)))) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm => by
      simp only [hd, foldH_dyadicRoundC_fixed n w hm]⟩)
  exact tendsto_nhds_unique h2 (hy.2.1 k d hdH)

/-- A sample agreeing with a regular one on all folded circles centred in `ℍ̄` is regular with
the same witness. -/
theorem isRegularWith_of_fc_eq {x y : FieldSample} {F : ℂ × ℝ → ℝ} (hy : IsRegularWith y F)
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r)) :
    IsRegularWith x F :=
  ⟨hy.1, fun k z hz => (hy.2.1 k z hz).congr fun n =>
    (h _ (CircleCont.dyadicRoundC_mem_Hbar hz n) _ (radius_pos k)).symm, hy.2.2⟩

/-! ## Elementary bounds -/

theorem abs_log_max_le {ρ t R : ℝ} (hρ : 0 < ρ) (hle : max ρ t ≤ R) :
    |Real.log (max ρ t)| ≤ |Real.log ρ| + |Real.log R| := by
  have h1 : Real.log ρ ≤ Real.log (max ρ t) := Real.log_le_log hρ (le_max_left _ _)
  have h2 : Real.log (max ρ t) ≤ Real.log R :=
    Real.log_le_log (lt_of_lt_of_le hρ (le_max_left _ _)) hle
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log ρ), le_abs_self (Real.log R),
    abs_nonneg (Real.log ρ), abs_nonneg (Real.log R)]

theorem abs_log_mul_radius_le {b : ℝ} (hb : 0 < b) (k : ℕ) :
    |Real.log (b * radius k)| ≤ |Real.log b| + k := by
  have hr : radius k ≠ 0 := (radius_pos k).ne'
  rw [Real.log_mul hb.ne' hr]
  have e : Real.log (radius k) = -(k * Real.log 2) := by
    simp [radius, Real.log_pow, Real.log_inv]
  rw [e]
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (mul_nonneg hk h2'.le)]
  nlinarith

theorem abs_circPot_zero_le {ρ R : ℝ} (hρ : 0 < ρ) {c : ℂ} (hle : max ρ ‖c‖ ≤ R) :
    |CircleCont.circPot ρ c ((0 : ℝ) : ℂ) / 2| ≤ |Real.log ρ| + |Real.log R| := by
  have e : CircleCont.circPot ρ c ((0 : ℝ) : ℂ) / 2 = -Real.log (max ρ ‖c‖) := by
    simp only [CircleCont.circPot, Complex.ofReal_zero, map_zero, sub_zero]
    ring
  rw [e, abs_neg]
  exact abs_log_max_le hρ hle

theorem abs_integral_fc_le {G : ℂ → ℝ} {M R : ℝ} (hM : ∀ x ∈ closedBall (0 : ℂ) R, ‖G x‖ ≤ M)
    {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 ≤ ρ) (hcR : ‖c‖ + ρ ≤ R) :
    |∫ v, G v ∂foldedCircle c ρ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := foldedCircle c ρ) (f := G) (C := M) ?_
  · rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  · filter_upwards [E6.foldedCircle_ae_dist_le_pc hc hρ] with u hu
    refine hM u (mem_closedBall.2 ?_)
    rw [dist_zero_right]
    calc ‖u‖ ≤ ‖u - c‖ + ‖c‖ := by
          have := norm_add_le (u - c) c; simpa using this
      _ ≤ ρ + ‖c‖ := by gcongr; rw [← dist_eq_norm]; exact hu
      _ ≤ R := by linarith

theorem norm_foldH_dyadicRoundC_le (n : ℕ) (w : ℂ) : ‖foldH (dyadicRoundC n w)‖ ≤ ‖w‖ + 2 := by
  have h1 : ‖foldH (dyadicRoundC n w)‖ = ‖dyadicRoundC n w‖ := by
    unfold foldH; split_ifs <;> simp [Complex.norm_conj]
  have h2 := CircleCont.norm_dyadicRoundC_sub_le n w
  have h3 : 2 * (1 / (2 : ℝ) ^ n) ≤ 2 := by
    have : 1 / (2 : ℝ) ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have h4 := norm_sub_norm_le (dyadicRoundC n w) w
  rw [h1]; linarith

theorem radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-! ## The reduction -/

/-- **`CircAvgLogGrowthStmt` from the free-field log growth.** -/
theorem circAvgLogGrowth_of_free (hF : FreeCircLogGrowthStmt) : CircAvgLogGrowthStmt := by
  intro γ Ω _ P _ B Y hS hI
  have hP := isPStarSample_of_setting hS
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds (γ ^ 2) P Y B hP
  obtain ⟨Ω₃, _, Q₃, _, X'', G, hX'', -, -, hdec⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds (γ ^ 2) hκ hκ4 (P.prod Q) X' A B'' hX hA hInd hB hIB
  have hγ' : 0 < Real.sqrt (γ ^ 2) := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt (γ ^ 2) < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ' hγ2
  have hspec := Wire2.ae_wedge_canonical_spec hγ' hγ2 hα hX hA hInd
  have lift2 : ∀ {p : Ω × Ω₂ → Prop}, (∀ᵐ ω ∂(P.prod Q), p ω) →
      ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1 := fun h =>
    ae_of_ae_map measurable_fst.aemeasurable (by rw [measurePreserving_fst.map_eq]; exact h)
  have lift1 : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1.1 :=
    fun h => lift2 (ae_of_ae_map measurable_fst.aemeasurable
      (by rw [measurePreserving_fst.map_eq]; exact h))
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) (WedgeUnzip.ae_of_ae_prod_fst (Q := Q₃) ?_)
  filter_upwards [lift1 hI.1, lift2 hae, lift2 hspec, hdec, hF _ X'' hX'',
    RegSample.ae_isRegularSample hX''] with ω hYg hR hsp hD hFX hXreg
  intro Rr
  obtain ⟨havg, -⟩ := hR
  obtain ⟨FY, hFY⟩ := hYg.1.1
  obtain ⟨hGc, -, hZfc⟩ := hD
  obtain ⟨FX, hFXw⟩ := hXreg
  set s := Real.sqrt (γ ^ 2) with hs
  set α := s - 2 / s with hαdef
  set Z := F2.zU s X' A ω.1 with hZ
  set b := scaleParam s Z with hbdef
  have hb : 0 < b := hsp.1
  have hW1 := hFXw.add_ofFun_log' α 0
  have e1 : (X'' ω + ofFun fun v => α * -Real.log ‖v - ((0 : ℝ) : ℂ)‖) =
      X'' ω + F2.logSingField (γ ^ 2) := by
    simp [F2.logSingField, hαdef, hs]
  rw [e1] at hW1
  have hW2 := hW1.add_ofFun' hGc.continuousOn
  have hZw := isRegularWith_of_fc_eq hW2 hZfc
  set R₁ := b * (|Rr| + 2) with hR₁
  have hR₁b : b ≤ R₁ := by
    have : (1 : ℝ) ≤ |Rr| + 2 := by linarith [abs_nonneg Rr]
    nlinarith
  obtain ⟨C₁, hC₁, hC₁b⟩ := hFX R₁
  obtain ⟨MG, hMG⟩ := (isCompact_closedBall (0 : ℂ) (2 * R₁)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG 0 (mem_closedBall_self (by positivity)))
  set L := |Real.log b| with hL
  set A0 := C₁ * (1 + L) + |α| * (L + |Real.log R₁|) + MG + |Qc s * Real.log b| with hA0
  have hA0n : 0 ≤ A0 := by positivity
  refine ⟨A0 + (C₁ + |α|), by positivity, fun k n w hw => ?_⟩
  set d := foldH (dyadicRoundC n w) with hd
  have hdH : d ∈ Hbar := CircleFubini.foldH_mem_Hbar' _
  set ρ := b * radius k with hρdef
  have hρ : 0 < ρ := mul_pos hb (radius_pos k)
  have hcH : (b : ℂ) * d ∈ Hbar := by
    show 0 ≤ ((b : ℂ) * d).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hb.le hdH
  have hval : Y ω.1.1 (foldedCircle (dyadicRoundC n w) (radius k)) =
      (FX ((b : ℂ) * d, ρ) + α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ) + (Qc s * Real.log b + 0) := by
    rw [raw_dyadic_eq_evalReg hFY, F1.evalReg_fc_of_avgReg_rescale ⟨_, hZw⟩ (Qc s) hb 0 ?_ hdH
      (radius_pos k), hZw.evalReg_fc_of_mem hcH hρ]
    rw [havg]
    congr 1
    funext μ
    simp [addConst]
    rfl
  -- geometry
  have hnd : ‖d‖ ≤ |Rr| + 2 := (norm_foldH_dyadicRoundC_le n w).trans (by
    linarith [le_abs_self Rr])
  have hnc : ‖(b : ℂ) * d‖ ≤ R₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    exact mul_le_mul_of_nonneg_left hnd hb.le
  have hρR : ρ ≤ b := by
    have := radius_le_one k
    calc ρ = b * radius k := rfl
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left this hb.le
      _ = b := mul_one b
  have hmax : max ρ ‖(b : ℂ) * d‖ ≤ R₁ := max_le (hρR.trans hR₁b) hnc
  have hlogρ : |Real.log ρ| ≤ L + k := abs_log_mul_radius_le hb k
  -- the three bounds
  have hbX : |FX ((b : ℂ) * d, ρ)| ≤ C₁ * (1 + |Real.log ρ|) := by
    rw [← hFXw.evalReg_fc_of_mem hcH hρ]
    exact hC₁b _ hcH hnc ρ hρ (hρR.trans hR₁b)
  have hbP := abs_circPot_zero_le hρ hmax
  have hbG : |∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ| ≤ MG :=
    abs_integral_fc_le hMG hcH hρ.le (by linarith)
  rw [hval]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsum : |FX ((b : ℂ) * d, ρ) + α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ + (Qc s * Real.log b + 0)| ≤
      C₁ * (1 + (L + k)) + |α| * ((L + k) + |Real.log R₁|) + MG + |Qc s * Real.log b| := by
    have t1 := abs_add_le (FX ((b : ℂ) * d, ρ) +
      α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ) (Qc s * Real.log b + 0)
    have t2 := abs_add_le (FX ((b : ℂ) * d, ρ) +
      α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2))
        (∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ)
    have t3 := abs_add_le (FX ((b : ℂ) * d, ρ))
      (α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2))
    rw [abs_mul] at t3
    have t4 : |Qc s * Real.log b + 0| = |Qc s * Real.log b| := by rw [add_zero]
    have u1 : C₁ * (1 + |Real.log ρ|) ≤ C₁ * (1 + (L + k)) := by gcongr
    have u2 : |α| * |CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2| ≤
        |α| * ((L + k) + |Real.log R₁|) := by gcongr; linarith
    linarith
  refine hsum.trans ?_
  have hαn := abs_nonneg α
  nlinarith

end RTHmp
end R18
end QuantumZipper
