import QuantumZipper.Proofs.Zipper.E1CoordChange2
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.LQG.MeasurabilityAE

/-!
# E1-PW (part 1): the global limit for `𝔥₀` (E1-EX) and the Palm formula on an open window

`handoff/E1-PLAN.md`, sub-nodes **E1-EX** and the window form of `palm_formula_norm_local` used by
**E1-PW**.

* **E1-EX** (`ae_exists_isVagueLimitR_normAt_h0rev`): for a free field `X` and any probability
  measure `ϖ`, a.s. `bdryApprox γ (N_ϖ(ofFun 𝔥₀ + X))` has a global vague limit. Since
  `𝔥₀ = (2/γ) log|·|` is the log potential `logPot (−2/γ) 0` of strength `−2/γ < Q`, this is
  M4-P4 (`LogSing.ae_logSingularity`, with the P3(b) bound `LogSing.p3bBound`) — local limits
  off `0` plus tightness at `0` — followed by an additive constant (`LocalRule`).
  Paper: Duplantier–Sheffield, *LQG and KPZ*, arXiv:0808.1560, §3 (log singularities of strength
  `α < Q`), as formalized in node M4-P4.
* **`palm_formula_Ioo`**: `PalmNorm.palm_formula_norm_local` with the indicator of `(a,b)` in
  place of a continuous weight, by monotone convergence along `openBump (a,b) n ↑ 1_{(a,b)}`.
  The `ω`-measurability needed for monotone convergence comes from the a.s. measurability of the
  boundary measure as a random measure (`LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae`) and the
  s-finite restricted kernel `Palm.kerI`. Own bookkeeping (no source needed: monotone
  convergence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open PalmNorm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## 1. E1-EX: the global vague limit for the `𝔥₀` field -/

theorem logPot_h0rev (κ : ℝ) : LogSing.logPot (-(2 / Real.sqrt κ)) 0 = h0rev κ := by
  funext v
  simp only [LogSing.logPot, h0rev, Complex.ofReal_zero, sub_zero]
  ring

/-- **E1-EX.** A.s. the approximations of `N_ϖ(ofFun 𝔥₀ + X)` converge vaguely on all of `ℝ`. -/
theorem ae_exists_isVagueLimitR_normAt_h0rev [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {ϖ : Measure ℂ}
    (hϖ1 : ϖ univ = 1) :
    ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ)
      (normAt ϖ (ofFun (h0rev κ) + X ω))) ν := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := by
    rw [hγdef, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  have hαQ : -(2 / γ) < Qc γ := by
    unfold Qc; have : 0 < 2 / γ := by positivity
    linarith [div_pos hγ (show (0 : ℝ) < 2 by norm_num)]
  filter_upwards [LogSing.ae_logSingularity hX hγ hγ2 1 hαQ 0
      (LogSing.p3bBound hX hγ hγ2 one_pos (by simp)), RegSample.ae_isRegularSample hX]
    with ω hω hreg
  obtain ⟨hglob, -⟩ := hω
  have hY : IsRegularSample (BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0)) :=
    (hreg.addConst' _).add_ofFun_log' _ 0
  set c := -((ofFun (h0rev κ) + BdryExist.zField X 1 ω) ϖ) with hc
  have h := LocalRule.isVagueLimitR_add_ofFun hY hglob (φ := fun _ => c) isOpen_univ
    (fun t => mem_univ _) continuousOn_const
  have e : normAt ϖ (ofFun (h0rev κ) + BdryExist.zField X 1 ω) =
      BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0) + ofFun (fun _ => c) := by
    rw [hγdef, logPot_h0rev]
    unfold normAt
    rw [GoodSample.addConst_eq_add_ofFun]
    congr 1
    exact add_comm _ _
  rw [normAt_zField hϖ1 1 (h0rev κ) ω, e]
  exact ⟨_, h⟩

/-! ## 2. Small helpers -/

/-- `qBoundaryMeasureOn γ x I` never charges `Iᶜ` (also in the junk case). -/
theorem qBoundaryMeasureOn_compl (γ : ℝ) (x : FieldSample) (I : Set ℝ) :
    qBoundaryMeasureOn γ x I Iᶜ = 0 := by
  unfold qBoundaryMeasureOn
  split_ifs with h
  · exact h.choose_spec.1
  · simp

/-- On a live window, `realRevMap v t` agrees with a global order isomorphism. -/
theorem exists_orderIso_eq_realRevMap {v : ℝ → ℝ} {t a b : ℝ} (hv : Continuous v) (ht : 0 ≤ t)
    (hab : a < b) (hw : ∀ x ∈ Icc a b, IsLive v t x) :
    ∃ Φ : ℝ ≃o ℝ, ∀ x ∈ Icc a b, Φ x = realRevMap v t x := by
  obtain ⟨U, hUo, hJU, hdiff, hH, hreal, him, hne⟩ :=
    exists_revMapExt_window hv ht (a := a) (b := b) hw
  have hmono : StrictMonoOn (fun x : ℝ => (RevMapExtension.revMapExt v t x).re) (Icc a b) := by
    intro x hx y hy hxy
    simp only [hreal x hx, hreal y hy, Complex.ofReal_re]
    exact RealLine.strictMonoOn_realRevMap hv ht (exists_isRealRevSol_of_isLive (hw x hx))
      (exists_isRealRevSol_of_isLive (hw y hy)) hxy
  refine ⟨CoordChange.extIso hab.le
    (CoordChange.continuousOn_re_of_differentiableOn hJU hdiff) hmono, fun x hx => ?_⟩
  rw [CoordChange.extIso_eq _ _ _ hx, hreal x hx, Complex.ofReal_re]

/-! ## 3. The Palm formula on an open window -/

/-- A measurable version of an a.e. measurable random measure, restricted to `I`: agrees a.s.
with `ν` on `I` when `ν ω I < ∞` a.s. (`Palm.nuMod`, without the integrability hypothesis). -/
theorem nuMod_ae_eq' {ν : Ω → Measure ℝ} (hν : AEMeasurable ν P) {I : Set ℝ}
    (hfin : ∀ᵐ ω ∂P, ν ω I < ∞) : ∀ᵐ ω ∂P, Palm.nuMod hν I ω = ν ω := by
  filter_upwards [hν.ae_eq_mk, hfin] with ω h1 h2
  unfold Palm.nuMod
  rw [← h1, if_pos h2]

/-- **Palm formula on the window `(a,b)`** (`palm_formula_norm_local` with the weight
`1_{(a,b)}`), in `lintegral` form. The measurability of the right side in `x` is a hypothesis
(`hK`, `hρ`), discharged by the caller. -/
theorem palm_formula_Ioo {X : Ω → FieldSample} {h h' : ℂ → ℝ} {ϖ : Measure ℂ}
    {μ : ℕ → Measure ℂ} {γ a b : ℝ}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2)
    {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hh' : Continuous h')
    {W : Set ℂ} (hW : IsOpen W) (habW : ∀ t ∈ Icc a b, (t : ℂ) ∈ W) (hEq : EqOn h h' W)
    (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1) (hμ : ∀ j, IsAdmissibleH (μ j))
    (hhϖ : Integrable h ϖ) (hhμ : ∀ j, Integrable h (μ j))
    (hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox γ (normAt ϖ (ofFun h + X ω))) ν)
    {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hφ : Measurable (Function.uncurry φ))
    (hρ : Measurable (rhoNorm γ h ϖ))
    (hK : Measurable fun x =>
      ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P) :
    ∫⁻ ω, ∫⁻ x in Ioo a b, φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
        ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω))) ∂P =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (rhoNorm γ h ϖ x) *
        ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
  set I : Set ℝ := Ioo a b with hIdef
  set wn : ℕ → ℝ → ℝ := fun n => LQGMeas.openBump I n with hwn
  have hIc : Iᶜ.Nonempty := ⟨b, fun h => lt_irrefl b h.2⟩
  have hsup : ∀ x, ⨆ n, ENNReal.ofReal (wn n x) = I.indicator 1 x := fun x =>
    LQGMeas.iSup_openBump isOpen_Ioo hIc x
  have hmono : ∀ x, Monotone fun n => ENNReal.ofReal (wn n x) := fun x _ _ hnm =>
    ENNReal.ofReal_le_ofReal (LQGMeas.openBump_mono I x hnm)
  have hwc : ∀ n, Continuous (wn n) := fun n => LQGMeas.continuous_openBump I n
  have hwab : ∀ n, ∀ x ∉ Icc a b, wn n x = 0 := fun n x hx => by
    by_contra hne
    exact hx (Ioo_subset_Icc_self (LQGMeas.tsupport_openBump_subset I n (subset_tsupport _ hne)))
  have hPn := fun n => palm_formula_norm_local (P := P) (μ := μ) hX hγ hγ2 hab hh' hW habW hEq
    hϖ hϖ1 hμ hhϖ hhμ hex (hwc n) (LQGMeas.hasCompactSupport_openBump (isBounded_Ioo a b) n)
    (fun x => LQGMeas.openBump_nonneg I n x) (hwab n) hφ
  -- notation
  set Nf : Ω → FieldSample := fun ω => normAt ϖ (ofFun h + X ω) with hNf
  set c : Ω → ℕ → ℝ := fun ω j => Nf ω (μ j) with hc
  set ν : Ω → Measure ℝ := fun ω => qBoundaryMeasure γ (Nf ω) with hν
  have hcm : Measurable c := measurable_pi_iff.2 fun j => by
    simp only [hc, hNf, normAt, addConst, Pi.add_apply]
    exact ((measurable_const.add (hX.measurable_coord _)).add
      ((measurable_const.add (hX.measurable_coord _)).neg.mul measurable_const))
  have hφx : ∀ v, Measurable (φ v) := fun v => hφ.comp (measurable_const.prodMk measurable_id)
  -- left side: monotone convergence
  have hL : ∀ ω, ∫⁻ x in I, φ (c ω) x ∂ν ω = ⨆ n, ∫⁻ x, ENNReal.ofReal (wn n x) * φ (c ω) x ∂ν ω :=
    fun ω => by
      rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_iSup
        (f := fun n x => ENNReal.ofReal (wn n x) * φ (c ω) x)
        (fun n => ((hwc n).measurable.ennreal_ofReal).mul (hφx _))
        (fun n m hnm x => mul_le_mul_left (hmono x hnm) _)]
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.iSup_mul, hsup x]
      by_cases hx : x ∈ I
      · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hνae : AEMeasurable ν P := by
    refine LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (fun μ' => ?_) ?_
    · simp only [hNf, normAt, addConst, Pi.add_apply]
      exact (measurable_const.add (hX.measurable_coord _)).add
        ((measurable_const.add (hX.measurable_coord _)).neg.mul measurable_const)
    · filter_upwards [hex] with ω ⟨ν', hν'⟩
      rw [qBoundaryMeasure_eq hν']; exact hν'
  have hfin : ∀ᵐ ω ∂P, ν ω (Icc a b) < ∞ := by
    filter_upwards [hex] with ω ⟨ν', hν'⟩
    have := hν'.1
    show qBoundaryMeasure γ (Nf ω) (Icc a b) < ∞
    rw [qBoundaryMeasure_eq hν']
    exact isCompact_Icc.measure_lt_top
  have hgm : ∀ n, AEMeasurable (fun ω => ∫⁻ x, ENNReal.ofReal (wn n x) * φ (c ω) x ∂ν ω) P := by
    intro n
    have hF : Measurable fun p : Ω × ℝ => ENNReal.ofReal (wn n p.2) * φ (c p.1) p.2 :=
      ((hwc n).measurable.comp measurable_snd).ennreal_ofReal.mul
        (hφ.comp ((hcm.comp measurable_fst).prodMk measurable_snd))
    refine ⟨_, hF.lintegral_kernel_prod_right' (κ := Palm.kerI hνae (measurableSet_Icc (a := a) (b := b))), ?_⟩
    filter_upwards [nuMod_ae_eq' hνae hfin] with ω hω
    rw [Palm.kerI_apply, hω, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hwab n x hx, ENNReal.ofReal_zero, zero_mul]
  have hLHS : ∫⁻ ω, ∫⁻ x in I, φ (c ω) x ∂ν ω ∂P =
      ⨆ n, ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (wn n x) * φ (c ω) x ∂ν ω ∂P := by
    simp_rw [hL]
    exact lintegral_iSup' hgm (ae_of_all _ fun ω n m hnm =>
      lintegral_mono fun x => mul_le_mul_left (hmono x hnm) _)
  -- right side: monotone convergence
  set K : ℝ → ℝ≥0∞ := fun x =>
    ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P with hKdef
  have hRn : ∀ n x, ENNReal.ofReal (wn n x * rhoNorm γ h ϖ x) * K x =
      ENNReal.ofReal (wn n x) * (ENNReal.ofReal (rhoNorm γ h ϖ x) * K x) := fun n x => by
    rw [ENNReal.ofReal_mul (LQGMeas.openBump_nonneg I n x), mul_assoc]
  have hRHS : ∫⁻ x in I, ENNReal.ofReal (rhoNorm γ h ϖ x) * K x =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (wn n x * rhoNorm γ h ϖ x) * K x := by
    simp_rw [hRn]
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_iSup
      (f := fun n x => ENNReal.ofReal (wn n x) * (ENNReal.ofReal (rhoNorm γ h ϖ x) * K x))
      (fun n => ((hwc n).measurable.ennreal_ofReal).mul (hρ.ennreal_ofReal.mul hK))
      (fun n m hnm x => mul_le_mul_left (hmono x hnm) _)]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.iSup_mul, hsup x]
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  show ∫⁻ ω, ∫⁻ x in I, φ (c ω) x ∂ν ω ∂P = ∫⁻ x in I, ENNReal.ofReal (rhoNorm γ h ϖ x) * K x
  rw [hLHS, hRHS]
  exact iSup_congr fun n => hPn n

end E1
end QuantumZipper
