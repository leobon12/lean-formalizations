import QuantumZipper.Proofs.Zipper.UnifSWMain
import QuantumZipper.Proofs.Zipper.B5VHccZero

/-!
# UNIF-UO (1): fixed-time inputs for the off-tip windows

Task UNIF-UO (decision D26). Fixed-time facts used by `UnifOffTipStmt`:

* **`ae_hcc_ext`**: the fixed-time coordinate-change windows `B5.ae_hcc` for **all** rational
  windows `u < v < 0₋(T − s)` of the fully unzipped picture, including the outer real line
  `u < 0₋(T)` and windows straddling `0₋(T)`. The proof of `B5.ae_hcc` never uses its lower bound
  `0₋(T) < u` (liveness of `u` follows from `u < v` and the liveness of `v`); it is reproduced here
  without that hypothesis.
* **`ae_windows_rat_ext`**: at all positive rational times at once,
  `ν_{h⁰_T}(u,v) = ν_{h⁰_r}(F_r u, F_r v)` for all rational `u < v < 0₋(T − r)`.
* **`ae_zero_time_atomless`**: at time `0`, `h⁰_0` has a global atomless vague limit
  (`AtomlessUncond.ae_gamma0_logSingularity`, M4-P5 `ae_noAtoms_free'`).

Source: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68); the transfer is the
bookkeeping of `B5VHccMain` (own).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B5 E1 E1.M4 CoordsFull Collision B1Full B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **`B5.ae_hcc` without the lower bound `0₋(T) < u`.** -/
theorem ae_hcc_ext (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) :
    ∀ᵐ ω ∂P, ∀ u v : ℚ, (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - s) →
      qBoundaryMeasureOn (Real.sqrt κ)
          (coordChange (h0f κ s B X ω) (revMap (Vr κ T B ω) (T - s)) (Qc (Real.sqrt κ)))
          (Ioo u v) (Ioo u v) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ s B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v)) := by
  have hT : 0 < T := hs.trans_le hsT
  have ht : 0 ≤ T - s := sub_nonneg.2 hsT
  have htT : T - s < T := sub_lt_self T hs
  set t := T - s with htdef
  have hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular
  refine ae_all_iff.2 fun u => ae_all_iff.2 fun v => ?_
  by_cases huv : (u : ℝ) < v
  swap
  · exact Eventually.of_forall fun ω h => absurd h huv
  filter_upwards [ae_mem_eqP_data hκ hκ4 hB hX hind ht htT huv, hB.cont,
    b2_coordsFull_eq (κ := κ) hB hX hind ht htT.le,
    ae_rawConverges_h0f (κ := κ) hB hX hind hT.le, ae_rawConverges_h0f (κ := κ) hB hX hind hs.le,
    ae_bCert_h0f hReg hκ hκ4 hT hB hX hind 0, ae_bCert_h0f hReg hκ hκ4 hs hB hX hind 0,
    ae_all_iff.2 (ae_regShift_Yf_fc κ hB hX hind ht htT.le),
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hE hc hcf hrawT hraws hbT hbs hrs hK _ hv
  have hmR : ∀ S, mReg κ S B X 0 ω = 0 := fun S => evalReg_zero_measure _
  rw [hmR, addConst_neg_zero] at hbT hbs
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hc) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set Y := Yf κ T t B X ω with hYdef
  have hYs : Y = h0f κ s B X ω := Yf_sub_eq_h0f s ω
  rw [← hYs]
  rw [← hYs] at hraws hbs
  set c0 := Y (foldedCircle 0 1) with hc0
  set p := dataH κ T t B X ω with hp
  set W := CharFun.Wof 1 t ht p.2 with hWdef
  have hWc : Continuous W := CharFun.continuous_Wof 1 t ht p.2
  have heq : EqOn W V (Icc 0 t) := eqOn_Wof_extC_Vstop ht hc
  have hw0 : p.2 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 := by
    show extC t (Vstop κ T t B ω) _ = 0
    rw [extC_Vstop hc]; exact vrev_zero hT.le
  have hW0 : W 0 = 0 := by simp [hWdef, CharFun.Wof, projIcc_left, hw0]
  have hlive : liveNeg W t = liveNeg V t := liveNeg_congr_drive hWc hVc ht heq
  have hvl : (v : ℝ) ∈ liveNeg V t := mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK ht htT.le hv
  have hul : (u : ℝ) ∈ liveNeg V t :=
    ⟨huv.trans hvl.1, hvl.2.trans_le (realHitTime_anti hVc huv.le (by rw [hV0]; exact hvl.1))⟩
  have hrev : revMap W t = revMap V t := funext fun z => ReverseFlow.revMap_congr_drive z heq
  set Z := coordChange Y (revMap V t) (Qc (Real.sqrt κ)) with hZdef
  have hZ : coordsFull (Zr κ ht p) = coordsFull (addConst Z (-c0)) := by
    rw [coordsFull_Zr, ← hWdef, hrev]
    exact coordsFull_coordChange_fromC_nrm hrs
  have hrawZ : LocalRule.RawConverges Z Hbar := rawConverges_congr_full hcf hrawT
  have hC : BCert (Real.sqrt κ) (Zr κ ht p) :=
    bCert_congr_full (hZ.trans (coordsFull_addConst_congr hcf.symm _)).symm
      (bCert_addConst hrawT hbT _)
  have hF : coordsFull (fromC p.1) = coordsFull (addConst Y (-c0)) := coordsFull_fromC (nrm Y)
  have hC1 : BCert (Real.sqrt κ) (fromC p.1) :=
    bCert_congr_full hF.symm (bCert_addConst hraws hbs _)
  have hg : p ∈ goodP κ ht v := ⟨⟨⟨hw0, by rw [← hWdef, hlive]; exact hvl⟩, hC⟩, hC1⟩
  have hLR : LP κ ht u v p = RP κ ht u v p := by
    rcases hE with h | h
    · exact absurd hg h
    · exact h
  have hFu : Fm t ht u p.2 = realRevMap V t u := by
    rw [Fm_eq_realRevMap ht ((congrArg (fun S => (u : ℝ) ∈ S) hlive).mpr hul).2
      (show (u : ℝ) < W 0 by rw [hW0]; exact hul.1)]
    exact realRevMap_congr_drive' heq _
  have hFv : Fm t ht v p.2 = realRevMap V t v := by
    rw [Fm_eq_realRevMap ht ((congrArg (fun S => (v : ℝ) ∈ S) hlive).mpr hvl).2
      (show (v : ℝ) < W 0 by rw [hW0]; exact hvl.1)]
    exact realRevMap_congr_drive' heq _
  simp only [LP, RP] at hLR
  rw [gM_Ioo_eq hC, qBoundaryMeasureOn_congr_full hZ,
    LocalRule.qBoundaryMeasureOn_addConst (x := Z) hrawZ _ _ isOpen_Ioo, Measure.smul_apply,
    gM, if_pos hC1, qBoundaryMeasure_congr_full hF,
    LocalRule.qBoundaryMeasure_addConst' hraws, Measure.smul_apply, hFu, hFv,
    smul_eq_mul, smul_eq_mul] at hLR
  exact (ENNReal.mul_right_inj (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top).1 hLR

/-- **Extended fixed-time windows at all positive rational times** (outer real line included). -/
theorem ae_windows_rat_ext (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ r : ℚ, (0 : ℝ) < r → (r : ℝ) ≤ T → ∀ u v : ℚ,
      (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - r) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u v) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ r B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - r) u) (realRevMap (Vr κ T B ω) (T - r) v)) := by
  refine ae_all_iff.2 fun r => ?_
  by_cases h : (0 : ℝ) < r ∧ (r : ℝ) ≤ T
  · filter_upwards [ae_hcc_ext hκ hκ4 hB hX hind h.1 h.2,
      ae_window_h0_eq_qBoundaryMeasureOn RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4
        hB hX hind h.1.le h.2 hT] with ω hc hw _ _ u v huv hv
    rw [hw]
    exact hc u v huv hv
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h

omit [IsProbabilityMeasure P] in
theorem gamma_lt_two_of_kappa (hκ4 : κ < 4) : Real.sqrt κ < 2 :=
  (Real.sqrt_lt' (by norm_num)).2 (by norm_num; linarith)

/-- **Time `0`**: a.s. the approximations of `h⁰_0` have a global atomless vague limit. -/
theorem ae_zero_time_atomless (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ 0 B X ω)) ν ∧
      ∀ x, ν {x} = 0 := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  filter_upwards [ae_coordsFull_h0f_zero (κ := κ) hB hX,
    AtomlessUncond.ae_gamma0_logSingularity hX hκ hκ4,
    AtomlessUncond.ae_noAtoms_free' hX hγ (gamma_lt_two_of_kappa hκ4)] with ω hcf hg hna
  rw [Factorization.bdryApprox_congr (avgReg_congr_full hcf)]
  refine ⟨_, hg.1, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; exact hg.2.2
  rw [hg.2.1, withDensity_apply _ (measurableSet_singleton x)]
  have h0 : ((qBoundaryMeasure (Real.sqrt κ) (X ω)).restrict {0}ᶜ).restrict {x} = 0 := by
    rw [Measure.restrict_eq_zero]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (measure_singleton x).le)
  rw [h0, lintegral_zero_measure]

end RegUnif
end QuantumZipper
