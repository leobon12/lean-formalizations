import QuantumZipper.Proofs.Zipper.B5VHccInd
import QuantumZipper.Proofs.Zipper.B5VBridge
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# B5V-HCC: the coordinate-change windows of `h⁰_s` (the hypothesis `hcc` of B5-V)

Task B5V-HCC (`handoff/B5.md`, B5V-FIX, "Remaining (R1-TR)").

* `ae_mem_eqP_data`: the window event `eqP` holds a.s. along the data
  `(coordsFull (nrm Y_t), V|[0,t])`. By B2 (`B2.b2_markov`) the two components are independent and
  the first has the law of `coordsFull (nrm (𝔥₀ + X))`; for each fixed path the event holds a.s.
  (`ae_mem_eqP_fixed`), so it holds a.s. for the product law (Fubini/Tonelli, `Measure.ae_ae_comm`).
* **`ae_hcc`**: the hypothesis `hcc` of `B5.ae_b5v_fixed_of_coordChange`, proved.
* **`ae_b5v_fixed_pos`**: B5-V at a fixed time `s ∈ (0,T]`, unconditional.

Source: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68) (the coordinate-change rule
applied to the independent pair `(h⁰_s, V|[0,t])`). The transfer is **own bookkeeping**, following
the E1-TR/M4 device (`E1.aemeasurable_Hf1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open E1 E1.M4 CoordsFull Collision B1Full B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The data of the transfer: circle coordinates of `nrm Y_t` and the continuous version of the
stopped driver. -/
def dataH (κ T t : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) : DP t :=
  (coordsFull (nrm (Yf κ T t B X ω)), extC t (Vstop κ T t B ω))

/-- **Transfer**: the window event holds a.s. along the data. -/
theorem ae_mem_eqP_data (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 ≤ t)
    (htT : t < T) {u v : ℝ} (huv : u < v) :
    ∀ᵐ ω ∂P, dataH κ T t B X ω ∈ eqP κ ht u v := by
  obtain ⟨hI, hL, -⟩ := b2_markov hκ hB hX hind ht htT
  set L := fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω with hLdef
  set L0 := fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω with hL0def
  set D := fun ω => (Vstop κ T t B ω, W0p κ T B ω) with hDdef
  have hg : Measurable (Prod.map (id : (ℕ → ℝ) × (TestFun H → ℝ) → _) (splitAt t)) :=
    measurable_id.prodMap (measurable_splitAt t)
  have hfg : AEMeasurable (fun ω => (L ω, D ω)) P := by
    rw [hLdef, hDdef, data_eq_comp ht htT.le]
    exact hg.comp_aemeasurable (aemeasurable_data_unzip hB hX hind (sub_pos.2 htT).le)
  have hL0m : AEMeasurable L0 P := (aemeasurable_data0 (κ := κ) hB hX).fst
  have hf2 : Measurable fun d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => extC t d.1 :=
    (measurable_extC t).comp measurable_fst
  have hD1 : AEMeasurable (fun ω => (L ω).1) P := measurable_fst.comp_aemeasurable hfg.fst
  have hD2 : AEMeasurable (fun ω => extC t (D ω).1) P := hf2.comp_aemeasurable hfg.snd
  have hI' : IndepFun (fun ω => (L ω).1) (fun ω => extC t (D ω).1) P :=
    hI.comp measurable_fst hf2
  have hLm : AEMeasurable L P := hfg.fst
  have hlaw : P.map (fun ω => (L ω).1) = P.map (fun ω => (L0 ω).1) := by
    calc P.map (fun ω => (L ω).1) = (P.map L).map Prod.fst :=
          (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hLm).symm
      _ = (P.map L0).map Prod.fst := by rw [hL]
      _ = _ := AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hL0m
  have hprod : P.map (dataH κ T t B X) =
      (P.map fun ω => (L0 ω).1).prod (P.map fun ω => extC t (D ω).1) := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hD1 hD2).1 hI'
  have hDm : AEMeasurable (dataH κ T t B X) P := hD1.prodMk hD2
  have hE := measurableSet_eqP κ ht u v
  refine (ae_map_iff hDm hE).1 ?_
  rw [hprod]
  refine ae_iff.2 ?_
  show ((P.map fun ω => (L0 ω).1).prod (P.map fun ω => extC t (D ω).1)) (eqP κ ht u v)ᶜ = 0
  rw [Measure.prod_apply_symm hE.compl]
  refine (lintegral_congr fun w => ?_).trans lintegral_zero
  have h := ae_mem_eqP_fixed hκ hκ4 hX ht w huv
  rw [ae_iff] at h
  have hm : AEMeasurable (fun ω => (L0 ω).1) P := measurable_fst.comp_aemeasurable hL0m
  rw [Measure.map_apply_of_aemeasurable hm (measurable_prodMk_right hE.compl)]
  exact h

/-- At time `0` every negative point is live. -/
theorem isLive_zero_time {W : ℝ → ℝ} (hW : Continuous W) {x : ℝ} (hx : x < W 0) :
    IsLive W 0 x := by
  refine (isLive_iff_exists hW le_rfl).2 ⟨fun _ => x - W 0, continuousOn_const, fun r hr => ?_⟩
  have hr0 : r = 0 := le_antisymm hr.2 hr.1
  subst hr0
  refine ⟨sub_ne_zero.2 hx.ne, ?_⟩
  simp

/-- A point left of `0₋(t)` is live and negative at time `t`. -/
theorem mem_liveNeg_of_lt_zeroMinus {V : ℝ → ℝ} (hVc : Continuous V) (hV0 : V 0 = 0) {T : ℝ}
    (hT : 0 < T) (hK : IsSimpleCurveHull (revHull V T)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {v : ℝ} (hv : v < zeroMinus V t) : v ∈ liveNeg V t := by
  rcases ht.eq_or_lt with h | h
  · subst h
    have hv0 : v < 0 := by rwa [zeroMinus_zero_time hVc hV0] at hv
    exact ⟨hv0, isLive_zero_time hVc (by rw [hV0]; exact hv0)⟩
  · exact ⟨hv.trans (zeroMinus_neg_of_le hVc hV0 hT hK h htT),
      ofReal_lt_realHitTime hVc hV0 hT hK h htT hv⟩

theorem realRevMap_congr_drive' {w w' : ℝ → ℝ} {t : ℝ} (h : EqOn w w' (Icc 0 t)) (x : ℝ) :
    realRevMap w t x = realRevMap w' t x := by
  have hP : IsRealRevSol w x t = IsRealRevSol w' x t :=
    funext fun u => propext (isRealRevSol_congr_drive h)
  unfold realRevMap
  rw [hP]

omit [IsProbabilityMeasure P] in
theorem addConst_neg_zero (x : FieldSample) : addConst x (-0) = x := by
  funext μ; simp [addConst]

/-- **`hcc` of `B5.ae_b5v_fixed_of_coordChange`**, proved. -/
theorem ae_hcc (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) :
    ∀ᵐ ω ∂P, ∀ u v : ℚ, zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v →
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
  · exact Eventually.of_forall fun ω _ h => absurd h huv
  filter_upwards [ae_mem_eqP_data hκ hκ4 hB hX hind ht htT huv, hB.cont,
    b2_coordsFull_eq (κ := κ) hB hX hind ht htT.le,
    ae_rawConverges_h0f (κ := κ) hB hX hind hT.le, ae_rawConverges_h0f (κ := κ) hB hX hind hs.le,
    ae_bCert_h0f hReg hκ hκ4 hT hB hX hind 0, ae_bCert_h0f hReg hκ hκ4 hs hB hX hind 0,
    ae_all_iff.2 (ae_regShift_Yf_fc κ hB hX hind ht htT.le),
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hE hc hcf hrawT hraws hbT hbs hrs hK _ _ hv
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

/-- **B5-V at a fixed time `s ∈ (0,T]`**, unconditional. -/
theorem ae_b5v_fixed_pos (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) :
    ∀ᵐ ω ∂P, (unzipLengths (Real.sqrt κ) (cfg κ B X ω) s).1 = lenRHS κ T B X ω s :=
  ae_b5v_fixed_of_coordChange RevCouplingReg.revCouplingBoundaryMeasureRegular
    RS.rohdeSchrammSimple hκ hκ4 hB hX hind hs hsT (ae_hcc hκ hκ4 hB hX hind hs hsT)

end B5
end QuantumZipper
