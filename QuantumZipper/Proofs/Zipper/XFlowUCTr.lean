import QuantumZipper.Proofs.Zipper.XFlowUCSplit
import QuantumZipper.Proofs.Zipper.UnifUCTr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC: transfer of the `Γ⁰` node from a fixed Hölder driver to the Brownian driver

**Main result** `xFlowGamUCQStmt_of_fixed : XFlowFixedUCQAllStmt → XFlowGamUCQStmt`.

This is the D33 transfer `RegUnif.unifUCStmt_of_fixedUCStmt` (`UnifUCTr.lean`) with the circle
parameters `(d, r)` free: the jointly measurable proxy `PWf` is `RegUnif.PWm` with the dyadic
circle `fc(d, 2^{-k})` replaced by `fc(d, r)` (same `AvgQ`, `Rm`, circle parametrization), it
agrees with `flowPhiY` along the driver of a good path (`PWf_eq_flowPhiY`), `flowPhiY` depends on
the driver only through `[0, T]` (`flowPhiY_congr_drive`), and conditioning on the independent
path (`CharFun.ae_indep`) turns the fixed-driver statement into the Brownian one.

Sources: as `UnifUCTr.lean` (Sheffield, arXiv:1012.4797, Lemma 5.6; Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)). Own bookkeeping.
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open CharFun TwoPoint RegCont MeasUnzip UnzipInvariance RegUnif

/-- **(Fixed-driver `Γ⁰` node.)** For a Hölder driver on `[0, 2m+2]`, a.s. in the field, the
`Γ⁰` pairings are uniformly Cauchy at the rational points of `flowBox m`. -/
def XFlowFixedUCQStmt (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W (2 * (m : ℝ) + 2) a CH →
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
        |flowPhiY κ (X ω) W j (flowQ q) - flowPhiY κ (X ω) W j' (flowQ q)| ≤ 1 / ((n : ℝ) + 1)

/-- The fixed-driver node for every free field. -/
def XFlowFixedUCQAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → XFlowFixedUCQStmt κ P X

section Proxy

variable {T : ℝ} (hT : 0 ≤ T)

/-- The jointly measurable proxy of `flowPhiY` (`RegUnif.PWm` with a general circle). -/
def PWf (κ : ℝ) (d : ℂ) (r : ℝ) (j : ℕ) (u s : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  ∫ θ, AvgQ hT κ (Real.sqrt κ) u j (p, Rm hT κ u s p (foldH (circleMap d r θ))) ∂circLeb

set_option maxHeartbeats 1000000 in
-- as `RegUnif.measurable_PWm`: the `whnf` steps unfold the nested integral proxy
theorem measurable_PWf (κ : ℝ) (d : ℂ) (r : ℝ) (j : ℕ) (u s : ℝ) :
    Measurable (PWf hT κ d r j u s) := by
  have hG : Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ =>
      AvgQ hT κ (Real.sqrt κ) u j (z.1, Rm hT κ u s z.1
        (foldH (circleMap d r z.2))) :=
    (measurable_AvgQ hT κ (Real.sqrt κ) u j).comp (measurable_id.fst.prodMk
      ((measurable_Rm hT κ u s).comp (measurable_id.fst.prodMk
        (measurable_foldH.comp ((measurable_circleMap d r).comp measurable_id.snd)))))
  exact (StronglyMeasurable.integral_prod_right' hG.stronglyMeasurable).measurable

/-- **Agreement of the proxy with `flowPhiY`** along the driver of a good path. -/
theorem PWf_eq_flowPhiY {κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT (1 / 3))
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) (d : ℂ) (r : ℝ) (j : ℕ)
    (x : FieldSample) :
    PWf hT κ d r j u s (f, x) = flowPhiY κ x (Wof κ T hT f) j (u, s, d, r) := by
  have hf0 : Wof κ T hT f 0 = 0 := Wof_zero_of_GoodP hT κ hf
  have hfpz : f ∈ PZ hT κ := hf0
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, by linarith⟩
  have hR : Measurable (revMap (B2.vrev (Wof κ T hT f) (u + s)) s) :=
    measurable_revMap_vrev hT κ hu hs hus f
  have hF : Measurable fun z : ℂ =>
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z :=
    RegClosure.measurable_avgReg_slice _ j
  rw [PWf]
  show _ = ∫ z, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z
    ∂(foldedCircle d r).map (revMap (B2.vrev (Wof κ T hT f) (u + s)) s)
  rw [integral_map_foldedCircle_eq (fun z => avgReg (unzippedField (Real.sqrt κ)
    (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z) hF hR d r]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show AvgQ hT κ (Real.sqrt κ) u j ((f, x), Rm hT κ u s (f, x) (foldH (circleMap d r θ))) =
    avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u) j
      (revMap (B2.vrev (Wof κ T hT f) (u + s)) s (foldH (circleMap d r θ)))
  rw [AvgQ_eq_avgReg hT hfpz huT (Real.sqrt κ) j x, Rm_eq_revMap hT κ hu hs hus f x]

end Proxy

/-- **`flowPhiY` depends on the driver only through its values on `[0,T]`.** -/
theorem flowPhiY_congr_drive (κ : ℝ) {T : ℝ} {W W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hEq : EqOn W W' (Icc (0 : ℝ) T))
    (d : ℂ) (r : ℝ) (j : ℕ) (x : FieldSample) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hus : u + s ≤ T) :
    flowPhiY κ x W j (u, s, d, r) = flowPhiY κ x W' j (u, s, d, r) := by
  have hrev : ∀ t ∈ Icc (0 : ℝ) s, B2.vrev W (u + s) t = B2.vrev W' (u + s) t := by
    intro t ht
    have h1 : min (max t 0) (u + s) = t := by
      rw [max_eq_left ht.1, min_eq_left (by linarith [ht.2, hs])]
    simp only [B2.vrev, h1]
    have ht1 : (0 : ℝ) ≤ t := ht.1
    have ht2 : t ≤ s := ht.2
    rw [show W (u + s - t) = W' (u + s - t) from hEq ⟨by linarith, by linarith⟩,
      show W (u + s) = W' (u + s) from hEq ⟨by linarith, hus⟩]
  have hfu : ∀ z : ℂ, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j z =
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W') u) j z := by
    intro z
    simp only [avgReg, unzippedField]
    refine congrArg (limUnder atTop) (funext fun n => ?_)
    exact coordChange_congr_of_eqOn (fwdMapInv_congr hW hW0 hW' hW'0 hEq ⟨hu, by linarith⟩)
      (ae_iff.1 (foldedCircle_ae_mem_H (dyadicRoundC n z) (radius_pos j))) _ _
  unfold flowPhiY flowNu
  simp only
  rw [Measure.map_congr (Filter.Eventually.of_forall fun w =>
    ReverseFlow.revMap_congr_drive w hrev)]
  exact congrArg (fun F : ℂ → ℝ => ∫ z, F z ∂(foldedCircle d r).map
    (revMap (B2.vrev W' (u + s)) s)) (funext hfu)

/-! ## The transfer -/

section Transfer

variable {T : ℝ} (hT : 0 ≤ T)

/-- The measurable event: the path is not good, or the proxy is uniformly Cauchy at the
rational points of `flowBox m`. -/
def UCsetF (κ : ℝ) (m : ℕ) : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
  {p | p.1 ∉ GoodP hT (1 / 3)} ∪
    {p | ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
        |PWf hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 j (flowQ q).1 (flowQ q).2.1 p -
          PWf hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 j' (flowQ q).1 (flowQ q).2.1 p| ≤
          1 / ((n : ℝ) + 1)}

theorem measurableSet_UCsetF (κ : ℝ) (m : ℕ) : MeasurableSet (UCsetF hT κ m) := by
  have e : UCsetF hT κ m = ((GoodP hT (1 / 3))ᶜ ×ˢ univ) ∪
      ⋂ n : ℕ, ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), ⋂ j' : ℕ, ⋂ (_ : N ≤ j'),
        ⋂ q : ℚ × ℚ × ℚ × ℚ × ℚ, ⋂ (_ : flowQ q ∈ flowBox m),
        {p | |PWf hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 j (flowQ q).1 (flowQ q).2.1 p -
          PWf hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 j' (flowQ q).1 (flowQ q).2.1 p| ≤
          1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [UCsetF, mem_union, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_prod, mem_compl_iff,
      mem_univ, and_true]
  rw [e]
  refine ((measurableSet_GoodP hT (1 / 3)).compl.prod MeasurableSet.univ).union ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp
    ((measurable_PWf hT κ _ _ j _ _).sub (measurable_PWf hT κ _ _ j' _ _))) measurable_const

end Transfer

/-- **`XFlowFixedUCQAllStmt ⇒ XFlowGamUCQStmt`** (conditioning on the Brownian path). -/
theorem xFlowGamUCQStmt_of_fixed (hfix : XFlowFixedUCQAllStmt) : XFlowGamUCQStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind m
  set T : ℝ := 2 * (m : ℝ) + 2 with hTdef
  have hT' : 0 < T := by positivity
  have hT0 : 0 ≤ T := hT'.le
  have hbox : ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
      0 ≤ (flowQ q).1 ∧ 0 ≤ (flowQ q).2.1 ∧ (flowQ q).1 + (flowQ q).2.1 ≤ T := by
    intro q hq
    exact ⟨hq.1.1, hq.2.1.1, by linarith [hq.1.2, hq.2.1.2]⟩
  have hfib : ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P, (f, X ω) ∈ UCsetF hT0 κ m := by
    intro f
    by_cases hf : f ∈ GoodP hT0 (1 / 3)
    · obtain ⟨C, hC⟩ := hf.2
      have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hf
      have hdrv : HolderDrv (Wof κ T hT0 f) T (1 / 3) (Real.sqrt κ * C) :=
        ⟨continuous_Wof κ T hT0 f, hf0, by norm_num, by norm_num, by positivity,
          Wof_holder hT0 κ hC⟩
      filter_upwards [hfix κ hκ hκ4 P X hX m (Wof κ T hT0 f) (1 / 3) (Real.sqrt κ * C) hdrv]
        with ω hω
      refine Or.inr fun n => ?_
      obtain ⟨N, hN⟩ := hω n
      refine ⟨N, fun j hj j' hj' q hq => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hbox q hq
      rw [PWf_eq_flowPhiY hT0 hf h1 h2 h3, PWf_eq_flowPhiY hT0 hf h1 h2 h3]
      exact hN j hj j' hj' q hq
    · exact ae_of_all _ fun ω => Or.inl hf
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind'
    (measurableSet_UCsetF hT0 κ m) hfib
  filter_upwards [hE, ae_pathC_good hB hB'c hB'eq hT', hB'eq] with ω hω hgood heq
  set f := pathC T B' hB'c ω with hfdef
  have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := drive_facts κ hB'c hT' heq hf0
  rcases hω with hbad | huc
  · exact absurd hgood hbad
  intro n
  obtain ⟨N, hN⟩ := huc n
  refine ⟨N, fun j hj j' hj' q hq => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hbox q hq
  have hconv : ∀ jj : ℕ, flowPhiY κ (X ω) (drive κ B ω) jj (flowQ q) =
      PWf hT0 κ (flowQ q).2.2.1 (flowQ q).2.2.2 jj (flowQ q).1 (flowQ q).2.1 (f, X ω) := by
    intro jj
    rw [PWf_eq_flowPhiY hT0 hgood h1 h2 h3]
    exact flowPhiY_congr_drive κ hdc hd0 (continuous_Wof κ T hT0 f) hf0 hEq _ _ jj (X ω) h1 h2 h3
  rw [hconv j, hconv j']
  exact hN j hj j' hj' q hq

end F1
end QuantumZipper
