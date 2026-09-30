import QuantumZipper.Proofs.Zipper.ZipLen2ContDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: transfer to the Brownian driver

`FlowFixedUCcStmt` (every fixed Hölder driver) implies `FlowBrownUCcStmt` (the Brownian driver),
by conditioning on the Brownian path. This is `F1.xFlowGamUCQStmt_of_fixed` (XFlowUCTr.lean)
with the dyadic scale `j` replaced by rational radii `ρ`: the jointly measurable proxy of
`flowPhiYc` is `PWc`, built from the proxy `AvgQ` of `avgReg` through the definition of
`evalReg` as a limit. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open F1 CharFun TwoPoint RegCont MeasUnzip UnzipInvariance RegUnif

section Proxy

variable {T : ℝ} (hT : 0 ≤ T)

/-- Proxy of `evalReg y_u (fc(z, ρ))`, jointly measurable in `((path, field), z)`. -/
def EvQ (κ : ℝ) (u ρ : ℝ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ) : ℝ :=
  limUnder atTop fun k : ℕ => ∫ w, AvgQ hT κ (Real.sqrt κ) u k (q.1, w) ∂foldedCircle q.2 ρ

theorem measurable_EvQ (κ u ρ : ℝ) : Measurable (EvQ hT κ u ρ) :=
  (StronglyMeasurable.limUnder fun k =>
    (measurable_integral_foldedCircle (measurable_AvgQ hT κ (Real.sqrt κ) u k) ρ
      ).stronglyMeasurable).measurable

/-- Proxy of `flowPhiYc`. -/
def PWc (κ : ℝ) (d : ℂ) (r ρ : ℝ) (u s : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  ∫ θ, EvQ hT κ u ρ (p, Rm hT κ u s p (foldH (circleMap d r θ))) ∂circLeb

set_option maxHeartbeats 1000000 in
-- as `F1.measurable_PWf`
theorem measurable_PWc (κ : ℝ) (d : ℂ) (r ρ : ℝ) (u s : ℝ) :
    Measurable (PWc hT κ d r ρ u s) := by
  have hG : Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ =>
      EvQ hT κ u ρ (z.1, Rm hT κ u s z.1 (foldH (circleMap d r z.2))) :=
    (measurable_EvQ hT κ u ρ).comp (measurable_id.fst.prodMk
      ((measurable_Rm hT κ u s).comp (measurable_id.fst.prodMk
        (measurable_foldH.comp ((measurable_circleMap d r).comp measurable_id.snd)))))
  exact (StronglyMeasurable.integral_prod_right' hG.stronglyMeasurable).measurable

theorem EvQ_eq_evalReg {κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) (ρ : ℝ) (x : FieldSample) (z : ℂ) :
    EvQ hT κ u ρ ((f, x), z) =
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u)
        (foldedCircle z ρ) := by
  unfold EvQ evalReg
  simp only [AvgQ_eq_avgReg hT hf hu]

/-- **Agreement of the proxy with `flowPhiYc`** along the driver of a good path. -/
theorem PWc_eq_flowPhiYc {κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT (1 / 3))
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) (d : ℂ) (r ρ : ℝ)
    (x : FieldSample) :
    PWc hT κ d r ρ u s (f, x) = flowPhiYc κ x (Wof κ T hT f) ρ (u, s, d, r) := by
  have hf0 : Wof κ T hT f 0 = 0 := Wof_zero_of_GoodP hT κ hf
  have hfpz : f ∈ PZ hT κ := hf0
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, by linarith⟩
  have hR : Measurable (revMap (B2.vrev (Wof κ T hT f) (u + s)) s) :=
    measurable_revMap_vrev hT κ hu hs hus f
  have hF : Measurable fun z : ℂ =>
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u)
        (foldedCircle z ρ) := by
    unfold evalReg
    exact (StronglyMeasurable.limUnder fun k =>
      ((measurable_integral_foldedCircle (α := Unit)
        (G := fun q : Unit × ℂ => avgReg (unzippedField (Real.sqrt κ)
          (ofFun (h0rev κ) + x, Wof κ T hT f) u) k q.2)
        ((RegClosure.measurable_avgReg_slice _ k).comp measurable_snd) ρ).comp
        ((measurable_const : Measurable fun _ : ℂ => ()).prodMk measurable_id)).stronglyMeasurable).measurable
  rw [PWc]
  show _ = ∫ z, evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u)
    (foldedCircle z ρ) ∂(foldedCircle d r).map (revMap (B2.vrev (Wof κ T hT f) (u + s)) s)
  rw [integral_map_foldedCircle_eq _ hF hR d r]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show EvQ hT κ u ρ ((f, x), Rm hT κ u s (f, x) (foldH (circleMap d r θ))) = _
  rw [EvQ_eq_evalReg hT hfpz huT ρ x, Rm_eq_revMap hT κ hu hs hus f x]

end Proxy

/-- **`flowPhiYc` depends on the driver only through its values on `[0,T]`.** -/
theorem flowPhiYc_congr_drive (κ : ℝ) {T : ℝ} {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hEq : EqOn W W' (Icc (0 : ℝ) T))
    (d : ℂ) (r ρ : ℝ) (x : FieldSample) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hus : u + s ≤ T) :
    flowPhiYc κ x W ρ (u, s, d, r) = flowPhiYc κ x W' ρ (u, s, d, r) := by
  have hrev : ∀ t ∈ Icc (0 : ℝ) s, B2.vrev W (u + s) t = B2.vrev W' (u + s) t := by
    intro t ht
    have h1 : min (max t 0) (u + s) = t := by
      rw [max_eq_left ht.1, min_eq_left (by linarith [ht.2, hs])]
    simp only [B2.vrev, h1]
    have ht1 : (0 : ℝ) ≤ t := ht.1
    have ht2 : t ≤ s := ht.2
    rw [show W (u + s - t) = W' (u + s - t) from hEq ⟨by linarith, by linarith⟩,
      show W (u + s) = W' (u + s) from hEq ⟨by linarith, hus⟩]
  have hfu : ∀ j : ℕ, ∀ z : ℂ,
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j z =
        avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W') u) j z := by
    intro j z
    simp only [avgReg, unzippedField]
    refine congrArg (limUnder atTop) (funext fun n => ?_)
    exact coordChange_congr_of_eqOn (fwdMapInv_congr hW hW0 hW' hW'0 hEq ⟨hu, by linarith⟩)
      (ae_iff.1 (foldedCircle_ae_mem_H (dyadicRoundC n z) (radius_pos j))) _ _
  have hev : ∀ z : ℂ,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) (foldedCircle z ρ) =
        evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W') u)
          (foldedCircle z ρ) := by
    intro z
    unfold evalReg
    simp only [hfu]
  unfold flowPhiYc flowNu
  simp only
  rw [Measure.map_congr (Filter.Eventually.of_forall fun w =>
    ReverseFlow.revMap_congr_drive w hrev)]
  exact congrArg (fun F : ℂ → ℝ => ∫ z, F z ∂(foldedCircle d r).map
    (revMap (B2.vrev W' (u + s)) s)) (funext hev)

/-! ## The transfer -/

section Transfer

variable {T : ℝ} (hT : 0 ≤ T)

/-- The measurable event: the path is not good, or the proxy is Cauchy along rational radii,
uniformly at the rational points of `flowBox m`. -/
def UCsetC (κ : ℝ) (m : ℕ) : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
  {p | p.1 ∉ GoodP hT (1 / 3)} ∪
    {p | ∀ n : ℕ, ∃ N : ℕ, ∀ ρ ρ' : ℚ, 0 < ρ → (ρ : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      0 < ρ' → (ρ' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
        |PWc hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 ρ (flowQ q).1 (flowQ q).2.1 p -
          PWc hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 ρ' (flowQ q).1 (flowQ q).2.1 p| ≤
          1 / ((n : ℝ) + 1)}

theorem measurableSet_UCsetC (κ : ℝ) (m : ℕ) : MeasurableSet (UCsetC hT κ m) := by
  have e : UCsetC hT κ m = ((GoodP hT (1 / 3))ᶜ ×ˢ univ) ∪
      ⋂ n : ℕ, ⋃ N : ℕ, ⋂ ρ : ℚ, ⋂ ρ' : ℚ, ⋂ (_ : 0 < ρ),
        ⋂ (_ : (ρ : ℝ) ≤ 1 / ((N : ℝ) + 1)), ⋂ (_ : 0 < ρ'),
        ⋂ (_ : (ρ' : ℝ) ≤ 1 / ((N : ℝ) + 1)),
        ⋂ q : ℚ × ℚ × ℚ × ℚ × ℚ, ⋂ (_ : flowQ q ∈ flowBox m),
        {p | |PWc hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 ρ (flowQ q).1 (flowQ q).2.1 p -
          PWc hT κ (flowQ q).2.2.1 (flowQ q).2.2.2 ρ' (flowQ q).1 (flowQ q).2.1 p| ≤
          1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [UCsetC, mem_union, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_prod,
      mem_compl_iff, mem_univ, and_true]
  rw [e]
  refine ((measurableSet_GoodP hT (1 / 3)).compl.prod MeasurableSet.univ).union ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iInter
    fun ρ => MeasurableSet.iInter fun ρ' => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp
    ((measurable_PWc hT κ _ _ _ _ _).sub (measurable_PWc hT κ _ _ _ _ _))) measurable_const

end Transfer

/-- **`FlowFixedUCcStmt ⇒ FlowBrownUCcStmt`** (conditioning on the Brownian path). -/
theorem flowBrownUCc_of_fixed
    (hfix : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : Ω → FieldSample), IsFreeGFFModConstH X P →
      FlowFixedUCcStmt κ P X)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    FlowBrownUCcStmt κ P B X := by
  intro m
  set T : ℝ := 2 * (m : ℝ) + 2 with hTdef
  have hT' : 0 < T := by positivity
  have hT0 : 0 ≤ T := hT'.le
  have hbox : ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
      0 ≤ (flowQ q).1 ∧ 0 ≤ (flowQ q).2.1 ∧ (flowQ q).1 + (flowQ q).2.1 ≤ T := by
    intro q hq
    exact ⟨hq.1.1, hq.2.1.1, by linarith [hq.1.2, hq.2.1.2]⟩
  have hfib : ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P, (f, X ω) ∈ UCsetC hT0 κ m := by
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
      refine ⟨N, fun ρ ρ' h1 h2 h3 h4 q hq => ?_⟩
      obtain ⟨b1, b2, b3⟩ := hbox q hq
      rw [PWc_eq_flowPhiYc hT0 hf b1 b2 b3, PWc_eq_flowPhiYc hT0 hf b1 b2 b3]
      exact hN ρ ρ' h1 h2 h3 h4 q hq
    · exact ae_of_all _ fun ω => Or.inl hf
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind'
    (measurableSet_UCsetC hT0 κ m) hfib
  filter_upwards [hE, ae_pathC_good hB hB'c hB'eq hT', hB'eq] with ω hω hgood heq
  set f := pathC T B' hB'c ω with hfdef
  have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := drive_facts κ hB'c hT' heq hf0
  rcases hω with hbad | huc
  · exact absurd hgood hbad
  intro n
  obtain ⟨N, hN⟩ := huc n
  refine ⟨N, fun ρ ρ' h1 h2 h3 h4 q hq => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hbox q hq
  have hconv : ∀ ρρ : ℚ, flowPhiYc κ (X ω) (drive κ B ω) ρρ (flowQ q) =
      PWc hT0 κ (flowQ q).2.2.1 (flowQ q).2.2.2 ρρ (flowQ q).1 (flowQ q).2.1 (f, X ω) := by
    intro ρρ
    rw [PWc_eq_flowPhiYc hT0 hgood b1 b2 b3]
    exact flowPhiYc_congr_drive κ hdc hd0 (continuous_Wof κ T hT0 f) hf0 hEq _ _ _ (X ω)
      b1 b2 b3
  rw [hconv ρ, hconv ρ']
  exact hN ρ ρ' h1 h2 h3 h4 q hq

end ZipLen
end B3d
end QuantumZipper
