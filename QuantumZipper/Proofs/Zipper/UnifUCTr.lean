import QuantumZipper.Proofs.Zipper.UnifUCTrBasic

/-!
# UNIF-RC3-TR (2/2): `FixedUCStmt ⇒ UnifUCStmt`

Task UNIF-RC3-TR (decision D33). The proxy `PWm` of `UnifUCTrBasic` agrees with `PhiW` along a
driver `Wof κ T hT f` with `f ∈ GoodP` (`PWm_eq_PhiW`): on `[0,s]` the reversed driver
`vrev (Wof κ T hT f) (u+s)` of the pushed circle is `Wof κ s hs (revPathUS f)` (`Rm_eq_revMap`),
and the unzipped field is the jointly measurable `unzRawJ` (`unzRawJ_eq`). The regularized
values `PhiW` only depend on the driver through its values on `[0,T]`
(`PhiW_congr_drive`), so the measurable event

`{p | p.1 ∉ GoodP} ∪ {p | PWm is uniformly Cauchy on triQ T}`

holds almost surely in the field for **every** fixed path (the fixed-driver hypothesis
`FixedUCStmt`), and `CharFun.ae_indep` transfers it to the Brownian driver, giving
**`unifUCStmt_of_fixedUCStmt : FixedUCStmt κ T P X → UnifUCStmt κ T P B X`**, whence
`capCocycleRegStmt_of_uc`.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through `CoordRegComp`);
Sheffield, arXiv:1012.4797, Lemma 5.6 (conditioning on the independent driver, as
`B5.ae_mem_eqP_data` / `RegUnif.ae_dataH_mem_of_fixed`); Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)
(Brownian paths are `1/3`-Hölder, `RS.bm_holder`). The transfer device is own bookkeeping.
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont MeasUnzip B2 UnzipInvariance

variable {T : ℝ} (hT : 0 ≤ T)

/-! ## Agreement of the proxy with `PhiW` along a fixed good path -/

/-- The reversed driver of the pushed circle is the driver of the reversed path at time `u+s`. -/
theorem Rm_eq_revMap (κ : ℝ) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T)
    (f : C(Icc (0 : ℝ) T, ℝ)) (x : FieldSample) (w : ℂ) :
    Rm hT κ u s (f, x) w = revMap (vrev (Wof κ T hT f) (u + s)) s w := by
  have huS : 0 ≤ u + s := add_nonneg hu hs
  have hmain := ReverseFlow.revMap_congr_drive w (W := Wof κ s hs (revPathUS hT u s huS f))
    (W' := B2.vrev (Wof κ T hT f) (u + s)) (T := s) ?_
  · unfold Rm
    rw [dite_eq_left (show 0 ≤ u ∧ 0 ≤ s from ⟨hu, hs⟩)]
    exact hmain
  intro r hr
  have h1 : min (max r 0) (u + s) = r := by
    rw [max_eq_left hr.1, min_eq_left (by linarith [hr.2, hs])]
  simp only [Wof, revPathUS, ContinuousMap.coe_mk, B2.vrev, h1, projIcc_of_mem hs hr]
  have hr1 : (0 : ℝ) ≤ r := hr.1
  have hr2 : r ≤ s := hr.2
  rw [projIcc_of_mem hT (show u + s - r ∈ Icc (0 : ℝ) T from
      ⟨by linarith, by linarith⟩),
    projIcc_of_mem hT (show u + s ∈ Icc (0 : ℝ) T from ⟨by linarith, hus⟩)]
  ring_nf

set_option maxHeartbeats 1000000 in
/-- The reverse map of the pushed circle is measurable in the point (as a function of the
driver path, through the jointly measurable reverse flow). -/
theorem measurable_revMap_vrev (κ : ℝ) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T)
    (f : C(Icc (0 : ℝ) T, ℝ)) :
    Measurable (revMap (vrev (Wof κ T hT f) (u + s)) s) := by
  have heq : revMap (vrev (Wof κ T hT f) (u + s)) s = fun w => Rm hT κ u s (f, 0) w :=
    funext fun w => (Rm_eq_revMap hT κ hu hs hus f 0 w).symm
  rw [heq]
  exact (measurable_Rm hT κ u s).comp (measurable_const.prodMk measurable_id)

/-- **The proxy is the regularized value.** For a path in `PZ`, `AvgQ` is `avgReg` of the
unzipped field. -/
theorem AvgQ_eq_avgReg {κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) (γ : ℝ) (j : ℕ) (x : FieldSample) (z : ℂ) :
    AvgQ hT κ γ u j ((f, x), z) =
      avgReg (unzippedField γ (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z := by
  unfold AvgQ avgReg
  refine congrArg (limUnder atTop) (funext fun n => ?_)
  exact (unzRawJ_eq hT γ κ hf hu (ofFun (h0rev κ) + x)
    (ae_iff.1 (foldedCircle_ae_mem_H (dyadicRoundC n z) (radius_pos j)))).symm

/-- **Unfolded form of `PhiW`** at a pair `(u, s)`. -/
theorem PhiW_apply (κ : ℝ) (W : ℝ → ℝ) (d : ℂ) (k j : ℕ) (x : FieldSample) (u s : ℝ) :
    PhiW κ W d k j x (u, s) = ∫ z, avgReg (unzippedField (Real.sqrt κ)
      (ofFun (h0rev κ) + x, W) u) j z
      ∂(foldedCircle d (radius k)).map (revMap (vrev W (u + s)) s) := rfl

/-- **Agreement of the proxy with `PhiW`** along the driver of a good path. -/
theorem PWm_eq_PhiW {κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT (1 / 3))
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) (d : ℂ) (k j : ℕ)
    (x : FieldSample) :
    PWm hT κ d k j u s (f, x) = PhiW κ (Wof κ T hT f) d k j x (u, s) := by
  have hf0 : Wof κ T hT f 0 = 0 := Wof_zero_of_GoodP hT κ hf
  have hfpz : f ∈ PZ hT κ := hf0
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, by linarith⟩
  have hR : Measurable (revMap (vrev (Wof κ T hT f) (u + s)) s) :=
    measurable_revMap_vrev hT κ hu hs hus f
  have hF : Measurable fun z : ℂ =>
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z :=
    RegClosure.measurable_avgReg_slice _ j
  rw [PWm, PhiW_apply]
  rw [integral_map_foldedCircle_eq (fun z => avgReg (unzippedField (Real.sqrt κ)
    (ofFun (h0rev κ) + x, Wof κ T hT f) u) j z) hF hR d (radius k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show AvgQ hT κ (Real.sqrt κ) u j ((f, x), Rm hT κ u s (f, x)
      (foldH (circleMap d (radius k) θ))) =
    avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, Wof κ T hT f) u) j
      (revMap (vrev (Wof κ T hT f) (u + s)) s (foldH (circleMap d (radius k) θ)))
  rw [AvgQ_eq_avgReg hT hfpz huT (Real.sqrt κ) j x, Rm_eq_revMap hT κ hu hs hus f x]

/-- **`PhiW` depends on the driver only through its values on `[0,T]`.** -/
theorem PhiW_congr_drive (κ : ℝ) {W W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hEq : EqOn W W' (Icc (0 : ℝ) T))
    (d : ℂ) (k j : ℕ) (x : FieldSample) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) :
    PhiW κ W d k j x (u, s) = PhiW κ W' d k j x (u, s) := by
  have hrev : ∀ r ∈ Icc (0 : ℝ) s, B2.vrev W (u + s) r = B2.vrev W' (u + s) r := by
    intro r hr
    have h1 : min (max r 0) (u + s) = r := by
      rw [max_eq_left hr.1, min_eq_left (by linarith [hr.2, hs])]
    simp only [B2.vrev, h1]
    have hr1 : (0 : ℝ) ≤ r := hr.1
    have hr2 : r ≤ s := hr.2
    rw [show W (u + s - r) = W' (u + s - r) from hEq ⟨by linarith, by linarith⟩,
      show W (u + s) = W' (u + s) from hEq ⟨by linarith, hus⟩]
  have hfu : ∀ z : ℂ, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) u) j z =
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W') u) j z := by
    intro z
    simp only [avgReg, unzippedField]
    refine congrArg (limUnder atTop) (funext fun n => ?_)
    exact coordChange_congr_of_eqOn (fwdMapInv_congr hW hW0 hW' hW'0 hEq ⟨hu, by linarith⟩)
      (ae_iff.1 (foldedCircle_ae_mem_H (dyadicRoundC n z) (radius_pos j))) _ _
  unfold PhiW alphaUS
  rw [Measure.map_congr (Filter.Eventually.of_forall fun w =>
    ReverseFlow.revMap_congr_drive w (hrev))]
  exact congrArg (fun F : ℂ → ℝ => ∫ z, F z ∂(foldedCircle d (radius k)).map
    (revMap (B2.vrev W' (u + s)) s)) (funext hfu)

/-! ## The transfer -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- The measurable event: the path is not good, or the proxy is uniformly Cauchy on the
rational points of the triangle at the dyadic circle `(d, 2^{-k})`. -/
def UCset (κ : ℝ) (d : ℂ) (k : ℕ) : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
  {p | p.1 ∉ GoodP hT (1 / 3)} ∪
    {p | ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' → ∀ q : ℚ × ℚ,
      ((q.1 : ℝ), (q.2 : ℝ)) ∈ triQ T →
      |PWm hT κ d k j (q.1 : ℝ) (q.2 : ℝ) p -
        PWm hT κ d k j' (q.1 : ℝ) (q.2 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)}

theorem measurableSet_UCset (κ : ℝ) (d : ℂ) (k : ℕ) : MeasurableSet (UCset hT κ d k) := by
  have e : UCset hT κ d k = ((GoodP hT (1 / 3))ᶜ ×ˢ univ) ∪
      ⋂ n : ℕ, ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), ⋂ j' : ℕ, ⋂ (_ : N ≤ j'),
        ⋂ q : ℚ × ℚ, ⋂ (_ : ((q.1 : ℝ), (q.2 : ℝ)) ∈ triQ T),
        {p | |PWm hT κ d k j (q.1 : ℝ) (q.2 : ℝ) p -
          PWm hT κ d k j' (q.1 : ℝ) (q.2 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [UCset, mem_union, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_prod, mem_compl_iff,
      mem_univ, and_true]
  rw [e]
  refine ((measurableSet_GoodP hT (1 / 3)).compl.prod MeasurableSet.univ).union ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp
    ((measurable_PWm hT κ d k j _ _).sub (measurable_PWm hT κ d k j' _ _))) measurable_const

/-- **The fibre statement**: for every fixed path, the event holds almost surely in the field. -/
theorem ae_UCset_fibre [IsProbabilityMeasure P]
    (hfix : FixedUCStmt κ T P X) (d : ℂ) (k : ℕ) :
    ∀ f : C(Icc (0 : ℝ) T, ℝ), ∀ᵐ ω ∂P, (f, X ω) ∈ UCset hT κ d k := by
  intro f
  by_cases hf : f ∈ GoodP hT (1 / 3)
  · obtain ⟨C, hC⟩ := hf.2
    have hf0 : Wof κ T hT f 0 = 0 := Wof_zero_of_GoodP hT κ hf
    have hdrv : HolderDrv (Wof κ T hT f) T (1 / 3) (Real.sqrt κ * C) :=
      ⟨continuous_Wof κ T hT f, hf0, by norm_num, by norm_num, by positivity, Wof_holder hT κ hC⟩
    filter_upwards [hfix (Wof κ T hT f) (1 / 3) (Real.sqrt κ * C) hdrv d k] with ω hω
    refine Or.inr fun n => ?_
    obtain ⟨N, hN⟩ := hω n
    exact ⟨N, fun j hj j' hj' q hq => by
      rw [PWm_eq_PhiW hT hf hq.1.1 hq.1.2.1 hq.1.2.2 d k j (X ω),
        PWm_eq_PhiW hT hf hq.1.1 hq.1.2.1 hq.1.2.2 d k j' (X ω)]
      exact hN j hj j' hj' _ hq⟩
  · exact ae_of_all _ fun ω => Or.inl hf

/-- **`FixedUCStmt ⇒ UnifUCStmt`** (for the Brownian driver `B`). -/
theorem unifUCStmt_of_fixedUCStmt [IsProbabilityMeasure P] {κ T : ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT' : 0 < T) (hfix : FixedUCStmt κ T P X) : UnifUCStmt κ T P B X := by
  have hT0 : 0 ≤ T := hT'.le
  intro k d hd
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind'
    (measurableSet_UCset hT0 κ d k) (ae_UCset_fibre hT0 hfix d k)
  filter_upwards [hE, ae_pathC_good hB hB'c hB'eq hT', hB'eq, hB.cont] with ω hω hgood heq hc
  have hev : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.eval_zero_ae_eq_zero
  set f := pathC T B' hB'c ω with hfdef
  have hf0 : Wof κ T hT0 f 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := drive_facts κ hB'c hT' heq hf0
  rcases hω with hbad | huc
  · exact absurd hgood hbad
  intro n
  obtain ⟨N, hN⟩ := huc n
  refine ⟨N, fun j hj j' hj' p hp => ?_⟩
  obtain ⟨a, b, hab⟩ := hp.2
  have htri : ((a : ℝ), (b : ℝ)) ∈ tri T := by
    rw [← hab]; exact hp.1
  have h := hN j hj j' hj' (a, b) ⟨htri, a, b, rfl⟩
  have hconv : ∀ jj : ℕ, PhiJ κ B X d k jj ω p =
      PWm hT0 κ d k jj (a : ℝ) (b : ℝ) (f, X ω) := by
    intro jj
    rw [show p = ((a : ℝ), (b : ℝ)) from hab, PhiJ_eq_PhiW,
      PhiW_congr_drive κ hdc hd0 (continuous_Wof κ T hT0 f) hf0 hEq d k jj (X ω)
        htri.1 htri.2.1 htri.2.2,
      ← PWm_eq_PhiW hT0 hgood htri.1 htri.2.1 htri.2.2 d k jj (X ω)]
  rw [hconv j, hconv j']
  exact h

end RegUnif
end QuantumZipper
