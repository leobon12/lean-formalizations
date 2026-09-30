import QuantumZipper.Proofs.Zipper.Cor15LastZc

/-!
# COR15-LAST (2): `Cor15PairReadStmt` from a per-test-function regularity statement

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18; no
proof in the paper). Own assembly.

`b1Data x` records the field modulo the additive constant `x.1 (foldedCircle 0 1)` (`nrm`), so the
pairing `(mod0Data (Z_t x)).1 ρ` (ρ of mass zero) is a function of `b1Data x` only where
regularization commutes with adding a constant, i.e. under `E1.RegShift` at the two pushed signed
parts of `ρ` (`mod0Data_zipCapUp_fst_eq_fromC`). This file:

* `regShift_congr_dyadic`, `regShift_addConst`, `regShift_fieldOf_iff`: `RegShift` only reads the
  dyadic folded circles and is invariant under constants (finite measures);
* `measurableSet_regShift_param`: `{a | RegShift (fromC (v a)) (μ.map (f a))}` is measurable for
  measurable `v` and jointly measurable `f` (a countable certificate, as in `E1.goodC`);
* **`cor15PairRead_of_reg`**: `Cor15PairReadStmt` from Theorem 1.3, Rohde–Schramm, and the
  statement `Cor15PairRegStmt` (a.s. `RegShift` of the unzipped field at the pushforwards of the
  two signed parts of each test function under `revMapInv (vrev (√κ B) t) t`). The good set is
  the driver-reading set of `exists_readVp` intersected with `BdryConvAE` and the two `RegShift`
  events; the reading is `CInv` (`Cor15RegDeriv`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

/-- `dyadicRoundC n` is measurable (copy of a private lemma of `Field/Sample.lean`). -/
theorem measurable_dyadicRoundC' (n : ℕ) : Measurable (dyadicRoundC n) := by
  have hR : Measurable (dyadicRound n) := by
    unfold dyadicRound
    exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
      (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))
  have hrw : dyadicRoundC n
      = fun z : ℂ => (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [dyadicRoundC]
  rw [hrw]
  exact (Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_re)).add
    ((Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_im)).mul_const
      Complex.I)

/-- Joint measurability of the raw dyadic folded-circle values (copy of the private
`measurable_eval_dyadic` of `Field/Sample.lean`). -/
theorem measurable_raw_dyadic (n k : ℕ) :
    Measurable (fun p : FieldSample × ℂ => p.1 (foldedCircle (dyadicRoundC n p.2) (radius k))) := by
  have hc : (Set.range (dyadicRoundC n)).Countable := by
    have hsub : Set.range (dyadicRoundC n) ⊆
        Set.range (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
      rintro _ ⟨z, rfl⟩
      exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
    exact (Set.countable_range _).mono hsub
  have : Countable (Set.range (dyadicRoundC n)) := hc.to_subtype
  intro T hT
  have key : (fun p : FieldSample × ℂ => p.1 (foldedCircle (dyadicRoundC n p.2) (radius k))) ⁻¹' T
      = ⋃ d : Set.range (dyadicRoundC n),
          {x : FieldSample | x (foldedCircle (d : ℂ) (radius k)) ∈ T} ×ˢ
            (dyadicRoundC n ⁻¹' ({(d : ℂ)} : Set ℂ)) := by
    ext ⟨x, z⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hmem
      exact ⟨⟨dyadicRoundC n z, Set.mem_range_self z⟩, hmem, rfl⟩
    · rintro ⟨d, hmem, hdz⟩
      rwa [hdz]
  rw [key]
  refine MeasurableSet.iUnion fun d => MeasurableSet.prod ?_ ?_
  · exact measurable_pi_apply (foldedCircle (d : ℂ) (radius k)) hT
  · exact (measurable_dyadicRoundC' n) (measurableSet_singleton _)

theorem measurableSet_rawConv : MeasurableSet {p : FieldSample × ℂ | ∀ k : ℕ, ∃ l,
    Tendsto (fun n => p.1 (foldedCircle (dyadicRoundC n p.2) (radius k))) atTop (𝓝 l)} := by
  have e : {p : FieldSample × ℂ | ∀ k : ℕ, ∃ l,
      Tendsto (fun n => p.1 (foldedCircle (dyadicRoundC n p.2) (radius k))) atTop (𝓝 l)} =
      ⋂ k : ℕ, {p : FieldSample × ℂ | ∃ l,
        Tendsto (fun n => p.1 (foldedCircle (dyadicRoundC n p.2) (radius k))) atTop (𝓝 l)} := by
    ext p; simp
  rw [e]
  exact MeasurableSet.iInter fun k => measurableSet_exists_tendsto fun n => measurable_raw_dyadic n k

/-- `RegShift` reads the field only at the dyadic folded circles. -/
theorem regShift_congr_dyadic {y y' : FieldSample} {ν : Measure ℂ}
    (h : ∀ (n k : ℕ) (z : ℂ), y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y' (foldedCircle (dyadicRoundC n z) (radius k)))
    (hy : E1.RegShift y ν) : E1.RegShift y' ν := by
  have ha : avgReg y = avgReg y' := by
    funext k z
    unfold avgReg
    congr 1
    funext n
    exact h n k z
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.mono fun z hz k => ?_, fun k => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := hz k
    exact ⟨l, hl.congr fun n => h n k z⟩
  · rw [← ha]; exact h2 k
  · rw [← ha]; exact h3

/-- `RegShift` is stable under adding a constant (finite measures). -/
theorem regShift_addConst {y : FieldSample} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (h : E1.RegShift y ν) (c : ℝ) : E1.RegShift (addConst y c) ν := by
  obtain ⟨hraw, hint, L, hL⟩ := h
  have hae : ∀ k : ℕ, (fun z => avgReg (addConst y c) k z) =ᵐ[ν] fun z => avgReg y k z + c :=
    fun k => hraw.mono fun z hz => LocalRule.avgReg_addConst_of_tendsto (hz k) c
  refine ⟨hraw.mono fun z hz k => ?_,
    fun k => ((hint k).add (integrable_const c)).congr (hae k).symm, L + c * (ν univ).toReal, ?_⟩
  · obtain ⟨l, hl⟩ := hz k
    exact ⟨l + c, by simpa [addConst, measure_univ] using hl.add_const c⟩
  · have hk : ∀ k : ℕ, ∫ z, avgReg (addConst y c) k z ∂ν =
        ∫ z, avgReg y k z ∂ν + c * (ν univ).toReal := by
      intro k
      rw [integral_congr_ae (hae k), integral_add (hint k) (integrable_const c)]
      simp [integral_const, Measure.real, mul_comm]
    simpa only [hk] using hL.add_const (c * (ν univ).toReal)

theorem regShift_fieldOf_iff {x : FieldSample} {ν : Measure ℂ} [IsFiniteMeasure ν] :
    E1.RegShift (fieldOf x) ν ↔ E1.RegShift x ν := by
  have h1 : ∀ (n k : ℕ) (z : ℂ), fieldOf x (foldedCircle (dyadicRoundC n z) (radius k)) =
      addConst x (-(x (foldedCircle 0 1))) (foldedCircle (dyadicRoundC n z) (radius k)) := by
    intro n k z
    rw [fieldOf_apply_fc]
    simp [addConst, measure_univ, sub_eq_add_neg]
  have h2 : ∀ (n k : ℕ) (z : ℂ), addConst (addConst x (-(x (foldedCircle 0 1))))
      (x (foldedCircle 0 1)) (foldedCircle (dyadicRoundC n z) (radius k)) =
      x (foldedCircle (dyadicRoundC n z) (radius k)) := by
    intro n k z
    simp [addConst, measure_univ]
  constructor
  · intro h
    exact regShift_congr_dyadic h2 (regShift_addConst (regShift_congr_dyadic h1 h) _)
  · intro h
    exact regShift_congr_dyadic (fun n k z => (h1 n k z).symm) (regShift_addConst h _)

/-- **Measurability of the `RegShift` event** at a parametrized pushforward. -/
theorem measurableSet_regShift_param {α : Type*} [MeasurableSpace α] {v : α → ℕ → ℝ}
    (hv : Measurable v) {f : α → ℂ → ℂ} (hf : Measurable fun p : α × ℂ => f p.1 p.2)
    (μ : Measure ℂ) [SFinite μ] :
    MeasurableSet {a | E1.RegShift (E1.fromC (v a)) (μ.map (f a))} := by
  have hq : Measurable fun p : α × ℂ => (E1.fromC (v p.1), f p.1 p.2) :=
    (measurable_fromC.comp (hv.comp measurable_fst)).prodMk hf
  have hfa : ∀ a, Measurable (f a) := fun a => hf.comp (measurable_const.prodMk measurable_id)
  set T : Set (α × ℂ) := {p | ∀ k : ℕ, ∃ l, Tendsto (fun n =>
    E1.fromC (v p.1) (foldedCircle (dyadicRoundC n (f p.1 p.2)) (radius k))) atTop (𝓝 l)}
    with hTdef
  have hT : MeasurableSet T := hq measurableSet_rawConv
  have hJ : ∀ k, Measurable fun p : α × ℂ => avgReg (E1.fromC (v p.1)) k (f p.1 p.2) :=
    fun k => (measurable_avgReg k).comp hq
  have e : {a | E1.RegShift (E1.fromC (v a)) (μ.map (f a))} =
      ({a | μ (Prod.mk a ⁻¹' Tᶜ) = 0} ∩
        ⋂ k : ℕ, {a | ∫⁻ w, ‖avgReg (E1.fromC (v a)) k (f a w)‖ₑ ∂μ < ⊤}) ∩
      {a | ∃ L, Tendsto (fun k => ∫ w, avgReg (E1.fromC (v a)) k (f a w) ∂μ) atTop (𝓝 L)} := by
    ext a
    have hA : ∀ k, Measurable fun z => avgReg (E1.fromC (v a)) k z := fun k => CoordRegComp.measurable_avgReg_right _ k
    have hS : MeasurableSet {z : ℂ | ∀ k : ℕ, ∃ l,
        Tendsto (fun n => (E1.fromC (v a)) (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)} :=
      ((measurable_const : Measurable fun _ : ℂ => E1.fromC (v a)).prodMk measurable_id)
        measurableSet_rawConv
    have i1 : (∀ᵐ z ∂(μ.map (f a)), ∀ k : ℕ, ∃ l,
        Tendsto (fun n => (E1.fromC (v a)) (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) ↔
        μ (Prod.mk a ⁻¹' Tᶜ) = 0 := by
      rw [ae_map_iff (hfa a).aemeasurable hS, ae_iff]
      rfl
    have i2 : ∀ k : ℕ, Integrable (fun z => avgReg (E1.fromC (v a)) k z) (μ.map (f a)) ↔
        ∫⁻ w, ‖avgReg (E1.fromC (v a)) k (f a w)‖ₑ ∂μ < ⊤ := by
      intro k
      refine ⟨fun h => ?_, fun h => ⟨(hA k).aestronglyMeasurable, ?_⟩⟩
      · have h' := h.2
        unfold HasFiniteIntegral at h'
        rwa [lintegral_map (hA k).enorm (hfa a)] at h'
      · unfold HasFiniteIntegral
        rwa [lintegral_map (hA k).enorm (hfa a)]
    have i3 : ∀ k : ℕ, ∫ z, avgReg (E1.fromC (v a)) k z ∂(μ.map (f a)) = ∫ w, avgReg (E1.fromC (v a)) k (f a w) ∂μ :=
      fun k => integral_map (hfa a).aemeasurable (hA k).aestronglyMeasurable
    show (_ ∧ _ ∧ _) ↔ _
    rw [i1, forall_congr' i2]
    simp only [i3, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq]
    exact and_assoc.symm
  rw [e]
  refine (MeasurableSet.inter ?_ (MeasurableSet.iInter fun k => ?_)).inter ?_
  · exact measurableSet_eq_fun (measurable_measure_prodMk_left hT.compl) measurable_const
  · exact measurableSet_lt ((hJ k).enorm.lintegral_prod_right') measurable_const
  · exact measurableSet_exists_tendsto fun k =>
      (hJ k).stronglyMeasurable.integral_prod_right'.measurable

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Remaining input for `Cor15PairReadStmt`** (not proved here): a.s. the unzipped field is
`RegShift`-regular at the pushforwards, under the centered map `f_t = revMapInv (vrev (√κ B) t) t`,
of the two signed parts of each test function. -/
def Cor15PairRegStmt (κ t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
    E1.RegShift (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens ρ.1).map (revMapInv (B2.vrev (drive κ B ω) t) t)) ∧
      E1.RegShift (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens fun z => -ρ.1 z).map (revMapInv (B2.vrev (drive κ B ω) t) t))

/-- **COR15-LAST (2): `Cor15PairReadStmt`**, conditional on `Cor15PairRegStmt`. -/
theorem cor15PairRead_of_reg (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hR : Cor15PairRegStmt κ t P B X) : Cor15PairReadStmt κ t P B X := by
  obtain ⟨Vp, hVc, hV0, hVm, A, hAm, hdet, hyA, -⟩ :=
    exists_readVp h13 hRSS hκ hκ4 hB hX hind ht
  have hRm : Measurable fun p : ℂ × B1E => revMapInv (Vp p.2) t p.1 :=
    measurable_revMapInv_param hVc hV0 hVm ht
  have hRm' : Measurable fun p : B1E × ℂ => revMapInv (Vp p.1) t p.2 := by
    simpa only [Function.comp_def] using
      hRm.comp (f := fun p : B1E × ℂ => (p.2, p.1)) (measurable_snd.prodMk measurable_fst)
  have hv : Measurable fun e : B1E => e.1.1 := measurable_fst.comp measurable_fst
  intro ρ
  have := isFiniteMeasure_tdens ρ.1
  have := isFiniteMeasure_tdens_neg ρ.1
  refine ⟨fun e => CInv Vp t (Qc (Real.sqrt κ)) (CharFun.tdens ρ.1.1) (e.1.1, e) -
      CInv Vp t (Qc (Real.sqrt κ)) (CharFun.tdens fun z => -ρ.1.1 z) (e.1.1, e), ?_,
    A ∩ {e | BdryConvAE (E1.fromC e.1.1)} ∩
      {e | E1.RegShift (E1.fromC e.1.1) ((CharFun.tdens ρ.1.1).map (revMapInv (Vp e) t))} ∩
      {e | E1.RegShift (E1.fromC e.1.1)
        ((CharFun.tdens fun z => -ρ.1.1 z).map (revMapInv (Vp e) t))}, ?_, ?_, ?_⟩
  · have hp : Measurable fun e : B1E => (e.1.1, e) := hv.prodMk measurable_id
    exact ((measurable_CInv hVc hV0 hVm ht _ _).comp hp).sub
      ((measurable_CInv hVc hV0 hVm ht _ _).comp hp)
  · exact ((hAm.inter (hv measurableSet_bdryConvAE_fromC)).inter
      (measurableSet_regShift_param hv hRm' _)).inter (measurableSet_regShift_param hv hRm' _)
  · rintro x ⟨⟨⟨hA, hbc⟩, hr1⟩, hr2⟩
    obtain ⟨hEq, hnull⟩ := hdet x hA
    have hbcx : BdryConvAE x.1 := (bdryConvAE_fieldOf_iff x.1).1 hbc
    have hinv : revMapInv (weldDriver (Real.sqrt κ) x.1 t) t = revMapInv (Vp (b1Data x)) t :=
      revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hEq
    have hfm := measurable_revMapInv (hVc (b1Data x)) ht.le
    have hr1' := (regShift_fieldOf_iff (x := x.1)).1 hr1
    have hr2' := (regShift_fieldOf_iff (x := x.1)).1 hr2
    rw [mod0Data_zipCapUp_fst_eq_fromC hbcx ρ (by rw [hinv]; exact hfm.aemeasurable)
      (by rw [hinv]; exact hfm.aemeasurable)
      (by rw [hinv]; exact hr1') (by rw [hinv]; exact hr2'), weldDriver_fieldOf hbcx, hinv,
      pairRaw_revMapInv_eq_CInv hVc hV0 ht _ ρ.1 (fieldOf x.1) _ hnull,
      show coordsFull (fieldOf x.1) = (b1Data x).1.1 from E1.coordsFull_fromC (nrm x.1)]
  · filter_upwards [hyA, hR ρ.1, ae_reg_zipCapDown hκ hκ4 hB hX hind ht] with ω ⟨hA, hV⟩
      ⟨h1, h2⟩ ⟨hbc, _⟩
    set y := zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω) with hy
    have hinv : revMapInv (Vp (b1Data y)) t = revMapInv (B2.vrev (drive κ B ω) t) t :=
      revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hV
    refine ⟨⟨⟨hA, (bdryConvAE_fieldOf_iff y.1).2 hbc⟩, ?_⟩, ?_⟩
    · rw [Set.mem_ofPred_eq, hinv]; exact (regShift_fieldOf_iff (x := y.1)).2 h1
    · rw [Set.mem_ofPred_eq, hinv]; exact (regShift_fieldOf_iff (x := y.1)).2 h2

end Cor15Group
end QuantumZipper
