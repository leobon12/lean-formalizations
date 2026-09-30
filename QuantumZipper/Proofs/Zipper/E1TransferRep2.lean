import QuantumZipper.Proofs.Zipper.E1TransferRep
import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.GFF.CoordRegCompLim
import QuantumZipper.Proofs.GFF.CoordRegComp

/-!
# TR-MEAS, M3 for the zipped field `Y_t`: `RegShift` at the pushed measures, almost surely

`handoff/E1-TR.md` (M3). For `0 ≤ t ≤ T`, `B` Brownian independent of the free field `X`:

* `ae_regShift_Yf_fc`: for every `i`, a.s. `RegShift (Y_t) (fc_i.map (revMap V t))`;
* `ae_regShift_Yf_compact`: a.s. `RegShift (Y_t) (ϖ.map (revMap V t))` for a Frostman probability
  measure `ϖ` carried by a compact subset of `ℍ`.

Proof: the convergence form of RC3 for fixed drivers (`CoordRegComp.ae_regShift_comp_fixed`), a
measurable certificate in (path, field) (`goodC`: the countable regularity certificate
`GoodMeas.C1`, finiteness of `∫⁻ |avgReg|`, existence of the limit of `∫ avgReg`), Fubini over
the independent path (`CharFun.ae_indep`), and the pathwise identification of the drivers, as in
`CoordRegComp.ae_evalReg_Yf_push`. Sources: Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1 (through RC3); Sheffield arXiv:1012.4797 §5.2, pp. 57–59. The reduction is own
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull CoordRegComp CoordReg

/-- `RegShift` depends on the field only through its values at folded circles of positive
radius. -/
theorem regShift_congr {y y' : FieldSample} {ν : Measure ℂ}
    (h : ∀ (w : ℂ) (r : ℝ), 0 < r → y (foldedCircle w r) = y' (foldedCircle w r))
    (hy : RegShift y ν) : RegShift y' ν := by
  have ha : avgReg y = avgReg y' := by
    funext k z
    unfold avgReg
    congr 1
    funext n
    exact h _ _ (radius_pos k)
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.mono fun z hz k => ?_, fun k => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := hz k
    exact ⟨l, hl.congr fun n => h _ _ (radius_pos k)⟩
  · rw [← ha]; exact h2 k
  · rw [← ha]; exact h3

variable (κ : ℝ) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ T - t) (Q : ℝ) (μ : Measure ℂ)

/-- The field of the composition law as a function of (path, field). -/
abbrev fieldC (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : FieldSample :=
  coordChange (ofFun (h0rev κ) + p.2)
    (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) p.1)) (T - t)) Q

/-- The measurable certificate of `RegShift` for `fieldC` at `μ` pushed by `revMap V t`. -/
def goodC : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
  {p | GoodMeas.C1 (fieldC κ hT hs Q p)} ∩
    {p | ∀ k : ℕ, ∫⁻ u, ‖avgReg (fieldC κ hT hs Q p) k (Fm κ t ht (revPath hT T t p.1, u))‖ₑ ∂μ
      < ⊤} ∩
    {p | ∃ L, Tendsto (fun k => ∫ u, avgReg (fieldC κ hT hs Q p) k
      (Fm κ t ht (revPath hT T t p.1, u)) ∂μ) atTop (𝓝 L)}

theorem measurable_avgReg_fieldC_base (k : ℕ) : Measurable fun q : (C(Icc (0 : ℝ) (T - t), ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun (h0rev κ) + q.1.2) (revMap (Wof κ (T - t) hs q.1.1) (T - t)) Q) k q.2 :=
  CoordReg.measurable_avgReg_coordChange κ hs (h0rev κ) Q k

theorem measurable_revPath_fst : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      (revPath hT (T - t) (T - t) q.1.1) :=
  (measurable_revPath hT (T - t) (T - t)).comp (measurable_fst.comp measurable_fst)

theorem measurable_Fm_revPath : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      Fm κ t ht (revPath hT T t q.1.1, q.2) :=
  (measurable_Fm κ t ht).comp (((measurable_revPath hT T t).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd)

theorem measurable_avgReg_fieldC (k : ℕ) : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg (fieldC κ hT hs Q q.1) k (Fm κ t ht (revPath hT T t q.1.1, q.2)) := by
  have h := (measurable_avgReg_fieldC_base κ hs Q k).comp ((measurable_revPath_fst hT (t := t)).prodMk (measurable_snd.comp measurable_fst) |>.prodMk
    (measurable_Fm_revPath κ hT ht))
  exact h

theorem measurableSet_C1_fieldC : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      GoodMeas.C1 (fieldC κ hT hs Q p)} := by
  have h := (measurableSet_C1_h0rev κ hs Q).preimage
      (((measurable_revPath hT (T - t) (T - t)).comp measurable_fst).prodMk
        (measurable_snd (α := C(Icc (0 : ℝ) T, ℝ)) (β := FieldSample)))
  exact h

theorem measurableSet_goodC [SFinite μ] : MeasurableSet (goodC κ hT ht hs Q μ) := by
  have hJ := measurable_avgReg_fieldC κ hT ht hs Q
  have h1 := measurableSet_C1_fieldC κ hT hs Q
  have h2 : ∀ k : ℕ, MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      ∫⁻ u, ‖avgReg (fieldC κ hT hs Q p) k (Fm κ t ht (revPath hT T t p.1, u))‖ₑ ∂μ < ⊤} :=
    fun k => measurableSet_lt (hJ k).enorm.lintegral_prod_right' measurable_const
  have h3 : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample | ∃ L, Tendsto (fun k =>
      ∫ u, avgReg (fieldC κ hT hs Q p) k (Fm κ t ht (revPath hT T t p.1, u)) ∂μ) atTop
        (𝓝 L)} :=
    measurableSet_exists_tendsto fun k =>
      (hJ k).stronglyMeasurable.integral_prod_right'.measurable
  have h2' := MeasurableSet.iInter h2
  rw [← ofPred_forall] at h2'
  exact (h1.inter h2').inter h3

/-- On the certificate, `RegShift` holds for `fieldC` at the pushed measure. -/
theorem regShift_of_goodC {f : C(Icc (0 : ℝ) T, ℝ)} {x : FieldSample}
    (hμH : ∀ᵐ z ∂μ, z ∈ H) (hp : (f, x) ∈ goodC κ hT ht hs Q μ) :
    RegShift (fieldC κ hT hs Q (f, x)) (μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)) := by
  obtain ⟨⟨hC1, hfin⟩, L, hL⟩ := hp
  have hF := TwoPoint.measurable_revMap (continuous_Wof κ t ht (revPath hT T t f)) ht
  have hA : ∀ k, Measurable fun z => avgReg (fieldC κ hT hs Q (f, x)) k z := fun k =>
    measurable_avgReg_right _ k
  have hFm : ∀ u, Fm κ t ht (revPath hT T t f, u) =
      revMap (Wof κ t ht (revPath hT T t f)) t u := fun u => rfl
  refine ⟨?_, fun k => ⟨(hA k).aestronglyMeasurable, ?_⟩, L, ?_⟩
  · have hH : ∀ᵐ z ∂(μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)), z ∈ H :=
      (ae_map_iff hF.aemeasurable isOpen_H.measurableSet).2
        (hμH.mono fun u hu => TwoPoint.im_revMap_pos (continuous_Wof κ t ht _) hu ht)
    filter_upwards [hH] with z hz k
    exact ⟨_, GoodMeas.tendsto_raw_of_C1 hC1 k (H_subset_Hbar hz)⟩
  · unfold HasFiniteIntegral
    rw [lintegral_map (hA k).enorm hF]
    simpa only [hFm] using hfin k
  · simp only [integral_map hF.aemeasurable (hA _).aestronglyMeasurable]
    simpa only [hFm] using hL

/-- The fixed-path certificate, from the convergence form of RC3 for fixed drivers (the drivers
read off one path as in `CoordRegComp.hfix_of_law`). -/
theorem goodC_of_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (htT : t ≤ T)
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t)) Q) ∧
        (∀ k : ℕ, Integrable (fun z => avgReg (coordChange (ofFun (h0rev κ) + X ω)
          (revMap A (T - t)) Q) k z) (μ.map (revMap V t))) ∧
        ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange (ofFun (h0rev κ) + X ω)
          (revMap A (T - t)) Q) k z ∂(μ.map (revMap V t))) atTop (𝓝 L))
    (f : C(Icc (0 : ℝ) T, ℝ)) : ∀ᵐ ω ∂P, (f, X ω) ∈ goodC κ hT ht hs Q μ := by
  have hV := continuous_Wof κ t ht (revPath hT T t f)
  have hF := TwoPoint.measurable_revMap hV ht
  have hFm : ∀ u, Fm κ t ht (revPath hT T t f, u) = revMap (Wof κ t ht (revPath hT T t f)) t u :=
    fun u => rfl
  have hl := hlaw (Wof κ T hT (revPath hT T T f)) (Wof κ t ht (revPath hT T t f))
    (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (continuous_Wof κ T hT _) hV
    (continuous_Wof κ (T - t) hs _)
    (fun r hr => by
      rw [Wof_revPath κ hT hT T f ⟨hr.1, hr.2.trans htT⟩, Wof_revPath κ hT ht T f hr])
    (fun r hr => by
      rw [Wof_revPath κ hT hT T f ⟨by linarith [hr.1], by linarith [hr.2]⟩,
        Wof_revPath κ hT hT T f ⟨ht, htT⟩, Wof_revPath κ hT hs (T - t) f hr,
        show T - (t + r) = T - t - r by ring]
      ring)
  filter_upwards [hl] with ω hω
  obtain ⟨⟨F, hreg⟩, hint, L, hL⟩ := hω
  refine ⟨⟨GoodMeas.C1_of_regular hreg, fun k => ?_⟩, L, ?_⟩
  · have h := (hint k).2
    unfold HasFiniteIntegral at h
    rw [lintegral_map (measurable_avgReg_right _ k).enorm hF] at h
    simpa only [hFm] using h
  · simp only [integral_map hF.aemeasurable (measurable_avgReg_right _ _).aestronglyMeasurable]
      at hL
    simpa only [hFm] using hL

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit hT ht hs μ in
/-- **`RegShift` for `Y_t` at a pushed measure**, from the fixed-driver law. -/
theorem ae_regShift_Yf_push (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {μ : Measure ℂ}
    [IsProbabilityMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ H)
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t))
          (Qc (Real.sqrt κ))) ∧
        (∀ k : ℕ, Integrable (fun z => avgReg (coordChange (ofFun (h0rev κ) + X ω)
          (revMap A (T - t)) (Qc (Real.sqrt κ))) k z) (μ.map (revMap V t))) ∧
        ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange (ofFun (h0rev κ) + X ω)
          (revMap A (T - t)) (Qc (Real.sqrt κ))) k z ∂(μ.map (revMap V t))) atTop (𝓝 L)) :
    ∀ᵐ ω ∂P, RegShift (Yf κ T t B X ω) (μ.map (revMap (Vr κ T B ω) t)) := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : 0 ≤ T - t := sub_nonneg.2 htT
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hr := ae_indep (measurable_pathC T hB₁m hB₁c) hXm (indepFun_pathC T hind₁ hB₁c)
    (measurableSet_goodC κ hT ht hs (Qc (Real.sqrt κ)) μ)
    (goodC_of_law κ hT ht hs (Qc (Real.sqrt κ)) μ htT hlaw)
  filter_upwards [hr, hB₁eq, hB.eval_zero_ae_eq_zero] with ω h h1 h0
  set f := pathC T B₁ hB₁c ω with hf
  have hPj : ∀ x (hx : x ∈ Icc (0 : ℝ) T), f (projIcc 0 T hT x) = B x.toNNReal ω := by
    intro x hx
    rw [projIcc_of_mem hT hx]
    exact h1 _
  have hcB : Continuous fun s => B s ω := by
    have : (fun s => B s ω) = fun s => B₁ s ω := funext fun s => (h1 s).symm
    rw [this]; exact hB₁c ω
  have hW : Continuous (drive κ B ω) := continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by
    have : B 0 ω = 0 := h0
    simp [drive, this]
  have hFeq : revMap (Vr κ T B ω) t = revMap (Wof κ t ht (revPath hT T t f)) t :=
    funext fun z => ReverseFlow.revMap_congr_drive z fun r hr => by
      rw [Wof_revPath κ hT ht T f hr, Vr, vrev_of_mem ⟨hr.1, hr.2.trans htT⟩,
        hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩, hPj _ ⟨hT, le_rfl⟩]
      simp only [drive]; ring
  have hEq : EqOn (fwdMapInv (drive κ B ω) (T - t))
      (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (T - t)) H := fun z hz => by
    rw [eqOn_fwdMapInv hW hW0 hs hz]
    exact ReverseFlow.revMap_congr_drive z fun r hr => by
      show drive κ B ω (T - t - r) - drive κ B ω (T - t) = _
      rw [Wof_revPath κ hT hs (T - t) f hr, hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩,
        hPj _ ⟨hs, by linarith⟩]
      simp only [drive]; ring
  have key : RegShift (fieldC κ hT hs (Qc (Real.sqrt κ)) (f, X ω))
      (μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)) :=
    regShift_of_goodC κ hT ht hs (Qc (Real.sqrt κ)) μ hμH h
  have hY : Yf κ T t B X ω = coordChange (ofFun (h0rev κ) + X ω)
      (fwdMapInv (drive κ B ω) (T - t)) (Qc (Real.sqrt κ)) := by rw [Yf_eq_unzippedField]; rfl
  have key2 : RegShift (Yf κ T t B X ω) (μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)) :=
    regShift_congr (y := fieldC κ hT hs (Qc (Real.sqrt κ)) (f, X ω)) (fun w r hr => by
      rw [hY, coordChange_congr_of_eqOn_H _ hEq _ (TwoPoint.foldedCircle_ae_mem_H w hr)]) key
  rw [hFeq]
  exact key2

omit hT ht hs μ in
/-- **`RegShift` for `Y_t` at every pushed dyadic folded circle.** -/
theorem ae_regShift_Yf_fc (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ i : ℕ, ∀ᵐ ω ∂P, RegShift (Yf κ T t B X ω) (pfc (Vr κ T B ω) t i) := by
  intro i
  have hr := UnzipFull.fullIndex_radius_pos i
  refine ae_regShift_Yf_push κ hB hX hind ht htT (TwoPoint.foldedCircle_ae_mem_H _ hr)
    fun Vf V A hVf hV hA hVV hAV => ?_
  rw [h0rev_eq_logAdd κ]
  exact ae_regShift_comp_fc hX (2 / Real.sqrt κ) continuous_const _ hVf hV hA ht
    (sub_nonneg.2 htT) hVV hAV _ hr

omit hT ht hs μ in
/-- **`RegShift` for `Y_t` at the pushed normalizer.** -/
theorem ae_regShift_Yf_compact (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {ϖ : Measure ℂ}
    [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0)
    {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, RegShift (Yf κ T t B X ω) (varpiT (Vr κ T B ω) t ϖ) := by
  refine ae_regShift_Yf_push κ hB hX hind ht htT ((ae_iff.2 hϖ).mono fun z hz => hKH hz)
    fun Vf V A hVf hV hA hVV hAV => ?_
  rw [h0rev_eq_logAdd κ]
  exact ae_regShift_comp_compact hX (2 / Real.sqrt κ) continuous_const _ hVf hV hA ht
    (sub_nonneg.2 htT) hVV hAV hK hKH hϖ hFϖ hα

end E1
end QuantumZipper
