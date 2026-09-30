import QuantumZipper.Proofs.Zipper.E1TransferM4Field
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae

/-!
# M4 (TR-MEAS): a.e.-measurability of the transfer integrand

`handoff/E1-TR.md` (M4). **Correction of the M4 target.** The integrand `Hf0` of
`E1TransferRep3` reads the driver as `stopDrive d` (the raw first path component). On the product
`σ`-algebra of `ℝ≥0 → ℝ`, the set of paths continuous on `[0,t]` is not measurable (it has inner
measure `0` and outer measure `1` under the law of `V^t`), and `trInt` vanishes at every path
that is discontinuous on `[0,t]` (no reverse solution, `liveNeg = ∅`). Hence `Hf0` is in general
**not** a.e.-measurable. We therefore use `Hf1`, which reads the driver through the measurable
continuous version `M4.extC` (Bernstein approximants); `Hf1 = Hf0` along the data
`(lawData, (V^t, W⁰))` whenever `B` is continuous, so E1-TR follows in the same way
(`E1TransferFinal`).

* `Hf1_eq_KQ`: on the measurable set `goodQ` (boundary certificate `M4.BCert` of the zipped field
  rebuilt from coordinates, and driver path starting at `0`), `Hf1` equals the explicitly
  measurable `KQ` (Giry-measurable boundary measure, measurable live set, finite truncated kernels);
* `ae_goodQ`: almost surely the data lie in `goodQ` (B2(b), M3 at the pushed circles, and
  `ae_bCert_h0f`);
* **`aemeasurable_Hf1`** (M4, corrected).

Own bookkeeping (measurability). Sources of the statement being formalized: Sheffield,
arXiv:1012.4797, Lemma 5.6 (pp. 66–68), §5.2 (pp. 57–59).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull CoordsFull B1Full M4

/-- The data space of TR-MEAS. -/
abbrev QT := ((ℕ → ℝ) × (TestFun H → ℝ)) × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))

/-- **The transfer integrand, driver read through the continuous version `extC`.** -/
def Hf1 (κ t δ : ℝ) (ht : 0 ≤ t) (ϖ : Measure ℂ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (q : QT) : ℝ≥0∞ :=
  trInt κ t δ ϖ Ψ Φ (Wof 1 t ht (extC t q.2.1)) q.2 (fromC q.1.1)

section Det

variable (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (ϖ : Measure ℂ) (δ : ℝ)
  (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞)

/-- (coordinates, continuous driver path) read off the data. -/
def pq (t : ℝ) (q : QT) : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ) := (q.1.1, extC t q.2.1)

theorem measurable_pq (t : ℝ) : Measurable (pq t) :=
  (measurable_fst.comp measurable_fst).prodMk ((measurable_extC t).comp
    (measurable_fst.comp measurable_snd))

/-- The good set of the data. -/
def goodQ : Set QT :=
  {q | BCert (Real.sqrt κ) (zR κ ht ϖ (pq t q)) ∧ extC t q.2.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0}

open Classical in
/-- The boundary measure of the rebuilt field (junk `0` off the certificate). -/
def MQ (q : QT) : Measure ℝ :=
  if BCert (Real.sqrt κ) (zR κ ht ϖ (pq t q)) then qBoundaryMeasure (Real.sqrt κ) (zR κ ht ϖ (pq t q))
  else 0

/-- The live set in (data, point), restricted to paths starting at `0`. -/
def liveQ : Set (QT × ℝ) :=
  {a | (extC t a.1.2.1, a.2) ∈ {p : C(Icc (0 : ℝ) t, ℝ) × ℝ |
    p.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ p.2 ∈ liveNeg (Wof 1 t ht p.1) t}}

/-- The integrand in (data, point). -/
def fQ (a : QT × ℝ) : ℝ≥0∞ := (liveQ ht).indicator (fun a => Ψ a.2 a.1.2) a

/-- The measurable candidate. -/
def KQ (q : QT) : ℝ≥0∞ :=
  (goodQ κ ht ϖ).indicator (fun q => (∫⁻ x in Icc (-δ) 0, fQ ht Ψ (q, x) ∂MQ κ ht ϖ q) *
    Φ (coordsFull (addConst (fromC q.1.1) (-(mC κ ht ϖ (pq t q)))))) q

variable [SFinite ϖ] (hϖH : ∀ᵐ z ∂ϖ, z ∈ H)
include hϖH

theorem measurableSet_goodQ : MeasurableSet (goodQ κ ht ϖ) := by
  have h1 : MeasurableSet {q : QT | BCert (Real.sqrt κ) (zR κ ht ϖ (pq t q))} :=
    (measurableSet_bCert _).preimage ((measurable_zR κ ht ϖ hϖH).comp (measurable_pq t))
  have h2 : MeasurableSet {q : QT | extC t q.2.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0} :=
    measurableSet_eq_fun ((ContinuousMap.measurable_eval _).comp ((measurable_extC t).comp
      (measurable_fst.comp measurable_snd))) measurable_const
  exact h1.inter h2

theorem measurable_MQ : Measurable (MQ κ ht ϖ) := by
  have h := (measurable_qBoundaryMeasure_bCert (Real.sqrt κ)).comp
    ((measurable_zR κ ht ϖ hϖH).comp (measurable_pq t))
  exact h

omit [SFinite ϖ] hϖH in
theorem MQ_Icc_lt_top (q : QT) (a b : ℝ) : MQ κ ht ϖ q (Icc a b) < ⊤ := by
  unfold MQ
  split_ifs with h
  · have := (isVagueLimitR_qBoundaryMeasure (exists_isVagueLimitR_of_bCert h)).1
    exact measure_Icc_lt_top
  · simp

omit hϖH in
theorem measurable_fQ (hΨ : Measurable (Function.uncurry Ψ)) : Measurable (fQ ht Ψ) := by
  have hL : MeasurableSet (liveQ ht) := (measurableSet_liveNeg_Wof t ht).preimage
    (((measurable_extC t).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      measurable_snd)
  have hg : Measurable fun a : QT × ℝ => Ψ a.2 a.1.2 := by
    have h := hΨ.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst) :
      Measurable fun a : QT × ℝ => (a.2, a.1.2))
    exact h
  exact hg.indicator hL

theorem measurable_KQ (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    Measurable (KQ κ ht ϖ δ Ψ Φ) := by
  have hI : Measurable fun q => ∫⁻ x in Icc (-δ) 0, fQ ht Ψ (q, x) ∂MQ κ ht ϖ q :=
    measurable_setLIntegral_of_measurable_measure (measurable_MQ κ ht ϖ hϖH) measurableSet_Icc
      (fun q => MQ_Icc_lt_top κ ht ϖ q _ _) (measurable_fQ ht Ψ hΨ)
  have hC : Measurable fun q : QT => Φ (coordsFull (addConst (fromC q.1.1)
      (-(mC κ ht ϖ (pq t q))))) := by
    have h := hΦ.comp ((measurable_coords_shift κ ht ϖ hϖH).comp (measurable_pq t))
    exact h
  exact (hI.mul hC).indicator (measurableSet_goodQ κ ht ϖ hϖH)

omit [SFinite ϖ] hϖH in
/-- **Deterministic identification** of `Hf1` on the good set. -/
theorem Hf1_eq_KQ (hΨ : Measurable (Function.uncurry Ψ)) {q : QT} (hq : q ∈ goodQ κ ht ϖ) :
    Hf1 κ t δ ht ϖ Ψ Φ q = KQ κ ht ϖ δ Ψ Φ q := by
  obtain ⟨hC, h0⟩ := hq
  set p := pq t q with hp
  set w := extC t q.2.1 with hw
  set U := liveNeg (Wof 1 t ht w) t with hU
  have hUo : IsOpen U := isOpen_liveNeg (continuous_Wof 1 t ht w) t
  set l := qBoundaryMeasure (Real.sqrt κ) (zR κ ht ϖ p) with hl
  have hlim : IsVagueLimitR (bdryApprox (Real.sqrt κ) (zC κ ht ϖ p)) l := by
    rw [← bdryApprox_zR]; exact isVagueLimitR_qBoundaryMeasure (exists_isVagueLimitR_of_bCert hC)
  have hOn : qBoundaryMeasureOn (Real.sqrt κ) (zC κ ht ϖ p) U = l.restrict U :=
    LocalRule.qBoundaryMeasureOn_eq hUo (InfMass.isVagueLimitOnR_restrict hlim hUo)
  have hM : MQ κ ht ϖ q = l := if_pos hC
  have hf : ∀ x, fQ ht Ψ (q, x) = U.indicator (fun x => Ψ x q.2) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      exact indicator_of_mem (show (q, x) ∈ liveQ ht from ⟨h0, hx⟩) _
    · rw [indicator_of_notMem hx]
      exact indicator_of_notMem (fun h => hx h.2) _
  have hΨx : Measurable fun x => Ψ x q.2 := by
    have h := hΨ.comp (measurable_id.prodMk measurable_const : Measurable fun x : ℝ => (x, q.2))
    exact h
  rw [KQ, indicator_of_mem (show q ∈ goodQ κ ht ϖ from ⟨hC, h0⟩), hM]
  simp_rw [hf]
  change ∫⁻ x in Icc (-δ) 0, Ψ x q.2 * Φ (coordsFull (addConst (fromC q.1.1) (-(mC κ ht ϖ p))))
      ∂qBoundaryMeasureOn (Real.sqrt κ) (zC κ ht ϖ p) U = _
  rw [hOn, lintegral_mul_const _ hΨx, lintegral_indicator hUo.measurableSet,
    Measure.restrict_restrict measurableSet_Icc, Measure.restrict_restrict hUo.measurableSet,
    inter_comm]

end Det

/-- M3 at the level of coordinates: the zipped field built from `fromC (coordsFull (nrm Y))` has
the circle coordinates of the one built from `Y`. -/
theorem coordsFull_field_fromC_nrm {κ t : ℝ} {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ]
    {V : ℝ → ℝ} {Y : FieldSample}
    (h1 : RegShift Y (varpiT V t ϖ)) (h2 : ∀ i, RegShift Y (pfc V t i)) :
    coordsFull (addConst (coordChange (fromC (coordsFull (nrm Y))) (revMap V t)
        (Qc (Real.sqrt κ))) (-(evalReg (fromC (coordsFull (nrm Y))) (varpiT V t ϖ) +
          qt κ V t ϖ))) =
      coordsFull (addConst (coordChange Y (revMap V t) (Qc (Real.sqrt κ)))
        (-(evalReg Y (varpiT V t ϖ) + qt κ V t ϖ))) := by
  have hc := coordsFull_fromC (nrm Y)
  have e1 : evalReg (fromC (coordsFull (nrm Y))) = evalReg (nrm Y) :=
    funext (evalReg_congr_coordsFull hc)
  have e2 : coordChange (fromC (coordsFull (nrm Y))) = coordChange (nrm Y) := by
    funext F Q μ; simp only [coordChange, e1]
  rw [e1, e2]
  have : IsProbabilityMeasure (varpiT V t ϖ) := by unfold varpiT; infer_instance
  have : ∀ i, IsProbabilityMeasure (pfc V t i) := fun i => by unfold pfc; infer_instance
  funext i
  simp only [coordsFull_addConst]
  simp only [coordsFull, coordChange, nrm]
  rw [evalReg_addConst_of_regShift (h2 i), evalReg_addConst_of_regShift h1]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

omit [MeasurableSpace Ω] in
/-- On a sample with continuous `B`, the continuous version of `V^t` is `V` on `[0,t]`. -/
theorem extC_Vstop {ω : Ω} (hc : Continuous fun s => B s ω) (s : Icc (0 : ℝ) t) :
    extC t (Vstop κ T t B ω) s = Vr κ T B ω s := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hVs : Continuous (Vstop κ T t B ω) := by
    unfold Vstop; exact hV.comp (NNReal.continuous_coe.min continuous_const)
  rw [extC_apply_of_continuous hVs]
  simp only [Vstop, Real.coe_toNNReal _ s.2.1, min_eq_left s.2.2]

omit [MeasurableSpace Ω] in
theorem eqOn_Wof_extC_Vstop (ht : 0 ≤ t) {ω : Ω} (hc : Continuous fun s => B s ω) :
    EqOn (Wof 1 t ht (extC t (Vstop κ T t B ω))) (Vr κ T B ω) (Icc 0 t) := fun s hs => by
  simp only [Wof, Real.sqrt_one, one_mul, projIcc_of_mem ht hs]
  exact extC_Vstop hc ⟨s, hs⟩

/-- **A.s. the data lie in the good set.** -/
theorem ae_goodQ (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ) :
    ∀ᵐ ω ∂P, (lawData (fun ω => nrm (Yf κ T t B X ω)) ω, (Vstop κ T t B ω, W0p κ T B ω)) ∈
      goodQ κ ht ϖ := by
  have := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hT : 0 < T := ht.trans_lt htT
  filter_upwards [hB.cont, ae_regShift_Yf_compact κ hB hX hind ht htT.le hK hKH hϖK hF hα,
    ae_all_iff.2 (ae_regShift_Yf_fc κ hB hX hind ht htT.le),
    b2_coordsFull_eq (κ := κ) hB hX hind ht htT.le,
    b2_evalReg_split (κ := κ) hB hX hind ht htT.le hK hKH hϖK hF hα,
    ae_bCert_h0f hReg hκ hκ4 hT hB hX hind ϖ] with ω hc h1 h2 hcf hm hbc
  have hrev : revMap (Wof 1 t ht (extC t (Vstop κ T t B ω))) t = revMap (Vr κ T B ω) t :=
    funext fun z => ReverseFlow.revMap_congr_drive z (eqOn_Wof_extC_Vstop ht hc)
  refine ⟨?_, ?_⟩
  · have hcoords : coordsFull (zC κ ht ϖ (pq t (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω)))) =
        coordsFull (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω))) := by
      unfold zC mC pq
      simp only [varpiT, qt, hrev]
      have e := coordsFull_field_fromC_nrm (κ := κ) (ϖ := ϖ) h1 h2
      simp only [varpiT, qt] at e
      refine e.trans ?_
      rw [show mReg κ T B X ϖ ω = _ from hm]
      exact coordsFull_addConst_congr hcf.symm _
    have hb : bdryApprox (Real.sqrt κ) (zR κ ht ϖ (pq t (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω)))) =
        bdryApprox (Real.sqrt κ) (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω))) :=
      (bdryApprox_zR κ ht ϖ _ _).trans
        (Factorization.bdryApprox_congr (avgReg_congr_full hcoords) _)
    unfold BCert at hbc ⊢
    rw [hb]
    exact hbc
  · show extC t (Vstop κ T t B ω) ⟨0, ⟨le_rfl, ht⟩⟩ = 0
    rw [extC_Vstop hc]
    exact vrev_zero hT.le

/-- **M4 (corrected): the transfer integrand `Hf1` is a.e.-measurable for the product law.** -/
theorem aemeasurable_Hf1 (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    (δ : ℝ) {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} {Φ : (ℕ → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    AEMeasurable (Hf1 κ t δ ht ϖ Ψ Φ)
      ((P.map fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω).prod
        (P.map fun ω => (Vstop κ T t B ω, W0p κ T B ω))) := by
  have := hϖ.prob
  have hϖH : ∀ᵐ z ∂ϖ, z ∈ H := by
    obtain ⟨K, -, hKH, hϖK⟩ := hϖ.cpt
    exact ae_iff.2 (measure_mono_null (fun z hz hzK => hz (hKH hzK)) hϖK)
  obtain ⟨hI, hL, -⟩ := b2_markov hκ hB hX hind ht htT
  set L := fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω with hLdef
  set D := fun ω => (Vstop κ T t B ω, W0p κ T B ω) with hDdef
  have hg : Measurable (Prod.map (id : (ℕ → ℝ) × (TestFun H → ℝ) → _) (splitAt t)) :=
    measurable_id.prodMap (measurable_splitAt t)
  have hfg : AEMeasurable (fun ω => (L ω, D ω)) P := by
    rw [hLdef, hDdef, data_eq_comp ht htT.le]
    exact hg.comp_aemeasurable (aemeasurable_data_unzip hB hX hind (sub_pos.2 htT).le)
  have hprod : P.map (fun ω => (L ω, D ω)) =
      (P.map fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω).prod (P.map D) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hfg.fst hfg.snd).1 hI, hL]
  refine ⟨KQ κ ht ϖ δ Ψ Φ, measurable_KQ κ ht ϖ δ Ψ Φ hϖH hΨ hΦ, ?_⟩
  rw [← hprod]
  have hG : ∀ᵐ q ∂(P.map fun ω => (L ω, D ω)), q ∈ goodQ κ ht ϖ :=
    (ae_map_iff hfg (measurableSet_goodQ κ ht ϖ hϖH)).2
      (ae_goodQ hReg hκ hκ4 ht htT hB hX hind hϖ)
  filter_upwards [hG] with q hq using Hf1_eq_KQ κ ht ϖ δ Ψ Φ hΨ hq

end E1
end QuantumZipper
