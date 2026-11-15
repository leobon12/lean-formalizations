/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Inst
import InteractingSLE.Spec.Sec5.StagedS4Theta

/-!
# The candidate's chart clause at a fixed restarted time

Packet PROVE-STAGED-S4 (§5.2 of `planning/handoffs/PROVE-STAGED-S3.md`, steps R1–R6 of CROSSCOND-THETA, restarted).
For PIECES' candidate `(ℓ, t)` on the glued space of the root coupling (`StagedS4Inst`):

* `candSigma_le`: DEPTH's conditioning σ-algebras are sub-σ-algebras;
* `candEr r`, `candF r`: the validity event (alive, restarted chart avoidance at `r`) and the chart formula of the
  candidate's restarted word at the restarted time `r`;
* **`ae_condExp_cand_of_meas`**: for every sub-σ-algebra `𝓐` containing `candEr r` and the (indicated) chart formula
  at `r`, whose events inside `candEr r` meet the dyadic own-time level sets in events of DEPTH's σ-algebras (up to
  null sets), almost surely on `candEr r` the conditional characteristic value of the root field given `𝓐` is the
  chart formula at `r`. Proof: the dyadic optional passage (`setIntegral_eq_of_dyadic`) along strict upper dyadic own
  times, with (SW3) at the dyadic times (`ae_cand_charIdent`) and the right limit (`tendsto_s4F_dyF`).

The hypotheses on `𝓐` are properties of the filtration one conditions on (any `𝓐` with them works); the filtration
built for the martingale step must be shown to have them. R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedCand StagedDepth StagedS3
open Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyF dyqQ dyqQ_coe setIntegral_eq_of_dyadic ae_condExp_eq_of_forall_setIntegral)

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **DEPTH's conditioning σ-algebras of the candidate are sub-σ-algebras.** -/
theorem candSigma_le (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0) :
    candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  have hE := Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSched ℓ t q)
  have hreg := Prop59Sched.schedDrivers_regular h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)
  obtain ⟨h𝔄, -, -⟩ := exists_flowSide_schedule h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSched ℓ t q) hE hreg
    hus (schedL_mkSched hv hq).ge
  have hpm : Measurable (pastMap κ c.fn c.jumps (scheduleSpec (mkSched ℓ t q))
      (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)) (ℓ + 1)) :=
    measurable_pastMap runMeasStatement c.isPiecewiseConstantBoundaryData (scheduleSpec (mkSched ℓ t q))
      (k := ℓ + 1) (fun j _ => hE.1 j) (fun j _ => hreg j) (ℓ + 1) le_rfl
  have hUm := measurable_union_hitting ((h𝔄.comp hpm).comp measurable_fst)
    ((measurable_cfHullQ s).comp (measurable_snd (α := Ω)))
  have hFm : Measurable fun p : Ω × HistorySpace 0 0 =>
      cenTT κ (π / 2) (fun z => us z + π / 2 * chiC κ) (cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h p.1)) :=
    (measurable_cenTT κ (π / 2) _).comp (((measurable_cfFieldT κ (π / 2)).comp (measurable_rootField hG.1)).comp
      measurable_fst)
  refine sup_le (germSigma_le hUm hFm) ?_
  have hpair : Measurable fun p : Ω × HistorySpace 0 0 =>
      (pastMap κ c.fn c.jumps (scheduleSpec (mkSched ℓ t q))
        (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)) (ℓ + 1) p.1, p.2) :=
    (hpm.comp measurable_fst).prodMk measurable_snd
  have h𝔐 : (inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s) ≤
      (inferInstance : MeasurableSpace (PastData (ℓ + 1) × HistorySpace 0 0)) :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (stopSigma_le s))
  exact (MeasurableSpace.comap_mono h𝔐).trans hpair.comap_le

/-- **The validity event of the candidate's chart clause at the restarted time `r`.** -/
def candEr (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) :
    Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) ∧
    Sec7.Lemma71D.IsChartAvoid
      (fun r' => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
        (lastO ℓ t : ℝ) r' p)
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) p)
      (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) p) φ r}

/-- **The chart formula of the candidate's restarted word at the restarted time `r`** (stage weights, height
constant `2πχ + (θ_ℓ − θ₀)χ`). -/
def candF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℂ :=
  s4F κ (imgStageRhoL κ (π / 2) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (imgStageRhoR κ (π / 2) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (s3VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ))
    (s3VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ))
    s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)
    (2 * Real.pi * chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * chiC κ) φ r p

omit [StandardBorelSpace Ω] in
/-- The chart formula is a characteristic value (modulus at most one) before the restarted lifetime. -/
theorem norm_candF_le_one (hhm : Measurable h) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0} (φ : TestOn upperHalfPlaneOpens)
    {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ))
    (hr : (r : ℝ≥0∞) < s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
      (lastO ℓ t : ℝ) p) :
    ‖candF x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s φ r p‖ ≤ 1 := by
  have hEg : ∀ p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s,
      IsGood49 s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p := fun p hp => isGood49_of_mem_glueGood p hp
  have hv := chartVar_nonneg_of_conformal (isConformal_s3Chart hEg hp).1 (continuousOn_s3W hEg p) φ hr
  rw [candF, s4F, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub]
  linarith

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r`, for any admissible conditioning σ-algebra.** If
`𝓐` contains the validity event `candEr r` and the chart formula on it, the own time `θ_r` is measurable, and every
`𝓐`-event inside `candEr r` meets the dyadic own-time level sets and validity events in events of DEPTH's σ-algebras
(up to null sets), then almost surely on `candEr r` the conditional characteristic value of the root field given
`𝓐` is the chart formula of the restarted word at `r`. -/
theorem ae_condExp_cand_of_meas (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0) (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)))
    (hEr : MeasurableSet[𝓐 r] (candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r))
    (hFm : StronglyMeasurable[𝓐 r] ((candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r).indicator
      (candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r)))
    (hθ : Measurable (s4Theta s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
      (lastO ℓ t : ℝ) r))
    (hmeas : ∀ D : Set (Ω × HistorySpace 0 0), MeasurableSet[𝓐 r] D →
      D ⊆ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r → ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
        ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
          B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (D ∩ {p | dyIdx n (s4Theta s (candW x₀ h44 hκ hκ4 hb h ℓ t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) r p) = k} ∩
            s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)
              φ (dyq n k))) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) | 𝓐 r] p =
        candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r p := by
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  have h𝓐 := 𝓐.le r
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  set τ : ℝ := (lastO ℓ t : ℝ) with hτ
  set Er := candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r with hErdef
  set X : Ω × HistorySpace 0 0 → ℂ := fun p' =>
    Complex.exp (Complex.I * (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) with hXdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  have hXm : Measurable X := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (((LQGMetric.measurable_distOn_apply φ).comp (measurable_rootField hG.1)).comp measurable_fst)))
  have hXb : ∀ p, ‖X p‖ ≤ 1 := fun p => by
    simp only [hXdef]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable X μ := Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  have hFi : Integrable (Er.indicator (candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r)) μ := by
    refine Integrable.of_bound ((hFm.mono h𝓐).aestronglyMeasurable) 1 (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_candF_le_one x₀ h44 hκ hκ4 hb P h W ζ hG.1 φ hp.1 hp.2.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral h𝓐 hEr hXi hFm hFi fun A hA => ?_
  have hAv0 : ∀ n k, ¬ lastO ℓ t < dyqQ n k → s4Av s Wc Eg τ φ (dyq n k) = ∅ := by
    intro n k hq
    refine eq_empty_of_forall_notMem fun p hAv => absurd hAv.2.1 ?_
    have h1 : ((dyqQ n k : ℚ) : ℝ) ≤ (lastO ℓ t : ℝ) := by exact_mod_cast not_lt.1 hq
    rw [dyqQ_coe] at h1
    exact not_lt.2 h1
  classical
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n k => if lastO ℓ t < dyqQ n k then candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s else ⊥) ?_
    (Av := s4Av s Wc Eg τ φ)
    (F := fun q p => candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ (s4R s Wc Eg τ q p) p) ?_ ?_ hθ
    (h𝓐 _ (hA.inter hEr)) ?_ ?_
  · -- the σ-algebras are sub-σ-algebras
    intro n k
    by_cases hq : lastO ℓ t < dyqQ n k
    · simp only [hq, ↓reduceIte]
      exact candSigma_le x₀ h44 hκ hκ4 hb P h hG hus hv hq s
    · simp only [hq, ↓reduceIte]
      exact bot_le
  · intro q p hp
    exact norm_candF_le_one x₀ h44 hκ hκ4 hb P h W ζ hG.1 φ hp.1 hp.2.2.2.1
  · -- (SW3) at the dyadic own times
    intro n k
    by_cases hq : lastO ℓ t < dyqQ n k
    · simp only [hq, ↓reduceIte]
      filter_upwards [ae_cand_charIdent x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hq hs φ] with p hp hAv
      have hP : ((dyqQ n k : ℚ) : ℝ) ∈ gPre s (fun _ => ⊤) Wc Eg p := by rw [dyqQ_coe]; exact hAv.2.2.1
      have hav : Sec7.Lemma71D.IsChartAvoid (fun r => s3W s Wc Eg τ r p) (s3ζ s Wc Eg τ p) (s3Chart s Wc Eg τ p) φ
          ((capClock (gCurve s (fun _ => ⊤) Wc Eg p) ((dyqQ n k : ℚ) : ℝ)).toNNReal - s3Start s Wc Eg τ p) := by
        rw [dyqQ_coe]; exact hAv.2.2.2
      have key := hp hAv.1 hP hav
      rw [dyqQ_coe] at key
      exact key
    · rw [hAv0 n k hq]
      exact Eventually.of_forall fun p hp => absurd hp (notMem_empty p)
  · -- the pieces are in the σ-algebras
    intro n k
    by_cases hq : lastO ℓ t < dyqQ n k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hq)]
      exact hmeas _ (hA.inter hEr) inter_subset_right n k hq
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hq)]
      refine ⟨∅, @MeasurableSet.empty _ ⊥, ?_⟩
      rw [hAv0 n k hq, inter_empty]
  · -- the right limit
    filter_upwards with p hpD
    obtain ⟨-, hpA, hav⟩ := hpD
    exact tendsto_s4F_dyF hEg hpA (fun i => continuousOn_s3VL hEg _ _ _ p i)
      (fun i => continuousOn_s3VR hEg _ _ _ p i) _ hav

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
