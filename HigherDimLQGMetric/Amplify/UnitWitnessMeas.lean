import HigherDimLQGMetric.Amplify.UnitWitnessPath
import HigherDimLQGMetric.Amplify.Geometry

/-! Universal measurability of the unit-scale witness in a metric pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private def ampChainSetDist (D : ContMetric d) (V K L : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ u ∈ K, ⨅ v ∈ L, D.chainInf V u v

private def ampChainDiam (D : ContMetric d) (V K : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ u ∈ K, ⨆ v ∈ K, D.chainInf V u v

private def AmpUnitRegChain (M N : ContMetric d) (U a A₀ ℓ β₀ : ℝ) : Prop :=
  ENNReal.ofReal a ≤ acrossDist M 0 1 2 ∧
  ampChainDiam M (ann 0 (3 / 4) 3) (annCl 0 1 2) ≤ ENNReal.ofReal A₀ ∧
  (∀ ρ ∈ ({3 / 4, 3} : Set ℝ),
    ENNReal.ofReal (4 * max 1 U * ℓ) <
      ampChainSetDist M (ann 0 (1 / 2) 5) (annCl 0 1 2) (sphere 0 ρ) ∧
    ENNReal.ofReal (4 * max 1 U * ℓ) <
      ampChainSetDist N (ann 0 (1 / 2) 5) (annCl 0 1 2) (sphere 0 ρ)) ∧
  (∀ u ∈ annCl (0 : Rd d) 1 2, ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β₀ →
    M.chainInf (ann 0 (3 / 4) 3) u v < ENNReal.ofReal (ℓ / 4))

private theorem ampUnitReg_iff_chain (M N : ContMetric d)
    (hM : M.IsLength) (hN : N.IsLength) (U a A₀ ℓ β₀ : ℝ) :
    UnitReg M N U a A₀ ℓ β₀ ↔ AmpUnitRegChain M N U a A₀ ℓ β₀ := by
  have hMJ : M.internal (ann 0 (1 / 2) 5) = M.chainInf (ann 0 (1 / 2) 5) := by
    funext u v
    exact M.internal_eq_chainInf hM (isOpen_ann _ _ _) u v
  have hNJ : N.internal (ann 0 (1 / 2) 5) = N.chainInf (ann 0 (1 / 2) 5) := by
    funext u v
    exact N.internal_eq_chainInf hN (isOpen_ann _ _ _) u v
  have hMO : M.internal (ann 0 (3 / 4) 3) = M.chainInf (ann 0 (3 / 4) 3) := by
    funext u v
    exact M.internal_eq_chainInf hM (isOpen_ann _ _ _) u v
  simp only [UnitReg, AmpUnitRegChain, diamIn, setDistIn,
    ampChainDiam, ampChainSetDist, hMJ, hNJ, hMO]

private theorem ampMeasurableAcross :
    Measurable fun M : ContMetric d => acrossDist M 0 1 2 := by
  have he : (fun M : ContMetric d => acrossDist M 0 1 2) =
      fun M => ⨅ p ∈ sphere (0 : Rd d) 1 ×ˢ sphere 0 2,
        ENNReal.ofReal (M.1 p) := by
    funext M
    unfold acrossDist
    rw [biInf_prod]
  rw [he]
  refine LQGMetric.measurable_biInf_of_continuous
    (f := fun (M : ContMetric d) (p : Rd d × Rd d) => ENNReal.ofReal (M.1 p))
    (fun M => ENNReal.continuous_ofReal.comp M.1.continuous) (fun p => ?_) _
  exact (ENNReal.continuous_ofReal.comp
    (continuous_contMetric_apply_select.comp
      (continuous_id.prodMk continuous_const))).measurable

private theorem ampMeasurableChain (V : Set (Rd d)) :
    Measurable fun p : (ContMetric d × ContMetric d) × (Rd d × Rd d) =>
      p.1.1.chainInf V p.2.1 p.2.2 :=
  (ContMetric.measurable_chainInf V).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

private theorem ampMeasurableChain2 (V : Set (Rd d)) :
    Measurable fun p : (ContMetric d × ContMetric d) × (Rd d × Rd d) =>
      p.1.2.chainInf V p.2.1 p.2.2 :=
  (ContMetric.measurable_chainInf V).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

private theorem ampUnitRegChain_uMeasurable (U a A₀ ℓ β₀ : ℝ) :
    UMeasurableSet {q : ContMetric d × ContMetric d |
      AmpUnitRegChain q.1 q.2 U a A₀ ℓ β₀} := by
  let K := annCl (0 : Rd d) 1 2
  let O := ann (0 : Rd d) (3 / 4) 3
  let J := ann (0 : Rd d) (1 / 2) 5
  have hK : MeasurableSet (K ×ˢ K) :=
    (isClosed_annCl 0 1 2).measurableSet.prod (isClosed_annCl 0 1 2).measurableSet
  have hcross : UMeasurableSet {q : ContMetric d × ContMetric d |
      ENNReal.ofReal a ≤ acrossDist q.1 0 1 2} :=
    UMeasurableSet.of_measurableSet
      (measurableSet_le measurable_const (ampMeasurableAcross.comp measurable_fst))
  have hdiam : UMeasurableSet {q : ContMetric d × ContMetric d |
      ampChainDiam q.1 O K ≤ ENNReal.ofReal A₀} := by
    have hm := uMeasurableSet_iSup_le (K ×ˢ K) hK
      (ampMeasurableChain O) (c := fun _ : ContMetric d × ContMetric d => ENNReal.ofReal A₀)
      measurable_const
    convert hm using 1
    ext q
    simp only [ampChainDiam, biSup_prod]
  have hcoll (f : (ContMetric d × ContMetric d) × (Rd d × Rd d) → ℝ≥0∞)
      (hf : Measurable f) (ρ : ℝ) :
      UMeasurableSet {q : ContMetric d × ContMetric d |
        ENNReal.ofReal (4 * max 1 U * ℓ) <
          ⨅ p ∈ K ×ˢ sphere 0 ρ, f (q, p)} := by
    exact uMeasurableSet_lt_iInf (K ×ˢ sphere 0 ρ)
      ((isClosed_annCl 0 1 2).measurableSet.prod isClosed_sphere.measurableSet)
      hf measurable_const
  have hcollOne (ρ : ℝ) : UMeasurableSet {q : ContMetric d × ContMetric d |
      ENNReal.ofReal (4 * max 1 U * ℓ) <
        ampChainSetDist q.1 J K (sphere 0 ρ) ∧
      ENNReal.ofReal (4 * max 1 U * ℓ) <
        ampChainSetDist q.2 J K (sphere 0 ρ)} := by
    convert (hcoll _ (ampMeasurableChain J) ρ).inter
      (hcoll _ (ampMeasurableChain2 J) ρ) using 1
    ext q
    simp only [ampChainSetDist, biInf_prod, mem_ofPred_eq, mem_inter_iff]
  have hcollAll : UMeasurableSet {q : ContMetric d × ContMetric d |
      ∀ ρ ∈ ({3 / 4, 3} : Set ℝ),
        ENNReal.ofReal (4 * max 1 U * ℓ) <
          ampChainSetDist q.1 J K (sphere 0 ρ) ∧
        ENNReal.ofReal (4 * max 1 U * ℓ) <
          ampChainSetDist q.2 J K (sphere 0 ρ)} := by
    convert (hcollOne (3 / 4)).inter (hcollOne 3) using 1
    ext q
    simp [mem_insert_iff]
  have hmod : UMeasurableSet {q : ContMetric d × ContMetric d |
      ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ β₀ →
        q.1.chainInf O u v < ENNReal.ofReal (ℓ / 4)} := by
    let L : Set (Rd d × Rd d) :=
      {p | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ β₀}
    have hL : MeasurableSet L := hK.inter
      (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const).measurableSet
    have hRel : MeasurableSet {p : (ContMetric d × ContMetric d) ×
        (Rd d × Rd d) | p.1.1.chainInf O p.2.1 p.2.2 < ENNReal.ofReal (ℓ / 4)} :=
      measurableSet_lt (ampMeasurableChain O) measurable_const
    have hm := uMeasurableSet_forall_mem L hL hRel
    convert hm using 1
    ext q
    constructor
    · intro h p hp
      exact h p.1 hp.1.1 p.2 hp.1.2 hp.2
    · intro h u hu v hv huv
      exact h (u,v) ⟨⟨hu,hv⟩,huv⟩
  exact hcross.inter (hdiam.inter (hcollAll.inter hmod))

private def AmpUnitRel (t ℓ : ℝ) :
    Set ((ContMetric d × ContMetric d) × C(unitInterval, Rd d)) :=
  {p | (∀ s : unitInterval, p.2 s ∈ annCl 0 1 2) ∧
    p.1.1.len (pathExt p.2) 0 1 =
      p.1.1.chainInf (ann 0 (3 / 4) 3) (p.2 0) (p.2 1) ∧
    ENNReal.ofReal (ℓ / 2) ≤ p.1.1.len (pathExt p.2) 0 1 ∧
    p.1.1.len (pathExt p.2) 0 1 ≤ ENNReal.ofReal ℓ ∧
    ENNReal.ofReal t * p.1.1.len (pathExt p.2) 0 1 <
      p.1.2.chainInf (ann 0 (3 / 4) 3) (p.2 0) (p.2 1)}

private theorem ampUnitRel_measurable (t ℓ : ℝ) :
    MeasurableSet (AmpUnitRel (d := d) t ℓ) := by
  have hp (s : unitInterval) :
      Measurable fun p : (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
        p.2 s := (continuous_eval_const s).measurable.comp measurable_snd
  have hlen : Measurable fun p :
      (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
        p.1.1.len (pathExt p.2) 0 1 :=
    measurable_lenPath.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hIA : Measurable fun p :
      (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
        p.1.1.chainInf (ann 0 (3 / 4) 3) (p.2 0) (p.2 1) :=
    (ContMetric.measurable_chainInf _).comp
      ((measurable_fst.comp measurable_fst).prodMk ((hp 0).prodMk (hp 1)))
  have hIB : Measurable fun p :
      (ContMetric d × ContMetric d) × C(unitInterval, Rd d) =>
        p.1.2.chainInf (ann 0 (3 / 4) 3) (p.2 0) (p.2 1) :=
    (ContMetric.measurable_chainInf _).comp
      ((measurable_snd.comp measurable_fst).prodMk ((hp 0).prodMk (hp 1)))
  have hpath : MeasurableSet {p : (ContMetric d × ContMetric d) ×
      C(unitInterval, Rd d) | ∀ s : unitInterval, p.2 s ∈ annCl 0 1 2} := by
    have hc : IsClosed {η : C(unitInterval, Rd d) |
        ∀ s : unitInterval, η s ∈ annCl 0 1 2} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun s => (isClosed_annCl 0 1 2).preimage
        (continuous_eval_const s)
    exact hc.measurableSet.preimage measurable_snd
  unfold AmpUnitRel
  exact hpath.inter ((measurableSet_eq_fun hlen hIA).inter
    ((measurableSet_le measurable_const hlen).inter
      ((measurableSet_le hlen measurable_const).inter
        (measurableSet_lt (measurable_const.mul hlen) hIB))))

def AmpUnitWitChain (q : ContMetric d × ContMetric d)
    (U a A₀ ℓ β₀ t : ℝ) : Prop :=
  AmpUnitRegChain q.1 q.2 U a A₀ ℓ β₀ ∧
    ∃ η : C(unitInterval, Rd d), (q, η) ∈ AmpUnitRel t ℓ

theorem ampUnitWitChain_uMeasurable (U a A₀ ℓ β₀ t : ℝ) :
    UMeasurableSet {q : ContMetric d × ContMetric d |
      AmpUnitWitChain q U a A₀ ℓ β₀ t} := by
  have he : UMeasurableSet {q : ContMetric d × ContMetric d |
      ∃ η : C(unitInterval, Rd d), (q, η) ∈ AmpUnitRel t ℓ} :=
    UMeasurableSet.setOf_exists (ampUnitRel_measurable t ℓ)
  exact (ampUnitRegChain_uMeasurable U a A₀ ℓ β₀).inter he

theorem ampUnitWit_iff_chain (M N : ContMetric d)
    (hM : M.IsLength) (hN : N.IsLength) (U a A₀ ℓ β₀ t : ℝ) :
    AmplifyUnitWit M N U a A₀ ℓ β₀ t ↔
      AmpUnitWitChain (M,N) U a A₀ ℓ β₀ t := by
  let O := ann (0 : Rd d) (3 / 4) 3
  have hO : IsOpen O := isOpen_ann _ _ _
  have hIO : annCl (0 : Rd d) 1 2 ⊆ O :=
    by convert
      (amplify_core_subset_open (s := 1) (by norm_num) (0 : Rd d))
        using 1 <;> norm_num [O]
  constructor
  · rintro ⟨hReg, R, hRI, ⟨hRc, hRO, hGeo⟩, hLow, hHigh, hRatio⟩
    obtain ⟨η, hηR, hLen⟩ := exists_pathContinuousMap hRc
    have hη0 : η 0 = R 0 := (pathExt_zero η).symm.trans (hηR (by norm_num))
    have hη1 : η 1 = R 1 := (pathExt_one η).symm.trans (hηR (by norm_num))
    have hηI : ∀ s : unitInterval, η s ∈ annCl 0 1 2 := by
      intro s
      have hs : η s ∈ range η := ⟨s, rfl⟩
      rw [← pathExt_range η] at hs
      obtain ⟨u, hu, huEq⟩ := hs
      rw [← huEq, hηR hu]
      exact hRI u hu
    refine ⟨(ampUnitReg_iff_chain M N hM hN U a A₀ ℓ β₀).1 hReg,
      η, hηI, ?_, ?_, ?_, ?_⟩
    · change M.len (pathExt η) 0 1 = M.chainInf O (η 0) (η 1)
      rw [← M.internal_eq_chainInf hM hO, hη0, hη1, hLen]
      exact hGeo
    · rw [hLen]
      exact hLow
    · rw [hLen]
      exact hHigh
    · change ENNReal.ofReal t * M.len (pathExt η) 0 1 <
        N.chainInf O (η 0) (η 1)
      rw [hLen, ← N.internal_eq_chainInf hN hO, hη0, hη1]
      exact hRatio
  · rintro ⟨hReg, η, hηI, hGeo, hLow, hHigh, hRatio⟩
    let R : ℝ → Rd d := pathExt η
    have hRI : ∀ u ∈ Icc (0 : ℝ) 1, R u ∈ annCl 0 1 2 := by
      intro u hu
      have hs : R u ∈ R '' Icc (0 : ℝ) 1 := ⟨u, hu, rfl⟩
      rw [pathExt_range η] at hs
      obtain ⟨s, hs⟩ := hs
      rw [← hs]
      exact hηI s
    have hRO : ∀ u ∈ Icc (0 : ℝ) 1, R u ∈ O :=
      fun u hu => hIO (hRI u hu)
    have hRgeo : IsGeodIn M O R := by
      refine ⟨pathExt_continuousOn η, hRO, ?_⟩
      change M.len (pathExt η) 0 1 = M.internal O (pathExt η 0) (pathExt η 1)
      rw [pathExt_zero, pathExt_one, M.internal_eq_chainInf hM hO]
      exact hGeo
    have hRatio' : ENNReal.ofReal t * M.len R 0 1 <
        N.internal O (R 0) (R 1) := by
      change ENNReal.ofReal t * M.len (pathExt η) 0 1 <
        N.internal O (pathExt η 0) (pathExt η 1)
      rw [pathExt_zero, pathExt_one, N.internal_eq_chainInf hN hO]
      exact hRatio
    exact ⟨(ampUnitReg_iff_chain M N hM hN U a A₀ ℓ β₀).2 hReg,
      R, hRI, hRgeo, hLow, hHigh, hRatio'⟩

/-- The unit witness is measurable in the completion of any probability law
supported on pairs of length metrics. -/
theorem amplify_nullMeasurableSet_unitWit
    (μ : Measure (ContMetric d × ContMetric d)) [IsProbabilityMeasure μ]
    (hM : ∀ᵐ q ∂μ, q.1.IsLength) (hN : ∀ᵐ q ∂μ, q.2.IsLength)
    (U a A₀ ℓ β₀ t : ℝ) :
    NullMeasurableSet {q : ContMetric d × ContMetric d |
      AmplifyUnitWit q.1 q.2 U a A₀ ℓ β₀ t} μ := by
  have hE : NullMeasurableSet {q : ContMetric d × ContMetric d |
      AmpUnitWitChain q U a A₀ ℓ β₀ t} μ :=
    (ampUnitWitChain_uMeasurable U a A₀ ℓ β₀ t).nullMeasurableSet μ
  have heq : {q : ContMetric d × ContMetric d |
      AmplifyUnitWit q.1 q.2 U a A₀ ℓ β₀ t} =ᵐ[μ]
      {q | AmpUnitWitChain q U a A₀ ℓ β₀ t} := by
    filter_upwards [hM, hN] with q hm hn
    exact propext (ampUnitWit_iff_chain q.1 q.2 hm hn U a A₀ ℓ β₀ t)
  exact hE.congr heq.symm

end HigherDimLQGMetric
