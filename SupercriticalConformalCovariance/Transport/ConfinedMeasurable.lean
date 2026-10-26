import SupercriticalConformalCovariance.Transport.Scale
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GammaLower
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.MovingBall

/-! Borel measurability of the closed-disk confined metric in the LSC function topology. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Transport

theorem compact_inf_joint_lsc {f : LSCMetric × (ℂ × ℂ) → EReal}
    (hf : LowerSemicontinuous f) {K : Set (ℂ × ℂ)} (hK : IsCompact K) :
    LowerSemicontinuous (fun D : LSCMetric => ⨅ q ∈ K, f (D, q)) := by
  by_cases hKe : K = ∅
  · simpa [hKe] using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : LSCMetric => (⊤ : EReal)))
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : LSCMetric × K → EReal := fun p => f (p.1, p.2.1)
  have hg : LowerSemicontinuous g :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro t
  have hclosed : IsClosed {p : LSCMetric × K | g p ≤ t} := hg.isClosed_preimage t
  have hproj : IsClosed (Prod.fst '' {p : LSCMetric × K | g p ≤ t}) :=
    isClosedMap_fst_of_compactSpace _ hclosed
  have heq : (fun D : LSCMetric => ⨅ q ∈ K, f (D, q)) ⁻¹' Iic t =
      Prod.fst '' {p : LSCMetric × K | g p ≤ t} := by
    ext D
    simp only [mem_preimage, mem_Iic, mem_image, mem_setOf_eq]
    constructor
    · intro h
      have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
      have hfix : LowerSemicontinuous (fun q : ℂ × ℂ => f (D, q)) :=
        hf.comp (continuous_const.prodMk continuous_id)
      obtain ⟨q, hq, hmin⟩ :=
        (hfix.lowerSemicontinuousOn K).exists_isMinOn hne hK
      refine ⟨(D, ⟨q, hq⟩), ?_, rfl⟩
      change f (D, q) ≤ t
      have hle : f (D, q) ≤ ⨅ q ∈ K, f (D, q) :=
        le_iInf₂ fun q' hq' => hmin hq'
      exact hle.trans h
    · rintro ⟨⟨D', ⟨q, hq⟩⟩, hp, rfl⟩
      exact (iInf₂_le q hq).trans hp
  rw [heq]
  exact hproj

/-- The intrinsic metric of a closed disk, set to infinity outside its endpoint carrier, as an
`LSCFun`. It cannot be an `LSCMetric` on the plane because its diagonal is infinite outside. -/
def closedDiskFun (c : ℂ) (R : ℝ) (D : LSCMetric) : LSCFun :=
  ⟨fun q => ((SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
      D c R q.1 q.2 : ℝ≥0∞) : EReal),
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (SupercriticalConformalCovariance.Compact.closed_disk_intrinsic_lsc D c R)
      EReal.coe_ennreal_strictMono.monotone⟩

/-- The closed-disk confined metric is a Borel `LSCFun`-valued function of its global metric. -/
theorem measurable_closedDiskFun [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (c : ℂ) (R : ℝ) :
    Measurable (closedDiskFun c R) := by
  let f : LSCMetric × (ℂ × ℂ) → EReal := fun p =>
    ((SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
      p.1 c R p.2.1 p.2.2 : ℝ≥0∞) : EReal)
  have hjoint : LowerSemicontinuous f := by
    have hc : Continuous (fun p : LSCMetric × (ℂ × ℂ) => (p.1, (c, (R, p.2)))) :=
      continuous_fst.prodMk (continuous_const.prodMk
        (continuous_const.prodMk continuous_snd))
    have hraw : LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) =>
        SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
          p.1 c R p.2.1 p.2.2) := by
      change LowerSemicontinuous
        ((fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
          SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
            p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
          (fun p : LSCMetric × (ℂ × ℂ) => (p.1, (c, (R, p.2)))))
      exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf_joint_lsc.comp hc
    exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hraw
      EReal.coe_ennreal_strictMono.monotone
  have hcomp : ∀ K : Set (ℂ × ℂ), IsCompact K →
      Measurable (fun D : LSCMetric => ⨅ q ∈ K, (closedDiskFun c R D).1 q) := by
    intro K hK
    exact (compact_inf_joint_lsc hjoint hK).measurable
  apply SupercriticalLQGUniqueness.B2.PfeAxioms.measurable_lscFun_of_tests
  · intro O hO r
    have heq : {D : LSCMetric | ∃ q ∈ O, (closedDiskFun c R D).1 q < (((r : ℝ) : EReal))} =
        (fun D => ⨅ q ∈ O, (closedDiskFun c R D).1 q) ⁻¹' Iio (((r : ℝ) : EReal)) := by
      ext D
      simp only [mem_ofPred_eq, mem_preimage, mem_Iio, iInf_lt_iff, exists_prop]
    rw [heq]
    have hm : Measurable (fun D : LSCMetric => ⨅ q ∈ O, (closedDiskFun c R D).1 q) := by
      simp_rw [SupercriticalLQGUniqueness.B2.PfeAxioms.iInf_open_eq_iInf_ballFamily
        (u := fun q => (closedDiskFun c R _).1 q) hO]
      refine Measurable.iInf fun j => ?_
      by_cases hj : SupercriticalLQGUniqueness.B2.PfeAxioms.ballFamily j ⊆ O
      · simp only [hj, iInf_pos]
        exact hcomp _ (SupercriticalLQGUniqueness.B2.PfeAxioms.isCompact_ballFamily j)
      · simp only [hj, iInf_false]
        exact measurable_const
    exact hm measurableSet_Iio
  · intro K hK r
    have heq : {D : LSCMetric | ∀ q ∈ K, (((r : ℝ) : EReal)) < (closedDiskFun c R D).1 q} =
        (fun D => ⨅ q ∈ K, (closedDiskFun c R D).1 q) ⁻¹' Ioi (((r : ℝ) : EReal)) := by
      ext D
      simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
      exact SupercriticalLQGUniqueness.B2.PfeAxioms.forall_lt_iff_lt_iInf
        (closedDiskFun c R D).2 hK _ (EReal.coe_ne_top _)
    rw [heq]
    exact hcomp K hK measurableSet_Ioi

/-- A measurable `LSCFun` version of the confined domain metric on a fixed closed disk.
The same theorem applies to the source realization and to the realization of the pulled field. -/
theorem exists_measurable_confined_version {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : LQGMetric.DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn V}
    {h₀ : Ω → LQGMetric.DistC} {f : Ω → C(V, ℝ)}
    (hR : SupercriticalConformalCovariance.IsDomainRealization V P h h₀ f)
    (c : ℂ) (R : ℝ) (hKV : Metric.closedBall c R ⊆ V)
    [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    ∃ F : Ω → LSCFun, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
        (F ω).1 q = ((SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) q : ℝ≥0∞) : EReal) := by
  obtain ⟨n, hn⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen (isCompact_closedBall c R) hKV
  let g : Ω → LQGMetric.DistC := fun ω =>
    LQGMetric.addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω))
  have hfcut : Measurable (fun ω => SupercriticalConformalCovariance.Domain.cutF V n (f ω)) := by
    change Measurable (fun ω => SupercriticalConformalCovariance.Domain.cutExt V.isOpen
      (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) n) (f ω))
    exact SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen _ hR.2.2.1
  have hgm : Measurable g := LQGMetric.measurable_addFun.comp
    (hR.2.1.1.prodMk hfcut)
  refine ⟨fun ω => closedDiskFun c R (D (g ω)),
    (measurable_closedDiskFun c R).comp (hD.1.comp hgm), ?_⟩
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hR.2.1] with ω hω q
  have heq : SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) q =
      SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
        (D (g ω)) c R q.1 q.2 := by
    unfold SupercriticalConformalCovariance.Domain.confined
    split_ifs with hq
    · rw [hω _ (SupercriticalConformalCovariance.Domain.resC hKV (f ω))
        (SupercriticalConformalCovariance.Domain.cutF V n (f ω))
        (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f ω) z (hn hz))]
      rfl
    · symm
      refine eq_top_iff.2 (le_iInf fun P => le_iInf fun a => le_iInf fun b =>
        le_iInf fun hP => le_iInf fun hK => le_iInf fun ha => le_iInf fun hb => ?_)
      exfalso
      refine hq ⟨?_, ?_⟩
      · rw [← ha]; exact hK a (left_mem_Icc.2 hP.1)
      · rw [← hb]; exact hK b (right_mem_Icc.2 hP.1)
  exact congrArg (fun x : ℝ≥0∞ => (x : EReal)) heq.symm

end SupercriticalConformalCovariance.Transport
