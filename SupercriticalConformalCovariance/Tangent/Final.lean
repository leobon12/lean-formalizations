import SupercriticalConformalCovariance.Tangent.TangentLaw
import SupercriticalConformalCovariance.Tangent.Conf
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete

/-!
# Lemma 3.3, final forms

* `tangent_limit_final`: Lemma 3.3 (strong form, convergence in probability) with **no hypothesis
  beyond the setting**: `0 < Q` now comes from the sealed positivity theorem `axpos` (every weak LQG
  metric has `Q > 0`).
* `exists_measurable_versions`: Borel `LSCFun`-valued versions of `d_n` and `e_n`. The version of
  `d_n` is a Borel function of the field `h` (`diskMetric (R n) (D h)`); the version of `e_n` is a
  Borel function of the realization data `(h̄_n, f_n)` (the target-locality lemmas' compact pull-back confinement,
  copied into `SupercriticalConformalCovariance.Tangent.CompactPull`).
* `tangent_limit_law_final`: (5) in law, for these versions, with no extra hypotheses.
* `tangent_limit_conf`: the same convergence for the diagonal-corrected confined metrics as global
  `LSCMetric`s (the form the Proposition 4.3 proof consumes), for **any** `LSCMetric`-valued families that agree with
  `d_n`, `e_n` off the diagonal; `exists_measurable_conf_versions` constructs Borel such families
  (`confDisk`, `confPull`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC IsWholePlaneGFF restrictTo addFun CoordJ pairJ IsGFFPlusCont)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric LSCTendsto IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn)
open SupercriticalConformalCovariance.Domain (confined resC cutF exW cutF_eq exists_subset_exW ae_weylScaleOn_eq_internal
  isGFFPlusCont_addFun_of_measurable measurable_cutExt)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)

/-- The image map `K → ψ(K)` of a map continuous on `K`. -/
def imageMapK (ψ : ℂ → ℂ) (K : Set ℂ) (hc : ContinuousOn ψ K) : C(K, ψ '' K) :=
  ⟨fun z => ⟨ψ z, mem_image_of_mem ψ z.2⟩,
    (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _⟩

theorem imageMapK_injective {ψ : ℂ → ℂ} {K : Set ℂ} (hc : ContinuousOn ψ K) (hi : InjOn ψ K) :
    Function.Injective (imageMapK ψ K hc) := fun x y hxy =>
  Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy))

/-- **Lemma 3.3, final strong form**: no hypothesis beyond the setting. -/
theorem tangent_limit_final {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n)) :
    SubseqLSC P (fun n ω q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) ∧
      SubseqLSC P (tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr)
        (fun ω q => (D (h ω) q : EReal)) :=
  tangent_limit hQ (SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.axpos ξ Q D
    (SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD)) hD hψ hexhaust
    hzero ha0 ha hR hRU P hh hbar fr hreal

/-- The realization-data form of `e_n`: for each `n`, a cut-off level `m` and the image map, the
compact pull-back confinement of the whole-plane field `h̄_n + χ_m f_n` equals `e_n` a.s. -/
theorem ae_compactPullFun_eq_tangentEval {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    {R : ℕ → ℝ} (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) (hhb : ∀ n, IsGFFPlusCont (hbar n) P)
    (n : ℕ) (hc : ContinuousOn (ψ n) (closedBall 0 (R n))) (hK : IsCompact (closedBall (0 : ℂ) (R n)))
    (hYc : IsCompact (ψ n '' closedBall (0 : ℂ) (R n))) (m : ℕ)
    (hm : ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) m) :
    ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      (compactPullFun _ _ hK hYc (imageMapK (ψ n) _ hc)
        (D (addFun (hbar n ω) (cutF (V n) m (fr n ω))))).1 q =
      (tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω q : EReal) := by
  classical
  filter_upwards [ae_weylScaleOn_eq_internal hD P (hhb n)] with ω hω q
  by_cases hq : q.1 ∈ closedBall (0 : ℂ) (R n) ∧ q.2 ∈ closedBall (0 : ℂ) (R n)
  · have h1 := compactPullFun_on _ _ hK hYc (imageMapK (ψ n) _ hc)
      (D (addFun (hbar n ω) (cutF (V n) m (fr n ω)))) (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)
    simp only at h1
    rw [h1]
    unfold tangentEval
    rw [if_pos hq]
    congr 1
    have hpY : ψ n q.1 ∈ ψ n '' closedBall (0 : ℂ) (R n) ∧ ψ n q.2 ∈ ψ n '' closedBall (0 : ℂ) (R n) :=
      ⟨mem_image_of_mem _ hq.1, mem_image_of_mem _ hq.2⟩
    unfold confined
    rw [dif_pos hpY]
    have hext : ∀ z (hz : z ∈ ψ n '' closedBall (0 : ℂ) (R n)),
        cutF (V n) m (fr n ω) z = resC (tangentImage_subset hψ hRU n) (fr n ω) ⟨z, hz⟩ :=
      fun z hz => by rw [cutF_eq (V n) m (fr n ω) z (hm hz)]; rfl
    rw [hω _ _ _ hext]
    rfl
  · rw [compactPullFun_off _ _ hK hYc _ _ q hq]
    unfold tangentEval
    rw [if_neg hq]
    rfl

/-- **Measurable versions of `d_n` and `e_n`.** -/
theorem exists_measurable_versions {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    {R : ℕ → ℝ} (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hhm : Measurable h) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hhb : ∀ n, IsGFFPlusCont (hbar n) P) (hfr : ∀ n, Measurable (fr n))
    [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    ∃ G E : ℕ → Ω → LSCFun, (∀ n, Measurable (G n)) ∧ (∀ n, Measurable (E n)) ∧
      (∀ n ω, (G n ω).1 = fun q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal)) ∧
      (∀ n, ∀ᵐ ω ∂P, (E n ω).1 = tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω) := by
  classical
  have hcl : ∀ n, closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) := fun n =>
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  have hc : ∀ n, ContinuousOn (ψ n) (closedBall 0 (R n)) := fun n =>
    (hψ n).1.continuousOn.mono (hcl n)
  have hK : ∀ n, IsCompact (closedBall (0 : ℂ) (R n)) := fun n => isCompact_closedBall _ _
  have hYc : ∀ n, IsCompact (ψ n '' closedBall (0 : ℂ) (R n)) := fun n =>
    (hK n).image_of_continuousOn (hc n)
  have hmex : ∀ n, ∃ m, ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) m := fun n =>
    exists_subset_exW (V n).isOpen (hYc n) (tangentImage_subset hψ hRU n)
  choose m hm using hmex
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  refine ⟨fun n ω => diskMetric (R n) (D (h ω)),
    fun n ω => compactPullFun _ _ (hK n) (hYc n) (imageMapK (ψ n) _ (hc n))
      (D (addFun (hbar n ω) (cutF (V n) (m n) (fr n ω)))), fun n => ?_, fun n => ?_,
    fun n ω => ?_, fun n => ?_⟩
  · exact (measurable_diskMetric _).comp (hD.1.comp hhm)
  · have hcm : Measurable fun ω => cutF (V n) (m n) (fr n ω) :=
      measurable_cutExt (V n).isOpen _ (hfr n)
    have hF : Measurable fun ω => addFun (hbar n ω) (cutF (V n) (m n) (fr n ω)) :=
      LQGMetric.measurable_addFun.comp ((hhb n).1.prodMk hcm)
    exact (measurable_compactPullFun _ _ _ _ _).comp (hD.1.comp hF)
  · funext q
    simp only [diskMetric_apply, closedBallPathInf_eq_extInternal]
  · filter_upwards [ae_compactPullFun_eq_tangentEval hD hψ hRU P hbar fr hhb n (hc n) (hK n) (hYc n)
      (m n) (hm n)] with ω hω
    funext q
    rw [hω q, tangentE_eq]

/-- **(5) in law**, for the measurable versions, with no extra hypotheses. -/
theorem tangent_limit_law_final {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    ∃ G E : ℕ → Ω → LSCFun, (∀ n, Measurable (G n)) ∧ (∀ n, Measurable (E n)) ∧
      (∀ n ω, (G n ω).1 = fun q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal)) ∧
      (∀ n, ∀ᵐ ω ∂P, (E n ω).1 = tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω) ∧
      ∀ F : BoundedContinuousFunction ((CoordJ → ℝ) × LSCFun × LSCFun) ℝ,
        Tendsto (fun n => ∫ ω, F (pairJ ⊤ (h ω), G n ω, E n ω) ∂P) atTop
          (𝓝 (∫ ω, F (pairJ ⊤ (h ω), (D (h ω)).toLSCFun, (D (h ω)).toLSCFun) ∂P)) := by
  obtain ⟨G, E, hGm, hEm, hG, hE⟩ := exists_measurable_versions hD hψ hRU P hh.measurable hbar fr
    (fun n => (hreal n).2.1) (fun n => (hreal n).2.2.1)
  refine ⟨G, E, hGm, hEm, hG, hE, fun F => ?_⟩
  exact tangent_limit_law hQ (SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.axpos ξ Q D
    (SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD)) hD hψ hexhaust
    hzero ha0 ha hR hRU P hh hbar fr hreal G E hGm hEm
    (fun n => Eventually.of_forall fun ω => hG n ω) hE F

/-- **Lemma 3.3 for diagonal-corrected confined metrics** (the form Proposition 4.3 consumes): for
any `LSCMetric`-valued families that agree with `d_n`, resp. `e_n`, off the diagonal almost surely,
convergence in probability to `D_h` in the topology of DG Definition 1.2. -/
theorem tangent_limit_conf {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    (Dd De : ℕ → Ω → LSCMetric)
    (hDd : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
      Dd n ω (x, y) = extInternal (D (h ω)) (closedBall 0 (R n)) (x, y))
    (hDe : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
      De n ω (x, y) = tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω (x, y)) :
    SubseqLSC P (fun n ω q => (Dd n ω q : EReal)) (fun ω q => (D (h ω) q : EReal)) ∧
      SubseqLSC P (fun n ω q => (De n ω q : EReal)) (fun ω q => (D (h ω) q : EReal)) := by
  obtain ⟨hd, he⟩ := tangent_limit_final hQ hD hψ hexhaust hzero ha0 ha hR hRU P hh hbar fr hreal
  have hD0 : ∀ ω x, D (h ω) (x, x) = 0 := fun ω x => (D (h ω)).2.1.1 x
  constructor
  · intro ns hns
    obtain ⟨ms, hms, hae⟩ := hd ns hns
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hae, ae_all_iff.2 hDd] with ω hω hdω
    exact lscTendsto_of_eqOn_offDiag (F := fun k q => extInternal (D (h ω)) (closedBall 0 (R (ns (ms k)))) q)
      (G := fun k q => Dd (ns (ms k)) ω q) (hD0 ω) (fun k x => (Dd (ns (ms k)) ω).2.1.1 x)
      (fun k q hq => hdω _ q.1 q.2 hq) hω
  · intro ns hns
    obtain ⟨ms, hms, hae⟩ := he ns hns
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hae, ae_all_iff.2 hDe] with ω hω heω
    have hω' : LSCTendsto
        (fun k q => (tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr
          (ns (ms k)) ω q : EReal)) (fun q => (D (h ω) q : EReal)) := by
      have e : (fun k => tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr (ns (ms k)) ω) =
          fun k q => (tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr
            (ns (ms k)) ω q : EReal) := by
        funext k q; exact tangentE_eq _ _ _ _ _ _ _ _ _ _ _
      rw [← e]; exact hω
    exact lscTendsto_of_eqOn_offDiag (G := fun k q => De (ns (ms k)) ω q) (hD0 ω)
      (fun k x => (De (ns (ms k)) ω).2.1.1 x) (fun k q hq => heω _ q.1 q.2 hq) hω'

/-- **Borel diagonal-corrected confined metrics** agreeing with `d_n`, `e_n` off the diagonal:
`confDisk (D h) R_n` (a Borel function of the field `h`) and the diagonal-corrected compact pull-back
of the realized target field (a Borel function of the realization data). -/
theorem exists_measurable_conf_versions {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    {R : ℕ → ℝ} (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hhm : Measurable h) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hhb : ∀ n, IsGFFPlusCont (hbar n) P) (hfr : ∀ n, Measurable (fr n)) :
    ∃ Dd De : ℕ → Ω → LSCMetric, (∀ n, Measurable (Dd n)) ∧ (∀ n, Measurable (De n)) ∧
      (∀ n ω, Dd n ω = confDisk (D (h ω)) (R n)) ∧
      (∀ n ω x y, x ≠ y → Dd n ω (x, y) = extInternal (D (h ω)) (closedBall 0 (R n)) (x, y)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
        De n ω (x, y) = tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω (x, y)) := by
  classical
  have hcl : ∀ n, closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) := fun n =>
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  have hc : ∀ n, ContinuousOn (ψ n) (closedBall 0 (R n)) := fun n =>
    (hψ n).1.continuousOn.mono (hcl n)
  have hK : ∀ n, IsCompact (closedBall (0 : ℂ) (R n)) := fun n => isCompact_closedBall _ _
  have hYc : ∀ n, IsCompact (ψ n '' closedBall (0 : ℂ) (R n)) := fun n =>
    (hK n).image_of_continuousOn (hc n)
  have hinj : ∀ n, Function.Injective (imageMapK (ψ n) _ (hc n)) := fun n =>
    imageMapK_injective (hc n) ((hψ n).2.injOn.mono (hcl n))
  have hmex : ∀ n, ∃ m, ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) m := fun n =>
    exists_subset_exW (V n).isOpen (hYc n) (tangentImage_subset hψ hRU n)
  choose m hm using hmex
  refine ⟨fun n ω => confDisk (D (h ω)) (R n),
    fun n ω => confPull (D (addFun (hbar n ω) (cutF (V n) (m n) (fr n ω))))
      (ψ n '' closedBall 0 (R n)) (closedBall 0 (R n)) (hK n) (hYc n) (imageMapK (ψ n) _ (hc n))
      (hinj n), fun n => ?_, fun n => ?_, fun n ω => rfl, fun n ω x y hxy => ?_, fun n => ?_⟩
  · exact (measurable_confDisk _).comp (hD.1.comp hhm)
  · have hcm : Measurable fun ω => cutF (V n) (m n) (fr n ω) :=
      measurable_cutExt (V n).isOpen _ (hfr n)
    have hF : Measurable fun ω => addFun (hbar n ω) (cutF (V n) (m n) (fr n ω)) :=
      LQGMetric.measurable_addFun.comp ((hhb n).1.prodMk hcm)
    exact (measurable_confPull _ _ (hK n) (hYc n) _ (hinj n)).comp (hD.1.comp hF)
  · show confDisk (D (h ω)) (R n) (x, y) = _
    rw [confDisk_apply, if_neg hxy]
  · filter_upwards [ae_compactPullFun_eq_tangentEval hD hψ hRU P hbar fr hhb n (hc n) (hK n) (hYc n)
      (m n) (hm n)] with ω hω x y hxy
    have h1 := hω (x, y)
    change SupercriticalConformalCovariance.Tangent.extendMetric _ (SupercriticalConformalCovariance.Tangent.pullInner _ _ _ _) (x, y) = _
    rw [extendMetric_pullInner_eq _ _ _ (hK n) (hYc n), if_neg hxy, h1, EReal.toENNReal_coe]

/-- **Lemma 3.3 for diagonal-corrected confined metrics, final form** (no hypothesis beyond the
setting): `confDisk (D h) R_n → D_h` in probability, and there is a Borel family of
diagonal-corrected confined target metrics, equal to `e_n` off the diagonal a.s., converging in
probability to `D_h`. -/
theorem tangent_limit_conf_final {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n)) :
    (∀ n, Measurable fun ω => confDisk (D (h ω)) (R n)) ∧
      SubseqLSC P (fun n ω q => (confDisk (D (h ω)) (R n) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) ∧
      ∃ De : ℕ → Ω → LSCMetric, (∀ n, Measurable (De n)) ∧
        (∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
          De n ω (x, y) = tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω (x, y)) ∧
        SubseqLSC P (fun n ω q => (De n ω q : EReal)) (fun ω q => (D (h ω) q : EReal)) := by
  obtain ⟨Dd, De, hDdm, hDem, hDd, hDdoff, hDe⟩ := exists_measurable_conf_versions hD hψ hRU P
    hh.measurable hbar fr (fun n => (hreal n).2.1) (fun n => (hreal n).2.2.1)
  have hc := tangent_limit_conf hQ hD hψ hexhaust hzero ha0 ha hR hRU P hh hbar fr hreal Dd De
    (fun n => Eventually.of_forall fun ω => hDdoff n ω) hDe
  have e : Dd = fun n ω => confDisk (D (h ω)) (R n) := by funext n ω; exact hDd n ω
  subst e
  exact ⟨hDdm, hc.1, De, hDem, hDe, hc.2⟩

end SupercriticalConformalCovariance.Tangent
