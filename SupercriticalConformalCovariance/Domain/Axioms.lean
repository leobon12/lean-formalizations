import SupercriticalConformalCovariance.Domain.AeEq
import SupercriticalConformalCovariance.Domain.Geometry
import SupercriticalConformalCovariance.Compact.ClosedDiskBridge

/-!
# Domain forms of the axioms, through realizations

For a strong LQG metric `D`, open `V`, and a realization `(h₀, f)` of a
field `h` on `V` (`IsDomainRealization`):

* **Weyl scaling (field level)** `isDomainRealization_add`: `(h₀, f + g)` realizes `h + g` for a
  measurable random `g ∈ C(V)`. The metric side, `d_{f+g} = (e^{ξ g} · d_f)_V` simultaneously in
  `g`, is `ae_domainMetric_add` (from `Geometry.weylScaleOn_add_eq_weylDistOnWith`).
* **Restriction** `isDomainRealization_restrictOn`: `(h₀, f|_W)` realizes `h|_W` for open `W ⊆ V`;
  `ae_domainMetric_restrict`: the `W`-metric is the internal metric of the `V`-metric on `W`.
* **Locality** `ae_domainMetric_eq_of_restrictOn_eq` (pathwise: fields agreeing on `W` have equal
  `W`-metrics, whatever their realizations) and `exists_measurable_domainMetric` (the domain metric
  is a.s. a measurable function of `h`, Axiom II's shape).
* **Length space** `ae_domainMetric_isLength`, and **consistency with the whole-plane metric**
  `ae_domainMetric_eq_internal` (if `F ∈ C(ℂ)` extends `f`, the domain metric is
  `D_{h₀+F}(·, ·; V)`, simultaneously in `F`), with `isDomainRealization_restrictTo` (`(h₀, 0)`
  realizes `h₀|_V`) and `ae_domainMetric_zero_eq_internal` (`d_0 = D_{h₀}(·, ·; V)`).
* **Lower semicontinuity of confined metrics** `ae_confined_lsc`: for every closed disk
  `K ⊆ V`, the confined domain metric on `K` (∞ off `K × K`) is lower semicontinuous on `ℂ × ℂ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open LQGMetric (DistC DistOn TestOn TestC restrictTo IsGFFPlusCont addFun ofCont)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric weylScale)
open SupercriticalConformalCovariance (IsDomainRealization domainMetric weylScaleOn)

/-! ## Restriction of distributions between open sets -/

/-- `h|_W` for `h ∈ 𝒟'(V)`, `W ⊆ V`. -/
def restrictOn {W V : Opens ℂ} (hWV : W ≤ V) (h : DistOn V) : DistOn W :=
  h.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V))

theorem restrictOn_apply {W V : Opens ℂ} (hWV : W ≤ V) (h : DistOn V) (φ : TestOn W) :
    restrictOn hWV h φ = h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V) φ) :=
  rfl

theorem measurable_restrictOn {W V : Opens ℂ} (hWV : W ≤ V) :
    Measurable (restrictOn hWV) :=
  LQGMetric.measurable_distOn_iff.2 fun φ => LQGMetric.measurable_distOn_apply _

/-- `restrictTo` factors through `restrictOn`. -/
theorem restrictOn_restrictTo {W V : Opens ℂ} (hWV : W ≤ V) (h₀ : DistC) :
    restrictOn hWV (restrictTo V h₀) = restrictTo W h₀ := by
  ext φ
  show h₀ _ = h₀ _
  congr 1
  ext x
  simp only [ContinuousLinearMap.coe_coe]
  rw [coe_monoCLM le_top, coe_monoCLM le_top, coe_monoCLM hWV]

theorem measurable_resC {W V : Set ℂ} (hWV : W ⊆ V) :
    Measurable (resC (V := V) hWV) :=
  (ContinuousMap.continuous_precomp _).measurable

/-! ## Distributions of continuous functions on `V`, through cutoffs -/

/-- For `φ ∈ 𝓓(V)` supported in `W n`, the pairing of `f ∈ C(V)` (extended by `0`) with `φ` is the
pairing of the cut-off extension `χ_n f ∈ C(ℂ)` with `φ`. -/
theorem ofFun_extZ_apply (V : Opens ℂ) (f : C((V : Set ℂ), ℝ)) (φ : TestOn V) {n : ℕ}
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ exW V n) :
    Distribution.ofFun V (Function.extend Subtype.val f 0) volume ⊤ φ =
      ofCont (cutF V n f) (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) := by
  have hloc : LocallyIntegrableOn (Function.extend Subtype.val f 0) (V : Set ℂ) volume :=
    (continuousOn_extZ f).locallyIntegrableOn V.isOpen.measurableSet
  rw [Distribution.ofFun_apply hloc, LQGMetric.ofCont_apply]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [coe_monoCLM le_top, smul_eq_mul]
  by_cases hx : φ x = 0
  · simp [hx]
  · have hxW : x ∈ exW V n := hφ (subset_tsupport _ hx)
    have e := extZ_of_mem f (exW_subset V n hxW)
    unfold extZ at e
    rw [cutF_eq V n f x hxW, e]

theorem exists_tsupport_subset_exW (V : Opens ℂ) (φ : TestOn V) :
    ∃ n, tsupport (φ : ℂ → ℝ) ⊆ exW V n :=
  exists_subset_exW V.isOpen φ.hasCompactSupport.isCompact φ.tsupport_subset

theorem measurable_ofFun_extZ (V : Opens ℂ) {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → C((V : Set ℂ), ℝ)} (hg : Measurable g) :
    Measurable fun ω => Distribution.ofFun V (Function.extend Subtype.val (g ω) 0) volume ⊤ := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  obtain ⟨n, hn⟩ := exists_tsupport_subset_exW V φ
  simp_rw [ofFun_extZ_apply V _ φ hn]
  exact (LQGMetric.measurable_ofCont_apply _).comp (measurable_cutExt V.isOpen _ hg)

theorem cutF_add (V : Opens ℂ) (n : ℕ) (f g : C((V : Set ℂ), ℝ)) :
    cutF V n (f + g) = cutF V n f + cutF V n g := by
  ext z
  simp only [cutF, ContinuousMap.add_apply, cutExt_apply]
  by_cases hz : z ∈ (V : Set ℂ)
  · rw [extZ_of_mem _ hz, extZ_of_mem _ hz, extZ_of_mem _ hz, ContinuousMap.add_apply, mul_add]
  · rw [extZ_of_notMem _ hz, extZ_of_notMem _ hz, extZ_of_notMem _ hz]; ring

theorem ofFun_extZ_add (V : Opens ℂ) (f g : C((V : Set ℂ), ℝ)) :
    Distribution.ofFun V (Function.extend Subtype.val (f + g) 0) volume ⊤ =
      Distribution.ofFun V (Function.extend Subtype.val f 0) volume ⊤ +
        Distribution.ofFun V (Function.extend Subtype.val g 0) volume ⊤ := by
  ext φ
  obtain ⟨n, hn⟩ := exists_tsupport_subset_exW V φ
  rw [add_apply, ofFun_extZ_apply V _ φ hn, ofFun_extZ_apply V _ φ hn, ofFun_extZ_apply V _ φ hn,
    cutF_add, ofCont_add, add_apply]

/-! ## Weyl scaling: field level -/

/-- **Domain Weyl scaling, field level.** `(h₀, f + g)` realizes `h + g`. -/
theorem isDomainRealization_add {V : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn V} {h₀ : Ω → DistC} {f g : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) (hg : Measurable g) :
    IsDomainRealization V P
      (fun ω => h ω + Distribution.ofFun V (Function.extend Subtype.val (g ω) 0) volume ⊤)
      h₀ (fun ω => f ω + g ω) := by
  obtain ⟨hh, hh₀, hf, hae⟩ := hR
  have : LocallyCompactSpace (V : Set ℂ) := V.isOpen.locallyCompactSpace
  refine ⟨LQGMetric.measurable_distOn_iff.2 fun φ => ?_, hh₀, ?_, ?_⟩
  · show Measurable fun ω => h ω φ +
      Distribution.ofFun V (Function.extend Subtype.val (g ω) 0) volume ⊤ φ
    exact ((LQGMetric.measurable_distOn_apply φ).comp hh).add
      ((LQGMetric.measurable_distOn_apply φ).comp (measurable_ofFun_extZ V hg))
  · rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.add_apply]
    exact ((ContinuousMap.measurable_eval x).comp hf).add ((ContinuousMap.measurable_eval x).comp hg)
  filter_upwards [hae] with ω hω
  beta_reduce
  rw [hω, add_assoc]
  congr 1
  exact (ofFun_extZ_add V (f ω) (g ω)).symm

/-! ## Restriction -/

/-- **Restriction of realizations.** `(h₀, f|_W)` realizes `h|_W` for open `W ⊆ V`. -/
theorem isDomainRealization_restrictOn {V W : Opens ℂ} (hWV : W ≤ V) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn V} {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) :
    IsDomainRealization W P (fun ω => restrictOn hWV (h ω)) h₀
      (fun ω => resC (SetLike.coe_subset_coe.2 hWV) (f ω)) := by
  obtain ⟨hh, hh₀, hf, hae⟩ := hR
  refine ⟨(measurable_restrictOn hWV).comp hh, hh₀, (measurable_resC _).comp hf, ?_⟩
  filter_upwards [hae] with ω hω
  beta_reduce
  rw [hω]
  ext φ
  rw [restrictOn_apply, add_apply, add_apply]
  congr 1
  · exact congrFun (congrArg DFunLike.coe (restrictOn_restrictTo hWV (h₀ ω))) φ
  · have hlocV : LocallyIntegrableOn (Function.extend Subtype.val (f ω) 0) (V : Set ℂ) volume :=
      (continuousOn_extZ (f ω)).locallyIntegrableOn V.isOpen.measurableSet
    have hlocW := (continuousOn_extZ (resC (SetLike.coe_subset_coe.2 hWV) (f ω))).locallyIntegrableOn
      W.isOpen.measurableSet (μ := volume)
    unfold extZ at hlocW
    rw [Distribution.ofFun_apply hlocV]
    erw [Distribution.ofFun_apply hlocW]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [coe_monoCLM hWV, smul_eq_mul, smul_eq_mul]
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxW : x ∈ (W : Set ℂ) := φ.tsupport_subset (subset_tsupport _ hx)
      have e1 := extZ_of_mem (f ω) (hWV hxW)
      have e2 := extZ_of_mem (resC (SetLike.coe_subset_coe.2 hWV) (f ω)) hxW
      unfold extZ at e1 e2
      exact congrArg (φ x * ·) (e1.trans e2.symm)

/-! ## Locality -/

/-- **Pathwise locality for domain fields.** If `h` on `V` and `h'` on `V'` agree a.s. on an open
`W ⊆ V ∩ V'`, then a.s. the `W`-metrics of their restricted realizations agree. -/
theorem ae_domainMetric_eq_of_restrictOn_eq {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) {V V' W : Opens ℂ}
    (hWV : W ≤ V) (hWV' : W ≤ V') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn V} {h' : Ω → DistOn V'} {h₀ h₀' : Ω → DistC}
    {f : Ω → C(V, ℝ)} {f' : Ω → C(V', ℝ)}
    (hR : IsDomainRealization V P h h₀ f) (hR' : IsDomainRealization V' P h' h₀' f')
    (hW : ∀ᵐ ω ∂P, restrictOn hWV (h ω) = restrictOn hWV' (h' ω)) :
    ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D W (h₀ ω) (resC (SetLike.coe_subset_coe.2 hWV) (f ω)) =
      domainMetric (ξ : ℝ) D W (h₀' ω) (resC (SetLike.coe_subset_coe.2 hWV') (f' ω)) := by
  have R1 := isDomainRealization_restrictOn hWV hR
  have R2 := isDomainRealization_restrictOn hWV' hR'
  have R2' : IsDomainRealization W P (fun ω => restrictOn hWV (h ω)) h₀'
      (fun ω => resC (SetLike.coe_subset_coe.2 hWV') (f' ω)) := by
    refine ⟨R1.1, R2.2.1, R2.2.2.1, ?_⟩
    filter_upwards [hW, R2.2.2.2] with ω e1 e2
    rw [e1, e2]
  exact ae_domainMetric_eq_of_isDomainRealization hD W R1 R2'

theorem measurable_iInf_dprop {δ : Type*} [MeasurableSpace δ] {p : Prop} {F : p → δ → ℝ≥0∞}
    (hF : ∀ hp, Measurable (F hp)) : Measurable fun b => ⨅ hp : p, F hp b := by
  by_cases hp : p
  · simp only [iInf_pos hp]; exact hF hp
  · simp only [iInf_neg hp]; exact measurable_const

/-- **Locality, functional form** (Axiom II's shape): the domain metric of a realization of `h` is
a.s. a measurable function of `h`. -/
theorem exists_measurable_domainMetric {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn V} {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) :
    ∃ G : DistOn V → (V × V → ℝ≥0∞), Measurable G ∧
      ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = G (h ω) := by
  have hloc := fun n : ℕ => hD.2.2.1 P (fun ω => addFun (h₀ ω) (cutF V n (f ω)))
    (isGFFPlusCont_addFun_of_measurable hR.2.1 (measurable_cutExt V.isOpen _ hR.2.2.1))
    (exWO V n)
  choose F hFm hFae using hloc
  refine ⟨fun k p => ⨅ (n : ℕ) (hx : (p.1 : ℂ) ∈ exW V n) (hy : (p.2 : ℂ) ∈ exW V n),
    F n (restrictOn (exWO_le V n) k) (⟨p.1, hx⟩, ⟨p.2, hy⟩), ?_, ?_⟩
  · refine Measurable.of_eval fun p => ?_
    refine Measurable.iInf fun n => measurable_iInf_dprop fun hx => measurable_iInf_dprop fun hy => ?_
    exact (measurable_pi_apply _).comp ((hFm n).comp (measurable_restrictOn _))
  · have hres : ∀ n, ∀ᵐ ω ∂P, restrictTo (exWO V n) (addFun (h₀ ω) (cutF V n (f ω))) =
        restrictOn (exWO_le V n) (h ω) := by
      intro n
      filter_upwards [ae_restrictTo_cutF hR n] with ω hω
      ext φ
      exact hω φ
    filter_upwards [ae_domainMetric_eq_iInf_internal hD V P h h₀ f hR, ae_all_iff.2 hFae,
      ae_all_iff.2 hres] with ω e1 e2 e3
    funext p
    rw [e1 p]
    refine iInf_congr fun n => iInf_congr fun hx => iInf_congr fun hy => ?_
    change (D (addFun (h₀ ω) (cutF V n (f ω)))).internal ((exWO V n : Opens ℂ) : Set ℂ) _ = _
    rw [e2 n, e3 n]
    rfl

/-! ## Length space, Weyl scaling and restriction of the metric (on the sample event) -/

/-- **Domain Weyl scaling, metric level**, simultaneously for all `g ∈ C(V)`:
`d_{f + g} = (e^{ξ g} · d_f)_V` on the carrier `(ℂ, D_{h₀})`. -/
theorem ae_domainMetric_add {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (f g : C(V, ℝ)) (p : V × V), domainMetric (ξ : ℝ) D V (h₀ ω) (f + g) p =
      HigherDimLQGMetric.weylDistOnWith (dV (D (h₀ ω)) (ξ : ℝ) f) (wV (D (h₀ ω)) (ξ : ℝ) g)
        (SV (D (h₀ ω)) V) ((D (h₀ ω)).pt p.1) ((D (h₀ ω)).pt p.2) := by
  filter_upwards [ae_sample_of_isGFFPlusCont hD P h₀ hh₀] with ω ⟨hf, _, _⟩ f g p
  exact weylScaleOn_add_eq_weylDistOnWith hf V.isOpen f g p

/-- **Length space**: a.s. the domain metric is the length metric it induces on `V`, and equals
`(e^{ξ f}·D_{h₀})_V` (simultaneously in `f`). -/
theorem ae_domainMetric_isLength {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (f : C(V, ℝ)) (p : V × V),
      domainMetric (ξ : ℝ) D V (h₀ ω) f p = dV (D (h₀ ω)) (ξ : ℝ) f ((D (h₀ ω)).pt p.1)
        ((D (h₀ ω)).pt p.2) ∧
      HigherDimLQGMetric.internalWith (dV (D (h₀ ω)) (ξ : ℝ) f) (SV (D (h₀ ω)) V)
        ((D (h₀ ω)).pt p.1) ((D (h₀ ω)).pt p.2) = domainMetric (ξ : ℝ) D V (h₀ ω) f p := by
  filter_upwards [ae_sample_of_isGFFPlusCont hD P h₀ hh₀] with ω ⟨hf, _, _⟩ f p
  have e := weylScaleOn_eq_dV (ξ := (ξ : ℝ)) hf f p
  exact ⟨e, (internalWith_dV hf V.isOpen f _ _).trans e.symm⟩

/-- **Restriction of the metric**: a.s., for every open `W ⊆ V` and every `f`, the `W`-metric of
`f|_W` is the internal metric on `W` of the `V`-metric of `f`. -/
theorem ae_domainMetric_restrict {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (W : Opens ℂ) (hWV : W ≤ V) (f : C(V, ℝ)) (p : W × W),
      domainMetric (ξ : ℝ) D W (h₀ ω) (resC (SetLike.coe_subset_coe.2 hWV) f) p =
        HigherDimLQGMetric.internalWith (dV (D (h₀ ω)) (ξ : ℝ) f) (SV (D (h₀ ω)) W)
          ((D (h₀ ω)).pt p.1) ((D (h₀ ω)).pt p.2) := by
  filter_upwards [ae_sample_of_isGFFPlusCont hD P h₀ hh₀] with ω ⟨hf, _, _⟩ W hWV f p
  exact weylScaleOn_resC_eq_internalWith hf V.isOpen _ f p

/-! ## Consistency with the whole-plane metric -/

/-- **Consistency**: a.s., for every `F ∈ C(ℂ)` extending `f ∈ C(K)` (any `K ⊆ ℂ`), the domain
metric of `f` on `K` is `D_{h₀ + F}(·, ·; K)`. -/
theorem ae_weylScaleOn_eq_internal {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn (ξ : ℝ) f (D (h₀ ω)) p = (D (addFun (h₀ ω) F)).internal K p := by
  filter_upwards [ae_sample_of_isGFFPlusCont hD P h₀ hh₀] with ω ⟨hf, hL, hW⟩ K f F hFf p
  exact weylScaleOn_eq_internal_of_extension (le_of_lt ξ.2) hf hL f F hFf _
    (fun q => (congrFun (hW F) q).symm) p

/-- **Consistency on `V`**: a.s., for every `F ∈ C(ℂ)` extending `f`, the domain metric is
`D_{h₀ + F}(·, ·; V)`. -/
theorem ae_domainMetric_eq_internal {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (f : C(V, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ V), F z = f ⟨z, hz⟩) →
      ∀ p : V × V, domainMetric (ξ : ℝ) D V (h₀ ω) f p =
        (D (addFun (h₀ ω) F)).internal (V : Set ℂ) p := by
  filter_upwards [ae_weylScaleOn_eq_internal hD P hh₀] with ω hω f F hFf p
  exact hω V f F hFf p

theorem addFun_zero (h₀ : DistC) : addFun h₀ 0 = h₀ := by
  have : ofCont 0 = 0 := by
    have h := ofCont_add 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  rw [addFun, this, add_zero]

/-- **The domain metric of `h₀|_V`**: a.s. `d_0 = D_{h₀}(·, ·; V)`. -/
theorem ae_domainMetric_zero_eq_internal {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) 0 = (D (h₀ ω)).internal (V : Set ℂ) := by
  filter_upwards [ae_domainMetric_eq_internal hD V P hh₀] with ω hω
  funext p
  rw [hω 0 0 (fun _ _ => rfl) p, addFun_zero]

/-- `(h₀, 0)` realizes `h₀|_V`. -/
theorem isDomainRealization_restrictTo (V : Opens ℂ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    IsDomainRealization V P (fun ω => restrictTo V (h₀ ω)) h₀ (fun _ => 0) := by
  refine ⟨LQGMetric.measurable_distOn_iff.2 fun φ => (LQGMetric.measurable_distOn_apply
    (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ)).comp hh₀.1, hh₀,
    measurable_const, Eventually.of_forall fun ω => ?_⟩
  show restrictTo V (h₀ ω) = restrictTo V (h₀ ω) +
    Distribution.ofFun V (Function.extend Subtype.val (⇑(0 : C(V, ℝ))) 0) volume ⊤
  have : Function.extend Subtype.val (⇑(0 : C(V, ℝ))) (0 : ℂ → ℝ) = 0 := by
    funext z
    by_cases hz : z ∈ V
    · have := Subtype.val_injective.extend_apply (⇑(0 : C(V, ℝ))) (0 : ℂ → ℝ) ⟨z, hz⟩
      simpa using this
    · rw [Function.extend_apply']
      rintro ⟨a, rfl⟩
      exact hz a.2
  rw [this, Distribution.ofFun_zero, add_zero]

/-! ## Lower semicontinuity of the confined metrics -/

open Classical in
/-- The confined domain metric on `K ⊆ V`, on `ℂ × ℂ` (`∞` off `K × K`). -/
def confined (ξ : ℝ) (D₀ : LSCMetric) {V K : Set ℂ} (hKV : K ⊆ V) (f : C(V, ℝ)) (q : ℂ × ℂ) :
    ℝ≥0∞ :=
  if hq : q.1 ∈ K ∧ q.2 ∈ K then weylScaleOn ξ (resC hKV f) D₀ (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩) else ⊤

/-- **Lower semicontinuity of the confined metrics** (paper Lemma 1.2, last clause): a.s., for every
`f ∈ C(V)` and every closed disk `K ⊆ V`, the confined domain metric on `K` is lower semicontinuous
on `ℂ × ℂ`. -/
theorem ae_confined_lsc {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsGFFPlusCont h₀ P) :
    ∀ᵐ ω ∂P, ∀ (f : C(V, ℝ)) (c : ℂ) (R : ℝ) (hKV : Metric.closedBall c R ⊆ V),
      LowerSemicontinuous (confined (ξ : ℝ) (D (h₀ ω)) hKV f) := by
  filter_upwards [ae_weylScaleOn_eq_internal hD P hh₀] with ω hω f c R hKV
  obtain ⟨n, hn⟩ := exists_subset_exW V.isOpen (isCompact_closedBall c R) hKV
  set E := D (addFun (h₀ ω) (cutF V n f)) with hE
  have heq : confined (ξ : ℝ) (D (h₀ ω)) hKV f = fun q =>
      SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf E c R q.1 q.2 := by
    funext q
    unfold confined
    split_ifs with hq
    · rw [hω _ (resC hKV f) (cutF V n f) (fun z hz => cutF_eq V n f z (hn hz))]
      rfl
    · symm
      refine eq_top_iff.2 (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
        le_iInf fun hK => le_iInf fun ha => le_iInf fun hb => ?_)
      exfalso
      refine hq ⟨?_, ?_⟩
      · rw [← ha]; exact hK a (left_mem_Icc.2 hP.1)
      · rw [← hb]; exact hK b (right_mem_Icc.2 hP.1)
  rw [heq]
  exact SupercriticalConformalCovariance.Compact.closed_disk_intrinsic_lsc E c R

end SupercriticalConformalCovariance.Domain
