import SupercriticalConformalCovariance.BiLip.Lengths
import SupercriticalConformalCovariance.Root.Transfer
import LQGMetric.Metric.CurveNatural
import LQGMetric.Metric.Geodesic

/-!
# Proposition 4.3: Lemma 2.1 for the confined metrics

Paper l. 352–353: "Lemma 2.1 compares lengths, hence also confined metrics, with the same
deterministic constant `C`."

Deterministic core, for one sample. The source metric `M₁` is a lower semicontinuous metric on `ℂ`
and `d = pathInf M₁ U` its internal metric on the source domain `U`; the target is the domain metric
`dV = (e^{ξ f} · D₀)_V` on `V`, and `e = eT D₀ ξ f ψ` its pullback by `ψ : U → V`.
Lemma 2.1 gives `e ≤ C d` and `d ≤ C e` on `U × U`. For a compact `K ⊆ U` the confined source metric is
`pathInf M₁ K` and the confined target metric is the internal metric of `dV` on `ψ(K)`, i.e.
`internalWith dV (SV D₀ (ψ '' K))`. Both comparisons pass to them with the same `C`:
* `confinedTarget_le`: a source curve in `K`, reparametrized by `M₁`-length, is mapped by `ψ` to a
  `D₀`-continuous curve in `ψ(K)` (continuity from `e ≤ C d` and `exists_edist_lt_of_weylDistOn_lt`),
  whose `dV`-length is its `e`-length;
* `confinedSource_le`: a `D₀`-continuous target curve in `ψ(K)` is pulled back by `ψ⁻¹` to an
  `M₁`-curve in `K` (continuity from `d ≤ C e` and `exists_weylDistOn_lt_of_isLocallyLengthOn`, `D₀` a
  length space), whose `M₁`-length is at most its `d`-length.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.P43Final

open SupercriticalLQGUniqueness (LSCMetric)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalConformalCovariance.BiLip (eT pathInf pathInf_le_len)
open SupercriticalConformalCovariance.Domain (dV SV wV)
open HigherDimLQGMetric (curveLengthWith internalWith partitionSup)

/-- `D ≤ D(·, ·; U)`. -/
theorem le_pathInf (D : LSCMetric) (U : Set ℂ) (x y : ℂ) : D (x, y) ≤ pathInf D U x y := by
  unfold pathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact D.apply_le_len P hP.1

/-- The length of a curve for the internal metric of a set containing it is at most its length. -/
theorem curveLengthWith_pathInf_le_len (D : LSCMetric) (U : Set ℂ) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hU : ∀ t ∈ Icc a b, P t ∈ U) :
    curveLengthWith (pathInf D U) P a b ≤ D.len P a b := by
  refine HigherDimLQGMetric.partitionSup_le fun p => ?_
  calc p.sum (fun u v => pathInf D U (P u) (P v))
      ≤ ∑ i ∈ Finset.range p.n,
          partitionSup (fun u v => edist ((D.pt ∘ P) u) ((D.pt ∘ P) v)) (p.t i) (p.t (i + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
        have hsub : Icc (p.t i) (p.t (i + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h3
        have hc : D.IsCurve P (p.t i) (p.t (i + 1)) := ⟨h2, hP.2.mono hsub⟩
        have he := HigherDimLQGMetric.curveLengthWith_edist (D.pt ∘ P) (p.t i) (p.t (i + 1))
        unfold curveLengthWith at he
        rw [he]
        exact pathInf_le_len D U hc (fun t ht => hU t (hsub ht))
    _ ≤ partitionSup (fun u v => edist ((D.pt ∘ P) u) ((D.pt ∘ P) v)) a b :=
        p.sum_partitionSup_le _
    _ = D.len P a b := HigherDimLQGMetric.curveLengthWith_edist (D.pt ∘ P) a b

/-- The length of a curve is at most its length for the internal metric of any set. -/
theorem len_le_curveLengthWith_pathInf (D : LSCMetric) (U : Set ℂ) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b ≤ curveLengthWith (pathInf D U) P a b := by
  have he := HigherDimLQGMetric.curveLengthWith_edist (D.pt ∘ P) a b
  refine le_trans (le_of_eq he.symm) ?_
  exact HigherDimLQGMetric.partitionSup_mono fun u v _ _ _ => le_pathInf D U (P u) (P v)

/-- **Unit-speed reparametrization** of a finite-length curve of a lower semicontinuous metric:
same endpoints, same trace, same length, and length `t - s` on every `[s, t] ⊆ [0, L]`. -/
theorem exists_unitSpeed_reparam (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hfin : D.len P a b ≠ ⊤) :
    ∃ (Q : ℝ → ℂ) (L : ℝ), 0 ≤ L ∧ D.IsCurve Q 0 L ∧ Q 0 = P a ∧ Q L = P b ∧
      Q '' Icc 0 L = P '' Icc a b ∧ D.len Q 0 L = D.len P a b ∧
      ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.len Q s t = ENNReal.ofReal (t - s) := by
  let f : ℝ → D.Space := D.pt ∘ P
  let L : ℝ := (D.len P a b).toReal
  let Q : ℝ → ℂ := fun t => ((LQGMetric.MetricGeometry.lengthParam f a b t : D.Space) : ℂ)
  have hf : ContinuousOn f (Icc a b) := hP.2
  have hfin' : LQGMetric.MetricGeometry.curveLength f a b ≠ ⊤ := hfin
  have hL : L = (LQGMetric.MetricGeometry.curveLength f a b).toReal := rfl
  have hDQ : D.pt ∘ Q = LQGMetric.MetricGeometry.lengthParam f a b := by
    funext t
    rfl
  have hrep (t : ℝ) (ht : t ∈ Icc a b) :
      Q (variationOnFromTo f (Icc a b) a t) = P t := by
    have h := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hfin' ht
    exact congrArg (fun v : D.Space => (v : ℂ)) h
  have hQ0 : Q 0 = P a := by
    have h := hrep a ⟨le_rfl, hP.1⟩
    rw [variationOnFromTo.self] at h
    exact h
  have hQL : Q L = P b := by
    have h := hrep b ⟨hP.1, le_rfl⟩
    rw [variationOnFromTo.eq_of_le _ _ hP.1, Set.inter_self] at h
    exact h
  have himg : Q '' Icc 0 L = P '' Icc a b := by
    have hs := LQGMetric.MetricGeometry.variationOnFromTo_image_Icc hP.1 hf hfin'
    ext y
    constructor
    · rintro ⟨s, hs', rfl⟩
      have hs'' : s ∈ Icc 0 (LQGMetric.MetricGeometry.curveLength f a b).toReal := by
        simpa only [hL] using hs'
      rw [← hs] at hs''
      obtain ⟨t, ht, rfl⟩ := hs''
      exact ⟨t, ht, (hrep t ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      have hs' : variationOnFromTo f (Icc a b) a t ∈ Icc 0 L := by
        rw [hL, ← hs]
        exact ⟨t, ht, rfl⟩
      exact ⟨_, hs', hrep t ht⟩
  have hu := LQGMetric.MetricGeometry.hasUnitSpeedOn_lengthParam hP.1 hf hfin'
  have hQLip : LipschitzOnWith (1 : NNReal) (D.pt ∘ Q) (Icc 0 L) := by
    rw [hDQ, hL]
    exact LQGMetric.MetricGeometry.lipschitzOnWith_lengthParam hP.1 hf hfin'
  refine ⟨Q, L, ENNReal.toReal_nonneg, ⟨ENNReal.toReal_nonneg, hQLip.continuousOn⟩, hQ0, hQL, himg,
    ?_, ?_⟩
  · change LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) 0 L =
      LQGMetric.MetricGeometry.curveLength f a b
    rw [hDQ, hL]
    exact LQGMetric.MetricGeometry.curveLength_lengthParam hP.1 hf hfin'
  · intro s hs t ht
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) s t = _
    rw [hDQ]
    exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hu hs ht

/-- **Lemma 2.1 for confined metrics, target side**: `e(·,·; K) ≤ C d(·,·; K)`. -/
theorem confinedTarget_le (M₁ D₀ : LSCMetric) (ξ : ℝ) {U V : Set ℂ} (fr : C(V, ℝ))
    (hV : IsOpen V) (hf₀ : Continuous (forget D₀))
    (ψ : ℂ → ℂ) {K : Set ℂ} (hKU : K ⊆ U) (hψKV : MapsTo ψ K V) {C : ℝ≥0∞} (hC0 : C ≠ 0)
    (hCt : C ≠ ⊤)
    (hle : ∀ u ∈ U, ∀ v ∈ U, eT D₀ ξ fr ψ u v ≤ C * pathInf M₁ U u v) (x y : ℂ) :
    internalWith (dV D₀ ξ fr) (SV D₀ (ψ '' K)) (D₀.pt (ψ x)) (D₀.pt (ψ y)) ≤
      C * pathInf M₁ K x y := by
  conv_rhs => unfold pathInf
  simp only [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPK => le_iInf fun hPa => le_iInf fun hPb => ?_
  by_cases hfin : M₁.len P a b = ⊤
  · rw [hfin, ENNReal.mul_top hC0]
    exact le_top
  obtain ⟨P', L, hL0, hP', hP'0, hP'L, himg, hlen, hunit⟩ :=
    exists_unitSpeed_reparam M₁ hP hfin
  have hP'K : ∀ t ∈ Icc 0 L, P' t ∈ K := fun t ht => by
    have : P' t ∈ P '' Icc a b := himg ▸ mem_image_of_mem P' ht
    obtain ⟨s, hs, hst⟩ := this
    exact hst ▸ hPK s hs
  have hP'U : ∀ t ∈ Icc 0 L, P' t ∈ U := fun t ht => hKU (hP'K t ht)
  let Q : ℝ → D₀.Space := fun t => D₀.pt (ψ (P' t))
  -- `dV(Q s, Q t) ≤ C |t - s|`
  have hstep : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      dV D₀ ξ fr (Q s) (Q t) ≤ C * ENNReal.ofReal (t - s) := by
    intro s hs t ht hst
    have hc : M₁.IsCurve P' s t := ⟨hst, hP'.2.mono (Icc_subset_Icc hs.1 ht.2)⟩
    have h1 := hle (P' s) (hP'U s hs) (P' t) (hP'U t ht)
    have h2 := pathInf_le_len M₁ U hc (fun r hr => hP'U r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩)
    rw [hunit s hs t ht] at h2
    exact h1.trans (mul_le_mul' le_rfl h2)
  have hdist : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      dV D₀ ξ fr (Q s) (Q t) ≤ C * ENNReal.ofReal |t - s| := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [abs_of_nonneg (sub_nonneg.2 hst)]
      exact hstep s hs t ht hst
    · rw [abs_of_nonpos (sub_nonpos.2 hts), neg_sub]
      unfold dV
      rw [HigherDimLQGMetric.weylDistOn_comm]
      exact hstep t ht s hs hts
  have hQS : MapsTo Q (Icc 0 L) (SV D₀ (ψ '' K)) := fun t ht =>
    (mem_image_of_mem ψ (hP'K t ht) : ψ (P' t) ∈ ψ '' K)
  have hQV : ∀ t ∈ Icc 0 L, Q t ∈ SV D₀ V := fun t ht => (hψKV (hP'K t ht) : ψ (P' t) ∈ V)
  have hQc : ContinuousOn Q (Icc 0 L) := by
    intro t₀ ht₀
    have hw : ContinuousAt (wV D₀ ξ fr) (Q t₀) :=
      (SupercriticalConformalCovariance.Domain.continuousOn_wV hf₀ fr).continuousAt
        ((SupercriticalConformalCovariance.Domain.isOpen_SV hf₀ hV).mem_nhds (hQV t₀ ht₀))
    rw [ContinuousWithinAt, EMetric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ', hδ', hδ'ε⟩ := HigherDimLQGMetric.exists_edist_lt_of_weylDistOn_lt
      (U := SV D₀ V) hw (SupercriticalConformalCovariance.Domain.wV_pos fr _) hε
    have h1 : Tendsto (fun t : ℝ => C * ENNReal.ofReal |t - t₀|) (𝓝 t₀) (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => ENNReal.ofReal |t - t₀|) (𝓝 t₀) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => ENNReal.ofReal |t - t₀| :=
          ENNReal.continuous_ofReal.comp (by fun_prop)
        simpa using hc.tendsto t₀
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hCt)
    have hev : ∀ᶠ t in 𝓝[Icc 0 L] t₀, C * ENNReal.ofReal |t - t₀| < δ' :=
      (h1.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ')
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htI
    rw [edist_comm]
    exact hδ'ε _ ((hdist t₀ ht₀ t htI).trans_lt ht)
  have hint := SupercriticalConformalCovariance.BiLip.internalWith_le_curveLengthWith (dV D₀ ξ fr) hL0 hQc hQS
  have hQ0 : Q 0 = D₀.pt (ψ x) := by simp only [Q, hP'0, hPa]
  have hQL : Q L = D₀.pt (ψ y) := by simp only [Q, hP'L, hPb]
  rw [hQ0, hQL] at hint
  calc internalWith (dV D₀ ξ fr) (SV D₀ (ψ '' K)) (D₀.pt (ψ x)) (D₀.pt (ψ y))
      ≤ curveLengthWith (dV D₀ ξ fr) Q 0 L := hint
    _ = curveLengthWith (eT D₀ ξ fr ψ) P' 0 L := rfl
    _ ≤ C * curveLengthWith (pathInf M₁ U) P' 0 L :=
        SupercriticalConformalCovariance.BiLip.curveLengthWith_le_of_le_on hle hP'U
    _ ≤ C * M₁.len P' 0 L := mul_le_mul' le_rfl (curveLengthWith_pathInf_le_len M₁ U hP' hP'U)
    _ = C * M₁.len P a b := by rw [hlen]

/-- **Lemma 2.1 for confined metrics, source side**: `d(·,·; K) ≤ C e(·,·; K)`. -/
theorem confinedSource_le (M₁ D₀ : LSCMetric) (ξ : ℝ) {U V : Set ℂ} (fr : C(V, ℝ))
    (hV : IsOpen V) (hf₀ : Continuous (forget D₀)) (hL₀ : D₀.IsLengthSpace)
    (ψ χ : ℂ → ℂ) {K : Set ℂ} (hKU : K ⊆ U) (hψKV : MapsTo ψ K V)
    (hχc : ContinuousOn χ (ψ '' K)) (hχψ : ∀ x ∈ K, χ (ψ x) = x)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ⊤)
    (hle : ∀ u ∈ U, ∀ v ∈ U, pathInf M₁ U u v ≤ C * eT D₀ ξ fr ψ u v)
    (x y : ℂ) (hx : x ∈ K) (hy : y ∈ K) :
    pathInf M₁ K x y ≤
      C * internalWith (dV D₀ ξ fr) (SV D₀ (ψ '' K)) (D₀.pt (ψ x)) (D₀.pt (ψ y)) := by
  conv_rhs => unfold internalWith
  simp only [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun Q => le_iInf fun hQc => le_iInf fun hQ0 => le_iInf fun hQ1 =>
    le_iInf fun hQS => ?_
  let P : ℝ → ℂ := fun t => χ (forget D₀ (Q t))
  have hpre : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x' ∈ K, forget D₀ (Q t) = ψ x' := fun t ht => by
    obtain ⟨x', hx', hxe⟩ := hQS ht
    exact ⟨x', hx', hxe.symm⟩
  have hPK : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ K := fun t ht => by
    obtain ⟨x', hx', hxe⟩ := hpre t ht
    change χ (forget D₀ (Q t)) ∈ K
    rw [hxe, hχψ x' hx']
    exact hx'
  have hψP : ∀ t ∈ Icc (0 : ℝ) 1, ψ (P t) = forget D₀ (Q t) := fun t ht => by
    obtain ⟨x', hx', hxe⟩ := hpre t ht
    change ψ (χ (forget D₀ (Q t))) = _
    rw [hxe, hχψ x' hx']
  have hPU : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U := fun t ht => hKU (hPK t ht)
  have hP0 : P 0 = x := by
    change χ (forget D₀ (Q 0)) = x
    rw [hQ0]
    exact hχψ x hx
  have hP1 : P 1 = y := by
    change χ (forget D₀ (Q 1)) = y
    rw [hQ1]
    exact hχψ y hy
  have hQV : ∀ t ∈ Icc (0 : ℝ) 1, Q t ∈ SV D₀ V := fun t ht => by
    obtain ⟨x', hx', hxe⟩ := hpre t ht
    change forget D₀ (Q t) ∈ V
    rw [hxe]
    exact hψKV hx'
  -- `M₁(P s, P t) ≤ C dV(Q s, Q t)`
  have hcmp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      M₁ (P s, P t) ≤ C * dV D₀ ξ fr (Q s) (Q t) := by
    intro s hs t ht
    have h := (le_pathInf M₁ U (P s) (P t)).trans (hle (P s) (hPU s hs) (P t) (hPU t ht))
    have he : eT D₀ ξ fr ψ (P s) (P t) = dV D₀ ξ fr (Q s) (Q t) := by
      unfold eT
      rw [hψP s hs, hψP t ht]
      rfl
    rwa [he] at h
  have hloc : HigherDimLQGMetric.IsLocallyLengthOn (SV D₀ V) :=
    SupercriticalConformalCovariance.Root.isLocallyLengthOn_of_isLengthSpace D₀ hL₀ (SupercriticalConformalCovariance.Domain.isOpen_SV hf₀ hV)
  have hPc : M₁.IsCurve P 0 1 := by
    refine ⟨zero_le_one, fun t₀ ht₀ => ?_⟩
    have hw : ContinuousAt (wV D₀ ξ fr) (Q t₀) :=
      (SupercriticalConformalCovariance.Domain.continuousOn_wV hf₀ fr).continuousAt
        ((SupercriticalConformalCovariance.Domain.isOpen_SV hf₀ hV).mem_nhds (hQV t₀ ht₀))
    have hQt : ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ t in 𝓝[Icc 0 1] t₀, edist (Q t₀) (Q t) < δ := by
      intro δ hδ
      have := (EMetric.tendsto_nhds.1 (hQc t₀ ht₀)) δ hδ
      filter_upwards [this] with t ht
      rwa [edist_comm]
    have hdV : Tendsto (fun t => dV D₀ ξ fr (Q t) (Q t₀)) (𝓝[Icc 0 1] t₀) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := HigherDimLQGMetric.exists_weylDistOn_lt_of_isLocallyLengthOn hloc
        (hQV t₀ ht₀) hw hε
      filter_upwards [hQt δ hδ] with t ht
      unfold dV
      rw [HigherDimLQGMetric.weylDistOn_comm]
      exact (hδε _ ht).le
    have hCt' : Tendsto (fun t => C * dV D₀ ξ fr (Q t) (Q t₀)) (𝓝[Icc 0 1] t₀) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hdV (Or.inr hCt)
    have hM : Tendsto (fun t => M₁ (P t, P t₀)) (𝓝[Icc 0 1] t₀) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCt'
        (Eventually.of_forall fun _ => zero_le)
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact hcmp t ht t₀ ht₀)
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
    exact hM
  calc pathInf M₁ K x y = pathInf M₁ K (P 0) (P 1) := by rw [hP0, hP1]
    _ ≤ M₁.len P 0 1 := pathInf_le_len M₁ K hPc hPK
    _ ≤ curveLengthWith (pathInf M₁ U) P 0 1 := len_le_curveLengthWith_pathInf M₁ U P 0 1
    _ ≤ C * curveLengthWith (eT D₀ ξ fr ψ) P 0 1 :=
        SupercriticalConformalCovariance.BiLip.curveLengthWith_le_of_le_on hle hPU
    _ = C * curveLengthWith (dV D₀ ξ fr) Q 0 1 := by
        congr 1
        unfold curveLengthWith
        refine HigherDimLQGMetric.partitionSup_congr fun u v hu huv hv => ?_
        unfold eT
        rw [hψP u ⟨hu, huv.trans hv⟩, hψP v ⟨hu.trans huv, hv⟩]
        rfl

end SupercriticalConformalCovariance.P43Final
