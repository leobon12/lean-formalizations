import HigherDimLQGMetric.Coord.RecoveryUnit
import HigherDimLQGMetric.Metric.Reparam

/-! # Lemma 2.4 for arbitrary finite-length curves -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Coordinate arc-length parametrization stays in the old path's compact set,
and preserves both length and weighted length. -/
theorem coordinate_lengthParam_props
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ)
    (hρ : IsCoordinate ρ) (w : X → ℝ)
    {K : Set X} (Q : I →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hfin : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≠ ∞) :
    ∃ ℓ : ℝ, ∃ P : ℝ → X,
      0 ≤ ℓ ∧ ContinuousOn P (Icc 0 ℓ) ∧
      (∀ t ∈ Icc 0 ℓ, P t ∈ K) ∧ P 0 = Q 0 ∧ P ℓ = Q 1 ∧
      (∀ a ∈ Icc 0 ℓ, ∀ b ∈ Icc 0 ℓ, a ≤ b →
        curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) P a b =
          ENNReal.ofReal (b - a)) ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P 0 ℓ =
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one Q) 0 1 ∧
      ENNReal.ofReal ℓ = curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 := by
  let T : ℝ → MetricFunSpace ρ hρ.metric := fun t => MetricFunSpace.pt ρ hρ.metric
    ((Set.IccExtend zero_le_one Q) t)
  have hQext : Continuous (Set.IccExtend zero_le_one Q) :=
    continuous_IccExtend_iff.mpr Q.continuous
  have hTcont : ContinuousOn T (Icc (0 : ℝ) 1) := by
    exact (hρ.pt_continuous.comp hQext).continuousOn
  have hTfin : curveLength T 0 1 ≠ ∞ := by
    rw [curveLengthWith_metricFunSpace hρ.metric] at hfin
    exact hfin
  let ℓ : ℝ := (curveLength T 0 1).toReal
  let P : ℝ → X := fun t => LQGMetric.metricFunSpaceVal ρ hρ.metric
    (lengthParam T 0 1 t)
  have hTmaps : MapsTo T (Icc (0 : ℝ) 1)
      (MetricFunSpace.pt ρ hρ.metric '' K) := by
    intro t ht
    refine ⟨(Set.IccExtend zero_le_one Q) t, ?_, rfl⟩
    simpa only [Set.IccExtend_of_mem _ _ ht] using hQK ⟨t, ht⟩
  obtain ⟨hu, hPc, hP0, hPℓ, hPS⟩ :=
    lengthParam_props zero_le_one hTcont hTfin hTmaps
  have hPcont : ContinuousOn P (Icc 0 ℓ) :=
    hρ.val_continuous.comp_continuousOn hPc
  have hPK : ∀ t ∈ Icc 0 ℓ, P t ∈ K := by
    intro t ht
    obtain ⟨x, hx, heq⟩ := hPS ht
    change LQGMetric.metricFunSpaceVal ρ hρ.metric (lengthParam T 0 1 t) ∈ K
    rw [← heq]
    exact hx
  have hA0 : P 0 = Q 0 := by
    change LQGMetric.metricFunSpaceVal ρ hρ.metric (lengthParam T 0 1 0) = Q 0
    rw [hP0]
    change LQGMetric.metricFunSpaceVal ρ hρ.metric
      (MetricFunSpace.pt ρ hρ.metric ((Set.IccExtend zero_le_one Q) 0)) = Q 0
    rw [Set.IccExtend_of_mem _ _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)]
    rfl
  have hAℓ : P ℓ = Q 1 := by
    change LQGMetric.metricFunSpaceVal ρ hρ.metric (lengthParam T 0 1 ℓ) = Q 1
    rw [hPℓ]
    change LQGMetric.metricFunSpaceVal ρ hρ.metric
      (MetricFunSpace.pt ρ hρ.metric ((Set.IccExtend zero_le_one Q) 1)) = Q 1
    rw [Set.IccExtend_of_mem _ _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
    rfl
  have hptP : (fun t => MetricFunSpace.pt ρ hρ.metric (P t)) = lengthParam T 0 1 := by
    funext t
    rfl
  have hunit : ∀ a ∈ Icc 0 ℓ, ∀ b ∈ Icc 0 ℓ, a ≤ b →
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) P a b =
        ENNReal.ofReal (b - a) := by
    intro a ha b hb hab
    rw [curveLengthWith_metricFunSpace hρ.metric]
    change curveLength (fun t => MetricFunSpace.pt ρ hρ.metric (P t)) a b = _
    rw [hptP]
    have h := curveLength_of_hasUnitSpeedOn hu ha hb
    simpa [Set.inter_self, edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hw_eq : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P 0 ℓ =
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 := by
    rw [weightedLengthWith_metricFunSpace hρ.metric w P,
      weightedLengthWith_metricFunSpace hρ.metric w
        (Set.IccExtend zero_le_one Q)]
    change weightedLength (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric)
        (fun t => MetricFunSpace.pt ρ hρ.metric (P t)) 0 ℓ =
      weightedLength (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric) T 0 1
    rw [hptP]
    exact (weightedLength_eq_lengthParam zero_le_one hTcont hTfin).symm
  refine ⟨ℓ, P, ENNReal.toReal_nonneg, hPcont, hPK, hA0, hAℓ,
    hunit, hw_eq, ?_⟩
  exact (ENNReal.ofReal_toReal hTfin).trans (by
    rw [curveLengthWith_metricFunSpace hρ.metric]
    rfl)

/-- Constant coordinate-speed parametrization of a finite-length bounded curve,
with weighted length preserved. -/
theorem coordinate_reparam_bounded
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ)
    (hρ : IsCoordinate ρ) (w : X → ℝ)
    {K : Set X} (Q : I →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hfin : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≠ ∞) :
    ∃ R : I →ᵇ X, (∀ t, R t ∈ K) ∧ R 0 = Q 0 ∧ R 1 = Q 1 ∧
      (∀ s t : I,
        ρ (R s, R t) ≤
          (curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1).toReal * dist s t) ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one R) 0 1 =
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one Q) 0 1 := by
  obtain ⟨ℓ, P, hℓ, hPc, hPK, hP0, hPℓ, hunit, hweight, hlen⟩ :=
    coordinate_lengthParam_props ρ hρ w Q hQK hfin
  let φ : ℝ → ℝ := fun t => ℓ * t
  have hφmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 ℓ) := by
    intro t ht
    dsimp [φ]
    constructor
    · exact mul_nonneg hℓ ht.1
    · exact mul_le_of_le_one_right hℓ ht.2
  have hRc : ContinuousOn (P ∘ φ) (Icc (0 : ℝ) 1) :=
    hPc.comp (by fun_prop) hφmap
  let R : I →ᵇ X := mkOfCompact
    ⟨fun t => P (φ t), hRc.comp_continuous continuous_subtype_val Subtype.prop⟩
  have hRmem : ∀ t, R t ∈ K := fun t => hPK _ (hφmap t.property)
  have hR0 : R 0 = Q 0 := by simpa [R, φ] using hP0
  have hR1 : R 1 = Q 1 := by simpa [R, φ] using hPℓ
  have hRspeed : ∀ s t : I,
      ρ (R s, R t) ≤
        (curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1).toReal * dist s t := by
    intro s t
    have hℓval : (curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1).toReal = ℓ := by
      rw [← hlen, ENNReal.toReal_ofReal hℓ]
    rw [hℓval]
    rcases le_total (s : ℝ) t with hst | hts
    · have hφst : φ s ≤ φ t := mul_le_mul_of_nonneg_left hst hℓ
      have h := le_curveLengthWith
        (δ := fun u v => ENNReal.ofReal (ρ (u, v))) (P := P) hφst
      rw [hunit _ (hφmap s.property) _ (hφmap t.property) hφst] at h
      have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hφst)).1 h
      change ρ (P (φ s), P (φ t)) ≤ _
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
      dsimp [φ] at hreal ⊢
      nlinarith
    · have hφts : φ t ≤ φ s := mul_le_mul_of_nonneg_left hts hℓ
      have h := le_curveLengthWith
        (δ := fun u v => ENNReal.ofReal (ρ (u, v))) (P := P) hφts
      rw [hunit _ (hφmap t.property) _ (hφmap s.property) hφts] at h
      have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hφts)).1 h
      change ρ (P (φ s), P (φ t)) ≤ _
      rw [hρ.metric.symm]
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
      dsimp [φ] at hreal ⊢
      nlinarith
  have hRweight : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
      (Set.IccExtend zero_le_one R) 0 1 =
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 := by
    calc
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one R) 0 1 =
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (P ∘ φ) 0 1 := by
            apply weightedLengthWith_congr_path
            intro t ht
            rw [Set.IccExtend_of_mem _ _ ht]
            rfl
      _ = weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P 0 ℓ := by
        rw [weightedLengthWith_comp_monotoneOn _ _ _ zero_le_one (by fun_prop)
          (fun s _ t _ hst => mul_le_mul_of_nonneg_left hst hℓ)]
        simp
      _ = _ := hweight
  exact ⟨R, hRmem, hR0, hR1, hRspeed, hRweight⟩

/-- MA1 Lemma 2.4: a finite-length curve in `K` can be recovered for a nearby
coordinate using the uniform local realization property. -/
theorem lemma24
    {X : Type*} [MetricSpace X]
    (ρ ρ' : X × X → ℝ) (hρ : IsCoordinate ρ) (hρ' : IsCoordinate ρ')
    (w : X → ℝ) {K O : Set X} (hKO : K ⊆ closure O)
    {L δ e δloc χ Ω M : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (he : 0 ≤ e) (heδ : e ≤ δ) (hδloc : 2 * δ < δloc)
    (hχ : 0 ≤ χ) (hΩ : 0 ≤ Ω) (hΩM : Ω ≤ M)
    (Q : I →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hQlen : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal L)
    (hclose : ∀ u ∈ closure O, ∀ v ∈ closure O,
      |ρ (u, v) - ρ' (u, v)| ≤ e)
    (hmod : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hmod' : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ' (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hw : ∀ z ∈ closure O, 0 ≤ w z ∧ w z ≤ M)
    (hwosc : ∀ u ∈ closure O, ∀ v ∈ closure O,
      dist u v ≤ χ → |w u - w v| ≤ Ω)
    (hlocal : ∀ x ∈ K, ∀ y ∈ K, ρ' (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ' (x, y))) :
    ∃ oldPath newPath : Path (Q 0) (Q 1),
      (∀ t, oldPath t ∈ K) ∧ (∀ t, newPath t ∈ closure O) ∧
      coordinatePathLength (fun u v => ENNReal.ofReal (ρ' (u, v))) newPath ≤
        ENNReal.ofReal (L + (L / δ + 1) * e) ∧
      coordinatePathWeightedLength (fun u v => ENNReal.ofReal (ρ' (u, v))) w
          newPath ≤
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one Q) 0 1 +
          ENNReal.ofReal (2 * Ω * L + 2 * M * (L / δ + 1) * e) ∧
      (∀ t : I, dist (oldPath t) (newPath t) ≤ 2 * χ) := by
  have hfin : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlen
  obtain ⟨ℓ, P, hℓ, hPc, hPK, hP0, hPℓ, hunit, hweight, hlen⟩ :=
    coordinate_lengthParam_props ρ hρ w Q hQK hfin
  have hℓL : ℓ ≤ L :=
    (ENNReal.ofReal_le_ofReal_iff hL).1 (hlen.trans_le hQlen)
  obtain ⟨old, new, hOldK, hNewO, hNewLen, hNewWeight, hclosePaths⟩ :=
    lemma24_unitSpeed ρ ρ' hρ hρ' w hKO hℓ hδ he heδ hδloc hχ hΩ hΩM
      P hPc hPK hunit hclose hmod hmod' hw hwosc hlocal
  have hM : 0 ≤ M := by
    have := hw (Q 0) (hKO (hQK 0))
    linarith
  have hdiv : ℓ / δ ≤ L / δ := by gcongr
  have hlenReal : ℓ + (ℓ / δ + 1) * e ≤ L + (L / δ + 1) * e := by
    nlinarith [mul_le_mul_of_nonneg_right hdiv he]
  have hweightReal : 2 * Ω * ℓ + 2 * M * (ℓ / δ + 1) * e ≤
      2 * Ω * L + 2 * M * (L / δ + 1) * e := by
    have h1 := mul_le_mul_of_nonneg_left hℓL (by positivity : 0 ≤ 2 * Ω)
    have h2 := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * M * e)
    nlinarith
  let old' : Path (Q 0) (Q 1) := old.cast hP0.symm hPℓ.symm
  let new' : Path (Q 0) (Q 1) := new.cast hP0.symm hPℓ.symm
  refine ⟨old', new', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [old', Path.cast_coe] using hOldK
  · simpa [new', Path.cast_coe] using hNewO
  · simpa [new', coordinatePathLength, Path.extend_cast] using
      hNewLen.trans (ENNReal.ofReal_le_ofReal hlenReal)
  · rw [← hweight]
    simpa [new', coordinatePathWeightedLength, Path.extend_cast] using
      hNewWeight.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hweightReal))
  · simpa [old', new', Path.cast_coe] using hclosePaths

end HigherDimLQGMetric
