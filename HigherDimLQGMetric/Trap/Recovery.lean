import HigherDimLQGMetric.Trap.Transport

/-!
# Uniform recovery of fixed competitors ([S] Lemma 2.4 with uniform parameters)

Packet S3 (MA1 A17, "Stability (i)" and the recovery of the concrete shortcut in "Stability (ii)").
For a family `Fam` of coordinates with a common lower modulus and a common local realization
threshold on a collar `closure O` (properties (P1)–(P2) of MA1 A4), M2a's `lemma24` recovers every
curve of bounded base length inside `K₀ ⊆ O` with an error that is uniform over the curve and over
all coordinates of `Fam` that are uniformly `e`-close to the base coordinate on `closure O`
(`trap_uniform_recovery`). Unlike M2a's `lemma24_eventual_recovery` (a sequence and one fixed
curve), the error bound here is uniform; this gives the relative neighbourhood of MA1 A17 directly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A curve continuous on `[0, 1]` as a bounded continuous function on the unit interval. -/
def trapCurveBCF {X : Type*} [MetricSpace X] (Q : ℝ → X) (hQ : ContinuousOn Q (Icc 0 1)) :
    I →ᵇ X :=
  mkOfCompact ⟨fun t => Q t, hQ.comp_continuous continuous_subtype_val Subtype.prop⟩

theorem trapCurveBCF_apply {X : Type*} [MetricSpace X] (Q : ℝ → X)
    (hQ : ContinuousOn Q (Icc 0 1)) (t : I) : trapCurveBCF Q hQ t = Q t := rfl

theorem trapCurveBCF_extend {X : Type*} [MetricSpace X] (Q : ℝ → X)
    (hQ : ContinuousOn Q (Icc 0 1)) : EqOn (Set.IccExtend zero_le_one (trapCurveBCF Q hQ)) Q
      (Icc 0 1) := fun t ht => by
  rw [Set.IccExtend_of_mem _ _ ht]
  rfl

/-- The upper bound of `w` on a compact set (made `≥ 1`). -/
theorem trap_exists_weight_bound {X : Type*} [MetricSpace X] {w : X → ℝ} {C : Set X}
    (hC : IsCompact C) (hw : ContinuousOn w C) : ∃ M : ℝ, 1 ≤ M ∧ ∀ z ∈ C, w z ≤ M := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hw
  refine ⟨max M 1, le_max_right _ _, fun z hz => ?_⟩
  exact (le_abs_self _).trans ((Real.norm_eq_abs (w z) ▸ hM z hz).trans (le_max_left _ _))

/-- **Uniform recovery** ([S] Lemma 2.4 with parameters uniform over a family of coordinates). -/
theorem trap_uniform_recovery {X : Type*} [MetricSpace X]
    (Fam : Set (X × X → ℝ)) (hFam : ∀ ρ' ∈ Fam, IsCoordinate ρ')
    {ρ : X × X → ℝ} (hρFam : ρ ∈ Fam)
    {w : X → ℝ} {K₀ O : Set X} (hK₀O : K₀ ⊆ O) (hOc : IsCompact (closure O))
    (hw : ContinuousOn w (closure O)) (hw0 : ∀ z ∈ closure O, 0 ≤ w z)
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ ρ' ∈ Fam, ∀ u ∈ closure O, ∀ v ∈ closure O, ρ' (u, v) < m → dist u v < χ)
    (hloc : ∃ δloc : ℝ, 0 < δloc ∧ ∀ ρ' ∈ Fam, ∀ x ∈ K₀, ∀ y ∈ K₀, ρ' (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ' (x, y)))
    {L₀ η : ℝ} (hL₀ : 0 ≤ L₀) (hη : 0 < η) :
    ∃ e : ℝ, 0 < e ∧ ∀ ρ' ∈ Fam,
      (∀ u ∈ closure O, ∀ v ∈ closure O, |ρ (u, v) - ρ' (u, v)| ≤ e) →
      ∀ Q : ℝ → X, ContinuousOn Q (Icc 0 1) → MapsTo Q (Icc 0 1) K₀ →
        curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) Q 0 1 ≤ ENNReal.ofReal L₀ →
        weylDistOnWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w (closure O) (Q 0) (Q 1) ≤
          weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 +
            ENNReal.ofReal η := by
  obtain ⟨M, hM1, hwM⟩ := trap_exists_weight_bound hOc hw
  obtain ⟨δloc, hδloc, hlocal⟩ := hloc
  set Ω := min 1 (η / (4 * (L₀ + 1))) with hΩ_def
  have hΩ : 0 < Ω := lt_min one_pos (by positivity)
  have hΩM : Ω ≤ M := (min_le_left _ _).trans hM1
  have hΩerr : 2 * Ω * L₀ ≤ η / 2 := by
    have hΩle : Ω ≤ η / (4 * (L₀ + 1)) := min_le_right _ _
    have h1 : 2 * Ω * L₀ ≤ 2 * (η / (4 * (L₀ + 1))) * L₀ := by
      have := mul_le_mul_of_nonneg_right hΩle (by positivity : 0 ≤ 2 * L₀)
      nlinarith
    have h2 : 2 * (η / (4 * (L₀ + 1))) * L₀ ≤ η / 2 := by
      rw [show 2 * (η / (4 * (L₀ + 1))) * L₀ = (η * L₀) / (2 * (L₀ + 1)) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨χ, hχ, hosc⟩ :=
    Metric.uniformContinuousOn_iff_le.mp (hOc.uniformContinuousOn_of_continuous hw) Ω hΩ
  obtain ⟨m, hm, hmodm⟩ := hmod χ hχ
  set δ := min m δloc / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδm : 2 * δ < m := by
    have := min_le_left m δloc
    rw [hδ_def]
    linarith
  have hδloc' : 2 * δ < δloc := by
    have := min_le_right m δloc
    rw [hδ_def]
    linarith
  set Cc := 2 * M * (L₀ / δ + 1) with hCc_def
  have hCc : 0 ≤ Cc := by positivity
  set e := min δ (η / (2 * (Cc + 1))) with he_def
  have he : 0 < e := lt_min hδ (by positivity)
  have heδ : e ≤ δ := min_le_left _ _
  have heC : Cc * e ≤ η / 2 := by
    have he' : e ≤ η / (2 * (Cc + 1)) := min_le_right _ _
    have h1 : Cc * e ≤ Cc * (η / (2 * (Cc + 1))) := mul_le_mul_of_nonneg_left he' hCc
    have h2 : Cc * (η / (2 * (Cc + 1))) ≤ η / 2 := by
      rw [show Cc * (η / (2 * (Cc + 1))) = (Cc * η) / (2 * (Cc + 1)) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨e, he, fun ρ' hρ' hclose Q hQc hQK hQlen => ?_⟩
  set Qb := trapCurveBCF Q hQc with hQb_def
  have hQbK : ∀ t : I, Qb t ∈ K₀ := fun t => hQK t.2
  have hext := trapCurveBCF_extend Q hQc
  have hQblen : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Qb) 0 1 ≤ ENNReal.ofReal L₀ := by
    rw [curveLengthWith_congr_path hext]
    exact hQlen
  have hmodρ : ∀ u ∈ closure O, ∀ v ∈ closure O, ρ (u, v) ≤ 2 * δ → dist u v ≤ χ :=
    fun u hu v hv huv => (hmodm ρ hρFam u hu v hv (huv.trans_lt hδm)).le
  have hmodρ' : ∀ u ∈ closure O, ∀ v ∈ closure O, ρ' (u, v) ≤ 2 * δ → dist u v ≤ χ :=
    fun u hu v hv huv => (hmodm ρ' hρ' u hu v hv (huv.trans_lt hδm)).le
  have hwbd : ∀ z ∈ closure O, 0 ≤ w z ∧ w z ≤ M := fun z hz => ⟨hw0 z hz, hwM z hz⟩
  have hwosc : ∀ u ∈ closure O, ∀ v ∈ closure O, dist u v ≤ χ → |w u - w v| ≤ Ω := by
    intro u hu v hv huv
    simpa [Real.dist_eq] using hosc u hu v hv huv
  have hloc' : ∀ x ∈ K₀, ∀ y ∈ K₀, ρ' (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ' (x, y)) :=
    fun x hx y hy hxy => hlocal ρ' hρ' x hx y hy hxy
  obtain ⟨-, new, -, hNewO, -, hweighted, -⟩ :=
    lemma24 ρ ρ' (hFam ρ hρFam) (hFam ρ' hρ') w (K := K₀) (O := O)
      (hK₀O.trans subset_closure) hL₀ hδ he.le heδ hδloc' hχ.le hΩ.le hΩM Qb hQbK hQblen
      hclose hmodρ hmodρ' hwbd hwosc hloc'
  have hdist := weylDistOnWith_le
    (E := fun u v => ENNReal.ofReal (ρ' (u, v))) (w := w) (S := closure O)
    (P := new.extend) new.continuous_extend.continuousOn
    new.extend_zero new.extend_one (fun t ht => by
      rw [Path.extend_apply new ht]
      exact hNewO ⟨t, ht⟩)
  have hwl : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
      (Set.IccExtend zero_le_one Qb) 0 1 =
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 :=
    weightedLengthWith_congr_path hext
  have herr : ENNReal.ofReal (2 * Ω * L₀ + 2 * M * (L₀ / δ + 1) * e) ≤ ENNReal.ofReal η := by
    apply ENNReal.ofReal_le_ofReal
    have : 2 * M * (L₀ / δ + 1) * e = Cc * e := by rw [hCc_def]
    linarith
  calc weylDistOnWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w (closure O) (Q 0) (Q 1)
      = weylDistOnWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w (closure O) (Qb 0) (Qb 1) := rfl
    _ ≤ coordinatePathWeightedLength (fun u v => ENNReal.ofReal (ρ' (u, v))) w new := hdist
    _ ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
          (Set.IccExtend zero_le_one Qb) 0 1 +
          ENNReal.ofReal (2 * Ω * L₀ + 2 * M * (L₀ / δ + 1) * e) := hweighted
    _ ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 + ENNReal.ofReal η := by
        rw [hwl]
        exact add_le_add le_rfl herr

end HigherDimLQGMetric
