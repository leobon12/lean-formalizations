import HigherDimLQGContinuity.Final.Xi
import HigherDimLQGContinuity.Final.Gamma
import LQGMetric.Metric.Midpoint

/-!
# Same-event continuous length metrics in Theorem 1.1

Packet E4, ruling N20. The Euclidean endpoint proof follows A1D's checked
`A1DT11M.euclid_clause` scratch lemma; the positive clause uses `MetricVersionStmt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

namespace HigherDimLQGContinuity

private theorem e4_euclid_isContinuousMetric (d : ℕ) : IsContinuousMetric (euclidDistC d) := by
  refine ⟨⟨fun x => ?_, fun x y h => ?_, fun x y => ?_, fun x y z => ?_⟩,
    fun x ε hε => ?_⟩
  · exact dist_self x
  · exact dist_eq_zero.1 h
  · exact dist_comm x y
  · exact dist_triangle x y z
  · refine ⟨ε, hε, fun y hy => ?_⟩
    have : dist x y < ε := hy
    rwa [dist_eq_norm] at this

private def e4_euclidCM (d : ℕ) : ContMetric d :=
  ⟨euclidDistC d, e4_euclid_isContinuousMetric d⟩

private theorem e4_euclidCM_isLength (d : ℕ) : (e4_euclidCM d).IsLength := by
  rw [ContMetric.isLength_iff_curves]
  intro z w ε hε
  set P : ℝ → Rd d := fun t => z + t • (w - z) with hP
  have hPc : Continuous P := by fun_prop
  refine ⟨P, hPc.continuousOn, by simp [hP], by simp [hP], ?_⟩
  have hlip : LipschitzWith ‖w - z‖₊ ((e4_euclidCM d).pt ∘ P) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    change dist (P s) (P t) ≤ _
    rw [dist_eq_norm, hP]
    simp only [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, coe_nnnorm,
      Real.dist_eq]
    rw [mul_comm]
  have hvar := (hlip.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := id)
    (s := Icc (0 : ℝ) 1) (mapsTo_univ _ _)
  have hid : eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) = ENNReal.ofReal 1 := by
    have h := (monotone_id (α := ℝ)).monotoneOn (univ : Set ℝ) |>.eVariationOn_eq
      (a := 0) (b := 1) (mem_univ _) (mem_univ _)
    simp only [univ_inter, id_eq, sub_zero] at h
    exact h
  have hlen : (e4_euclidCM d).len P 0 1 ≤ ENNReal.ofReal ‖w - z‖ := by
    rw [ContMetric.len_def, LQGMetric.MetricGeometry.curveLength]
    refine hvar.trans ?_
    rw [hid, ENNReal.ofReal_one, mul_one]
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  refine hlen.trans (le_add_right ?_)
  change ENNReal.ofReal ‖w - z‖ ≤ ENNReal.ofReal (dist z w)
  rw [dist_eq_norm, norm_sub_rev]

/-- The Euclidean member is a continuous length metric in every dimension. -/
theorem e4_euclid_clause (d : ℕ) :
    ∃ M : ContMetric d, M.1 = euclidDistC d ∧ M.IsLength :=
  ⟨e4_euclidCM d, rfl, e4_euclidCM_isLength d⟩

private theorem e4_metric_xi_for {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) (hE : EndpointStmt d X)
    (hMV : MetricVersionStmt d X) :
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D ξ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P,
          (∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
            Tendsto (fun ξ => supDistLU d R (D ξ (h ω)) (D ξ₀ (h ω)))
              (𝓝[xiRange d] ξ₀) (𝓝 0)) ∧
          ∀ ξ ∈ xiRange d, ∃ M : ContMetric d, M.1 = D ξ (h ω) ∧ M.IsLength := by
  have hAE : ∀ᵐ g ∂(normLGFLaw d),
      (ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        Tendsto (fun ξ => X ξ g) (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d))) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∃ M : ContMetric d, M.1 = X ξ g ∧ M.IsLength) :=
    (hX.2.2.and hE).and hMV
  obtain ⟨N, hNsub, hNm, hNzero⟩ :=
    exists_measurable_superset_of_null ((ae_iff).1 hAE)
  let Good : Set (DistRd d) := Nᶜ
  have hGm : MeasurableSet Good := hNm.compl
  have hGAE : ∀ᵐ g ∂(normLGFLaw d), g ∈ Good :=
    (ae_iff).2 (show normLGFLaw d {g | g ∉ Good} = 0 by
      have hset : {g | g ∉ Good} = N := by ext g; simp [Good]
      rw [hset]
      exact hNzero)
  have hG (g : DistRd d) (hg : g ∈ Good) :
      (ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        Tendsto (fun ξ => X ξ g) (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d))) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∃ M : ContMetric d, M.1 = X ξ g ∧ M.IsLength) := by
    by_contra hn
    exact hg (hNsub hn)
  refine ⟨finalVersion d X Good, e4_finalVersion_measurable hd hX hGm, ?_, ?_, ?_⟩
  · intro g
    have hzero : (0 : ℝ) ∉ subcritSet d := by simp [subcritSet]
    simp [finalVersion, hzero]
  · intro ξ hξ hsub E hEstrong hM Ω _ P _ hf hh
    have hcanon : ∀ᵐ g ∂(normLGFLaw d),
        finalVersion d X Good ξ g = (E g).1 := by
      filter_upwards [hGAE, version_medianOne_ae hd hX hξ hsub hEstrong hM]
        with g hg hnorm
      have hmem : ξ ∈ subcritSet d := ⟨hξ, hsub⟩
      simpa [finalVersion, hmem, hg] using hnorm
    exact ae_of_normLGFLaw (by omega) hcanon hh
  · intro Ω _ P _ hf hh
    have hcanon : ∀ᵐ g ∂(normLGFLaw d),
        (∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R
            (finalVersion d X Good ξ g) (finalVersion d X Good ξ₀ g))
            (𝓝[xiRange d] ξ₀) (𝓝 0)) ∧
        ∀ ξ ∈ xiRange d, ∃ M : ContMetric d,
          M.1 = finalVersion d X Good ξ g ∧ M.IsLength := by
      filter_upwards [hGAE] with g hg
      constructor
      · intro ξ₀ hξ₀ R _
        exact e4_tendsto_supDistLU
          (e4_finalVersion_tendsto hd hX hE hg (hG g hg).1.1 (hG g hg).1.2 hξ₀) R
      · intro ξ hξ
        rcases (xiRange_eq_insert_subcritSet d ▸ hξ : ξ ∈ insert 0 (subcritSet d))
          with hzero | hpos
        · subst ξ
          have hzero : (0 : ℝ) ∉ subcritSet d := by simp [subcritSet]
          simpa [finalVersion, hzero] using e4_euclid_clause d
        · obtain ⟨M, hM, hL⟩ := (hG g hg).2 ξ hpos.1 hpos.2
          obtain ⟨⟨E, hEE, -⟩, -⟩ := theorem12 d ξ hd hpos.1 hpos.2
          have hm : 0 < medianXi d X ξ := (medianXi_spec hd hX hpos.1 hpos.2 hEE).1
          let c := (medianXi d X ξ)⁻¹
          have hc : 0 < c := inv_pos.mpr hm
          refine ⟨M.smul c hc, ?_, ContMetric.isLength_smul hc hL⟩
          change c • M.1 = finalVersion d X Good ξ g
          rw [hM]
          simp [c, finalVersion, hpos, hg]
    exact ae_of_normLGFLaw (by omega) hcanon hh

/-- Packet E4, ruling N20: the median-one `γ` version and the continuous
length-metric clause hold on the same almost-sure event. -/
theorem theorem11_metric_of_parts
    (h : ∀ d : ℕ, 3 ≤ d → SubcritLocal d ∧ ∃ X : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      PosVersionStmt d X ∧ EndpointStmt d X ∧ MetricVersionStmt d X)
    (h₂ : Prop18Stmt) : Theorem11MetricStmt := by
  intro d hd
  obtain ⟨-, X, hX, hE, hMV⟩ := h d hd
  obtain ⟨D', hmeas, h0, hver, hcont⟩ := e4_metric_xi_for hd hX hE hMV
  obtain ⟨Ξ, hΞ0, -, hΞc, hΞim, hΞiff, -⟩ := (h₂ d hd).2.2.2
  set I : Set ℝ := Ico 0 (Real.sqrt (2 * d)) with hI
  have ha : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, ha⟩
  let Ξ' : ℝ → ℝ := I.piecewise Ξ (fun _ => 0)
  have hΞ'm : Measurable Ξ' :=
    hΞc.measurable_piecewise continuousOn_const measurableSet_Ico
  have hΞ'eq : ∀ γ ∈ I, Ξ' γ = Ξ γ :=
    fun γ hγ => Set.piecewise_eq_of_mem _ _ _ hγ
  refine ⟨fun γ => D' (Ξ' γ), ?_, ?_, ?_, ?_⟩
  · have heq : Function.uncurry (fun γ => D' (Ξ' γ)) =
        Function.uncurry D' ∘ (fun p : ℝ × DistRd d => (Ξ' p.1, p.2)) := rfl
    rw [heq]
    exact hmeas.comp ((hΞ'm.comp measurable_fst).prodMk measurable_snd)
  · intro g
    simp only [hΞ'eq 0 h0I, hΞ0, h0]
  · intro γ hγ0 hγ1 ξ hξ hQ E hE hE1 Ω _ P _ hh hnorm
    have hξeq : ξ = Ξ γ := (hΞiff γ ⟨hγ0, hγ1⟩ ξ hξ).1 hQ
    have hsub : Real.sqrt (2 * d) < distExp d ξ := hQ ▸ e4_gammaQ_gt d hγ0 hγ1
    have hΞ' : Ξ' γ = ξ := by rw [hΞ'eq γ ⟨hγ0.le, hγ1⟩, hξeq]
    simpa only [hΞ'] using hver ξ hξ hsub E hE hE1 P hh hnorm
  · intro Ω _ P _ hh hnorm
    filter_upwards [hcont P hh hnorm] with ω hω
    constructor
    · intro γ₀ hγ₀ R hR
      have hmem : Ξ γ₀ ∈ xiRange d := hΞim ▸ Set.mem_image_of_mem Ξ hγ₀
      have hT : Tendsto Ξ' (𝓝[I] γ₀) (𝓝[xiRange d] (Ξ γ₀)) := by
        apply tendsto_nhdsWithin_iff.2
        constructor
        · have h1 : Tendsto Ξ (𝓝[I] γ₀) (𝓝 (Ξ γ₀)) := hΞc γ₀ hγ₀
          exact h1.congr' (eventually_nhdsWithin_of_forall fun γ hγ =>
            (hΞ'eq γ hγ).symm)
        · filter_upwards [self_mem_nhdsWithin] with γ hγ
          rw [hΞ'eq γ hγ, ← hΞim]
          exact Set.mem_image_of_mem Ξ hγ
      have hc := ((hω.1 (Ξ γ₀) hmem R hR).comp hT)
      simpa only [Function.comp_def, hΞ'eq γ₀ hγ₀] using hc
    · intro γ hγ
      have hmem : Ξ γ ∈ xiRange d := hΞim ▸ Set.mem_image_of_mem Ξ hγ
      simpa only [hΞ'eq γ hγ] using hω.2 (Ξ γ) hmem

end HigherDimLQGContinuity
