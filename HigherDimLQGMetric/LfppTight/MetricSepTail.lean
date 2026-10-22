import HigherDimLQGMetric.LfppTight.MetricSepShell
import HigherDimLQGMetric.LfppTight.FarTight

/-! Uniform probability of separation on bounded centers and arbitrary outer points. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_finite_shell_tail (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (T : Finset (Rd d)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ θ : ℝ, 0 < θ → ∃ t : ℝ, 0 < t ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ c ∈ T, DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ))
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ t} ≤
          ENNReal.ofReal θ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      intro θ hθ
      refine ⟨1, by norm_num, ?_⟩
      intro ε hε
      simp
  | @insert c T hc ih =>
      intro θ hθ
      have hhalf : 0 < θ / 2 := by positivity
      obtain ⟨t₁, ht₁, htail₁⟩ := l6a_pure_shell_tail hL1e hDGZ
        hAdapter P h hh c (by linarith : 0 < 2 * ρ)
        (by linarith : 2 * ρ < 4 * ρ) hhalf
      obtain ⟨t₂, ht₂, htail₂⟩ := ih (θ / 2) hhalf
      let t := min t₁ t₂
      refine ⟨t, lt_min ht₁ ht₂, ?_⟩
      intro ε hε
      let D := fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
      let E₁ : Set Ω := {ω | DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ)) (D ω) ≤ t₁}
      let E₂ : Set Ω := {ω | ∃ c' ∈ T,
        DGZ.nd_setInf (sphere c' (2 * ρ)) (sphere c' (4 * ρ)) (D ω) ≤ t₂}
      have hsub : {ω | ∃ c' ∈ insert c T,
          DGZ.nd_setInf (sphere c' (2 * ρ)) (sphere c' (4 * ρ)) (D ω) ≤ t} ⊆
          E₁ ∪ E₂ := by
        rintro ω ⟨c', hc', hbound⟩
        rcases Finset.mem_insert.mp hc' with rfl | hc'T
        · exact Or.inl (hbound.trans (min_le_left _ _))
        · exact Or.inr ⟨c', hc'T, hbound.trans (min_le_right _ _)⟩
      calc
        P {ω | ∃ c' ∈ insert c T,
          DGZ.nd_setInf (sphere c' (2 * ρ)) (sphere c' (4 * ρ)) (D ω) ≤ t} ≤
          P (E₁ ∪ E₂) := measure_mono hsub
        _ ≤ P E₁ + P E₂ := measure_union_le _ _
        _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
          add_le_add (htail₁ ε hε) (htail₂ ε hε)
        _ = ENNReal.ofReal θ := by
          rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
          congr 1
          ring

theorem l6a_metricSep_tail (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (R m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ k : ℕ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) ∉
        metricSepSet_select R m k} ≤ ENNReal.ofReal θ := by
  classical
  let ρ : ℝ := 1 / (8 * ((m : ℝ) + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨T₀, -, hT₀, hcover₀⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Rd d) R) hρ
  let T : Finset (Rd d) := hT₀.toFinset
  have hcover : closedBall (0 : Rd d) R ⊆ ⋃ c ∈ T, ball c ρ := by
    simpa only [T, hT₀.mem_toFinset] using hcover₀
  obtain ⟨t, ht, htail⟩ :=
    l6a_finite_shell_tail hL1e hDGZ hAdapter P h hh T hρ θ hθ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt ht
  refine ⟨k, ?_⟩
  intro ε hε
  have hae : 0 < aEps κ ξ ε :=
    l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1
  have hcont := l10a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel
    P h hh hε.1
  have hsub : ∀ᵐ ω ∂P,
      toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) ∉
        metricSepSet_select R m k →
      ∃ c ∈ T, DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ))
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ t := by
    filter_upwards [hcont] with ω hc hbad
    by_contra hn
    let D : C(Rd d × Rd d, ℝ) :=
      toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
    have hbarrier : ∀ c ∈ T, ∀ x ∈ closedBall c (2 * ρ),
        ∀ y ∉ ball c (4 * ρ),
          DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ)) D ≤ D (x, y) := by
      intro c hcT x hx y hy
      change DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ))
        (DGZ.normMetricC ξ (convMollify κ ε (h ω)) (aEps κ ξ ε)) ≤
        DGZ.normMetricC ξ (convMollify κ ε (h ω)) (aEps κ ξ ε) (x, y)
      exact l6a_normMetric_shell_barrier ξ (aEps κ ξ ε)
        (convMollify κ ε (h ω)) hc hae c (by linarith) hx hy
    have hgood : ∀ c ∈ T,
        t < DGZ.nd_setInf (sphere c (2 * ρ)) (sphere c (4 * ρ)) D := by
      intro c hcT
      exact lt_of_not_ge (fun hle => hn ⟨c, hcT, hle⟩)
    have hmem : D ∈ metricSepSet_select R m k :=
      l6a_metricSep_of_shell R m k T D ρ t rfl hk.le hcover hbarrier hgood
    exact hbad hmem
  exact (measure_mono_ae hsub).trans (htail ε hε)

end HigherDimLQGMetric
