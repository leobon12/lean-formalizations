import HigherDimLQGMetric.Limits.LengthLFPP
import HigherDimLQGMetric.Limits.StableLaw
import HigherDimLQGMetric.LfppTight.LawInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Stable subsequential limits of normalized LFPP are almost surely length
metrics. This closes the probabilistic use of Lemma 3.1(1). -/
theorem l6c_ae_stable_limit_length
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)) :
    ∀ᵐ ω ∂P, (Dh ω).IsLength := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let Q := Classical.choose hB2
  have hQ := (Classical.choose_spec hB2).1
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n ω => lfppSeq κ ξ εs (h ω) n
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  have hXa (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hQ.dim κ hQ.kernel ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hYm : Measurable Y := measurable_subtype_coe.comp hDh
  let νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    fun n => ⟨P.map (X n), inferInstance⟩
  let μ : ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    ⟨P.map Y, inferInstance⟩
  have hconv : Tendsto νn atTop (𝓝 μ) :=
    l6c_stable_metric_law P h X Y hXa hYm.aemeasurable hstable νn μ
      (fun _ => rfl) rfl
  have hev : ∀ᶠ n in atTop, εs n < 1 :=
    hεt.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hμmem : μ ∈ closure
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ ε ∈ Ioo (0 : ℝ) 1,
          (ν : Measure C(Rd d × Rd d, ℝ)) =
            P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))} := by
    have ht : Tendsto (fun n => νn (n + N)) atTop (𝓝 μ) :=
      hconv.comp (tendsto_add_atTop_nat N)
    apply mem_closure_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨εs (n + N), ⟨hεs _, hN (n + N) (by omega)⟩, ?_⟩
    rfl
  have hlenlaw := l6c_lemma31_lengthLimit hL6a ξ κ hB2 P h hh μ hμmem
  change ∀ᵐ D ∂P.map Y, IsContLengthFn D at hlenlaw
  have hlen : ∀ᵐ ω ∂P, IsContLengthFn (Y ω) :=
    ae_of_ae_map hYm.aemeasurable hlenlaw
  exact hlen.mono fun ω hω => hω.2

end HigherDimLQGMetric
