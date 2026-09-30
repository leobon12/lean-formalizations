import QuantumZipper.Proofs.GFF.K3.MixedM5Bound

/-!
# Two Hilbert-space extension lemmas (GFF-K3 node M5, preparation)

* `inner_eq_integral_of_mem_closure_span`: if `⟪y, g⟫ = ∫ ⟪v z, g⟫ dμ` for `g` in a set `G`,
  with `v` essentially bounded and `z ↦ ⟪v z, g⟫` measurable, then the same holds (with
  measurability) for every `u` in the closed span of `G` (a weak form of `y = ∫ v dμ`).
* `tendsto_inner_of_mem_closure_span`: an eventually bounded family converging weakly on `G`
  converges weakly on the closed span of `G`.

Both are standard (density plus dominated convergence, resp. an `ε/2` argument); own elementary
proofs.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology RealInnerProductSpace

namespace QuantumZipper.K3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_eq_integral_of_mem_closure_span {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {G : Set E} {v : α → E} {B : ℝ} (hB : ∀ᵐ z ∂μ, ‖v z‖ ≤ B)
    (hm : ∀ g ∈ G, AEStronglyMeasurable (fun z => ⟪v z, g⟫) μ) {y : E}
    (hy : ∀ g ∈ G, ⟪y, g⟫ = ∫ z, ⟪v z, g⟫ ∂μ) {u : E}
    (hu : u ∈ (Submodule.span ℝ G).topologicalClosure) :
    AEStronglyMeasurable (fun z => ⟪v z, u⟫) μ ∧ ⟪y, u⟫ = ∫ z, ⟪v z, u⟫ ∂μ := by
  have hbd : ∀ a : E, ∀ᵐ z ∂μ, ‖⟪v z, a⟫‖ ≤ max B 0 * ‖a‖ := fun a => by
    filter_upwards [hB] with z hz
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hz.trans (le_max_left _ _)) (norm_nonneg _))
  have hint : ∀ a, AEStronglyMeasurable (fun z => ⟪v z, a⟫) μ →
      Integrable (fun z => ⟪v z, a⟫) μ := fun a ha => Integrable.of_bound ha _ (hbd a)
  have hspan : ∀ a ∈ Submodule.span ℝ G,
      AEStronglyMeasurable (fun z => ⟪v z, a⟫) μ ∧ ⟪y, a⟫ = ∫ z, ⟪v z, a⟫ ∂μ := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg => exact ⟨hm g hg, hy g hg⟩
    | zero => simpa using aestronglyMeasurable_const
    | add a b _ _ ha hb =>
      refine ⟨by simp only [inner_add_right]; exact ha.1.add hb.1, ?_⟩
      simp only [inner_add_right]
      rw [integral_add (hint a ha.1) (hint b hb.1), ha.2, hb.2]
    | smul c a _ ha =>
      refine ⟨by simpa only [inner_smul_right] using ha.1.const_mul c, ?_⟩
      simp only [inner_smul_right]
      rw [integral_const_mul, ha.2]
  have hu' : u ∈ closure (Submodule.span ℝ G : Set E) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hu'
  have hpt : ∀ z, Tendsto (fun n => ⟪v z, a n⟫) atTop (𝓝 ⟪v z, u⟫) := fun z =>
    tendsto_const_nhds.inner hlim
  have hmeas : AEStronglyMeasurable (fun z => ⟪v z, u⟫) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hspan _ (ha n)).1) (ae_of_all _ hpt)
  refine ⟨hmeas, ?_⟩
  have hev : ∀ᶠ n in atTop, ‖a n‖ ≤ ‖u‖ + 1 :=
    (hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))).mono fun n hn => hn.le
  have hI : Tendsto (fun n => ∫ z, ⟪v z, a n⟫ ∂μ) atTop (𝓝 (∫ z, ⟪v z, u⟫ ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => max B 0 * (‖u‖ + 1))
      (Eventually.of_forall fun n => (hspan _ (ha n)).1) ?_ (integrable_const _)
      (ae_of_all _ hpt)
    filter_upwards [hev] with n hn
    filter_upwards [hbd (a n)] with z hz
    exact hz.trans (mul_le_mul_of_nonneg_left hn (le_max_right _ _))
  have hL : Tendsto (fun n => ⟪y, a n⟫) atTop (𝓝 ⟪y, u⟫) := tendsto_const_nhds.inner hlim
  exact tendsto_nhds_unique hL (hI.congr fun n => ((hspan _ (ha n)).2).symm)

theorem tendsto_inner_of_mem_closure_span {ι : Type*} {l : Filter ι} {G : Set E} {x : ι → E}
    {x₀ : E} {B : ℝ} (hB : ∀ᶠ t in l, ‖x t‖ ≤ B)
    (hG : ∀ g ∈ G, Tendsto (fun t => ⟪x t, g⟫) l (𝓝 ⟪x₀, g⟫)) {u : E}
    (hu : u ∈ (Submodule.span ℝ G).topologicalClosure) :
    Tendsto (fun t => ⟪x t, u⟫) l (𝓝 ⟪x₀, u⟫) := by
  have hspan : ∀ a ∈ Submodule.span ℝ G, Tendsto (fun t => ⟪x t, a⟫) l (𝓝 ⟪x₀, a⟫) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg => exact hG g hg
    | zero => simpa using tendsto_const_nhds
    | add a b _ _ ha hb => simpa only [inner_add_right] using ha.add hb
    | smul c a _ ha => simpa only [inner_smul_right] using ha.const_mul c
  have hu' : u ∈ closure (Submodule.span ℝ G : Set E) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := max B 0 + ‖x₀‖ + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨a, ha, hua⟩ := Metric.mem_closure_iff.mp hu' (ε / (2 * C)) (by positivity)
  filter_upwards [hB, Metric.tendsto_nhds.mp (hspan a ha) (ε / 2) (by positivity)]
    with t ht1 ht2
  rw [Real.dist_eq] at ht2 ⊢
  have e : ⟪x t, u⟫ - ⟪x₀, u⟫ = (⟪x t, a⟫ - ⟪x₀, a⟫) + ⟪x t - x₀, u - a⟫ := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have h1 : |⟪x t - x₀, u - a⟫| ≤ C * dist u a := by
    rw [dist_eq_norm]
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_sub_le _ _).trans ?_
    rw [hC]; linarith [le_max_left B 0]
  have h2 : C * dist u a ≤ ε / 2 := by
    have := mul_lt_mul_of_pos_left hua hC0
    rw [show C * (ε / (2 * C)) = ε / 2 by field_simp] at this
    exact this.le
  rw [e]
  calc |(⟪x t, a⟫ - ⟪x₀, a⟫) + ⟪x t - x₀, u - a⟫|
      ≤ |⟪x t, a⟫ - ⟪x₀, a⟫| + |⟪x t - x₀, u - a⟫| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht2 (h1.trans h2)
    _ = ε := add_halves ε

end QuantumZipper.K3
