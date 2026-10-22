import HigherDimLQGMetric.Routing.Lemma41Mesh
import HigherDimLQGMetric.Coord.RecoveryHelpers

/-!
# A marked witness and its two mesh connectors

This is the edgewise construction in Lemma 4.1′. The middle arc is fixed before routing, and
the two connectors attach only to its exterior stubs.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry HigherDimLFPP
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_edge_routing_full {d : ℕ} (hd : 3 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {m n : Fin d → ℤ} (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (hγbox : MapsTo γ (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ ρ (γ 0, γ 1))
    (hE : curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ 0, γ 1))) :
    ∃ (s t u q : ℝ) (βl βr σ : ℝ → MetricFunSpace ρ hρ.metric),
      0 < s ∧ s < t ∧ t < 1 ∧ 0 ≤ u ∧ u < s ∧ t < q ∧ q ≤ 1 ∧
      ContinuousOn σ (Icc 0 1) ∧ InjOn σ (Icc 0 1) ∧
      σ 0 = MetricFunSpace.pt ρ hρ.metric (γ s) ∧
      σ 1 = MetricFunSpace.pt ρ hρ.metric (γ t) ∧
      σ = (fun r => MetricFunSpace.pt ρ hρ.metric (γ (s + (t - s) * r))) ∧
      a₁ / 2 < dist (σ 0) (σ 1) ∧
      curveLengthWith E σ 0 1 < ENNReal.ofReal (c₃ * dist (σ 0) (σ 1)) ∧
      MapsTo σ (Icc 0 1)
        (MetricFunSpace.pt ρ hρ.metric ''
          centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)) ∧
      ContinuousOn βl (Icc 0 1) ∧ InjOn βl (Icc 0 1) ∧
      curveLength βl 0 1 ≠ ∞ ∧
      βl 0 = MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ m) ∧
      βl 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
      (∀ r ∈ Icc (0 : ℝ) 1,
        LQGMetric.metricFunSpaceVal ρ hρ.metric (βl r) ∈
          routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
        βl r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) ∧
      ContinuousOn βr (Icc 0 1) ∧ InjOn βr (Icc 0 1) ∧
      curveLength βr 0 1 ≠ ∞ ∧
      βr 0 = MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ n) ∧
      βr 1 = MetricFunSpace.pt ρ hρ.metric (γ q) ∧
      (∀ r ∈ Icc (0 : ℝ) 1,
        LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r) ∈
          routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, βr r ∉ βl '' Icc 0 1) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
        βr r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  let pγ : ℝ → MetricFunSpace ρ hρ.metric := MetricFunSpace.pt ρ hρ.metric ∘ γ
  have hpγc : ContinuousOn pγ (Icc 0 1) :=
    hρ.pt_continuous.continuousOn.comp hγc (fun _ _ => mem_univ _)
  have hsep' : a₁ ≤ dist (pγ 0) (pγ 1) := by
    simpa only [pγ, Function.comp_apply, MetricFunSpace.dist_pt] using hsep
  obtain ⟨s, t, hs₀, hst, ht₁, hmarksep, hmarkE⟩ :=
    lemma41_trim E pγ hpγc ha₁ hc₂ hc₂₃ hsep' hE
  have hreg := lemma41_mesh_edgeRegions hδ hmn ρ γ hγbox ⟨hs₀, hst, ht₁⟩
  obtain ⟨u, q, hu₀, hus, htq, hq₁, βl, βr, hβlc, hβli, hβllen,
    hβl0, hβl1, hβlΩ, hβlavoid, hβrc, hβri, hβrlen, hβr0,
    hβr1, hβrΩ, hβravoidl, hβravoidγ⟩ :=
    lemma41_pair_connectors hd ρ hρ hreal γ hγc hγi s t
      (Topology.latticePoint δ m) (Topology.latticePoint δ n)
      (routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      (routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)) hreg
  let φ : ℝ → ℝ := fun r => s + (t - s) * r
  let σ : ℝ → MetricFunSpace ρ hρ.metric := pγ ∘ φ
  have hφc : Continuous φ := continuous_const.add (continuous_const.mul continuous_id)
  have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc s t) := by
    intro r hr
    constructor <;> dsimp [φ] <;> nlinarith [mul_nonneg (sub_pos.mpr hst).le hr.1,
      mul_le_of_le_one_right (sub_pos.mpr hst).le hr.2]
  have hφmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    dsimp [φ]
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hab (sub_pos.mpr hst).le) s)
  have hσc : ContinuousOn σ (Icc 0 1) :=
    (hpγc.mono (Icc_subset_Icc hs₀.le ht₁.le)).comp hφc.continuousOn hφmem
  have hpγi : InjOn pγ (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    apply hγi ha hb
    exact heq
  have hσi : InjOn σ (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    have hφeq := hpγi (Icc_subset_Icc hs₀.le ht₁.le (hφmem ha))
      (Icc_subset_Icc hs₀.le ht₁.le (hφmem hb)) heq
    dsimp [φ] at hφeq
    have hdiff : t - s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
    nlinarith
  have hσ0 : σ 0 = pγ s := by simp [σ, φ]
  have hσ1 : σ 1 = pγ t := by simp [σ, φ]
  have hσE : curveLengthWith E σ 0 1 = curveLengthWith E pγ s t := by
    calc
      curveLengthWith E σ 0 1 = curveLengthWith E pγ (φ 0) (φ 1) :=
        curveLengthWith_comp_monotoneOn E pγ (by norm_num : (0 : ℝ) ≤ 1)
          hφc.continuousOn hφmono
      _ = curveLengthWith E pγ s t := by
        simp only [φ, mul_zero, mul_one, add_zero]
        congr 1
        ring
  refine ⟨s, t, u, q, βl, βr, σ, hs₀, hst, ht₁, hu₀, hus, htq, hq₁,
    hσc, hσi, hσ0, hσ1, rfl, ?_, ?_, ?_, hβlc, hβli, hβllen,
    hβl0, hβl1, hβlΩ, hβlavoid, hβrc, hβri, hβrlen, hβr0,
    hβr1, hβrΩ, hβravoidl, hβravoidγ⟩
  · simpa only [hσ0, hσ1] using hmarksep
  · simpa only [hσ0, hσ1, hσE] using hmarkE
  · intro r hr
    refine ⟨γ (φ r), hγbox (Icc_subset_Icc hs₀.le ht₁.le (hφmem hr)), rfl⟩

theorem lemma41_edge_routing {d : ℕ} (hd : 3 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {m n : Fin d → ℤ} (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (hγbox : MapsTo γ (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ ρ (γ 0, γ 1))
    (hE : curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ 0, γ 1))) :
    ∃ (s t u q : ℝ) (βl βr σ : ℝ → MetricFunSpace ρ hρ.metric),
      0 < s ∧ s < t ∧ t < 1 ∧ 0 ≤ u ∧ u < s ∧ t < q ∧ q ≤ 1 ∧
      ContinuousOn σ (Icc 0 1) ∧ InjOn σ (Icc 0 1) ∧
      σ 0 = MetricFunSpace.pt ρ hρ.metric (γ s) ∧
      σ 1 = MetricFunSpace.pt ρ hρ.metric (γ t) ∧
      a₁ / 2 < dist (σ 0) (σ 1) ∧
      curveLengthWith E σ 0 1 < ENNReal.ofReal (c₃ * dist (σ 0) (σ 1)) ∧
      MapsTo σ (Icc 0 1)
        (MetricFunSpace.pt ρ hρ.metric ''
          centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)) ∧
      ContinuousOn βl (Icc 0 1) ∧ InjOn βl (Icc 0 1) ∧
      curveLength βl 0 1 ≠ ∞ ∧
      βl 0 = MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ m) ∧
      βl 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
      (∀ r ∈ Icc (0 : ℝ) 1,
        LQGMetric.metricFunSpaceVal ρ hρ.metric (βl r) ∈
          routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
        βl r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) ∧
      ContinuousOn βr (Icc 0 1) ∧ InjOn βr (Icc 0 1) ∧
      curveLength βr 0 1 ≠ ∞ ∧
      βr 0 = MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ n) ∧
      βr 1 = MetricFunSpace.pt ρ hρ.metric (γ q) ∧
      (∀ r ∈ Icc (0 : ℝ) 1,
        LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r) ∈
          routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, βr r ∉ βl '' Icc 0 1) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
        βr r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  obtain ⟨s, t, u, q, βl, βr, σ, hs₀, hst, ht₁, hu₀, hus, htq, hq₁,
    hσc, hσi, hσ0, hσ1, _, hmarksep, hmarkE, hσbox, hβlc, hβli, hβllen,
    hβl0, hβl1, hβlΩ, hβlavoid, hβrc, hβri, hβrlen, hβr0,
    hβr1, hβrΩ, hβravoidl, hβravoidγ⟩ :=
    lemma41_edge_routing_full hd hδ hmn ρ hρ hreal E γ hγc hγi hγbox
      ha₁ hc₂ hc₂₃ hsep hE
  exact ⟨s, t, u, q, βl, βr, σ, hs₀, hst, ht₁, hu₀, hus, htq, hq₁,
    hσc, hσi, hσ0, hσ1, hmarksep, hmarkE, hσbox, hβlc, hβli, hβllen,
    hβl0, hβl1, hβlΩ, hβlavoid, hβrc, hβri, hβrlen, hβr0,
    hβr1, hβrΩ, hβravoidl, hβravoidγ⟩

end HigherDimLQGMetric
