import HigherDimLQGMetric.Select.GeodRel
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Compact bounded geodesic fibers

Packet M3a, MA1 A10. The compact ball supplies pointwise compactness; the fact that
`D` induces the Euclidean topology turns the constant `D`-speed into Euclidean
equicontinuity. Arzelà–Ascoli then gives compactness in the compact-open topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology unitInterval

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A bounded fiber of the geodesic relation for a fixed continuous metric. -/
def geodBoundFiber (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    Set C(unitInterval, Rd d) :=
  {η | (D.1, η) ∈ geodBoundRel x y n}

theorem isClosed_geodBoundFiber (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    IsClosed (geodBoundFiber D x y n) := by
  exact (isClosed_geodBoundRel x y n).preimage
    (continuous_const.prodMk continuous_id)

private theorem continuous_of_geodEq (D : ContMetric d) (x y : Rd d)
    {f : unitInterval → Rd d}
    (hf : ∀ s t : unitInterval,
      D.1 (f s, f t) = |(s : ℝ) - t| * D.1 (x, y)) : Continuous f := by
  have hc : ∀ t : unitInterval,
      ContinuousAt (fun u : unitInterval => |(u : ℝ) - t| * D.1 (x, y)) t := by
    intro t
    fun_prop
  have hcont : ∀ t : unitInterval,
      ContinuousAt (fun u : unitInterval => D.pt (f u)) t := by
    intro t
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hzero : |(t : ℝ) - t| * D.1 (x, y) = 0 := by simp
    have he : ∀ᶠ (u : unitInterval) in 𝓝 t, |(u : ℝ) - t| * D.1 (x, y) < ε := by
      have ht := (hc t).tendsto
      rw [hzero] at ht
      exact ht (gt_mem_nhds hε)
    filter_upwards [he] with u hu
    rw [D.dist_pt, hf]
    exact hu
  have h := D.continuous_unpt.comp (continuous_iff_continuousAt.mpr hcont)
  have he : (D.unpt ∘ fun u : unitInterval => D.pt (f u)) = f := by
    funext u
    exact D.unpt_pt (f u)
  rw [he] at h
  exact h

private def rawGeodBoundFiber (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    Set (unitInterval → Rd d) :=
  {f | f 0 = x ∧ f 1 = y ∧
    (∀ s t : unitInterval,
      D.1 (f s, f t) = |(s : ℝ) - t| * D.1 (x, y)) ∧
    ∀ t : unitInterval, ‖f t‖ ≤ n}

private theorem isClosed_rawGeodBoundFiber (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    IsClosed (rawGeodBoundFiber D x y n) := by
  have h1 : IsClosed {f : unitInterval → Rd d | f 0 = x} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have h2 : IsClosed {f : unitInterval → Rd d | f 1 = y} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have h3 : IsClosed {f : unitInterval → Rd d |
      ∀ s t : unitInterval,
        D.1 (f s, f t) = |(s : ℝ) - t| * D.1 (x, y)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_eq (D.1.continuous.comp
        ((continuous_apply s).prodMk (continuous_apply t))) continuous_const
  have h4 : IsClosed {f : unitInterval → Rd d | ∀ t : unitInterval, ‖f t‖ ≤ n} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_le (continuous_apply t).norm continuous_const
  change IsClosed ({f : unitInterval → Rd d | f 0 = x} ∩
    ({f | f 1 = y} ∩ ({f | ∀ s t : unitInterval,
      D.1 (f s, f t) = |(s : ℝ) - t| * D.1 (x, y)} ∩
      {f | ∀ t : unitInterval, ‖f t‖ ≤ n})))
  exact h1.inter (h2.inter (h3.inter h4))

private theorem geodBoundFiber_equicontinuous (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    Equicontinuous ((↑) : geodBoundFiber D x y n → unitInterval → Rd d) := by
  intro s
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hK : IsCompact (D.pt '' Metric.closedBall (0 : Rd d) n) :=
    D.isCompact_image_pt (isCompact_closedBall (0 : Rd d) n)
  have hu : UniformContinuousOn D.unpt (D.pt '' Metric.closedBall (0 : Rd d) n) :=
    hK.uniformContinuousOn_of_continuous D.continuous_unpt.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  let a : ℝ := D.1 (x, y) + 1
  have ha : 0 < a := by dsimp [a]; linarith [D.nonneg x y]
  have hδ' : 0 < δ / a := div_pos hδ ha
  filter_upwards [Metric.ball_mem_nhds s hδ'] with t ht η
  have hη := η.2
  change IsConstSpeedGeodFn D.1 x y η.1 ∧ ∀ u, ‖η.1 u‖ ≤ n at hη
  have hs : D.pt (η.1 s) ∈ D.pt '' Metric.closedBall (0 : Rd d) n := by
    refine ⟨η.1 s, ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hη.2 s
  have ht' : D.pt (η.1 t) ∈ D.pt '' Metric.closedBall (0 : Rd d) n := by
    refine ⟨η.1 t, ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hη.2 t
  have hst : dist (D.pt (η.1 s)) (D.pt (η.1 t)) < δ := by
    rw [D.dist_pt, hη.1.2.2 s t, ← Real.dist_eq, ← Subtype.dist_eq]
    have hst' : dist s t < δ / a := by rwa [Metric.mem_ball, dist_comm] at ht
    have hnonneg : 0 ≤ dist s t := dist_nonneg
    have hprod : dist s t * a < δ := (lt_div_iff₀ ha).mp hst'
    have hle : dist s t * D.1 (x, y) ≤ dist s t * a :=
      mul_le_mul_of_nonneg_left (by dsimp [a]; linarith) (dist_nonneg)
    exact lt_of_le_of_lt hle hprod
  simpa only [D.unpt_pt] using hδu _ hs _ ht' hst

/-- Bounded sets of constant-speed `D`-geodesics are compact. -/
theorem isCompact_geodBoundFiber (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    IsCompact (geodBoundFiber D x y n) := by
  let S := geodBoundFiber D x y n
  let T := rawGeodBoundFiber D x y n
  have hT : IsCompact T := by
    have hsub : T ⊆ Set.pi univ fun _ : unitInterval => Metric.closedBall (0 : Rd d) n := by
      intro f hf t _
      simpa only [T, rawGeodBoundFiber, mem_ofPred_eq, Metric.mem_closedBall,
        dist_zero_right] using hf.2.2.2 t
    exact (isCompact_univ_pi fun _ : unitInterval => isCompact_closedBall (0 : Rd d) n).of_isClosed_subset
      (isClosed_rawGeodBoundFiber D x y n) hsub
  have himg : ContinuousMap.toFun '' S = T := by
    ext f
    constructor
    · rintro ⟨η, hη, rfl⟩
      change IsConstSpeedGeodFn D.1 x y η ∧ ∀ t, ‖η t‖ ≤ n at hη
      rcases hη with ⟨⟨h0, h1, h2⟩, hb⟩
      exact ⟨h0, h1, h2, hb⟩
    · intro hf
      have hc := continuous_of_geodEq D x y hf.2.2.1
      refine ⟨⟨f, hc⟩, ?_, rfl⟩
      rcases hf with ⟨h0, h1, h2, hb⟩
      exact ⟨⟨h0, h1, h2⟩, hb⟩
  exact ArzelaAscoli.isCompact_of_equicontinuous S (himg ▸ hT)
    (geodBoundFiber_equicontinuous D x y n)

end HigherDimLQGMetric
