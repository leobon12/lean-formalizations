import HigherDimLQGMetric.Metric.Internal

/-!
# First-exit barrier gives global distances ([C] (2.12))

Packet P5a. Source: blueprint Part A, Lemma `a:lem-212` ([C] (2.12), p. 6, l. 267–272); planning
audit NA1, item 19 and Details (c) **R3**; NA1's probe shape `internal_eq_global`.

**Statement** (`internal_eq_global`). Let `D` be a continuous length metric on `ℝ^d`, `U, K' ⊆ ℝ^d`,
`δ₁ > 0` with `B̄_{δ₁}(u) ⊆ U` for `u ∈ K'`, an exit barrier `ℓ` with `D(u, w; U) ≥ ℓ` whenever
`u ∈ K'` and `|w - u| = δ₁`, and a local competitor `δ₀` with `D(u, v; U) < ℓ` for `u, v ∈ K'`,
`|u - v| ≤ δ₀`. Then `D(u, v; U) = D(u, v)` for such `u, v`.

**Proof.** `D ≤ D(·, ·; U)` always. Let `P` be a near-optimal curve from `u` to `v` (length
metric). If `P` stays in `B̄_{δ₁}(u) ⊆ U`, its length bounds `D(u, v; U)`. Otherwise it hits the
sphere `|w - u| = δ₁` at a first time `s` (`exists_first_hit` on the closed set
`{δ₁ ≤ |w - u|}`), and `P|[0, s]` is a curve in `B̄_{δ₁}(u) ⊆ U`, so its length is at least
`D(u, P s; U) ≥ ℓ > D(u, v; U)`.

The openness of `U` (a hypothesis of NA1's probe shape) is not needed and is omitted. The
pointwise core `internal_eq_of_exit_barrier` takes the barrier in `[0, ∞]`. Since the hypotheses
involve `D` only through `D(·, ·; U)`, the conclusion holds for every length metric with the same
internal metric on `U` (`internal_eq_global_of_internal_eq`, "every exterior extension").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- **First exit from a closed ball.** A curve `P : [0, T] → ℝ^d` with `P 0 = u` that leaves the
closed ball `B̄_{δ₁}(u)` (`δ₁ > 0`) has a time `s ∈ (0, T]` with `|P s - u| = δ₁` before which it
stays in the closed ball. -/
theorem witness_exists_first_sphere_hit {P : ℝ → Rd d} {T δ₁ : ℝ} {u : Rd d} (hδ₁ : 0 < δ₁)
    (hP : ContinuousOn P (Icc 0 T)) (hP0 : P 0 = u)
    (hout : ∃ t ∈ Icc (0 : ℝ) T, P t ∉ closedBall u δ₁) :
    ∃ s ∈ Icc (0 : ℝ) T, ‖P s - u‖ = δ₁ ∧ MapsTo P (Icc 0 s) (closedBall u δ₁) := by
  have hA : IsClosed {w : Rd d | δ₁ ≤ ‖w - u‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  obtain ⟨t, ht, htout⟩ := hout
  have htA : P t ∈ {w : Rd d | δ₁ ≤ ‖w - u‖} := by
    simp only [mem_closedBall, dist_eq_norm, not_le] at htout
    exact htout.le
  obtain ⟨s, hs, hsA, hbefore⟩ := exists_first_hit hP hA ⟨t, ht, htA⟩
  have hbefore' : ∀ q ∈ Ico (0 : ℝ) s, P q ∈ ball u δ₁ := by
    intro q hq
    have h := hbefore q hq
    simp only [mem_ofPred_eq, not_le] at h
    rw [mem_ball, dist_eq_norm]
    exact h
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hP0] at hsA
      simp only [mem_ofPred_eq, sub_self, norm_zero] at hsA
      linarith
    · exact h
  -- `P s` is a limit of points of the open ball
  have hcl : P s ∈ closedBall u δ₁ := by
    have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
    have hlim : Tendsto P (𝓝[Ico 0 s] s) (𝓝 (P s)) :=
      ((hP.mono (Icc_subset_Icc le_rfl hs.2)).continuousWithinAt
        ⟨hs.1, le_rfl⟩).tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)
    exact closure_ball_subset_closedBall
      (mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall hbefore'))
  refine ⟨s, hs, ?_, ?_⟩
  · have h1 : ‖P s - u‖ ≤ δ₁ := by rwa [mem_closedBall, dist_eq_norm] at hcl
    exact le_antisymm h1 hsA
  · intro q hq
    rcases hq.2.eq_or_lt with h | h
    · rw [h]; exact hcl
    · exact ball_subset_closedBall (hbefore' q ⟨hq.1, h⟩)

/-- **(2.12), pointwise form.** Let `D` be a length metric, `δ₁ > 0` with `B̄_{δ₁}(u) ⊆ U`, and
`ℓ ∈ [0, ∞]` an exit barrier: `D(u, w; U) ≥ ℓ` for `|w - u| = δ₁`. If `D(u, v; U) < ℓ`, then
`D(u, v; U) = D(u, v)`. -/
theorem internal_eq_of_exit_barrier (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    {u v : Rd d} {δ₁ : ℝ} {ℓ : ℝ≥0∞} (hδ₁ : 0 < δ₁) (hbuf : closedBall u δ₁ ⊆ U)
    (hexit : ∀ w : Rd d, ‖w - u‖ = δ₁ → ℓ ≤ D.internal U u w)
    (hloc : D.internal U u v < ℓ) :
    D.internal U u v = ENNReal.ofReal (D.1 (u, v)) := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    (D.ofReal_le_internal U u v)
  obtain ⟨P, hPc, hP0, hP1, hPlen⟩ :=
    (D.isLength_iff_curves.1 hD) u v (ε : ℝ) (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hPlen
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ closedBall u δ₁
  · calc D.internal U u v = D.internal U (P 0) (P 1) := by rw [hP0, hP1]
      _ ≤ D.len P 0 1 := D.internal_le_len zero_le_one hPc fun t ht => hbuf (hstay t ht)
      _ ≤ _ := hPlen
  · push Not at hstay
    obtain ⟨s, hs, hsu, hmaps⟩ := witness_exists_first_sphere_hit hδ₁ hPc hP0 hstay
    calc D.internal U u v ≤ ℓ := hloc.le
      _ ≤ D.internal U u (P s) := hexit _ hsu
      _ = D.internal U (P 0) (P s) := by rw [hP0]
      _ ≤ D.len P 0 s :=
          D.internal_le_len hs.1 (hPc.mono (Icc_subset_Icc le_rfl hs.2)) (hmaps.mono_right hbuf)
      _ ≤ D.len P 0 1 := D.len_mono P le_rfl hs.2
      _ ≤ _ := hPlen

/-- **(2.12)** (`a:lem-212`; NA1 R3; NA1's probe shape `internal_eq_global` without the unused
openness of `U`): an exit barrier from `δ₁`-balls about the points of `K'` that costs more than the
local competitor forces `D(u, v; U) = D(u, v)` for `u, v ∈ K'` with `|u - v| ≤ δ₀`. -/
theorem internal_eq_global (D : ContMetric d) (hD : D.IsLength) {U Kset : Set (Rd d)}
    {δ₀ δ₁ ℓ : ℝ} (hδ₁ : 0 < δ₁)
    (hbuf : ∀ u ∈ Kset, closedBall u δ₁ ⊆ U)
    (hexit : ∀ u ∈ Kset, ∀ w : Rd d, ‖w - u‖ = δ₁ → ENNReal.ofReal ℓ ≤ D.internal U u w)
    (hloc : ∀ u ∈ Kset, ∀ v ∈ Kset, ‖u - v‖ ≤ δ₀ → D.internal U u v < ENNReal.ofReal ℓ) :
    ∀ u ∈ Kset, ∀ v ∈ Kset, ‖u - v‖ ≤ δ₀ → D.internal U u v = ENNReal.ofReal (D.1 (u, v)) :=
  fun u hu v hv huv =>
    internal_eq_of_exit_barrier D hD hδ₁ (hbuf u hu) (hexit u hu) (hloc u hu v hv huv)

/-- **(2.12) for every exterior extension** (`a:lem-212`, last sentence): the hypotheses of
`internal_eq_global` only involve `D(·, ·; U)`, so if a length metric `D'` has the same internal
metric on `U` as `D`, then `D(u, v; U) = D'(u, v)` for `u, v ∈ K'` with `|u - v| ≤ δ₀`. (`D` itself
need not be a length metric.) -/
theorem internal_eq_global_of_internal_eq (D D' : ContMetric d) (hD' : D'.IsLength)
    {U Kset : Set (Rd d)} {δ₀ δ₁ ℓ : ℝ} (hδ₁ : 0 < δ₁)
    (hbuf : ∀ u ∈ Kset, closedBall u δ₁ ⊆ U)
    (hexit : ∀ u ∈ Kset, ∀ w : Rd d, ‖w - u‖ = δ₁ → ENNReal.ofReal ℓ ≤ D.internal U u w)
    (hloc : ∀ u ∈ Kset, ∀ v ∈ Kset, ‖u - v‖ ≤ δ₀ → D.internal U u v < ENNReal.ofReal ℓ)
    (heq : ∀ z ∈ U, ∀ w ∈ U, D'.internal U z w = D.internal U z w) :
    ∀ u ∈ Kset, ∀ v ∈ Kset, ‖u - v‖ ≤ δ₀ → D.internal U u v = ENNReal.ofReal (D'.1 (u, v)) := by
  have hKU : ∀ u ∈ Kset, u ∈ U := fun u hu => hbuf u hu (mem_closedBall_self hδ₁.le)
  intro u hu v hv huv
  rw [← heq u (hKU u hu) v (hKU v hv)]
  refine internal_eq_global D' hD' (ℓ := ℓ) hδ₁ hbuf (fun u' hu' w hw => ?_)
    (fun u' hu' v' hv' h => ?_) u hu v hv huv
  · have hwU : w ∈ U := hbuf u' hu' (by rw [mem_closedBall, dist_eq_norm, hw])
    rw [heq u' (hKU u' hu') w hwU]
    exact hexit u' hu' w hw
  · rw [heq u' (hKU u' hu') v' (hKU v' hv')]
    exact hloc u' hu' v' hv' h

end HigherDimLQGContinuity
