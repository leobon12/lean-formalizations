import HigherDimLQGContinuity.Witness.FirstExit
import HigherDimLQGContinuity.Witness.Basic

/-!
# (2.12) on the local references

Packet P5a. Source: blueprint Part A, Lemma `a:lem-refs-212` (with Definition `a:def-refs`);
planning audit NA1, Details (c) **R3**; erratum EA (`a:err-refs`).

For reference constants `(H₀, σ₀, β₀, m, M)` put
`δ₀ = subdivDelta0 H₀ σ₀ β₀ = min (1/64) ((H₀⁻² 8^{-β₀})^{1/σ₀} / 2)`.

* `subdivDelta0_pos`, `subdivDelta0_le`, `subdivDelta0_spec` (`H₀ δ₀^{σ₀} < H₀⁻¹ 8^{-β₀}`).
* `LocalRefs.exit_barrier`: the lower reference gives the exit barrier `ℓ = H₀⁻¹ 8^{-β₀}` from the
  balls `B̄_{1/8}(u)`, `u ∈ K` (these lie in `annCl 0 (5/8) (9/8) ⊆ A`).
* `LocalRefs.local_competitor`: the upper reference at close points gives `G(u, v; A) < ℓ` for
  `u, v ∈ K` with `|u - v| ≤ δ₀`.
* `refs_internal_eq_global` (Lemma `a:lem-refs-212`): for a length metric with `LocalRefs`,
  `G(u, v; A) = G(u, v)` for `u, v ∈ K`, `|u - v| ≤ δ₀`; and
  `refs_internal_eq_global_of_internal_eq`: the same for every length metric with the same internal
  metric on `A` ("every exterior extension").
* `LocalRefs.of_internal_eq`: the references are a condition on the `A`-internal profile alone
  (with `setDistIn_congr_internal`, `diamIn_congr_internal`).

Only `0 < H₀` and `0 < σ₀` are used (the blueprint's reference constants have `H₀ ≥ 1`,
`0 < σ₀ < 1 < β₀`, `0 < m < M`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The local-competitor radius `δ₀` -/

/-- `δ₀(Rfc) = min(1/64, ½ (H₀⁻² 8^{-β₀})^{1/σ₀})` (Lemma `a:lem-refs-212`). -/
def subdivDelta0 (H₀ σ₀ β₀ : ℝ) : ℝ :=
  min (1 / 64) (((H₀ ^ 2)⁻¹ * (8 : ℝ) ^ (-β₀)) ^ (1 / σ₀) / 2)

theorem subdivDelta0_pos {H₀ σ₀ β₀ : ℝ} (hH₀ : 0 < H₀) : 0 < subdivDelta0 H₀ σ₀ β₀ := by
  unfold subdivDelta0
  refine lt_min (by norm_num) (div_pos (Real.rpow_pos_of_pos ?_ _) two_pos)
  exact mul_pos (inv_pos.2 (pow_pos hH₀ 2)) (Real.rpow_pos_of_pos (by norm_num) _)

theorem subdivDelta0_le (H₀ σ₀ β₀ : ℝ) : subdivDelta0 H₀ σ₀ β₀ ≤ 1 / 64 :=
  min_le_left _ _

/-- The defining property of `δ₀`: the upper reference at distance `δ₀` costs less than the exit
barrier `H₀⁻¹ 8^{-β₀}`. -/
theorem subdivDelta0_spec {H₀ σ₀ β₀ : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) :
    H₀ * subdivDelta0 H₀ σ₀ β₀ ^ σ₀ < H₀⁻¹ * (8 : ℝ) ^ (-β₀) := by
  set c : ℝ := (H₀ ^ 2)⁻¹ * (8 : ℝ) ^ (-β₀) with hc
  have hc0 : 0 < c := mul_pos (inv_pos.2 (pow_pos hH₀ 2)) (Real.rpow_pos_of_pos (by norm_num) _)
  have hδle : subdivDelta0 H₀ σ₀ β₀ ≤ c ^ (1 / σ₀) / 2 := min_le_right _ _
  have hδ0 : 0 ≤ subdivDelta0 H₀ σ₀ β₀ := (subdivDelta0_pos hH₀).le
  have hpow : subdivDelta0 H₀ σ₀ β₀ ^ σ₀ ≤ c / 2 ^ σ₀ := by
    calc subdivDelta0 H₀ σ₀ β₀ ^ σ₀ ≤ (c ^ (1 / σ₀) / 2) ^ σ₀ :=
          Real.rpow_le_rpow hδ0 hδle hσ₀.le
      _ = (c ^ (1 / σ₀)) ^ σ₀ / 2 ^ σ₀ :=
          Real.div_rpow (Real.rpow_nonneg hc0.le _) (by norm_num) _
      _ = c / 2 ^ σ₀ := by
          rw [one_div, Real.rpow_inv_rpow hc0.le hσ₀.ne']
  have h2 : 1 < (2 : ℝ) ^ σ₀ := Real.one_lt_rpow (by norm_num) hσ₀
  have hlt : c / 2 ^ σ₀ < c := div_lt_self hc0 h2
  have hHc : H₀ * c = H₀⁻¹ * (8 : ℝ) ^ (-β₀) := by
    rw [hc, ← mul_assoc]
    congr 1
    field_simp
  calc H₀ * subdivDelta0 H₀ σ₀ β₀ ^ σ₀ ≤ H₀ * (c / 2 ^ σ₀) :=
        mul_le_mul_of_nonneg_left hpow hH₀.le
    _ < H₀ * c := mul_lt_mul_of_pos_left hlt hH₀
    _ = H₀⁻¹ * (8 : ℝ) ^ (-β₀) := hHc

/-! ### Exit barrier and local competitor from the references -/

theorem annK_subset_annCl : annK d ⊆ annCl (0 : Rd d) (5 / 8) (3 / 2) := by
  intro x hx
  rw [mem_annK_iff] at hx
  simp only [annCl, mem_ofPred_eq, sub_zero]
  constructor <;> linarith [hx.1, hx.2]

/-- `B̄_{1/8}(u) ⊆ annCl 0 (5/8) (3/2)` for `u ∈ K`. -/
theorem closedBall_eighth_subset_annCl {u : Rd d} (hu : u ∈ annK d) :
    closedBall u (1 / 8) ⊆ annCl (0 : Rd d) (5 / 8) (3 / 2) := by
  intro w hw
  rw [mem_annK_iff] at hu
  rw [mem_closedBall, dist_eq_norm] at hw
  have h1 : ‖u‖ - ‖w - u‖ ≤ ‖w‖ := by
    have := norm_sub_norm_le u (u - w)
    rw [sub_sub_cancel, norm_sub_rev u w] at this
    linarith
  have h2 : ‖w‖ ≤ ‖u‖ + ‖w - u‖ := by
    have := norm_add_le u (w - u)
    rwa [add_sub_cancel] at this
  simp only [annCl, mem_ofPred_eq, sub_zero]
  constructor <;> linarith [hu.1, hu.2]

/-- `B̄_{1/8}(u) ⊆ A` for `u ∈ K`. -/
theorem closedBall_eighth_subset_annA {u : Rd d} (hu : u ∈ annK d) :
    closedBall u (1 / 8) ⊆ annA d := by
  intro w hw
  have h := closedBall_eighth_subset_annCl hu hw
  simp only [annCl, mem_ofPred_eq, sub_zero] at h
  rw [mem_annA_iff]
  constructor <;> linarith [h.1, h.2]

theorem annCl_subset_annA : annCl (0 : Rd d) (5 / 8) (3 / 2) ⊆ annA d := by
  intro x hx
  simp only [annCl, mem_ofPred_eq, sub_zero] at hx
  rw [mem_annA_iff]
  constructor <;> linarith [hx.1, hx.2]

theorem sphere_subset_annK {r : ℝ} (hr : r ∈ Icc (3 / 4 : ℝ) 1) :
    sphere (0 : Rd d) r ⊆ annK d := by
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  rw [mem_annK_iff, hx]
  exact hr

/-- `setDistIn` only sees the internal metric on pairs of `S × T`. -/
theorem setDistIn_congr_internal {G G' : ContMetric d} {V S T : Set (Rd d)}
    (heq : ∀ z ∈ S, ∀ w ∈ T, G'.internal V z w = G.internal V z w) :
    setDistIn G' V S T = setDistIn G V S T := by
  unfold setDistIn
  exact iInf_congr fun z => iInf_congr fun hz => iInf_congr fun w => iInf_congr fun hw =>
    heq z hz w hw

/-- `diamIn` only sees the internal metric on pairs of `S × S`. -/
theorem diamIn_congr_internal {G G' : ContMetric d} {V S : Set (Rd d)}
    (heq : ∀ z ∈ S, ∀ w ∈ S, G'.internal V z w = G.internal V z w) :
    diamIn G' V S = diamIn G V S := by
  unfold diamIn
  exact iSup_congr fun z => iSup_congr fun hz => iSup_congr fun w => iSup_congr fun hw =>
    heq z hz w hw

namespace LocalRefs

variable {G : ContMetric d} {H₀ σ₀ β₀ m M : ℝ}

/-- The references depend only on the `A`-internal profile of the metric. -/
theorem of_internal_eq {G' : ContMetric d} (hR : LocalRefs G H₀ σ₀ β₀ m M)
    (heq : ∀ z ∈ annA d, ∀ w ∈ annA d, G'.internal (annA d) z w = G.internal (annA d) z w) :
    LocalRefs G' H₀ σ₀ β₀ m M := by
  have hK : ∀ z ∈ annK d, z ∈ annA d := fun z hz => annK_subset_annA hz
  have h34 : sphere (0 : Rd d) (3 / 4) ⊆ annK d := sphere_subset_annK ⟨le_rfl, by norm_num⟩
  have h1 : sphere (0 : Rd d) 1 ⊆ annK d := sphere_subset_annK ⟨by norm_num, le_rfl⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy hxy => ?_, ?_, ?_, ?_⟩
  · rw [heq x (annCl_subset_annA hx) y (annCl_subset_annA hy)]
    exact hR.lower x hx y hy
  · rw [heq x (annCl_subset_annA hx) y (annCl_subset_annA hy)]
    exact hR.upper x hx y hy hxy
  · rw [setDistIn_congr_internal fun z hz w hw => heq z (hK z (h34 hz)) w (hK w (h1 hw))]
    exact hR.cross
  · rw [diamIn_congr_internal fun z hz w hw => heq z (hK z (h1 hz)) w (hK w (h1 hw))]
    exact hR.diam
  · rw [diamIn_congr_internal fun z hz w hw => heq z (hK z hz) w (hK w hw)]
    exact hR.diamK

/-- The exit barrier of the references: `G(u, w; A) ≥ H₀⁻¹ 8^{-β₀}` for `u ∈ K`, `|w - u| = 1/8`
(lower reference; both points lie in `annCl 0 (5/8) (3/2)`). -/
theorem exit_barrier (hR : LocalRefs G H₀ σ₀ β₀ m M) {u w : Rd d} (hu : u ∈ annK d)
    (hw : ‖w - u‖ = 1 / 8) :
    ENNReal.ofReal (H₀⁻¹ * (8 : ℝ) ^ (-β₀)) ≤ G.internal (annA d) u w := by
  have hwmem : w ∈ annCl (0 : Rd d) (5 / 8) (3 / 2) :=
    closedBall_eighth_subset_annCl hu (by rw [mem_closedBall, dist_eq_norm, hw])
  have h := hR.lower u (annK_subset_annCl hu) w hwmem
  have hnorm : ‖u - w‖ ^ β₀ = (8 : ℝ) ^ (-β₀) := by
    rw [norm_sub_rev, hw, one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  rwa [hnorm] at h

/-- The local competitor of the references: `G(u, v; A) < H₀⁻¹ 8^{-β₀}` for `u, v ∈ K` with
`|u - v| ≤ δ₀` (upper reference at close points and `subdivDelta0_spec`). -/
theorem local_competitor (hR : LocalRefs G H₀ σ₀ β₀ m M) (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀)
    {u v : Rd d} (hu : u ∈ annK d) (hv : v ∈ annK d) (huv : ‖u - v‖ ≤ subdivDelta0 H₀ σ₀ β₀) :
    G.internal (annA d) u v < ENNReal.ofReal (H₀⁻¹ * (8 : ℝ) ^ (-β₀)) := by
  have hup := hR.upper u (annK_subset_annCl hu) v (annK_subset_annCl hv)
    (huv.trans (subdivDelta0_le H₀ σ₀ β₀))
  have hpos : 0 < H₀⁻¹ * (8 : ℝ) ^ (-β₀) :=
    mul_pos (inv_pos.2 hH₀) (Real.rpow_pos_of_pos (by norm_num) _)
  refine hup.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hpos).2 ?_)
  calc H₀ * ‖u - v‖ ^ σ₀ ≤ H₀ * subdivDelta0 H₀ σ₀ β₀ ^ σ₀ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) huv hσ₀.le) hH₀.le
    _ < H₀⁻¹ * (8 : ℝ) ^ (-β₀) := subdivDelta0_spec hH₀ hσ₀

end LocalRefs

/-! ### (2.12) on the references -/

/-- **(2.12) on the references** (Lemma `a:lem-refs-212`; NA1 R3): if `G` is a continuous length
metric with `LocalRefs G (H₀, σ₀, β₀, m, M)`, then `G(u, v; A) = G(u, v)` for `u, v ∈ K` with
`|u - v| ≤ δ₀ = subdivDelta0 H₀ σ₀ β₀`. -/
theorem refs_internal_eq_global {G : ContMetric d} (hG : G.IsLength) {H₀ σ₀ β₀ m M : ℝ}
    (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hR : LocalRefs G H₀ σ₀ β₀ m M) :
    ∀ u ∈ annK d, ∀ v ∈ annK d, ‖u - v‖ ≤ subdivDelta0 H₀ σ₀ β₀ →
      G.internal (annA d) u v = ENNReal.ofReal (G.1 (u, v)) :=
  internal_eq_global G hG (δ₁ := 1 / 8) (by norm_num)
    (fun _ hu => closedBall_eighth_subset_annA hu) (fun _ hu _ hw => hR.exit_barrier hu hw)
    (fun _ hu _ hv huv => hR.local_competitor hH₀ hσ₀ hu hv huv)

/-- **(2.12) on the references, every exterior extension** (Lemma `a:lem-refs-212`, last
clause): if `G` satisfies `LocalRefs` and `G'` is a continuous length metric with the same internal
metric on `A`, then `G(u, v; A) = G'(u, v)` for `u, v ∈ K` with `|u - v| ≤ δ₀`. -/
theorem refs_internal_eq_global_of_internal_eq {G G' : ContMetric d} (hG' : G'.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hR : LocalRefs G H₀ σ₀ β₀ m M)
    (heq : ∀ z ∈ annA d, ∀ w ∈ annA d, G'.internal (annA d) z w = G.internal (annA d) z w) :
    ∀ u ∈ annK d, ∀ v ∈ annK d, ‖u - v‖ ≤ subdivDelta0 H₀ σ₀ β₀ →
      G.internal (annA d) u v = ENNReal.ofReal (G'.1 (u, v)) :=
  internal_eq_global_of_internal_eq G G' hG' (δ₁ := 1 / 8) (by norm_num)
    (fun _ hu => closedBall_eighth_subset_annA hu) (fun _ hu _ hw => hR.exit_barrier hu hw)
    (fun _ hu _ hv huv => hR.local_competitor hH₀ hσ₀ hu hv huv) heq

end HigherDimLQGContinuity
