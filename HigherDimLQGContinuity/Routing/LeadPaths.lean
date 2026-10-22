import HigherDimLQGContinuity.Routing.LeadsDefs
import HigherDimLQGContinuity.Routing.ArcModuli

/-!
# The polygonal path of one lead (before the moves)

Packet Q2 (ruling N9). Sources: planning audit `planning/audits/NA2-section-4.md`, Details (c)
**R1′**, **R3**; blueprint Part B, Lemma `b:lem-leads`, proof, paragraph "Paths".

`exists_prelead`: in the box `R = m + [-L, L]^d` (`⊆ B̄₄`), for an arc `η` with moduli `(2A, α, β)`
inside `B̄(m, L/32)` (the truncated favorable arc) and an endpoint `g ∈ B̄(m, L/32)` at distance
`≥ U` from `η` (`0 < U ≤ L/8`), there is a sequence `q 0 = m - L u` (the port), `q 1 = m - ¾L u`
(the port moved inward), …, `q (k+1) = g`, with `1 ≤ k ≤ C_pol U^{-d/(αβ)²}` (Lemma 4.1′,
polygonal form, `lemma41_polygonal_explicit` of packet Q1 in `Ω = int R`, `b₀ = L/2`, `R₀ = 4`),
all vertices in `R` (those after the port in `int R`), and every segment at distance
`≥ c₄₁′ U^{1/(αβ)²}` from `η` (the first segment `[q 0, q 1]` stays at distance `≥ 3L/4` from `m`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGContinuity.Topology (ArcModuli polygonalClearanceConst polygonalConst
  lemma41_polygonal_explicit)

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-- The points of the segment from the port `m - L u` to `m - ¾L u` stay at distance `≥ ¾L` from
`m` (`|u| = 1`). -/
lemma norm_sub_ge_of_mem_portSegment {m u x : Rd d} {L : ℝ} (hL : 0 ≤ L) (hu : ‖u‖ = 1)
    (hx : x ∈ segment ℝ (m - L • u) (m - (3 / 4 * L) • u)) : 3 / 4 * L ≤ ‖x - m‖ := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  have he : s • (m - L • u) + t • (m - (3 / 4 * L) • u) - m = (-(s * L + t * (3 / 4 * L))) • u := by
    obtain rfl : t = 1 - s := by linarith
    module
  rw [he, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity)]
  nlinarith

/-- **The polygonal path of one lead** (before the moves; blueprint `b:lem-leads`, "Paths"). -/
theorem exists_prelead (hd : 3 ≤ d) {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) {m : Rd d} {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (hbox : resBox m L ⊆ closedBall 0 4) {u : Rd d} (hu : ‖u‖ = 1) {η : ℝ → Rd d}
    (hη : ArcModuli η (2 * A) α β) (hηm : ∀ ς ∈ Icc (0 : ℝ) 1, η ς ∈ closedBall m (L / 32))
    {g : Rd d} (hg : g ∈ closedBall m (L / 32)) {U : ℝ} (hU : 0 < U) (hUL : U ≤ L / 8)
    (hgη : ∀ ς ∈ Icc (0 : ℝ) 1, U ≤ dist g (η ς)) :
    ∃ (k : ℕ) (q : ℕ → Rd d), q 0 = m - L • u ∧ q 1 = m - (3 / 4 * L) • u ∧ q (k + 1) = g ∧
      1 ≤ k ∧ (k : ℝ) ≤ polygonalConst d (2 * A) α β 4 * U ^ (-((d : ℝ) / (α * β) ^ 2)) ∧
      (∀ j ≤ k + 1, q j ∈ resBox m L) ∧ (∀ j, 1 ≤ j → j ≤ k + 1 → q j ∈ resBoxInt m L) ∧
      (∀ j < k + 1, ∀ x ∈ segment ℝ (q j) (q (j + 1)), ∀ ς ∈ Icc (0 : ℝ) 1,
        polygonalClearanceConst (2 * A) α β * U ^ ((α * β) ^ 2)⁻¹ ≤ dist x (η ς)) := by
  set Ω := resBoxInt m L with hΩdef
  have hΩ : IsOpen Ω := isOpen_resBoxInt m L
  have hΩc : Convex ℝ Ω := convex_resBoxInt m L
  have hΩR : Ω ⊆ closedBall 0 4 := (resBoxInt_subset_resBox m L).trans hbox
  have hA2 : (1 : ℝ) ≤ 2 * A := by linarith
  have hU1 : U ≤ 1 := by linarith
  -- the clearance constant is small
  set c := polygonalClearanceConst (2 * A) α β with hc
  have hc0 : 0 < c := Topology.polygonalClearanceConst_pos (by linarith)
  have hc1 : c ≤ 1 / 2 := polygonalClearanceConst_le_half hA2 hα hβ
  have hp := inv_sq_ge_one hα hα1 hβ hβ1
  have hUp : U ^ ((α * β) ^ 2)⁻¹ ≤ U := by
    have := Real.rpow_le_rpow_of_exponent_ge hU hU1 hp
    rwa [Real.rpow_one] at this
  have hUp0 : 0 ≤ U ^ ((α * β) ^ 2)⁻¹ := Real.rpow_nonneg hU.le _
  have hcU : c * U ^ ((α * β) ^ 2)⁻¹ ≤ L / 16 := by nlinarith
  -- hypotheses of Lemma 4.1′
  have hγΩ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (η t) (L / 2) ⊆ Ω := by
    intro t ht y hy
    apply mem_resBoxInt_of_norm_lt
    have h1 : ‖y - η t‖ ≤ L / 2 := by rw [← dist_eq_norm]; exact hy
    have h2 : ‖η t - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hηm t ht
    calc ‖y - m‖ = ‖(y - η t) + (η t - m)‖ := by congr 1; abel
      _ ≤ ‖y - η t‖ + ‖η t - m‖ := norm_add_le _ _
      _ < L := by linarith
  set x := m - (3 / 4 * L) • u with hx
  have hxm : ‖x - m‖ = 3 / 4 * L := by
    rw [hx, sub_sub_cancel_left, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hxΩ : closedBall x U ⊆ Ω := by
    intro y hy k
    have h1 : |y k - x k| ≤ U := (abs_coord_sub_le_norm y x k).trans (by
      rw [← dist_eq_norm]; exact hy)
    have h2 : |x k - m k| ≤ 3 / 4 * L := (abs_coord_sub_le_norm x m k).trans hxm.le
    have h3 : |y k - m k| ≤ |y k - x k| + |x k - m k| := by
      have := abs_add_le (y k - x k) (x k - m k)
      rwa [sub_add_sub_cancel] at this
    linarith
  have hgm : ‖g - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hg
  have hgΩ : closedBall g U ⊆ Ω := by
    intro y hy
    apply mem_resBoxInt_of_norm_lt
    have h1 : ‖y - g‖ ≤ U := by rw [← dist_eq_norm]; exact hy
    calc ‖y - m‖ = ‖(y - g) + (g - m)‖ := by congr 1; abel
      _ ≤ ‖y - g‖ + ‖g - m‖ := norm_add_le _ _
      _ < L := by linarith
  have hxu : ∀ t ∈ Icc (0 : ℝ) 1, U ≤ dist x (η t) := by
    intro t ht
    have h2 : ‖η t - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hηm t ht
    have : ‖x - m‖ ≤ ‖x - η t‖ + ‖η t - m‖ := by
      calc ‖x - m‖ = ‖(x - η t) + (η t - m)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [dist_eq_norm]
    linarith
  obtain ⟨n, z, hz0, hzn, hn, hseg⟩ := lemma41_polygonal_explicit hd hA2 hα hα1 hβ hβ1
    (by norm_num : (0 : ℝ) < 4) hη hΩ hΩc hΩR (b₀ := L / 2) hγΩ hU hU1 (by linarith) hxΩ hgΩ
    hxu hgη
  -- the vertices of `z` lie in `Ω`
  have hzΩ : ∀ i ≤ n, z i ∈ Ω := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact (hseg i h (z i) (left_mem_segment _ _ _)).1
    · have hin : i = n := le_antisymm hi h
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exfalso
          have : x = g := by rw [← hz0, ← hzn, h0]
          rw [this] at hxm
          linarith
        · exact h0
      have := (hseg (n - 1) (by omega) (z (n - 1 + 1)) (right_mem_segment _ _ _)).1
      rwa [Nat.sub_add_cancel hn0, ← hin] at this
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      have : x = g := by rw [← hz0, ← hzn, h0]
      rw [this] at hxm
      linarith
    · exact h0
  -- the sequence with the port prepended
  let q : ℕ → Rd d := fun j => if j = 0 then m - L • u else z (j - 1)
  have hq0 : q 0 = m - L • u := by simp [q]
  have hqs : ∀ j, q (j + 1) = z j := fun j => by simp [q]
  have hport : m - L • u ∈ resBox m L := by
    intro k
    have : (m - L • u) k - m k = -(L * u k) := by simp
    rw [this, abs_neg, abs_mul, abs_of_pos hL]
    have : |u k| ≤ 1 := by
      have := abs_coord_sub_le_norm u 0 k
      simpa [hu] using this
    nlinarith
  refine ⟨n, q, hq0, by rw [hqs, hz0], by rw [hqs, hzn], hn1, hn, fun j hj => ?_,
    fun j hj1 hj => ?_, fun j hj w hw t ht => ?_⟩
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hq0]; exact hport
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hqs]
      exact resBoxInt_subset_resBox m L (hzΩ i (by omega))
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hqs]
    exact hzΩ i (by omega)
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · -- the first segment `[m - L u, m - ¾L u]`
      rw [h0, hq0, zero_add, hqs, hz0] at hw
      have h1 := norm_sub_ge_of_mem_portSegment hL.le hu hw
      have h2 : ‖η t - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hηm t ht
      have : ‖w - m‖ ≤ ‖w - η t‖ + ‖η t - m‖ := by
        calc ‖w - m‖ = ‖(w - η t) + (η t - m)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm]
      linarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hqs, hqs] at hw
      exact (hseg i (by omega) w hw).2 t ht

end HigherDimLQGContinuity.Routing

end
