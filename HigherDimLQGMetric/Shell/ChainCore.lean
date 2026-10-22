import HigherDimLQGMetric.Shell.Geom

/-!
# Backward search for overlapping spheres

Port of `LQGMetric.LM.chain_back` and `chain_main` from circles to spheres in `Rd d`.
The target cost takes values in `ℝ≥0∞` so it also applies to internal distances.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Backward search: an exit point lying inside a later ball either gives an intersecting
earlier sphere, or the first path point lies inside the later ball. -/
theorem sphere_chain_back (hd : 2 ≤ d) (p w : ℕ → Rd d) (r : ℕ → ℝ) (J : ℕ)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i < J → ‖p i - w i‖ = r i)
    (hr : ∀ i, 0 < r i) (j : ℕ) (hj : j ≤ J) :
    ∀ i, i < j → ‖p i - w j‖ < r j →
      (∃ i', 1 ≤ i' ∧ i' ≤ i ∧
        (sphere (w i') (r i') ∩ sphere (w j) (r j)).Nonempty) ∨
        ‖p 0 - w j‖ < r j := by
  intro i
  induction i with
  | zero => intro _ h; exact Or.inr h
  | succ i ih =>
    intro hij hpi
    by_cases hmeet : (sphere (w (i + 1)) (r (i + 1)) ∩ sphere (w j) (r j)).Nonempty
    · exact Or.inl ⟨i + 1, le_add_self, le_rfl, hmeet⟩
    · have hsub : closedBall (w (i + 1)) (r (i + 1)) ⊆ ball (w j) (r j) := by
        apply closedBall_subset_ball_of_sphere_no_inter hd (hr _).le
          (x := p (i + 1))
        · rw [mem_sphere, dist_eq_norm]
          exact hon _ le_add_self (by omega)
        · rwa [mem_ball, dist_eq_norm]
        · exact hmeet
      have hpi' : ‖p i - w j‖ < r j := by
        have h1 := hin (i + 1) le_add_self (by omega)
        simp only [Nat.add_sub_cancel] at h1
        have hp : p i ∈ closedBall (w (i + 1)) (r (i + 1)) := by
          rw [mem_closedBall, dist_eq_norm]
          linarith [hr (i + 1)]
        have := hsub hp
        rwa [mem_ball, dist_eq_norm] at this
      rcases ih (by omega) hpi' with ⟨i', h1, h2, h3⟩ | h
      · exact Or.inl ⟨i', h1, by omega, h3⟩
      · exact Or.inr h

/-- Time-increment chaining estimate for any directed extended distance satisfying the
diagonal and triangle laws. -/
theorem sphere_chain_main (hd : 2 ≤ d) (δ : Rd d → Rd d → ℝ≥0∞)
    (hδ0 : ∀ x, δ x x = 0) (hδt : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (C : ℝ≥0∞) {ε : ℝ} (p w : ℕ → Rd d) (r T : ℕ → ℝ) (J : ℕ)
    (hT : Monotone T)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i < J → ‖p i - w i‖ = r i)
    (hr : ∀ i, 0 < r i) (hrε : ∀ i, r i ≤ ε)
    (hdiam : ∀ i, 1 ≤ i → i < J → ∀ u ∈ sphere (w i) (r i),
      ∀ v ∈ sphere (w i) (r i),
      δ u v ≤ C * ENNReal.ofReal (T i - T (i - 1))) :
    ∀ j, 1 ≤ j → j < J → ∀ u ∈ sphere (w j) (r j),
      ∃ x, ‖x - p 0‖ ≤ 2 * ε ∧ δ x u ≤ C * ENNReal.ofReal (T j - T 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjJ u hu
    have hpj : ‖p (j - 1) - w j‖ < r j := by linarith [hin j hj1 (by omega), hr j]
    rcases sphere_chain_back hd p w r J hin hon hr j (by omega) (j - 1) (by omega) hpj with
      ⟨i', h1, h2, y, hy1, hy2⟩ | h0
    · obtain ⟨x, hx, hxy⟩ := ih i' (by omega) h1 (by omega) y hy1
      refine ⟨x, hx, ?_⟩
      have hyu := hdiam j hj1 hjJ y hy2 u hu
      have hmono : T i' ≤ T (j - 1) := hT (by omega)
      have hnonneg : 0 ≤ T i' - T 0 := sub_nonneg.mpr (hT (by omega))
      have hnonneg' : 0 ≤ T j - T (j - 1) := sub_nonneg.mpr (hT (by omega))
      calc
        δ x u ≤ δ x y + δ y u := hδt x y u
        _ ≤ C * ENNReal.ofReal (T i' - T 0) +
            C * ENNReal.ofReal (T j - T (j - 1)) := add_le_add hxy hyu
        _ = C * (ENNReal.ofReal (T i' - T 0) +
            ENNReal.ofReal (T j - T (j - 1))) := (mul_add ..).symm
        _ ≤ C * ENNReal.ofReal (T j - T 0) := by
          gcongr
          rw [← ENNReal.ofReal_add hnonneg hnonneg']
          apply ENNReal.ofReal_le_ofReal
          linarith
    · refine ⟨u, ?_, ?_⟩
      · have hu' : ‖u - w j‖ = r j := by rw [mem_sphere, dist_eq_norm] at hu; exact hu
        calc
          ‖u - p 0‖ = ‖(u - w j) - (p 0 - w j)‖ := by congr 1; abel
          _ ≤ ‖u - w j‖ + ‖p 0 - w j‖ := norm_sub_le _ _
          _ ≤ 2 * ε := by linarith [hrε j]
      · rw [hδ0]
        exact bot_le

/-- Counting variant of the backward search: a connected first set supplies a point
on the first sphere reached by the backward search. -/
theorem sphere_chain_main_set (hd : 2 ≤ d) (δ : Rd d → Rd d → ℝ≥0∞)
    (hδt : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (M : ℝ≥0∞) {ε : ℝ} (p w : ℕ → Rd d) (r : ℕ → ℝ) (J : ℕ)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i < J → ‖p i - w i‖ = r i)
    (hr : ∀ i, 0 < r i) (hrε : ∀ i, r i ≤ ε)
    (hdiam : ∀ i, 1 ≤ i → i ≤ J → ∀ u ∈ sphere (w i) (r i),
      ∀ v ∈ sphere (w i) (r i), δ u v ≤ M)
    {K : Set (Rd d)} (hK : IsConnected K) (hp : p 0 ∈ K)
    (hKb : ∀ c : Rd d, ¬ K ⊆ ball c ε) :
    ∀ j, 1 ≤ j → j ≤ J → ∀ u ∈ sphere (w j) (r j),
      ∃ x ∈ K, δ x u ≤ (j : ℝ≥0∞) * M := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjJ u hu
    have hpj : ‖p (j - 1) - w j‖ < r j := by linarith [hin j hj1 hjJ, hr j]
    rcases sphere_chain_back hd p w r J hin hon hr j hjJ (j - 1) (by omega) hpj with
      ⟨i', h1, h2, y, hy1, hy2⟩ | h0
    · obtain ⟨x, hxK, hxy⟩ := ih i' (by omega) h1 (by omega) y hy1
      refine ⟨x, hxK, ?_⟩
      calc
        δ x u ≤ δ x y + δ y u := hδt x y u
        _ ≤ (i' : ℝ≥0∞) * M + M := add_le_add hxy (hdiam j hj1 hjJ y hy2 u hu)
        _ = ((i' + 1 : ℕ) : ℝ≥0∞) * M := by simp [Nat.cast_add, add_mul]
        _ ≤ (j : ℝ≥0∞) * M := by gcongr; exact_mod_cast Nat.succ_le_of_lt (by omega : i' < j)
    · have hout : ¬ K ⊆ ball (w j) (r j) := by
        intro hs
        exact hKb (w j) (hs.trans (ball_subset_ball (hrε j)))
      obtain ⟨x, hxK, hxS⟩ := connected_inter_sphere K hK
        ⟨p 0, hp, by rwa [mem_ball, dist_eq_norm]⟩ hout
      refine ⟨x, hxK, ?_⟩
      calc
        δ x u ≤ M := hdiam j hj1 hjJ x hxS u hu
        _ = (1 : ℝ≥0∞) * M := (one_mul M).symm
        _ ≤ (j : ℝ≥0∞) * M := by gcongr; exact_mod_cast hj1

end HigherDimLQGMetric
