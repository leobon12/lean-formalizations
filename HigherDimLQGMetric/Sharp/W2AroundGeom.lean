import HigherDimLQGMetric.Sharp.W2SpherePath
import HigherDimLQGMetric.Sharp.W2Det

/-! Geometry of annulus crossings for the upper around-distance estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A crossing meets every intermediate sphere at an interior parameter. -/
theorem w2_crossing_hits_sphere {z : Rd d} {a b m : ℝ}
    {P : ℝ → Rd d} (hP : IsShellCrossing z a b P)
    (ham : a < m) (hmb : m < b) :
    ∃ t ∈ Ioo (0 : ℝ) 1, P t ∈ sphere z m := by
  have hcont : ContinuousOn (fun t => ‖P t - z‖) (Icc 0 1) :=
    (hP.cont.sub continuousOn_const).norm
  have hstart : ‖P 0 - z‖ = a := by
    simpa only [mem_sphere, dist_eq_norm] using hP.start
  have hfinish : ‖P 1 - z‖ = b := by
    simpa only [mem_sphere, dist_eq_norm] using hP.finish
  obtain ⟨t, ht, htm⟩ := intermediate_value_Icc zero_le_one hcont
    (show m ∈ Icc ‖P 0 - z‖ ‖P 1 - z‖ from by rw [hstart, hfinish]; exact ⟨ham.le, hmb.le⟩)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro he
    have : t = 0 := he.symm
    subst t
    change ‖P 0 - z‖ = m at htm
    rw [hstart] at htm
    exact (ne_of_lt ham) htm)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    change ‖P 1 - z‖ = m at htm
    rw [hfinish] at htm
    exact (ne_of_gt hmb) htm)
  exact ⟨t, ⟨ht0, ht1⟩, by simpa only [mem_sphere, dist_eq_norm] using htm⟩

/-- The interior image of a crossing is connected and lies in the open shell. -/
theorem w2_crossing_interior_connected {z : Rd d} {a b : ℝ}
    {P : ℝ → Rd d} (hP : IsShellCrossing z a b P) :
    IsConnected (P '' Ioo (0 : ℝ) 1) := by
  exact (isConnected_Ioo (by norm_num : (0 : ℝ) < 1)).image P
    (hP.cont.mono Ioo_subset_Icc_self)

/-- The interior of a crossing cannot fit in a ball smaller than half the shell width. -/
theorem w2_crossing_interior_not_ball {z c : Rd d} {a b ρ : ℝ}
    {P : ℝ → Rd d} (hP : IsShellCrossing z a b P)
    (hgap : 2 * ρ < b - a) :
    ¬ P '' Ioo (0 : ℝ) 1 ⊆ ball c ρ := by
  intro hsub
  have hclosed : closure (P '' Ioo (0 : ℝ) 1) ⊆ closedBall c ρ :=
    closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall
  have hPc : ContinuousOn P (closure (Ioo (0 : ℝ) 1)) := by
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hP.cont
  have hcl := hPc.image_closure
  have h0 : P 0 ∈ closedBall c ρ := hclosed (hcl ⟨0, by
    simp only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), mem_Icc]; norm_num, rfl⟩)
  have h1 : P 1 ∈ closedBall c ρ := hclosed (hcl ⟨1, by
    simp only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), mem_Icc]; norm_num, rfl⟩)
  have hdist : dist (P 0) (P 1) ≤ 2 * ρ := by
    have ht := dist_triangle (P 0) c (P 1)
    rw [mem_closedBall] at h0 h1
    rw [dist_comm (P 1) c] at h1
    linarith only [ht, h0, h1]
  have hrad : b - a ≤ dist (P 0) (P 1) := by
    have ha : ‖P 0 - z‖ = a := by simpa only [mem_sphere, dist_eq_norm] using hP.start
    have hb : ‖P 1 - z‖ = b := by simpa only [mem_sphere, dist_eq_norm] using hP.finish
    have ht := norm_sub_norm_le (P 1 - z) (P 0 - z)
    have he : (P 1 - z) - (P 0 - z) = P 1 - P 0 := by abel
    rw [he, hb, ha] at ht
    rw [dist_eq_norm, norm_sub_rev]
    linarith only [ht]
  linarith only [hdist, hrad, hgap]

/-- Uniform Lipschitz connections between points of the middle sphere, with a
uniform Euclidean margin inside the annulus. -/
theorem w2_middle_sphere_paths (hd : 3 ≤ d) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : r₁ < r₂) :
    ∃ Λ R δ : ℝ, 0 ≤ Λ ∧ 0 ≤ R ∧ 0 < δ ∧
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z x y : Rd d,
        x ∈ sphere z (((r₁ + r₂) / 2) * 𝕣) →
        y ∈ sphere z (((r₁ + r₂) / 2) * 𝕣) →
        ∃ P : ℝ → Rd d,
          LipschitzOnWith (Real.toNNReal (𝕣 * Λ)) P (Icc 0 1) ∧
          P 0 = x ∧ P 1 = y ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ‖P t - z‖ ≤ R * 𝕣) ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            ball (P t) (δ * 𝕣) ⊆ ann z (r₁ * 𝕣) (r₂ * 𝕣)) := by
  let Δ : ℝ := r₂ - r₁
  let m : ℝ := (r₁ + r₂) / 2
  let δ : ℝ := Δ / 8
  let U₀ : Set (Rd d) := ann 0 (r₁ + Δ / 4) (r₂ - Δ / 4)
  let K : Set (Rd d) := sphere 0 m
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith only [hr₂]
  have hm : 0 < m := by dsimp [m]; linarith only [hr₁, hr₂]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKcompact : IsCompact K := isCompact_sphere 0 m
  have hrank : 1 < Module.rank ℝ (Rd d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < d by omega)
  have hKconn : IsConnected K := isConnected_sphere hrank 0 hm.le
  have hKU : K ⊆ U₀ := by
    intro v hv
    have hn : ‖v‖ = m := by simpa only [K, mem_sphere, dist_zero_right] using hv
    change r₁ + Δ / 4 < ‖v - 0‖ ∧ ‖v - 0‖ < r₂ - Δ / 4
    simp only [sub_zero, hn]
    dsimp [m, Δ]
    constructor <;> linarith only [hr₂]
  obtain ⟨Λ, hΛ, hpaths⟩ := w2_uniform_lipschitz_paths hKcompact hKconn
    hKconn.nonempty (isOpen_ann _ _ _) hKU
  let R : ℝ := r₂ + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith only [hr₁, hr₂]
  refine ⟨Λ, R, δ, hΛ, hR, hδ, ?_⟩
  intro 𝕣 h𝕣 z x y hx hy
  let u : Rd d := 𝕣⁻¹ • (x - z)
  let v : Rd d := 𝕣⁻¹ • (y - z)
  have hu : u ∈ K := by
    have hxnorm : ‖x - z‖ = m * 𝕣 := by
      simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hx
    change u ∈ sphere 0 m
    rw [mem_sphere, dist_zero_right]
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h𝕣), hxnorm]
    field_simp
  have hv : v ∈ K := by
    have hynorm : ‖y - z‖ = m * 𝕣 := by
      simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hy
    change v ∈ sphere 0 m
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h𝕣), hynorm]
    field_simp
  obtain ⟨Q, hQLip, hQ0, hQ1, hQU⟩ := hpaths u hu v hv
  let P : ℝ → Rd d := fun t => z + 𝕣 • Q t
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hQLip) s hs t ht
    have hdist : dist (P s) (P t) = 𝕣 * dist (Q s) (Q t) := by
      dsimp [P]
      rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos h𝕣]
    rw [hdist, Real.coe_toNNReal _ (mul_nonneg h𝕣.le hΛ)]
    rw [Real.coe_toNNReal _ hΛ] at h
    nlinarith only [h, h𝕣]
  · dsimp [P]
    rw [hQ0]
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ h𝕣.ne', one_smul]
    abel
  · dsimp [P]
    rw [hQ1]
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ h𝕣.ne', one_smul]
    abel
  · intro t ht
    have hQt := hQU ht
    have hQhi : ‖Q t‖ < r₂ - Δ / 4 := by simpa only [sub_zero] using hQt.2
    have hscale : ‖P t - z‖ = 𝕣 * ‖Q t‖ := by
      dsimp [P]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos h𝕣]
    rw [hscale]
    have hmul := mul_lt_mul_of_pos_left hQhi h𝕣
    dsimp [R]
    nlinarith only [hmul, hΔ, h𝕣]
  · intro t ht w hw
    have hQt := hQU ht
    have hQlo : r₁ + Δ / 4 < ‖Q t‖ := by simpa only [sub_zero] using hQt.1
    have hQhi : ‖Q t‖ < r₂ - Δ / 4 := by simpa only [sub_zero] using hQt.2
    have hscale : ‖P t - z‖ = 𝕣 * ‖Q t‖ := by
      dsimp [P]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos h𝕣]
    have hlo := mul_lt_mul_of_pos_left hQlo h𝕣
    have hhi := mul_lt_mul_of_pos_left hQhi h𝕣
    have hwd : ‖w - P t‖ < δ * 𝕣 := by
      simpa only [mem_ball, dist_eq_norm] using hw
    have htri₁ : ‖P t - z‖ ≤ ‖w - z‖ + ‖w - P t‖ := by
      have he : P t - z = (P t - w) + (w - z) := by abel
      rw [he]
      have hh := norm_add_le (P t - w) (w - z)
      simpa only [norm_sub_rev, add_comm] using hh
    have htri₂ : ‖w - z‖ ≤ ‖P t - z‖ + ‖w - P t‖ := by
      have he : w - z = (w - P t) + (P t - z) := by abel
      rw [he]
      simpa only [add_comm] using norm_add_le (w - P t) (P t - z)
    change r₁ * 𝕣 < ‖w - z‖ ∧ ‖w - z‖ < r₂ * 𝕣
    dsimp [δ] at hwd
    rw [hscale] at htri₁ htri₂
    constructor <;> nlinarith only [hlo, hhi, hwd, htri₁, htri₂, hΔ, h𝕣]

end HigherDimLQGMetric
