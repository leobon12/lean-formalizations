import HigherDimLQGMetric.Shell.Chain
import HigherDimLQGMetric.Sharp.W2Events
import HigherDimLQGMetric.Sharp.GridNear

/-!
# Deterministic sphere chain for internal distances

`ContMetric.internal U` is infinite on the diagonal outside `U`. We zero its
unusable diagonal values before applying W0's abstract chain theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Internal distance with a globally zero diagonal. -/
def w2InternalZeroed (D : ContMetric d) (U : Set (Rd d)) (x y : Rd d) : ℝ≥0∞ :=
  if x = y then 0 else D.internal U x y

theorem w2InternalZeroed_self (D : ContMetric d) (U : Set (Rd d)) (x : Rd d) :
    w2InternalZeroed D U x x = 0 := by simp only [w2InternalZeroed, ↓reduceIte]

theorem w2InternalZeroed_triangle (D : ContMetric d) (U : Set (Rd d))
    (x y z : Rd d) :
    w2InternalZeroed D U x z ≤ w2InternalZeroed D U x y + w2InternalZeroed D U y z := by
  by_cases hxz : x = z
  · subst z
    simp only [w2InternalZeroed, ↓reduceIte]
    exact bot_le
  by_cases hxy : x = y
  · subst y
    simp only [w2InternalZeroed, ↓reduceIte, hxz, zero_add, le_refl]
  by_cases hyz : y = z
  · subst z
    simp only [w2InternalZeroed, ↓reduceIte, hxy, add_zero, le_refl]
  simpa only [w2InternalZeroed, hxz, hxy, hyz, ite_false] using D.internal_triangle U x y z

theorem w2InternalZeroed_eq_internal (D : ContMetric d) (U : Set (Rd d))
    {x y : Rd d} (hx : x ∈ U) : w2InternalZeroed D U x y = D.internal U x y := by
  by_cases hxy : x = y
  · subst y
    rw [w2InternalZeroed_self, D.internal_self hx]
  · simp only [w2InternalZeroed, hxy, ite_false]

/-- W0's sphere chain applied to an internal distance. The endpoint membership
restores the original internal metric after the chain. -/
theorem w2_chain_setDist (hd : 2 ≤ d) (D : ContMetric d) (U : Set (Rd d))
    {ρ ε Λ : ℝ} (hρ : 0 < ρ) (hΛ : 0 ≤ Λ)
    (P : ℝ → Rd d) (hP : LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1))
    (good : Rd d → ℝ → Prop)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r,
      ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r)
    (M : ℝ≥0∞)
    (hM : ∀ w r, good w r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      D.internal U u v ≤ M)
    {K₁ K₂ : Set (Rd d)} (hK₁ : IsConnected K₁) (hK₂ : IsConnected K₂)
    (h₀ : P 0 ∈ K₁) (h₁ : P 1 ∈ K₂)
    (hK₁U : K₁ ⊆ U)
    (hK₁b : ∀ c : Rd d, ¬ K₁ ⊆ ball c ε)
    (hK₂b : ∀ c : Rd d, ¬ K₂ ⊆ ball c ε) :
    setDistIn D U K₁ K₂ ≤ ENNReal.ofReal (2 * Λ / ρ + 2) * M := by
  have hMz : ∀ w r, good w r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      w2InternalZeroed D U u v ≤ M := by
    intro w r hw u hu v hv
    by_cases huv : u = v
    · simp only [huv, w2InternalZeroed_self]
      exact bot_le
    · simpa only [w2InternalZeroed, huv, ite_false] using hM w r hw u hu v hv
  obtain ⟨x, hx, y, hy, hxy⟩ := chain_setDist hd (w2InternalZeroed D U)
    (w2InternalZeroed_self D U) (w2InternalZeroed_triangle D U)
    hρ hΛ P hP good hcov M hMz hK₁ hK₂ h₀ h₁ hK₁b hK₂b
  calc
    setDistIn D U K₁ K₂ ≤ D.internal U x y :=
      iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y (iInf_le_of_le hy le_rfl)))
    _ = w2InternalZeroed D U x y := (w2InternalZeroed_eq_internal D U (hK₁U hx)).symm
    _ ≤ ENNReal.ofReal (2 * Λ / ρ + 2) * M := hxy

/-- A good sphere controls its internal distance in every containing domain. -/
theorem w2_internal_le_sphereDiam (D : ContMetric d) (U : Set (Rd d))
    (w : Rd d) (r : ℝ) (hU : ann w (r / 2) (2 * r) ⊆ U)
    {u v : Rd d} (hu : u ∈ sphere w r) (hv : v ∈ sphere w r) :
    D.internal U u v ≤ sphereDiam D w r := by
  calc
    D.internal U u v ≤ D.internal (ann w (r / 2) (2 * r)) u v := D.internal_anti hU u v
    _ ≤ sphereDiam D w r :=
      le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))

/-- The W1 lattice covers a bounded path after translation and dilation. -/
theorem w2_path_cover_grid (hd : 3 ≤ d) (P : ℝ → Rd d) (z : Rd d)
    {𝕣 R ε : ℝ} (h𝕣 : 0 < 𝕣) (hR : 0 ≤ R)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - z‖ ≤ R * 𝕣)
    (hε : 0 < ε) (hε1 : ε < 1) (hεR : ε < 1 / (R + 2))
    (good : Rd d → ℝ → Prop)
    (hgrid : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
      ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
      good (z + w) (𝕣 / 2 ^ k)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ w r,
      ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧ ‖P t - w‖ < r / 2 ∧ good w r := by
  intro t ht
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < ε ^ 2 * 𝕣 / (10 * d) := by positivity
  obtain ⟨w, hwGrid, hwNear⟩ :=
    exists_gridPt_near hs (P t - z)
  have hnear : ‖(P t - z) - w‖ ≤ ε ^ 2 * 𝕣 / 10 := by
    have he : (d : ℝ) * (ε ^ 2 * 𝕣 / (10 * d)) = ε ^ 2 * 𝕣 / 10 := by
      field_simp
    rw [he] at hwNear
    exact hwNear
  have hwNorm : ‖w‖ ≤ R * 𝕣 + ε ^ 2 * 𝕣 / 10 := by
    have htri : ‖w‖ ≤ ‖P t - z‖ + ‖(P t - z) - w‖ := by
      calc
        ‖w‖ = ‖(P t - z) - ((P t - z) - w)‖ := by congr 1; abel
        _ ≤ ‖P t - z‖ + ‖(P t - z) - w‖ := norm_sub_le _ _
    linarith only [htri, hP t ht, hnear]
  have hRinv : (R + 1) * 𝕣 < 𝕣 / ε := by
    have hprod : ε * (R + 2) < 1 := by
      have h := (lt_div_iff₀ (by linarith : 0 < R + 2)).1 hεR
      nlinarith only [h]
    apply (lt_div_iff₀ hε).2
    have hdelta : 0 < 1 - ε * (R + 1) := by nlinarith only [hprod, hε]
    have hm := mul_pos h𝕣 hdelta
    nlinarith only [hm]
  have hwBall : w ∈ ball (0 : Rd d) (𝕣 / ε) := by
    rw [mem_ball, dist_zero_right]
    have hsmall : ε ^ 2 * 𝕣 / 10 < 𝕣 := by
      have hdelta : 0 < 1 - ε ^ 2 / 10 := by nlinarith only [hε, hε1]
      have hm := mul_pos h𝕣 hdelta
      nlinarith only [hm]
    linarith only [hwNorm, hRinv, hsmall]
  obtain ⟨k, hlow, hupp, hgood⟩ := hgrid w ⟨hwGrid, hwBall⟩
  refine ⟨z + w, 𝕣 / 2 ^ k, hlow, hupp, ?_, hgood⟩
  have he : P t - (z + w) = (P t - z) - w := by abel
  rw [he]
  have hsmall : ε ^ 2 * 𝕣 / 10 < (𝕣 / 2 ^ k : ℝ) / 2 := by
    linarith only [hlow, mul_pos (sq_pos_of_pos hε) h𝕣]
  exact hnear.trans_lt hsmall

/-- A good sphere and a sphere-average bound give a uniform diameter bound. -/
theorem w2_goodSphere_field_le {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    (D : DistRd d → ContMetric d) (g : DistRd d)
    {𝕣 ε r C M : ℝ} (h𝕣 : 0 < 𝕣) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (hrhi : r ≤ ε * 𝕣) (hC : 0 ≤ C)
    (z w : Rd d)
    (hgood : sphereDiam (D g) w r ≤ ENNReal.ofReal (C * sNorm ξ Q g r w))
    (hfield : |sphereAvg g r w - sphereAvg g 𝕣 z| ≤
      Real.sqrt M * Real.log ε⁻¹) :
    sphereDiam (D g) w r ≤ ENNReal.ofReal
      (C * 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z) *
        ε ^ (-(ξ * Real.sqrt M))) := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hξQ : 0 ≤ ξ * Q := mul_nonneg hξ.le hQ
  have hr𝕣 : r ≤ 𝕣 := by nlinarith only [hrhi, hε1, h𝕣]
  have hpow : r ^ (ξ * Q) ≤ 𝕣 ^ (ξ * Q) :=
    Real.rpow_le_rpow hr.le hr𝕣 hξQ
  have hfield' : sphereAvg g r w ≤ sphereAvg g 𝕣 z +
      Real.sqrt M * Real.log ε⁻¹ := by
    linarith only [hfield, le_abs_self (sphereAvg g r w - sphereAvg g 𝕣 z)]
  have hexp : Real.exp (ξ * sphereAvg g r w) ≤
      Real.exp (ξ * sphereAvg g 𝕣 z) * ε ^ (-(ξ * Real.sqrt M)) := by
    have hmul : ξ * sphereAvg g r w ≤
        ξ * sphereAvg g 𝕣 z + ξ * Real.sqrt M * Real.log ε⁻¹ := by
      nlinarith only [hfield', hξ]
    have hp : ε ^ (-(ξ * Real.sqrt M)) =
        Real.exp (ξ * Real.sqrt M * Real.log ε⁻¹) := by
      rw [Real.rpow_def_of_pos hε0, Real.log_inv]
      ring_nf
    rw [hp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hmul
  have hscale : C * sNorm ξ Q g r w ≤
      C * 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z) *
        ε ^ (-(ξ * Real.sqrt M)) := by
    dsimp [sNorm]
    have hpow0 : 0 ≤ 𝕣 ^ (ξ * Q) := (Real.rpow_pos_of_pos h𝕣 _).le
    have hexp0 : 0 ≤ Real.exp (ξ * sphereAvg g r w) := (Real.exp_pos _).le
    calc
      C * (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg g r w)) ≤
          C * (𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g r w)) := by
            gcongr
      _ ≤ C * (𝕣 ^ (ξ * Q) *
          (Real.exp (ξ * sphereAvg g 𝕣 z) * ε ^ (-(ξ * Real.sqrt M)))) := by
            gcongr
      _ = _ := by ring_nf
  exact hgood.trans (ENNReal.ofReal_le_ofReal hscale)

/-- Deterministic upper set-distance bound on the simultaneous good-grid and
sphere-average events. The path has a fixed Euclidean margin inside `V`. -/
theorem w2_setDist_det (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    (D : DistRd d → ContMetric d) (g : DistRd d)
    (V K₁ K₂ : Set (Rd d)) (z : Rd d)
    {𝕣 R ε Λ C M δ : ℝ} (h𝕣 : 0 < 𝕣) (hR : 0 ≤ R)
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hεR : ε < 1 / (R + 2))
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (_hδ : 0 < δ) (hεδ : 3 * ε * 𝕣 ≤ δ)
    (P : ℝ → Rd d) (hP : LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1))
    (hPbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - z‖ ≤ R * 𝕣)
    (hPmargin : ∀ t ∈ Icc (0 : ℝ) 1, ball (P t) δ ⊆ V)
    (hK₁ : IsConnected K₁) (hK₂ : IsConnected K₂)
    (h₀ : P 0 ∈ K₁) (h₁ : P 1 ∈ K₂) (hK₁V : K₁ ⊆ V)
    (hK₁b : ∀ c : Rd d, ¬ K₁ ⊆ ball c (ε * 𝕣))
    (hK₂b : ∀ c : Rd d, ¬ K₂ ⊆ ball c (ε * 𝕣))
    (hgrid : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
      ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
      w2GoodSphere ξ Q D g C (z + w) (𝕣 / 2 ^ k))
    (hfield : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε), ∀ k : ℕ,
      ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
      |sphereAvg g (𝕣 / 2 ^ k) (z + w) - sphereAvg g 𝕣 z| ≤
        Real.sqrt M * Real.log ε⁻¹) :
    setDistIn (D g) V K₁ K₂ ≤
      ENNReal.ofReal (2 * Λ / (ε ^ 2 * 𝕣) + 2) *
        ENNReal.ofReal (C * 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z) *
          ε ^ (-(ξ * Real.sqrt M))) := by
  let B : ℝ := C * 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z) *
    ε ^ (-(ξ * Real.sqrt M))
  let good : Rd d → ℝ → Prop := fun w r =>
    0 < r ∧ r ≤ ε * 𝕣 ∧ w2GoodSphere ξ Q D g C w r ∧
    |sphereAvg g r w - sphereAvg g 𝕣 z| ≤ Real.sqrt M * Real.log ε⁻¹ ∧
    ∃ t ∈ Icc (0 : ℝ) 1, ‖P t - w‖ < r / 2
  have hcov : ∀ t ∈ Icc (0 : ℝ) 1, ∃ w r,
      ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧ ‖P t - w‖ < r / 2 ∧ good w r := by
    intro t ht
    have hgrid' : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
      ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
      (w2GoodSphere ξ Q D g C (z + w) (𝕣 / 2 ^ k) ∧
        |sphereAvg g (𝕣 / 2 ^ k) (z + w) - sphereAvg g 𝕣 z| ≤
          Real.sqrt M * Real.log ε⁻¹) := by
      intro w hw
      obtain ⟨k, hlo, hhi, hgood⟩ := hgrid w hw
      exact ⟨k, hlo, hhi, hgood, hfield w hw k hlo hhi⟩
    obtain ⟨w, r, hlo, hhi, hnear, hgood⟩ :=
      w2_path_cover_grid hd P z h𝕣 hR hPbound hε.1 hε.2 hεR
        (fun w r => w2GoodSphere ξ Q D g C w r ∧
          |sphereAvg g r w - sphereAvg g 𝕣 z| ≤ Real.sqrt M * Real.log ε⁻¹)
        hgrid' t ht
    refine ⟨w, r, hlo, hhi, hnear, ?_⟩
    exact ⟨lt_of_lt_of_le (mul_pos (sq_pos_of_pos hε.1) h𝕣) hlo,
      hhi, hgood.1, hgood.2, t, ht, hnear⟩
  have hM : ∀ w r, good w r → ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      (D g).internal V u v ≤ ENNReal.ofReal B := by
    intro w r hg u hu v hv
    obtain ⟨hr, hrhi, hgood, hfield', t, ht, hnear⟩ := hg
    have hann : ann w (r / 2) (2 * r) ⊆ V := by
      intro x hx
      apply hPmargin t ht
      rw [mem_ball, dist_eq_norm]
      have htri : ‖x - P t‖ ≤ ‖x - w‖ + ‖P t - w‖ := by
        calc
          ‖x - P t‖ = ‖(x - w) - (P t - w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have hxl : ‖x - w‖ < 2 * r := hx.2
      have hbound : ‖x - P t‖ < (5 / 2 : ℝ) * r := by linarith only [htri, hxl, hnear]
      have hsmall : (5 / 2 : ℝ) * r < δ := by
        nlinarith only [hrhi, hεδ, hε.1, h𝕣]
      exact hbound.trans hsmall
    exact (w2_internal_le_sphereDiam (D g) V w r hann hu hv).trans
      (w2_goodSphere_field_le hξ hQ D g h𝕣 hε hr hrhi hC z w hgood hfield')
  exact w2_chain_setDist (by omega : 2 ≤ d) (D g) V
    (mul_pos (sq_pos_of_pos hε.1) h𝕣) hΛ P hP good hcov
    (ENNReal.ofReal B) hM hK₁ hK₂ h₀ h₁ hK₁V hK₁b hK₂b

end HigherDimLQGMetric
