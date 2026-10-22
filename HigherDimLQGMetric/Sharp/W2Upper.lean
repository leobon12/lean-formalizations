import HigherDimLQGMetric.Sharp.W2Geometry
import HigherDimLQGMetric.Sharp.W2Arith

/-! Superpolynomial upper tail for distances between compact connected sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The two good grid events force an upper bound at every scale. -/
theorem w2_setDist_good_event (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    (D : DistRd d → ContMetric d) {U K₁ K₂ : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial)
    (hK₂c : IsConnected K₂) (hK₂n : K₂.Nontrivial)
    (h₁ : K₁ ⊆ U) (h₂ : K₂ ⊆ U)
    {C M : ℝ} (hC : 0 < C) :
    ∃ B ε₀ : ℝ, 1 ≤ B ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ (g : DistRd d) (𝕣 : ℝ), 0 < 𝕣 → ∀ (z : Rd d) (ε : ℝ),
        ε ∈ Ioo (0 : ℝ) ε₀ →
        (∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩ ball (0 : Rd d) (𝕣 / ε),
          ∃ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
            w2GoodSphere ξ Q D g C (z + w) (𝕣 / 2 ^ k)) →
        (∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩ ball (0 : Rd d) (𝕣 / ε),
          ∀ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
            |sphereAvg g (𝕣 / 2 ^ k) (z + w) - sphereAvg g 𝕣 z| ≤
              Real.sqrt M * Real.log ε⁻¹) →
        setDistIn (D g) (affineSet 𝕣 z U) (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂) ≤
          ENNReal.ofReal ((B * ε ^ (-(2 + ξ * Real.sqrt M))) *
            (𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z))) := by
  classical
  obtain ⟨x, hx⟩ : K₁.Nonempty := hK₁n.nonempty
  obtain ⟨y, hy⟩ : K₂.Nonempty := hK₂n.nonempty
  obtain ⟨Λ, R, δ, hΛ, hR, hδ, hpath⟩ := w2_scaled_path hU hUc (h₁ hx) (h₂ hy)
  obtain ⟨η₁, hη₁, hsep₁⟩ := w2_nontrivial_sep hK₁n
  obtain ⟨η₂, hη₂, hsep₂⟩ := w2_nontrivial_sep hK₂n
  let ε₀ : ℝ := min (1 / 2) (min (1 / (R + 2)) (min (δ / 3) (min η₁ η₂)))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀1 : ε₀ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let B : ℝ := max 1 ((2 * Λ + 2) * C)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, ε₀, hB, hε₀, hε₀1, ?_⟩
  intro g 𝕣 h𝕣 z ε hε hgrid hfield
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2
    ((min_le_left _ _).trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hεR : ε < 1 / (R + 2) := lt_of_lt_of_le hε.2
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : 3 * ε * 𝕣 ≤ δ * 𝕣 := by
    have he : ε < δ / 3 := lt_of_lt_of_le hε.2
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [he, h𝕣]
  have hεη₁ : ε ≤ η₁ := (lt_of_lt_of_le hε.2
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))).le
  have hεη₂ : ε ≤ η₂ := (lt_of_lt_of_le hε.2
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))).le
  obtain ⟨P, hPLip, hP0, hP1, hPbound, hPmargin⟩ := hpath 𝕣 h𝕣 z
  have hK₁conn : IsConnected (affineSet 𝕣 z K₁) :=
    hK₁c.image (fun v => z + 𝕣 • v) (by fun_prop)
  have hK₂conn : IsConnected (affineSet 𝕣 z K₂) :=
    hK₂c.image (fun v => z + 𝕣 • v) (by fun_prop)
  have hK₁U : affineSet 𝕣 z K₁ ⊆ affineSet 𝕣 z U := image_mono h₁
  have hK₁b : ∀ c : Rd d, ¬ affineSet 𝕣 z K₁ ⊆ ball c (ε * 𝕣) := by
    intro c
    exact w2_affine_not_subset_ball hK₁n h𝕣 hε0.le (hsep₁ ε hεη₁) z c
  have hK₂b : ∀ c : Rd d, ¬ affineSet 𝕣 z K₂ ⊆ ball c (ε * 𝕣) := by
    intro c
    exact w2_affine_not_subset_ball hK₂n h𝕣 hε0.le (hsep₂ ε hεη₂) z c
  have hD := w2_setDist_det hd hξ hQ D g (affineSet 𝕣 z U)
    (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂) z h𝕣 hR
    (show ε ∈ Ioo (0 : ℝ) 1 from ⟨hε0, hε1⟩) hεR
    (mul_nonneg h𝕣.le hΛ) hC.le (mul_pos hδ h𝕣) hεδ P hPLip
    hPbound hPmargin hK₁conn hK₂conn
    (by exact ⟨x, hx, hP0.symm⟩) (by exact ⟨y, hy, hP1.symm⟩)
    hK₁U hK₁b hK₂b hgrid hfield
  let S : ℝ := 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg g 𝕣 z)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hfac : 0 ≤ 2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2 := by positivity
  have hterm : 0 ≤ C * S * ε ^ (-(ξ * Real.sqrt M)) := by positivity
  have hreal := w2_chain_coefficient hΛ hC.le h𝕣
    (show ε ∈ Ioo (0 : ℝ) 1 from ⟨hε0, hε1⟩) hS
    (u := ξ * Real.sqrt M)
  have hBreal : ((2 * Λ + 2) * C * ε ^ (-(2 + ξ * Real.sqrt M))) * S ≤
      (B * ε ^ (-(2 + ξ * Real.sqrt M))) * S := by
    have hbc : (2 * Λ + 2) * C ≤ B := le_max_right _ _
    gcongr
  calc
    setDistIn (D g) (affineSet 𝕣 z U) (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂) ≤
        ENNReal.ofReal (2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2) *
          ENNReal.ofReal (C * S * ε ^ (-(ξ * Real.sqrt M))) := by
            simpa only [S, mul_assoc] using hD
    _ = ENNReal.ofReal ((2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2) *
        (C * S * ε ^ (-(ξ * Real.sqrt M)))) := by
          rw [ENNReal.ofReal_mul hfac]
    _ ≤ ENNReal.ofReal (((2 * Λ + 2) * C * ε ^ (-(2 + ξ * Real.sqrt M))) * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal ((B * ε ^ (-(2 + ξ * Real.sqrt M))) * S) :=
      ENNReal.ofReal_le_ofReal hBreal

/-- Proposition 4.7, upper half: a superpolynomial outer tail for set distance. -/
theorem setDist_upper_superpoly (hA1 : ShellInputA1 d) (hd : 3 ≤ d)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 ≤ Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {U K₁ K₂ : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsConnected U)
    (_hK₁ : IsCompact K₁) (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial)
    (_hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂) (hK₂n : K₂.Nontrivial)
    (h₁ : K₁ ⊆ U) (h₂ : K₂ ⊆ U) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : Rd d, ∀ A : ℝ, 1 ≤ A →
      P {ω | ENNReal.ofReal (A * 𝕣 ^ (ξ * Q) *
        Real.exp (ξ * sphereAvg (h ω) 𝕣 z)) <
        setDistIn (D (h ω)) (affineSet 𝕣 z U)
          (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂)} ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  classical
  obtain ⟨M, hM, hMb⟩ := w2_choose_gaussian_exponent d hξ hp
  let a : ℝ := 2 + ξ * Real.sqrt M
  let b : ℝ := M / 8 - (3 * d + 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 2 * a * p ≤ b := hMb
  have hbpos : 0 < b := lt_of_lt_of_le (mul_pos (mul_pos two_pos ha) hp) hb
  obtain ⟨Cg, Kg, hCg, hGood⟩ := w2_goodSphere_everywhere hA1 hd hD hbpos
  obtain ⟨Kv, hGauss⟩ := w2_lemma49_grid_shifted hd
  obtain ⟨B, ε₀, hB, hε₀, hε₀1, hDet⟩ :=
    w2_setDist_good_event hd hξ hQ D hU hUc hK₁c hK₁n hK₂c hK₂n h₁ h₂ hCg
      (M := M)
  obtain ⟨A₀, hA₀, hChoice⟩ := w2_power_choice ha hb hB hε₀
  let Gc : ℝ := 4 * (25 * (d : ℝ)) ^ d * Real.exp (M * Kv / 32)
  have hGc : 0 ≤ Gc := by dsimp [Gc]; positivity
  let Kc : ℝ := max 0 Kg + Gc
  have hKc : 0 ≤ Kc := add_nonneg (le_max_left _ _) hGc
  let C : ℝ := max Kc (A₀ ^ p)
  have hCK : Kc ≤ C := le_max_left _ _
  have hCA : A₀ ^ p ≤ C := le_max_right _ _
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh 𝕣 h𝕣 z A hA
  let BadA : Set Ω := {ω | ENNReal.ofReal (A * 𝕣 ^ (ξ * Q) *
    Real.exp (ξ * sphereAvg (h ω) 𝕣 z)) <
    setDistIn (D (h ω)) (affineSet 𝕣 z U)
      (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂)}
  change P BadA ≤ _
  by_cases hlarge : A₀ ≤ A
  · let ε : ℝ := A ^ (-(1 / (2 * a)))
    obtain ⟨hε, hBA, htail⟩ := hChoice A hlarge
    have hεone : ε ∈ Ioo (0 : ℝ) 1 :=
      ⟨hε.1, lt_of_lt_of_le hε.2 hε₀1⟩
    let Gbad : Set Ω := {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε),
      ∀ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
        ¬ w2GoodSphere ξ Q D (h ω) Cg (z + w) (𝕣 / 2 ^ k)}
    let Fbad : Set Ω := {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
      ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
        ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) (z + w) - sphereAvg (h ω) 𝕣 z|}
    have hsub : BadA ⊆ Gbad ∪ Fbad := by
      intro ω hω
      by_cases hgb : ω ∈ Gbad
      · exact Or.inl hgb
      by_cases hfb : ω ∈ Fbad
      · exact Or.inr hfb
      exfalso
      have hgrid : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
          ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
          ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
          w2GoodSphere ξ Q D (h ω) Cg (z + w) (𝕣 / 2 ^ k) := by
        intro w hw
        by_contra hnone
        apply hgb
        refine ⟨w, hw, ?_⟩
        intro k hklo hkhi hgood
        exact hnone ⟨k, hklo, hkhi, hgood⟩
      have hfield : ∀ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
          ball (0 : Rd d) (𝕣 / ε), ∀ k : ℕ,
          ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
          |sphereAvg (h ω) (𝕣 / 2 ^ k) (z + w) - sphereAvg (h ω) 𝕣 z| ≤
            Real.sqrt M * Real.log ε⁻¹ := by
        intro w hw k hklo hkhi
        exact le_of_not_gt (fun hb => hfb ⟨w, hw, k, hklo, hkhi, hb⟩)
      have hdω := hDet (h ω) 𝕣 h𝕣 z ε hε hgrid hfield
      have hS : 0 ≤ 𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) 𝕣 z) := by
        positivity
      have hreal : (B * ε ^ (-a)) *
          (𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) 𝕣 z)) ≤
          A * (𝕣 ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) 𝕣 z)) :=
        mul_le_mul_of_nonneg_right hBA hS
      have hcontr : setDistIn (D (h ω)) (affineSet 𝕣 z U)
          (affineSet 𝕣 z K₁) (affineSet 𝕣 z K₂) ≤
          ENNReal.ofReal (A * 𝕣 ^ (ξ * Q) *
            Real.exp (ξ * sphereAvg (h ω) 𝕣 z)) := by
        have h' := hdω.trans (ENNReal.ofReal_le_ofReal hreal)
        simpa only [a, mul_assoc] using h'
      exact (not_lt_of_ge hcontr) hω
    have hG : P Gbad ≤ ENNReal.ofReal (max 0 Kg * ε ^ b) := by
      have h := hGood P h hh 𝕣 h𝕣 z ε hεone
      have hcoef : Kg * ε ^ b ≤ max 0 Kg * ε ^ b :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      exact h.trans (ENNReal.ofReal_le_ofReal hcoef)
    have hF : P Fbad ≤ ENNReal.ofReal (Gc * ε ^ b) := by
      simpa only [Fbad, Gc, b] using hGauss P h hh h𝕣 hεone hM.le z
    have hbound : P BadA ≤ ENNReal.ofReal (Kc * ε ^ b) := by
      calc
        P BadA ≤ P (Gbad ∪ Fbad) := measure_mono hsub
        _ ≤ P Gbad + P Fbad := measure_union_le _ _
        _ ≤ ENNReal.ofReal (max 0 Kg * ε ^ b) +
            ENNReal.ofReal (Gc * ε ^ b) := add_le_add hG hF
        _ = ENNReal.ofReal (Kc * ε ^ b) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [Kc]
          ring
    have htail' : Kc * ε ^ b ≤ C * A ^ (-p) := by
      calc
        Kc * ε ^ b ≤ Kc * A ^ (-p) := mul_le_mul_of_nonneg_left htail hKc
        _ ≤ C * A ^ (-p) := mul_le_mul_of_nonneg_right hCK (by positivity)
    exact hbound.trans (ENNReal.ofReal_le_ofReal htail')
  · have hsmall : A < A₀ := lt_of_not_ge hlarge
    have hA0 : 0 < A := by linarith only [hA]
    have hAp : A ^ p ≤ A₀ ^ p := Real.rpow_le_rpow hA0.le hsmall.le hp.le
    have hAinv : 0 ≤ A ^ (-p) := (Real.rpow_pos_of_pos hA0 _).le
    have hprod : 1 ≤ A₀ ^ p * A ^ (-p) := by
      have hmul := mul_le_mul_of_nonneg_right hAp hAinv
      rw [Real.rpow_neg hA0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hA0 p).ne'] at hmul
      rw [Real.rpow_neg hA0.le]
      exact hmul
    have hCprod : 1 ≤ C * A ^ (-p) := hprod.trans
      (mul_le_mul_of_nonneg_right hCA hAinv)
    calc
      P BadA ≤ 1 := by simpa only [measure_univ] using (measure_mono (subset_univ BadA) : P BadA ≤ P univ)
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * A ^ (-p)) := ENNReal.ofReal_le_ofReal hCprod

end HigherDimLQGMetric
