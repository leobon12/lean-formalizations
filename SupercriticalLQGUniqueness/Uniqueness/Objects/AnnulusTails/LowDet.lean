import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good




 
















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

 

 
def gridPt (z : ℂ) (r : ℝ) (N j : ℕ) : ℂ :=
  z + (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))

theorem norm_exp_I_sub_exp_I_le (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (Complex.I * (φ : ℂ))‖ ≤ |θ - φ| := by
  have hsplit : Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (Complex.I * (φ : ℂ)) =
      Complex.exp (Complex.I * (φ : ℂ)) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - φ)
  rwa [Real.norm_eq_abs] at this

theorem dist_gridPt_center (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (N j : ℕ) :
    dist (gridPt z r N j) z = r := by
  rw [gridPt, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_I_mul_ofReal,
    mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

 

theorem exists_gridPt_near_sphere (z : ℂ) {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 0 < N)
    {y : ℂ} (hy : dist y z = r) :
    ∃ j ≤ N, dist y (gridPt z r N j) ≤ Real.pi * r / N := by
  have hyz : y - z ≠ 0 := by
    intro h0
    have : dist y z = 0 := by rw [dist_eq_norm, h0, norm_zero]
    linarith
  set θ := Complex.arg (y - z) with hθdef
  have hθ1 : -Real.pi < θ := Complex.neg_pi_lt_arg _
  have hθ2 : θ ≤ Real.pi := Complex.arg_le_pi _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set u : ℝ := (θ + Real.pi) * N / (2 * Real.pi) with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; apply div_nonneg <;> nlinarith [Real.pi_pos]
  have huN : u ≤ N := by
    rw [hudef, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  set j := ⌊u + 1 / 2⌋₊ with hjdef
  have hj1 : (j : ℝ) ≤ u + 1 / 2 := Nat.floor_le (by linarith)
  have hj2 : u + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  have hjN : j ≤ N := by
    have : (j : ℝ) < N + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  refine ⟨j, hjN, ?_⟩
  have hang : |(-Real.pi + 2 * Real.pi * j / N) - θ| ≤ Real.pi / N := by
    have hident : (-Real.pi + 2 * Real.pi * j / N) - θ = 2 * Real.pi / N * (j - u) := by
      rw [hudef]
      field_simp
      ring
    rw [hident, abs_mul, abs_of_pos (by positivity)]
    have hju : |(j : ℝ) - u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc 2 * Real.pi / N * |(j : ℝ) - u| ≤ 2 * Real.pi / N * (1 / 2) :=
          mul_le_mul_of_nonneg_left hju (by positivity)
      _ = Real.pi / N := by ring
  have hpolar : y - z = (‖y - z‖ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    have := Complex.norm_mul_exp_arg_mul_I (y - z)
    rw [mul_comm (↑(Complex.arg (y - z))) Complex.I] at this
    exact this.symm
  have hρ : ‖y - z‖ = r := by rw [← dist_eq_norm]; exact hy
  rw [dist_eq_norm]
  have hrw : y - gridPt z r N j = (y - z) -
      (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ)) := by
    rw [gridPt]
    ring
  rw [hrw, hpolar, hρ, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  calc r * ‖Complex.exp (Complex.I * (θ : ℂ)) -
        Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖
      ≤ r * (Real.pi / N) := by
        gcongr
        calc ‖Complex.exp (Complex.I * (θ : ℂ)) -
              Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖
            ≤ |θ - (-Real.pi + 2 * Real.pi * j / N)| := norm_exp_I_sub_exp_I_le _ _
          _ = |(-Real.pi + 2 * Real.pi * j / N) - θ| := abs_sub_comm _ _
          _ ≤ Real.pi / N := hang
    _ = Real.pi * r / N := by ring

 
def gridSet (z : ℂ) (r : ℝ) (N : ℕ) : Finset ℂ := (Finset.range (N + 1)).image (gridPt z r N)

theorem card_gridSet_le (z : ℂ) (r : ℝ) (N : ℕ) : (gridSet z r N).card ≤ N + 1 :=
  Finset.card_image_le.trans (Finset.card_range _).le

theorem mem_gridSet_dist (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) {w : ℂ} (hw : w ∈ gridSet z r N) :
    dist w z = r := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
  exact dist_gridPt_center z hr N j

theorem exists_gridSet_near (z : ℂ) {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) {y : ℂ}
    (hy : dist y z = r) : ∃ w ∈ gridSet z r N, dist y w ≤ Real.pi * r / N := by
  obtain ⟨j, hj, hd⟩ := exists_gridPt_near_sphere z hr hN hy
  exact ⟨gridPt z r N j, Finset.mem_image.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩, hd⟩

 

 

theorem exists_crossing_times {f : ℝ → ℝ} {u v α β : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v)) (hfu : f u < α) (hαβ : α ≤ β) (hfv : β < f v) :
    ∃ τ₁ τ₂, u ≤ τ₁ ∧ τ₁ ≤ τ₂ ∧ τ₂ ≤ v ∧ f τ₁ = α ∧ f τ₂ = β := by
  obtain ⟨τ₁, hτ₁, hfτ₁⟩ := intermediate_value_Icc huv hf
    (show α ∈ Icc (f u) (f v) from ⟨hfu.le, by linarith⟩)
  have hτ₁v : τ₁ ≤ v := hτ₁.2
  have hf' : ContinuousOn f (Icc τ₁ v) := hf.mono (Icc_subset_Icc hτ₁.1 le_rfl)
  obtain ⟨τ₂, hτ₂, hfτ₂⟩ := intermediate_value_Icc hτ₁v hf'
    (show β ∈ Icc (f τ₁) (f v) from ⟨by rw [hfτ₁]; exact hαβ, hfv.le⟩)
  exact ⟨τ₁, τ₂, hτ₁.1, hτ₂.1, hτ₂.2, hfτ₁, hfτ₂⟩

 


theorem acr_ge_of_cover (D : LSCMetric) {y : ℂ} {ρ₁ ρ ρ₂ : ℝ} (h₁ : ρ₁ < ρ) (h₂ : ρ < ρ₂)
    (W : Finset ℂ) (t : ℂ → Ioi (0 : ℝ)) (X : ℝ≥0∞)
    (hcov : ∀ x ∈ sphere y ρ, ∃ w ∈ W, dist x w < t w)
    (hin : ∀ w ∈ W, closedBall w (2 * t w) ⊆ Objects.CorrectedEvent.ann y ρ₁ ρ₂)
    (hX : ∀ w ∈ W, X ≤ acrossDist D (ann12 w (t w))) :
    X ≤ Objects.CorrectedEvent.acr D y ρ₁ ρ₂ := by
  unfold Objects.CorrectedEvent.acr
  refine le_iInf fun P => le_iInf fun u => le_iInf fun v => le_iInf fun hP =>
    le_iInf fun hPK => le_iInf fun hPu => le_iInf fun hPv => ?_
  
  have hcont : ContinuousOn P (Icc u v) :=
    hP.continuousOn_of_mapsTo (isCompact_closedBall y ρ₂) (fun τ hτ => by
      have := hPK ⟨τ, hτ, rfl⟩
      exact mem_closedBall.2 this.2)
  have hduy : dist (P u) y = ρ₁ := mem_sphere.1 hPu
  have hdvy : dist (P v) y = ρ₂ := mem_sphere.1 hPv
  
  have hcy : ContinuousOn (fun τ => dist (P τ) y) (Icc u v) :=
    Continuous.comp_continuousOn (g := fun x : ℂ => dist x y) (by fun_prop) hcont
  have hρmem : ρ ∈ Icc (dist (P u) y) (dist (P v) y) := by
    rw [hduy, hdvy]
    exact ⟨h₁.le, h₂.le⟩
  obtain ⟨τ, hτ, hτρ⟩ := intermediate_value_Icc hP.1 hcy hρmem
  obtain ⟨w, hwW, hxw⟩ := hcov (P τ) (mem_sphere.2 hτρ)
  have hw0 : (0 : ℝ) < t w := (t w).2
  
  have hvout : 2 * (t w : ℝ) < dist (P v) w := by
    by_contra hle
    push Not at hle
    have hmem := hin w hwW (mem_closedBall.2 hle)
    exact lt_irrefl _ (hdvy ▸ hmem.2)
  have hcw : ContinuousOn (fun σ => dist (P σ) w) (Icc τ v) :=
    Continuous.comp_continuousOn (g := fun x : ℂ => dist x w) (by fun_prop)
      (hcont.mono (Icc_subset_Icc hτ.1 le_rfl))
  obtain ⟨τ₁, τ₂, hτ₁, h₁₂, hτ₂, hd₁, hd₂⟩ :=
    exists_crossing_times hτ.2 hcw hxw (by linarith) hvout
  have hu₁ : u ≤ τ₁ := hτ.1.trans hτ₁
  
  have hacr : acrossDist D (ann12 w (t w)) ≤ D (P τ₁, P τ₂) := by
    unfold acrossDist
    refine iInf₂_le_of_le (P τ₁) ?_ (iInf₂_le_of_le (P τ₂) ?_ le_rfl)
    · change P τ₁ ∈ sphere (ann12 w (t w)).center (ann12 w (t w)).innerRadius
      rw [ann12_center, ann12_innerRadius, mem_sphere]
      exact hd₁
    · change P τ₂ ∈ sphere (ann12 w (t w)).center (ann12 w (t w)).outerRadius
      rw [ann12_center, ann12_outerRadius, mem_sphere]
      exact hd₂
  calc X ≤ acrossDist D (ann12 w (t w)) := hX w hwW
    _ ≤ D (P τ₁, P τ₂) := hacr
    _ ≤ D.len P τ₁ τ₂ := LSCMetric.apply_le_len D P h₁₂
    _ ≤ D.len P u v := LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) hu₁ hτ₂

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
