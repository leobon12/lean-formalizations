import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem chord_le (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ φ : ℝ) :
    dist (c + (R : ℂ) * cexp ((θ : ℂ) * I)) (c + (R : ℂ) * cexp ((φ : ℂ) * I)) ≤ R * |θ - φ| := by
  rw [dist_eq_norm]
  have : c + (R : ℂ) * cexp ((θ : ℂ) * I) - (c + (R : ℂ) * cexp ((φ : ℂ) * I)) =
      (R : ℂ) * (cexp ((θ : ℂ) * I) - cexp ((φ : ℂ) * I)) := by ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left (norm_exp_sub_exp_le θ φ) hR

theorem exp_add_two_pi (θ : ℝ) : cexp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = cexp ((θ : ℂ) * I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

 
theorem shadow_mass (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (hforget : Continuous (BiLipschitz.Barrier.forget D))
    {c u : ℂ} {R₀ R₁ R₂ : NNReal} {dt : ℝ} (hR₀ : 0 < R₀) (hR₀₁ : (R₀ : ℝ) ≤ R₁)
    (hR₁₀ : R₁ ≤ 2 * R₀) (hgap : (R₁ : ℝ) - R₀ < 2 * C.A_sup * C.r)
    (hR₁def : (R₁ : ℝ) + C.A_sup * C.r ≤ R₀ + 2 * C.A_sup * C.r)
    (hR₁₂ : (R₁ : ℝ) < R₂) (hdt : 0 < C.lamConst * dt) (hlam : C.lamConst ≤ 1 / 48)
    (hu : u ∈ closedBall c (R₀ : ℝ))
    {P : ℝ → ℂ} {a b τ' σ' : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc τ' σ')
    (hcont : ContinuousOn P (Icc a b)) (hPD : MapsTo P (Icc a b) (closedBall c (R₂ : ℝ)))
    (hPa : P a ∈ sphere c (R₁ : ℝ)) (hPb : P b ∈ sphere c (R₁ : ℝ))
    (hfar : (R₀ : ℝ) / 8 ≤ dist (P a) (P b))
    (hnohit : ∀ t ∈ Icc a b, P t ∉ cheapSet D c u (R₀ : ℝ) (2 * C.lamConst * dt))
    (hbad : Objects.Shadow.circleOuter c R₀ 0
      (sphere c (R₀ : ℝ) \ goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu) ≤
        ENNReal.ofReal (C.lamConst * R₀ / 2))
    (hnear : Objects.Shadow.circleOuter c R₀ 0 (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * R₀)) :
    ∃ (θ₀ : ℝ) (W' : Set ℂ), W' ⊆ sphere c (R₁ : ℝ) ∧
      ENNReal.ofReal ((R₀ : ℝ) / 16) ≤ Objects.Shadow.circleOuter c R₁ θ₀ W' ∧
      ∀ w ∈ W', (∃ x, x ∈ goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu ∧
          x ∉ hitSet P τ' σ' (2 * C.A_sup * C.r) ∧ w = c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c)) ∧
        ∃ s ∈ Icc a b, (R₁ : ℝ) + C.A_sup * C.r ≤ ‖P s - c‖ ∧
          w = LQGMetric.Topo.Crosscut.rproj c (R₁ : ℝ) (P s) := by
  have hR0r : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hR1r : (0 : ℝ) < R₁ := lt_of_lt_of_le hR0r hR₀₁
  have hlam0 : 0 ≤ C.lamConst := C.lamPos.le
  set G := goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu with hG
  set N' := hitSet P τ' σ' (2 * C.A_sup * C.r) with hN'
  set Tm : ℂ → ℂ := fun z => c + ((R₁ : ℂ) / (R₀ : ℂ)) * (z - c) with hTm
  set W := Tm '' (G \ N') with hW
  set Φ : Set ℝ := {φ | c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) ∈ W} with hΦ
  
  set θa := Complex.arg (P a - c) with hθa
  have hPa' : P a = c + ((R₁ : ℝ) : ℂ) * cexp ((θa : ℂ) * I) := polar_rep hPa
  set θb := toIocMod Real.two_pi_pos θa (Complex.arg (P b - c)) with hθb
  have hθbmem : θb ∈ Ioc θa (θa + 2 * Real.pi) := toIocMod_mem_Ioc Real.two_pi_pos θa _
  have hPb' : P b = c + ((R₁ : ℝ) : ℂ) * cexp ((θb : ℂ) * I) := by
    rw [polar_rep hPb]
    congr 2
    have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos θa (Complex.arg (P b - c))
    rw [← hθb, zsmul_eq_mul] at h
    rw [← h]
    push_cast
    rw [add_mul, Complex.exp_add]
    have : cexp (((toIocDiv Real.two_pi_pos θa (Complex.arg (P b - c)) : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ)) * I) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (toIocDiv Real.two_pi_pos θa (Complex.arg (P b - c)))
      rw [← this]; congr 1; ring
    rw [this, mul_one]
  have hfar0 : 0 < dist (P a) (P b) := lt_of_lt_of_le (by positivity) hfar
  have hθbne : θb ≠ θa + 2 * Real.pi := by
    intro h
    apply (dist_pos.1 hfar0)
    rw [hPa', hPb', h, exp_add_two_pi]
  have hθb1 : θa < θb := hθbmem.1
  have hθb2 : θb < θa + 2 * Real.pi := lt_of_le_of_ne hθbmem.2 hθbne
  
  have hZ : ∀ φ ∈ Φ, ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = u ∧
      γ 1 = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) ∧
      MapsTo γ (Icc 0 1) (closedBall c (R₁ : ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc a b, γ t ≠ P s := by
    intro φ hφ
    obtain ⟨x, ⟨hxG, hxN⟩, hxeq⟩ := hφ
    obtain ⟨γ, h1, h2, h3, h4, h5⟩ := shadow_path C D hforget hR₀ hR₀₁ hgap hdt hu hsub hnohit hxG hxN
    exact ⟨γ, h1, h2, h3.trans hxeq, h4, h5⟩
  have hsh := Objects.Shadow.shadow (u := u) hR1r (hR₁₂) hab hcont hPD hPa' hPb' Φ hZ
  
  have hwit : ∀ φ ∈ Φ, ∀ s ∈ Icc a b, ∀ ρ ∈ Icc (R₁ : ℝ) R₂,
      P s = c + (ρ : ℂ) * cexp ((φ : ℂ) * I) →
      (∃ x, x ∈ G ∧ x ∉ N' ∧ c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) = Tm x) ∧
      (R₁ : ℝ) + C.A_sup * C.r ≤ ‖P s - c‖ ∧
      c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) = LQGMetric.Topo.Crosscut.rproj c (R₁ : ℝ) (P s) := by
    intro φ hφ s hs ρ hρ hPs
    obtain ⟨x, ⟨hxG, hxN⟩, hxeq⟩ := hφ
    have hxpol : x = c + ((R₀ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) := by
      have hR0c : ((R₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR0r.ne'
      have hR1c : ((R₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR1r.ne'
      have h := hxeq
      simp only [hTm] at h
      have : x - c = ((R₀ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) := by
        have h' : ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c) = ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I) := by
          have := congrArg (fun z => z - c) h
          simpa using this
        field_simp at h'
        linear_combination h'
      linear_combination this
    have hρ0 : 0 < ρ := lt_of_lt_of_le hR1r hρ.1
    have hnorm : ‖P s - c‖ = ρ := by rw [hPs]; exact norm_polar_sub c hρ0.le φ
    refine ⟨⟨x, hxG, hxN, hxeq.symm⟩, ?_, ?_⟩
    · 
      have hd : 2 * C.A_sup * C.r ≤ dist (P s) x := by
        by_contra hc
        push Not at hc
        exact hxN ⟨s, hsub hs, hc⟩
      have hdist : dist (P s) x = ρ - R₀ := by
        rw [hPs, hxpol, dist_eq_norm]
        have : c + (ρ : ℂ) * cexp ((φ : ℂ) * I) - (c + ((R₀ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)) =
            (((ρ - R₀ : ℝ)) : ℂ) * cexp ((φ : ℂ) * I) := by push_cast; ring
        rw [this, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.1])]
      rw [hnorm]
      linarith
    · rw [hPs, rproj_polar c hρ0 φ]
  
  have hcomp : Objects.Shadow.circleOuter c R₁ θa (sphere c (R₁ : ℝ) \ W) ≤
      ENNReal.ofReal (3 * C.lamConst * R₀) := by
    rw [circleOuter_window]
    exact Objects.Shadow.circleOuter_good_radial_complement hR₀ (lt_of_lt_of_le hR₀ (by exact_mod_cast hR₀₁))
      hR₁₀ hlam0 hR0r.le hbad hnear
  
  have arc_est : ∀ (lo hi : ℝ), θa ≤ lo → lo ≤ hi → hi ≤ θa + 2 * Real.pi →
      ENNReal.ofReal ((R₀ : ℝ) / 8) ≤ ENNReal.ofReal ((R₁ : ℝ) * (hi - lo)) →
      ENNReal.ofReal ((R₀ : ℝ) / 16) ≤ Objects.Shadow.circleOuter c R₁ θa
        ({w | ∃ φ ∈ Ioo lo hi, w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W) := by
    intro lo hi hlo hlohi hhi hchord
    set Arc := Ioo lo hi
    have hsub1 : Arc ∩ Φ ⊆ {θ ∈ Ico θa (θa + 2 * Real.pi) |
        c + (R₁ : ℂ) * cexp (θ * I) ∈ ({w | ∃ φ ∈ Ioo lo hi,
          w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W)} := by
      rintro θ ⟨hθ, hθΦ⟩
      exact ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ⟨θ, hθ, rfl⟩, hθΦ⟩
    have hsub2 : Arc \ Φ ⊆ {θ ∈ Ico θa (θa + 2 * Real.pi) |
        c + (R₁ : ℂ) * cexp (θ * I) ∈ sphere c (R₁ : ℝ) \ W} := by
      rintro θ ⟨hθ, hθΦ⟩
      refine ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_, hθΦ⟩
      rw [mem_sphere, dist_eq_norm]
      exact norm_polar_sub c (NNReal.coe_nonneg R₁) θ
    have hsplit : volume Arc ≤ volume (Arc ∩ Φ) + volume (Arc \ Φ) := by
      have : Arc ⊆ (Arc ∩ Φ) ∪ (Arc \ Φ) := fun θ hθ => by
        by_cases h : θ ∈ Φ
        · exact Or.inl ⟨hθ, h⟩
        · exact Or.inr ⟨hθ, h⟩
      exact (measure_mono this).trans (measure_union_le _ _)
    have hvol : volume Arc = ENNReal.ofReal (hi - lo) := Real.volume_Ioo
    have hmain : ENNReal.ofReal ((R₀ : ℝ) / 8) ≤
        Objects.Shadow.circleOuter c R₁ θa ({w | ∃ φ ∈ Ioo lo hi,
          w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W) + ENNReal.ofReal (3 * C.lamConst * R₀) := by
      calc ENNReal.ofReal ((R₀ : ℝ) / 8) ≤ ENNReal.ofReal ((R₁ : ℝ) * (hi - lo)) := hchord
        _ = ENNReal.ofReal (R₁ : ℝ) * volume Arc := by
            rw [hvol, ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        _ ≤ ENNReal.ofReal (R₁ : ℝ) * (volume (Arc ∩ Φ) + volume (Arc \ Φ)) := by gcongr
        _ = ENNReal.ofReal (R₁ : ℝ) * volume (Arc ∩ Φ) +
            ENNReal.ofReal (R₁ : ℝ) * volume (Arc \ Φ) := mul_add _ _ _
        _ ≤ Objects.Shadow.circleOuter c R₁ θa ({w | ∃ φ ∈ Ioo lo hi,
              w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W) +
            Objects.Shadow.circleOuter c R₁ θa (sphere c (R₁ : ℝ) \ W) := by
            unfold Objects.Shadow.circleOuter
            gcongr
        _ ≤ _ := by gcongr
    have hnum : ENNReal.ofReal ((R₀ : ℝ) / 16) + ENNReal.ofReal (3 * C.lamConst * R₀) ≤
        ENNReal.ofReal ((R₀ : ℝ) / 8) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (hnum.trans hmain)
  rcases hsh with h1 | h2
  · refine ⟨θa, {w | ∃ φ ∈ Ioo θa θb, w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W, ?_, ?_, ?_⟩
    · rintro w ⟨⟨φ, -, rfl⟩, -⟩
      rw [mem_sphere, dist_eq_norm]
      exact norm_polar_sub c (NNReal.coe_nonneg R₁) φ
    · refine arc_est θa θb le_rfl hθb1.le hθb2.le ?_
      apply ENNReal.ofReal_le_ofReal
      have := chord_le c (NNReal.coe_nonneg R₁) θa θb
      rw [← hPa', ← hPb', abs_sub_comm, abs_of_pos (by linarith)] at this
      linarith
    · rintro w ⟨⟨φ, hφ, rfl⟩, hwW⟩
      obtain ⟨s, hs, ρ, hρ, hPs⟩ := h1 φ hwW hφ.1 hφ.2
      obtain ⟨⟨x, hxG, hxN, hx⟩, hs2, hs3⟩ := hwit φ hwW s hs ρ hρ hPs
      exact ⟨⟨x, hxG, hxN, hx⟩, s, hs, hs2, hs3⟩
  · refine ⟨θa, {w | ∃ φ ∈ Ioo θb (θa + 2 * Real.pi),
      w = c + ((R₁ : ℝ) : ℂ) * cexp ((φ : ℂ) * I)} ∩ W, ?_, ?_, ?_⟩
    · rintro w ⟨⟨φ, -, rfl⟩, -⟩
      rw [mem_sphere, dist_eq_norm]
      exact norm_polar_sub c (NNReal.coe_nonneg R₁) φ
    · refine arc_est θb (θa + 2 * Real.pi) hθb1.le hθb2.le le_rfl ?_
      apply ENNReal.ofReal_le_ofReal
      have := chord_le c (NNReal.coe_nonneg R₁) θb (θa + 2 * Real.pi)
      rw [exp_add_two_pi, ← hPa', ← hPb', abs_sub_comm, abs_of_pos (by linarith),
        dist_comm] at this
      linarith
    · rintro w ⟨⟨φ, hφ, rfl⟩, hwW⟩
      obtain ⟨s, hs, ρ, hρ, hPs⟩ := h2 φ hwW hφ.1 hφ.2
      obtain ⟨⟨x, hxG, hxN, hx⟩, hs2, hs3⟩ := hwit φ hwW s hs ρ hρ hPs
      exact ⟨⟨x, hxG, hxN, hx⟩, s, hs, hs2, hs3⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
