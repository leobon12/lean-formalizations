import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA1




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 

section window

variable {A : Set ℝ} {T : ℝ}

theorem periodic_int (hper : ∀ x, x ∈ A ↔ x + T ∈ A) (k : ℤ) (x : ℝ) :
    x ∈ A ↔ x + k * T ∈ A := by
  have hP : Function.Periodic (fun x : ℝ => x ∈ A) T := fun x => propext (hper x).symm
  have h2 : (x + (k : ℝ) * T ∈ A) = (x ∈ A) := (hP.int_mul k) x
  rw [h2]

theorem vol_window_shift (hper : ∀ x, x ∈ A ↔ x + T ∈ A) (θ : ℝ) (k : ℤ) :
    volume (A ∩ Ico (θ + k * T) (θ + k * T + T)) = volume (A ∩ Ico θ (θ + T)) := by
  have hpre : (fun y : ℝ => y + k * T) ⁻¹' (A ∩ Ico (θ + k * T) (θ + k * T + T)) =
      A ∩ Ico θ (θ + T) := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_Ico]
    rw [← periodic_int hper k y]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  rw [← hpre, measure_preimage_add_right]

theorem vol_window_base (hper : ∀ x, x ∈ A ↔ x + T ∈ A) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ T) :
    volume (A ∩ Ico x (x + T)) = volume (A ∩ Ico 0 T) := by
  
  have h1 := measure_inter_add_sdiff (μ := volume) (A ∩ Ico x (x + T)) (measurableSet_Ico (a := x) (b := T))
  have h2 := measure_inter_add_sdiff (μ := volume) (A ∩ Ico 0 T) (measurableSet_Ico (a := x) (b := T))
  have e1 : A ∩ Ico x (x + T) ∩ Ico x T = A ∩ Ico x T := by
    ext y; simp only [mem_inter_iff, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, h4, h5⟩
    · rintro ⟨h1, h4, h5⟩; exact ⟨⟨h1, h4, by linarith⟩, h4, h5⟩
  have e2 : A ∩ Ico 0 T ∩ Ico x T = A ∩ Ico x T := by
    ext y; simp only [mem_inter_iff, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, h4, h5⟩
    · rintro ⟨h1, h4, h5⟩; exact ⟨⟨h1, by linarith, h5⟩, h4, h5⟩
  have e3 : (A ∩ Ico x (x + T)) \ Ico x T = A ∩ Ico T (x + T) := by
    ext y; simp only [mem_inter_iff, mem_sdiff, mem_Ico, not_and, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h4 h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by linarith, h3⟩, fun _ => h2⟩
  have e4 : (A ∩ Ico 0 T) \ Ico x T = A ∩ Ico 0 x := by
    ext y; simp only [mem_inter_iff, mem_sdiff, mem_Ico, not_and, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hc
      push Not at hc
      exact absurd (h4 hc) (not_le.2 h3)
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, by linarith⟩, fun h => absurd h (not_le.2 h3)⟩
  have e5 : volume (A ∩ Ico T (x + T)) = volume (A ∩ Ico 0 x) := by
    have := vol_window_shift (A := A) (T := T) hper 0 1
    have hpre : (fun y : ℝ => y + (1 : ℤ) * T) ⁻¹' (A ∩ Ico T (x + T)) = A ∩ Ico 0 x := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_Ico, Int.cast_one, one_mul]
      rw [← hper y]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    rw [← hpre, measure_preimage_add_right]
  rw [e1, e3, e5] at h1
  rw [e2, e4] at h2
  rw [← h1, ← h2]

theorem vol_window (hT : 0 < T) (hper : ∀ x, x ∈ A ↔ x + T ∈ A) (θ : ℝ) :
    volume (A ∩ Ico θ (θ + T)) = volume (A ∩ Ico 0 T) := by
  set x := toIcoMod hT 0 θ with hx
  set k := toIcoDiv hT 0 θ with hk
  have hmem : x ∈ Ico 0 (0 + T) := toIcoMod_mem_Ico hT 0 θ
  have hθ : θ = x + k * T := by
    have := toIcoMod_add_toIcoDiv_zsmul hT 0 θ
    rw [zsmul_eq_mul] at this
    linarith
  rw [hθ, vol_window_shift hper x k, vol_window_base hper hmem.1 (by linarith [hmem.2])]

end window

 

theorem circleOuter_window (c : ℂ) (R : NNReal) (θ₀ : ℝ) (S : Set ℂ) :
    Objects.Shadow.circleOuter c R θ₀ S = Objects.Shadow.circleOuter c R 0 S := by
  unfold Objects.Shadow.circleOuter
  congr 1
  set A : Set ℝ := {θ | c + (R : ℂ) * cexp (θ * I) ∈ S} with hA
  have hper : ∀ x, x ∈ A ↔ x + 2 * Real.pi ∈ A := by
    intro x
    simp only [hA, mem_ofPred_eq]
    have : cexp (((x + 2 * Real.pi : ℝ) : ℂ) * I) = cexp ((x : ℂ) * I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [this]
  have e : ∀ θ, {θ' ∈ Ico θ (θ + 2 * Real.pi) | c + (R : ℂ) * cexp (θ' * I) ∈ S} =
      A ∩ Ico θ (θ + 2 * Real.pi) := by
    intro θ; ext θ'; simp only [mem_ofPred_eq, mem_inter_iff, hA]; exact and_comm
  rw [e θ₀, e 0, zero_add]
  exact vol_window Real.two_pi_pos hper θ₀

 

theorem polar_rep {c z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) :
    z = c + (R : ℂ) * cexp ((Complex.arg (z - c) : ℂ) * I) := by
  have h := Complex.norm_mul_exp_arg_mul_I (z - c)
  rw [mem_sphere, dist_eq_norm] at hz
  rw [hz] at h
  rw [h]
  ring

theorem norm_polar_sub (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (φ : ℝ) :
    ‖(c + (R : ℂ) * cexp ((φ : ℂ) * I)) - c‖ = R := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hR]

 
theorem radial_polar (c : ℂ) {R₀ R₁ : NNReal} (hR₀ : 0 < R₀) (φ : ℝ) :
    c + ((R₁ : ℂ) / (R₀ : ℂ)) * ((c + (R₀ : ℂ) * cexp ((φ : ℂ) * I)) - c) =
      c + (R₁ : ℂ) * cexp ((φ : ℂ) * I) := by
  have h₀ : (R₀ : ℂ) ≠ 0 := by exact_mod_cast hR₀.ne'
  field_simp
  ring

 
theorem rproj_polar (c : ℂ) {R ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) :
    LQGMetric.Topo.Crosscut.rproj c R (c + (ρ : ℂ) * cexp ((φ : ℂ) * I)) =
      c + (R : ℂ) * cexp ((φ : ℂ) * I) := by
  unfold LQGMetric.Topo.Crosscut.rproj
  rw [norm_polar_sub c hρ.le φ, add_sub_cancel_left]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  push_cast
  field_simp

 
def segPathC (x y : ℂ) : Path x y where
  toFun t := x + ((t : ℝ) : ℂ) * (y - x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

 

 

theorem shadow_path (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (hforget : Continuous (BiLipschitz.Barrier.forget D))
    {c u : ℂ} {R₀ R₁ : NNReal} {dt : ℝ} (hR₀ : 0 < R₀) (hR₀₁ : (R₀ : ℝ) ≤ R₁)
    (hgap : (R₁ : ℝ) - R₀ < 2 * C.A_sup * C.r) (hdt : 0 < C.lamConst * dt)
    (hu : u ∈ closedBall c (R₀ : ℝ))
    {P : ℝ → ℂ} {a b τ' σ' : ℝ} (hsub : Icc a b ⊆ Icc τ' σ')
    (hnohit : ∀ t ∈ Icc a b, P t ∉ cheapSet D c u (R₀ : ℝ) (2 * C.lamConst * dt))
    {x : ℂ} (hxG : x ∈ goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu)
    (hxN : x ∉ hitSet P τ' σ' (2 * C.A_sup * C.r)) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = u ∧
      γ 1 = c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c) ∧ MapsTo γ (Icc 0 1) (closedBall c (R₁ : ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc a b, γ t ≠ P s := by
  obtain ⟨L, hLB, hLav, -⟩ := cheap_path_avoiding C D hforget hdt hu hnohit hxG
  have hxs : x ∈ sphere c (R₀ : ℝ) := hxG.1
  set w := c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c) with hw
  let seg := segPathC x w
  let γp : Path u w := L.trans seg
  refine ⟨γp.extend, γp.continuous_extend.continuousOn, γp.extend_zero, γp.extend_one, ?_, ?_⟩
  · 
    have hrange : ∀ τ : unitInterval, γp τ ∈ closedBall c (R₁ : ℝ) := by
      intro τ
      change (L.trans seg) τ ∈ closedBall c (R₁ : ℝ)
      rw [Path.trans_apply]
      split_ifs with h
      · exact closedBall_subset_closedBall hR₀₁ (hLB _)
      · 
        set t : ℝ := ((⟨2 * (τ : ℝ) - 1, by
            constructor <;> nlinarith [τ.2.1, τ.2.2]⟩ : unitInterval) : ℝ)
        change x + ((t : ℝ) : ℂ) * (w - x) ∈ closedBall c (R₁ : ℝ)
        have ht0 : 0 ≤ t := by simp only [t]; nlinarith [τ.2.1]
        have ht1 : t ≤ 1 := by simp only [t]; nlinarith [τ.2.2]
        rw [mem_closedBall, dist_eq_norm]
        have hR0ne : ((R₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR₀.ne'
        have hxc : ‖x - c‖ = R₀ := by rw [← dist_eq_norm]; exact hxs
        have hexp : x + (t : ℂ) * (w - x) - c =
            (((1 : ℝ) + t * ((R₁ : ℝ) / R₀ - 1) : ℝ) : ℂ) * (x - c) := by
          rw [hw]; push_cast; ring
        rw [hexp, norm_mul, Complex.norm_real, hxc, Real.norm_eq_abs]
        have hR0pos : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
        have hq : 0 ≤ (R₁ : ℝ) / R₀ - 1 := by
          rw [sub_nonneg, le_div_iff₀ hR0pos]; linarith
        rw [abs_of_nonneg (add_nonneg zero_le_one (mul_nonneg ht0 hq))]
        have hid : (1 + t * ((R₁ : ℝ) / R₀ - 1)) * R₀ = R₀ + t * (R₁ - R₀) := by
          field_simp
        rw [hid]
        nlinarith
    intro τ hτ
    have := hrange ⟨τ, hτ⟩
    rwa [Path.extend_apply γp hτ]
  · intro τ hτ s hs hEq
    rw [Path.extend_apply γp hτ] at hEq
    change (L.trans seg) ⟨τ, hτ⟩ = P s at hEq
    rw [Path.trans_apply] at hEq
    split_ifs at hEq with h
    · exact hLav _ s hs hEq
    · 
      apply hxN
      refine ⟨s, hsub hs, ?_⟩
      rw [← hEq]
      set t : ℝ := ((⟨2 * τ - 1, by constructor <;> nlinarith [hτ.1, hτ.2]⟩ : unitInterval) : ℝ)
      change dist (x + ((t : ℝ) : ℂ) * (w - x)) x < 2 * C.A_sup * C.r
      have ht0 : 0 ≤ t := by simp only [t]; nlinarith [hτ.1]
      have ht1 : t ≤ 1 := by simp only [t]; nlinarith [hτ.2]
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0]
      have hR0pos : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
      have hxc : ‖x - c‖ = R₀ := by rw [← dist_eq_norm]; exact hxs
      have hwx : w - x = ((((R₁ : ℝ) / R₀ - 1) : ℝ) : ℂ) * (x - c) := by
        rw [hw]; push_cast; ring
      rw [hwx, norm_mul, Complex.norm_real, hxc, Real.norm_eq_abs]
      have hq : 0 ≤ (R₁ : ℝ) / R₀ - 1 := by
        rw [sub_nonneg, le_div_iff₀ hR0pos]; linarith
      rw [abs_of_nonneg hq]
      have hid : ((R₁ : ℝ) / R₀ - 1) * R₀ = R₁ - R₀ := by field_simp
      rw [mul_assoc, hid]
      have : t * ((R₁ : ℝ) - R₀) ≤ (R₁ : ℝ) - R₀ := by
        have : 0 ≤ (R₁ : ℝ) - R₀ := by linarith
        nlinarith
      linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
