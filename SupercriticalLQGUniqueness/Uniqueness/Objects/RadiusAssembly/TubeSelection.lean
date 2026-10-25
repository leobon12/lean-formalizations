import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Table
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.SelectedParams




 
set_option autoImplicit false
noncomputable section
open Set Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly

 

def tubeParams {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) : Objects.Tube.TubeParams where
  ρ := t.ρ
  K := ⌈t.lam / (Objects.Density.locScale t.K_sh * t.ρ)⌉₊
  α := Kann
  n := 1
  ψu := 0
  ψv := 0
  sp := Objects.Density.endptScale t.m
  wp := t.lam * Objects.Density.endptScale t.m

 
theorem tubeSelection {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    Objects.TubeMesh.TubeSelection (t.toConstants r) (tubeParams t) := by
  have hEnd0 : 0 ≤ Objects.Density.endptScale t.m := (Objects.Density.endptScale_pos t.m).le
  have hEnd1 : Objects.Density.endptScale t.m ≤ 1 := Objects.Density.endptScale_le_one t.m
  have hSqrt : Objects.Density.endptScale t.m ≤ Real.sqrt (Objects.Density.endptScale t.m) := by
    nlinarith [Real.sq_sqrt hEnd0, Real.sqrt_nonneg (Objects.Density.endptScale t.m)]
  constructor
  · change t.lam < 1 / 10 ^ 100
    have h := t.lam_lt_tiny
    norm_num at h ⊢
    exact h
  · change 3 < Objects.Density.locScale t.K_sh
    unfold Objects.Density.locScale
    have h : 1 < (8 : ℝ) ^ t.K_sh := one_lt_pow₀ (by norm_num) (by have := t.K_sh_pos; omega)
    linarith
  · exact t.Kann_gt
  · exact t.Kann_lt
  · exact t.endpt_a
  · exact le_refl _
  · exact hSqrt
  · exact t.ρ_tube
  · rfl
  · rfl
  · rfl
  · norm_num [tubeParams]
  · norm_num [tubeParams]
  · change -(Real.pi / 2) ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  · change -(Real.pi / 2) ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2
    constructor <;> nlinarith [Real.pi_pos]
  · rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
