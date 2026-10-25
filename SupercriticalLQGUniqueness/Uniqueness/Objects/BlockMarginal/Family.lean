import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.S4Table
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.Consumers
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Table




 










set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
def orientations : Finset ℂ := {1, Complex.I, -1, -Complex.I}

 
def radiusRatios (m : ℕ) : Finset ℝ := (Finset.Icc m (2 * m)).image (fun k => (1 / 4 : ℝ) ^ k)

 
def gridHalf (δ : ℝ) : ℕ := ⌊π / 2 / δ⌋₊

 
def gridAngles (δ : ℝ) : Finset ℝ :=
  (Finset.Icc (-(gridHalf δ : ℤ)) (gridHalf δ : ℤ)).image (fun j : ℤ => δ * j)

 
def shapeData (δ : ℝ) (m : ℕ) : Finset (ℝ × ℝ × ℝ) :=
  radiusRatios m ×ˢ (gridAngles δ ×ˢ gridAngles δ)

 
def blockFamily (δ : ℝ) (m : ℕ) : Finset (ℂ × ℝ × ℝ × ℝ) := orientations ×ˢ shapeData δ m

 
def familyParams (lam Aendpt Kann Aloc ρ : ℝ) (x : ℂ × ℝ × ℝ × ℝ) : Objects.Tube.TubeParams where
  ρ := ρ
  K := ⌈lam / (Aloc * ρ)⌉₊
  α := Kann
  n := x.1
  ψu := x.2.2.1
  ψv := x.2.2.2
  sp := x.2.1
  wp := lam * Aendpt

theorem orientation_fourth {n : ℂ} (hn : n ∈ orientations) : n ^ 4 = 1 := by
  simp only [orientations, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · norm_num
  · rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Complex.I_sq]; norm_num
  · norm_num
  · rw [neg_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, Complex.I_sq]; norm_num

theorem orientation_norm {n : ℂ} (hn : n ∈ orientations) : ‖n‖ = 1 := by
  simp only [orientations, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp

theorem gridAngles_mem {δ : ℝ} (hδ : 0 < δ) {ψ : ℝ} (hψ : ψ ∈ gridAngles δ) :
    ψ ∈ Icc (-(π / 2)) (π / 2) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hψ
  rw [Finset.mem_Icc] at hj
  have hJ : (gridHalf δ : ℝ) * δ ≤ π / 2 := by
    have := Nat.floor_le (show 0 ≤ π / 2 / δ by positivity)
    rw [le_div_iff₀ hδ] at this
    exact this
  have h1 : -(gridHalf δ : ℝ) ≤ j := by exact_mod_cast hj.1
  have h2 : (j : ℝ) ≤ gridHalf δ := by exact_mod_cast hj.2
  constructor <;> nlinarith

theorem sqrt_sixteen_pow (m : ℕ) : Real.sqrt ((1 / 16 : ℝ) ^ m) = (1 / 4 : ℝ) ^ m := by
  rw [show (1 / 16 : ℝ) ^ m = ((1 / 4 : ℝ) ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  exact Real.sqrt_sq (by positivity)

theorem radiusRatios_bounds {m : ℕ} {sp : ℝ} (h : sp ∈ radiusRatios m) :
    (1 / 16 : ℝ) ^ m ≤ sp ∧ sp ≤ Real.sqrt ((1 / 16 : ℝ) ^ m) := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
  rw [Finset.mem_Icc] at hk
  rw [sqrt_sixteen_pow]
  constructor
  · rw [show (1 / 16 : ℝ) ^ m = (1 / 4) ^ (2 * m) by rw [pow_mul]; norm_num]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.2
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.1

theorem radiusRatios_pos {m : ℕ} {sp : ℝ} (h : sp ∈ radiusRatios m) : 0 < sp := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 h
  positivity

 
theorem familyParams_selection {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ))
    {x : ℂ × ℝ × ℝ × ℝ} (hx : x ∈ blockFamily (t.lam * Objects.Density.endptScale t.m) t.m) :
    Objects.TubeMesh.TubeSelection (t.toConstants r)
      (familyParams t.lam (Objects.Density.endptScale t.m) Kann (Objects.Density.locScale t.K_sh) t.ρ x) := by
  have hδ : 0 < t.lam * Objects.Density.endptScale t.m := mul_pos t.lam_pos (Objects.Density.endptScale_pos t.m)
  simp only [blockFamily, shapeData, Finset.mem_product] at hx
  obtain ⟨hn, hsp, hu, hv⟩ := hx
  have hspb := radiusRatios_bounds hsp
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
  · exact hspb.1
  · exact hspb.2
  · exact t.ρ_tube
  · rfl
  · rfl
  · rfl
  · exact orientation_fourth hn
  · exact orientation_norm hn
  · exact gridAngles_mem hδ hu
  · exact gridAngles_mem hδ hv
  · rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
