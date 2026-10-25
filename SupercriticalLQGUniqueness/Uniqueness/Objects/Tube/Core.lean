import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Pieces




 









set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

 

theorem range_segPath (a b : ℂ) : range (segPath a b) = segment ℝ a b := by
  apply Subset.antisymm (range_segPath_subset a b)
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨τ, hτ, rfl⟩ := hz
  refine ⟨⟨τ, hτ⟩, ?_⟩
  rw [segPath_apply]
  simp only [Complex.real_smul]

theorem range_corridor_eq (k : ℤ) :
    range (P.corridor r k) = segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1)) :=
  range_segPath _ _

theorem modMap_fun_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.modMap r (k + P.K) = P.modMap r k := by
  funext ζ; exact modMap_add_K hK k ζ

theorem conn_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.conn r (k + P.K) = P.conn r k := by
  rw [conn_eq, conn_eq, range_outA, range_outA, range_inA, range_inA, range_corridor_eq,
    range_corridor_eq, modMap_fun_add_K hK, twist_add_K hK, show k + P.K + 1 = (k + 1) + P.K by ring,
    modMap_fun_add_K hK, twist_add_K hK]
  unfold gatePlus gateMinus
  rw [modMap_fun_add_K hK, twist_add_K hK, modMap_fun_add_K hK, twist_add_K hK]

theorem piece_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) (a : ℕ) :
    P.piece r Asup (k + P.K) a = P.piece r Asup k a := by
  have hu : ∀ j, P.uC r (j + P.K) = P.uC r j := fun j => by unfold uC; rw [modMap_add_K hK]
  have hv : ∀ j, P.vC r (j + P.K) = P.vC r j := fun j => by unfold vC; rw [modMap_add_K hK]
  have hb : P.block r (k + P.K) = P.block r k := by unfold block; rw [modMap_fun_add_K hK]
  match a with
  | 0 => simp only [piece, βu, hu]
  | 1 => simp only [piece, Ob, βu, βv, hu, hv, hb]
  | 2 => simp only [piece, βv, hv]
  | (n + 3) =>
    simp only [piece, Λc, βu, βv, hu, hv, conn_add_K hK, show k + P.K + 1 = (k + 1) + P.K by ring]

theorem piece_add_K_mul (hK : (P.K : ℝ) ≠ 0) (m : ℤ) (k : ℤ) (a : ℕ) :
    P.piece r Asup (k + P.K * m) a = P.piece r Asup k a := by
  induction m using Int.induction_on generalizing k with
  | zero => simp
  | succ m ih =>
    rw [show k + (P.K : ℤ) * (m + 1) = (k + P.K * m) + P.K by ring, piece_add_K hK, ih]
  | pred m ih =>
    have := piece_add_K (r := r) (Asup := Asup) hK (k + P.K * (-m - 1)) a
    rw [show k + (P.K : ℤ) * (-m - 1) + P.K = k + P.K * (-m) by ring, ih] at this
    exact this.symm

theorem X_add_mul (hK : (P.K : ℝ) ≠ 0) (i m : ℤ) :
    P.X r Asup (i + 4 * (P.K * m)) = P.X r Asup i := by
  unfold X
  have key : ∀ M : ℤ, M = P.K * m → P.piece r Asup ((i + 4 * M) / 4) ((i + 4 * M) % 4).toNat =
      P.piece r Asup (i / 4) (i % 4).toNat := by
    intro M hM
    have h1 : (i + 4 * M) / 4 = i / 4 + M := by omega
    have h2 : (i + 4 * M) % 4 = i % 4 := by omega
    rw [h1, h2, hM, piece_add_K_mul hK]
  exact key _ rfl

 

section Contain

variable (hP : P.Good) (hr : 0 < r)
include hP hr

theorem dist_uC_site (k : ℤ) : dist (P.uC r k) (P.site r k) = P.α * (P.ρ * r) := by
  unfold uC
  rw [dist_modMap_site hP.n_norm (mul_pos hP.ρ_pos hr).le, norm_pol (by linarith [hP.α_gt])]; ring

theorem dist_vC_site (k : ℤ) : dist (P.vC r k) (P.site r k) = P.ρ * r := by
  unfold vC
  rw [dist_modMap_site hP.n_norm (mul_pos hP.ρ_pos hr).le, norm_pol (by norm_num)]; ring

theorem dist_block_site {k : ℤ} {x : ℂ} (hx : x ∈ P.block r k) : dist x (P.site r k) ≤ P.ρ * r := by
  obtain ⟨ζ, hζ, rfl⟩ := hx
  exact (dist_modMap_site_le hP hr k hζ.2.1.le).trans (by linarith)

theorem dist_outA_site {k : ℤ} {x : ℂ} (hx : x ∈ range (P.outA r k)) :
    dist x (P.site r k) ≤ 4 * (P.ρ * r) := by
  rw [range_outA] at hx
  obtain ⟨ζ, hζ, rfl⟩ := hx
  exact dist_modMap_site_le hP hr k
    (norm_le_four_of_mem_outPath hP.sp_pos.le hP.sp_le_two_thirds hζ)

theorem dist_inA_site {k : ℤ} {x : ℂ} (hx : x ∈ range (P.inA r k)) :
    dist x (P.site r k) ≤ 4 * (P.ρ * r) := by
  rw [range_inA] at hx
  obtain ⟨ζ, hζ, rfl⟩ := hx
  exact dist_modMap_site_le hP hr k
    (norm_le_four_of_mem_inPath hP.u_minus_pos hP.sp_pos.le (by linarith [hP.α_lt]) hζ)

 
theorem s_le (hA : 100 * Asup ≤ P.sp * P.ρ) :
    P.s r ≤ P.ρ * r / 400 ∧ 100 * (Asup * r) ≤ P.s r ∧ 100 * P.w r ≤ P.s r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  refine ⟨?_, ?_, ?_⟩
  · unfold s; nlinarith [hP.sp_le']
  · unfold s; nlinarith
  · unfold s w; nlinarith [hP.wp_le]

theorem dist_piece_site_le (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ) {k : ℤ} {a : ℕ}
    (ha : a ≤ 2) {x : ℂ} (hx : x ∈ P.piece r Asup k a) : dist x (P.site r k) ≤ 2 * (P.ρ * r) := by
  obtain ⟨hs1, hs2, -⟩ := s_le hP hr hA
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hα1 := hP.α_lt
  have hα0 : 0 ≤ P.α := by linarith [hP.α_gt]
  interval_cases a
  · have h := mem_ball.mp hx
    have := dist_triangle x (P.uC r k) (P.site r k)
    rw [dist_uC_site hP hr] at this
    nlinarith
  · obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx.1
    have := dist_triangle x y (P.site r k)
    have := dist_block_site hP hr hy
    nlinarith [mul_pos hA0 hr]
  · have h := mem_ball.mp hx
    have := dist_triangle x (P.vC r k) (P.site r k)
    rw [dist_vC_site hP hr] at this
    nlinarith

end Contain

 

section Far

variable (hP : P.Good) (hr : 0 < r)
include hP hr

 
theorem far_of_sectors {x y : ℂ} {a b c d : ℝ}
    (hx : InSector x (2 * r - 11 * (P.ρ * r)) a b) (hy : InSector y (2 * r - 11 * (P.ρ * r)) c d)
    (h1 : π / P.K ≤ c - b) (h2 : π / P.K ≤ a + 2 * π - d) : 100 * (P.ρ * r) ≤ dist x y := by
  have hK := hP.K_pos
  have hρ := hP.ρ_le
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hm0 : 0 ≤ 2 * r - 11 * (P.ρ * r) := by nlinarith
  have hγ0 : 0 ≤ π / P.K := by positivity
  have hγπ : π / P.K ≤ π := by
    rw [div_le_iff₀ hK]; nlinarith [Real.pi_pos, hP.K_ge]
  have := dist_ge_of_sectors hm0 hx hy hγ0 hγπ h1 h2
  have e : 2 * (2 * r - 11 * (P.ρ * r)) * (π / P.K) / π = 2 * (2 * r - 11 * (P.ρ * r)) / P.K := by
    field_simp
  rw [e] at this
  have hfar : 100 * (P.ρ * r) ≤ 2 * (2 * r - 11 * (P.ρ * r)) / P.K := by
    rw [le_div_iff₀ hK]
    have := hP.ρK_le
    nlinarith
  linarith

theorem inSector_near_site' {k : ℤ} {x : ℂ} (hx : dist x (P.site r k) ≤ 5 * (P.ρ * r)) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω k - 5 * P.ρ) (P.ω k + 5 * P.ρ) :=
  (inSector_of_near_site hP hr k hx).mono (by nlinarith [hP.ρ_pos]) le_rfl le_rfl

 
theorem inSector_near_corridor {k : ℤ} {x ℓ : ℂ}
    (hℓ : ℓ ∈ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1))) (hx : dist x ℓ ≤ P.ρ * r / 2) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω k - P.ρ) (P.ω (k + 1) + P.ρ) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hρ := hP.ρ_le
  obtain ⟨R, hR, φ, hφ, rfl⟩ := corridor_inSector hP hr k hℓ
  have hc := two_r_cos_ge hP hr
  have hR' : 2 * r - 10 * (P.ρ * r) ≤ R := le_trans hc hR
  have hRpos : 0 < R := by nlinarith
  have h := inSector_of_near (R := R) (θ := φ) (ε := P.ρ * r / 2) hRpos (by positivity)
    (by nlinarith) hx
  have hq : 2 * (P.ρ * r / 2) / R ≤ P.ρ := by
    rw [div_le_iff₀ hRpos]; nlinarith [hP.ρ_pos]
  exact h.mono (by linarith) (by linarith [hφ.1]) (by linarith [hφ.2])

theorem far_site_site {j : ℤ} {x y : ℂ} (hx : dist x (P.site r j) ≤ 5 * (P.ρ * r))
    (hy : dist y (P.site r (j + 1)) ≤ 5 * (P.ρ * r)) : 100 * (P.ρ * r) ≤ dist x y := by
  have hω := ω_add_one (P := P) hP.K_ne j
  have h10 := hP.pi_div_K_ge
  have hKge := hP.K_ge
  have hK := hP.K_pos
  have hpk : π / P.K ≤ π / 100 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hKge
  have e2 : 2 * π / P.K = 2 * (π / P.K) := by ring
  apply far_of_sectors hP hr (inSector_near_site' hP hr hx) (inSector_near_site' hP hr hy)
  · rw [hω]; nlinarith [hP.ρ_pos, Real.pi_pos]
  · rw [hω]; nlinarith [hP.ρ_pos, Real.pi_pos]

theorem far_site_site2 {j : ℤ} {x y : ℂ} (hx : dist x (P.site r j) ≤ 5 * (P.ρ * r))
    (hy : dist y (P.site r (j + 2)) ≤ 5 * (P.ρ * r)) : 100 * (P.ρ * r) ≤ dist x y := by
  have hω1 := ω_add_one (P := P) hP.K_ne j
  have hω2 := ω_add_one (P := P) hP.K_ne (j + 1)
  rw [show j + 1 + 1 = j + 2 by ring] at hω2
  have h10 := hP.pi_div_K_ge
  have hKge := hP.K_ge
  have hK := hP.K_pos
  have hpk : π / P.K ≤ π / 100 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hKge
  have e2 : 2 * π / P.K = 2 * (π / P.K) := by ring
  apply far_of_sectors hP hr (inSector_near_site' hP hr hx) (inSector_near_site' hP hr hy)
  · rw [hω2, hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]
  · rw [hω2, hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]

theorem far_site_corridor {j : ℤ} {x y ℓ : ℂ} (hx : dist x (P.site r j) ≤ 5 * (P.ρ * r))
    (hℓ : ℓ ∈ segment ℝ (P.gatePlus r (j + 1)) (P.gateMinus r (j + 1 + 1)))
    (hy : dist y ℓ ≤ P.ρ * r / 2) : 100 * (P.ρ * r) ≤ dist x y := by
  have hω1 := ω_add_one (P := P) hP.K_ne j
  have hω2 := ω_add_one (P := P) hP.K_ne (j + 1)
  have h10 := hP.pi_div_K_ge
  have hKge := hP.K_ge
  have hK := hP.K_pos
  have hpk : π / P.K ≤ π / 100 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hKge
  have e2 : 2 * π / P.K = 2 * (π / P.K) := by ring
  apply far_of_sectors hP hr (inSector_near_site' hP hr hx) (inSector_near_corridor hP hr hℓ hy)
  · rw [hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]
  · rw [hω2, hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]

theorem far_corridor_site {j : ℤ} {x y ℓ : ℂ}
    (hℓ : ℓ ∈ segment ℝ (P.gatePlus r j) (P.gateMinus r (j + 1))) (hx : dist x ℓ ≤ P.ρ * r / 2)
    (hy : dist y (P.site r (j + 2)) ≤ 5 * (P.ρ * r)) : 100 * (P.ρ * r) ≤ dist x y := by
  have hω1 := ω_add_one (P := P) hP.K_ne j
  have hω2 := ω_add_one (P := P) hP.K_ne (j + 1)
  rw [show j + 1 + 1 = j + 2 by ring] at hω2
  have h10 := hP.pi_div_K_ge
  have hKge := hP.K_ge
  have hK := hP.K_pos
  have hpk : π / P.K ≤ π / 100 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hKge
  have e2 : 2 * π / P.K = 2 * (π / P.K) := by ring
  apply far_of_sectors hP hr (inSector_near_corridor hP hr hℓ hx) (inSector_near_site' hP hr hy)
  · rw [hω2, hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]
  · rw [hω2, hω1]; nlinarith [hP.ρ_pos, Real.pi_pos]

end Far

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
