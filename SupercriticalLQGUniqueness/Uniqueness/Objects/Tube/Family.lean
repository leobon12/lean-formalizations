import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Bump




 










set_option autoImplicit false

noncomputable section

open Complex Set Metric Real
open scoped Pointwise

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 
def summand (P : TubeParams) (r : ℝ) (k : ℤ) : Set ℂ :=
  P.block r k ∪ ball (P.uC r k) (P.s r) ∪ ball (P.vC r k) (P.s r) ∪ thickening (P.w r) (P.conn r k)

theorem tube_eq_iUnion_summand : P.tube r = ⋃ k : ℤ, P.summand r k := rfl

theorem summand_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.summand r (k + P.K) = P.summand r k := by
  have hu : P.uC r (k + P.K) = P.uC r k := by unfold uC; rw [modMap_add_K hK]
  have hv : P.vC r (k + P.K) = P.vC r k := by unfold vC; rw [modMap_add_K hK]
  have hb : P.block r (k + P.K) = P.block r k := by unfold block; rw [modMap_fun_add_K hK]
  unfold summand; rw [hu, hv, hb, conn_add_K hK]

theorem summand_add_K_mul (hK : (P.K : ℝ) ≠ 0) (m k : ℤ) :
    P.summand r (k + P.K * m) = P.summand r k := by
  induction m using Int.induction_on generalizing k with
  | zero => simp
  | succ m ih =>
    rw [show k + (P.K : ℤ) * (m + 1) = (k + P.K * m) + P.K by ring, summand_add_K hK, ih]
  | pred m ih =>
    have := summand_add_K (r := r) hK (k + P.K * (-m - 1))
    rw [show k + (P.K : ℤ) * (-m - 1) + P.K = k + P.K * (-m) by ring, ih] at this
    exact this.symm

 

theorem tube_eq_biUnion (hKpos : 0 < P.K) :
    P.tube r = ⋃ k ∈ Icc (1 : ℤ) P.K, P.summand r k := by
  have hK : (P.K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hKZ : (0 : ℤ) < P.K := by exact_mod_cast hKpos
  rw [tube_eq_iUnion_summand]
  apply Subset.antisymm
  · intro x hx
    rw [mem_iUnion] at hx
    obtain ⟨k, hx⟩ := hx
    set k' := 1 + (k - 1) % (P.K : ℤ) with hk'
    have h0 : 0 ≤ (k - 1) % (P.K : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : (k - 1) % (P.K : ℤ) < P.K := Int.emod_lt_of_pos _ hKZ
    have hd := Int.mul_ediv_add_emod (k - 1) (P.K : ℤ)
    have hkk : k = k' + P.K * ((k - 1) / P.K) := by rw [hk']; linarith
    rw [hkk, summand_add_K_mul hK] at hx
    exact mem_biUnion (x := k') ⟨by omega, by omega⟩ hx
  · exact iUnion₂_subset fun k _ => subset_iUnion (P.summand r) k

 

theorem modMap_scale (k : ℤ) (ζ : ℂ) : P.modMap r k ζ = r • P.modMap 1 k ζ := by
  unfold modMap site pol
  rw [Complex.real_smul]; push_cast; ring

theorem gatePlus_scale (k : ℤ) : P.gatePlus r k = r • P.gatePlus 1 k := modMap_scale k _

theorem gateMinus_scale (k : ℤ) : P.gateMinus r k = r • P.gateMinus 1 k := modMap_scale k _

theorem connPath_scale (k : ℤ) (t : unitInterval) : P.connPath r k t = r • P.connPath 1 k t := by
  unfold connPath
  simp only [Path.trans_apply]
  split_ifs with h1 h2
  · exact modMap_scale k _
  · simp only [corridor, segPath_apply]
    rw [gatePlus_scale (r := r), gateMinus_scale (r := r)]
    simp only [Complex.real_smul]
    ring
  · exact modMap_scale (k + 1) _

theorem conn_scale (k : ℤ) : P.conn r k = r • P.conn 1 k := by
  ext x
  simp only [conn, mem_smul_set, mem_range]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨_, ⟨t, rfl⟩, (connPath_scale k t).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨t, connPath_scale k t⟩

theorem mem_smul_iff (hr : 0 < r) {S : Set ℂ} {x : ℂ} : x ∈ r • S ↔ r⁻¹ • x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · intro h
    refine ⟨r⁻¹ • x, h, ?_⟩
    show r • (r⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem dist_inv_smul (hr : 0 < r) (x y : ℂ) : dist (r⁻¹ • x) (r⁻¹ • y) = r⁻¹ * dist x y := by
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]

theorem mem_thickening_smul (hr : 0 < r) {δ : ℝ} {S : Set ℂ} {x : ℂ} :
    x ∈ thickening (r * δ) (r • S) ↔ r⁻¹ • x ∈ thickening δ S := by
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [mem_smul_iff hr] at hy
    refine ⟨r⁻¹ • y, hy, ?_⟩
    rw [dist_inv_smul hr, inv_mul_lt_iff₀ hr]; exact hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨r • y, ⟨y, hy, rfl⟩, ?_⟩
    have e : dist x (r • y) = r * dist (r⁻¹ • x) y := by
      calc dist x (r • y) = dist (r • (r⁻¹ • x)) (r • y) := by
            rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        _ = r * dist (r⁻¹ • x) y := by rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
    rw [e]
    exact mul_lt_mul_of_pos_left hxy hr

 
theorem mem_tube_iff (hr : 0 < r) {x : ℂ} : x ∈ P.tube r ↔ r⁻¹ • x ∈ P.tube 1 := by
  have hsr : P.s r = r * P.s 1 := by unfold s; ring
  have hwr : P.w r = r * P.w 1 := by unfold w; ring
  have hball : ∀ c : ℂ, ∀ ρ₀ : ℝ, (x ∈ ball (r • c) (r * ρ₀) ↔ r⁻¹ • x ∈ ball c ρ₀) := by
    intro c ρ₀
    rw [mem_ball, mem_ball]
    have : dist (r⁻¹ • x) c = r⁻¹ * dist x (r • c) := by
      rw [← dist_inv_smul hr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [this, inv_mul_lt_iff₀ hr]
  have hblock : ∀ k, (x ∈ P.block r k ↔ r⁻¹ • x ∈ P.block 1 k) := by
    intro k
    simp only [block, mem_image]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨ζ, hζ, by rw [modMap_scale (r := r), smul_smul, inv_mul_cancel₀ hr.ne', one_smul]⟩
    · rintro ⟨ζ, hζ, h⟩
      exact ⟨ζ, hζ, by rw [modMap_scale (r := r), h, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
  simp only [tube, mem_iUnion, mem_union]
  apply exists_congr
  intro k
  rw [hblock k, hsr, hwr, conn_scale (r := r), mem_thickening_smul hr,
    show P.uC r k = r • P.uC 1 k from modMap_scale k _,
    show P.vC r k = r • P.vC 1 k from modMap_scale k _, hball, hball]

theorem inv_smul_tube (hr : 0 < r) : r⁻¹ • P.tube r = P.tube 1 := by
  ext x
  rw [mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact (mem_tube_iff hr).mp hy
  · intro hx
    refine ⟨r • x, (mem_tube_iff hr).mpr ?_, ?_⟩
    · rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    · rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem mem_nbhd_iff (hr : 0 < r) {A : ℝ} {x : ℂ} : x ∈ P.nbhd r A ↔ r⁻¹ • x ∈ P.nbhd 1 A := by
  unfold nbhd
  have e : P.tube r = r • P.tube 1 := by
    rw [← inv_smul_tube hr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [e, show A * r = r * (A * 1) by ring, mem_thickening_smul hr]

 
theorem bump_scale (hr : 0 < r) (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (y : ℂ) :
    P.bump r Amax A (r • y) = P.bump 1 Amax A y := by
  rw [bump_smul hr.ne', inv_smul_tube hr]
  unfold bump
  rw [inv_one, one_smul, one_smul]

 

theorem finite_shapes {𝓡 : Set ℝ} (h𝓡 : ∀ r ∈ 𝓡, 0 < r) (D : ℝ → TubeParams)
    (hD : (D '' 𝓡).Finite) (A : Set.Ioi (0 : ℝ)) (Amax : ℝ) :
    ((fun r => r⁻¹ • (D r).tube r) '' 𝓡).Finite ∧
    ((fun r => r⁻¹ • (D r).nbhd r A) '' 𝓡).Finite ∧
    ((fun r => fun y : ℂ => (D r).bump r Amax A (r • y)) '' 𝓡).Finite := by
  refine ⟨?_, ?_, ?_⟩
  · apply (hD.image fun Q => Q.tube 1).subset
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨D r, ⟨r, hr, rfl⟩, (inv_smul_tube (h𝓡 r hr)).symm⟩
  · apply (hD.image fun Q => Q.nbhd 1 A).subset
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨D r, ⟨r, hr, rfl⟩, ?_⟩
    ext x
    rw [mem_smul_set]
    constructor
    · intro hx
      refine ⟨r • x, (mem_nbhd_iff (h𝓡 r hr)).mpr ?_, ?_⟩
      · rwa [smul_smul, inv_mul_cancel₀ (h𝓡 r hr).ne', one_smul]
      · rw [smul_smul, inv_mul_cancel₀ (h𝓡 r hr).ne', one_smul]
    · rintro ⟨y, hy, rfl⟩; exact (mem_nbhd_iff (h𝓡 r hr)).mp hy
  · apply (hD.image fun Q => Q.bump 1 Amax A).subset
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨D r, ⟨r, hr, rfl⟩, by funext y; exact (bump_scale (h𝓡 r hr) Amax A y).symm⟩

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
