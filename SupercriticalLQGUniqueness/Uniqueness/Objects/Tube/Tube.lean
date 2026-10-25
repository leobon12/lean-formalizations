import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.TableK




 


















set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
structure TubeParams where
   
  ρ : ℝ
   
  K : ℕ
   
  α : ℝ
   
  n : ℂ
   
  ψu : ℝ
   
  ψv : ℝ
   
  sp : ℝ
   
  wp : ℝ

 
theorem range_path_map {x y : ℂ} (γ : Path x y) {f : ℂ → ℂ} (hf : Continuous f) :
    range (γ.map hf) = f '' range γ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩

namespace TubeParams

variable (P : TubeParams) (r : ℝ)

 
def ω (k : ℤ) : ℝ := 2 * π * k / P.K

 
def site (k : ℤ) : ℂ := pol (2 * r) (P.ω k)

 
def tangent (k : ℤ) : ℂ := Complex.I * ex (P.ω k)

 
def twist (k : ℤ) : ℝ := Complex.arg (P.tangent k / P.n)

 
def modMap (k : ℤ) (ζ : ℂ) : ℂ := P.site r k + ((P.ρ * r : ℝ) : ℂ) * P.n * ζ

theorem continuous_modMap (k : ℤ) : Continuous (P.modMap r k) := by
  unfold modMap; fun_prop

 
def s : ℝ := P.sp * P.ρ * r

 
def w : ℝ := P.wp * P.ρ * r

 
def block (k : ℤ) : Set ℂ := P.modMap r k '' blockNorm P.α

 
def uC (k : ℤ) : ℂ := P.modMap r k (pol P.α P.ψu)

 
def vC (k : ℤ) : ℂ := P.modMap r k (pol 1 P.ψv)

 
def gatePlus (k : ℤ) : ℂ := P.modMap r k (pol 4 (P.twist k))

 
def gateMinus (k : ℤ) : ℂ := P.modMap r k (pol 4 (P.twist k + π))

 
def outA (k : ℤ) : Path (P.modMap r k (pol (1 + 3 * P.sp / 4) P.ψv)) (P.gatePlus r k) :=
  (outPath P.sp P.ψv (P.twist k)).map (P.continuous_modMap r k)

 
def inA (k : ℤ) : Path (P.gateMinus r k) (P.modMap r k (pol (P.α - 3 * P.sp / 4) P.ψu)) :=
  (inPath P.α P.sp P.ψu (P.twist k)).map (P.continuous_modMap r k)

 
def corridor (k : ℤ) : Path (P.gatePlus r k) (P.gateMinus r (k + 1)) := segPath _ _

 

def connPath (k : ℤ) :
    Path (P.modMap r k (pol (1 + 3 * P.sp / 4) P.ψv)) (P.modMap r (k + 1) (pol (P.α - 3 * P.sp / 4) P.ψu)) :=
  (P.outA r k).trans ((P.corridor r k).trans (P.inA r (k + 1)))

 
def conn (k : ℤ) : Set ℂ := range (P.connPath r k)

 
def tube : Set ℂ :=
  ⋃ k : ℤ, (P.block r k ∪ ball (P.uC r k) (P.s r) ∪ ball (P.vC r k) (P.s r) ∪
    thickening (P.w r) (P.conn r k))

 
def nbhd (Asup : ℝ) : Set ℂ := thickening (Asup * r) (P.tube r)

 

theorem range_outA (k : ℤ) :
    range (P.outA r k) = P.modMap r k '' range (outPath P.sp P.ψv (P.twist k)) :=
  range_path_map _ _

theorem range_inA (k : ℤ) :
    range (P.inA r k) = P.modMap r k '' range (inPath P.α P.sp P.ψu (P.twist k)) :=
  range_path_map _ _

theorem range_corridor (k : ℤ) :
    range (P.corridor r k) ⊆ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1)) :=
  range_segPath_subset _ _

theorem conn_eq (k : ℤ) :
    P.conn r k = range (P.outA r k) ∪ range (P.corridor r k) ∪ range (P.inA r (k + 1)) := by
  simp only [conn, connPath, Path.trans_range, union_assoc]

theorem isOpen_tube_of (hρr : P.ρ * r ≠ 0) (hn : P.n ≠ 0) : IsOpen (P.tube r) := by
  apply isOpen_iUnion
  intro k
  refine ((IsOpen.union (IsOpen.union ?_ isOpen_ball) isOpen_ball)).union isOpen_thickening
  
  have hc : ((P.ρ * r : ℝ) : ℂ) * P.n ≠ 0 := mul_ne_zero (by exact_mod_cast hρr) hn
  have hblock : P.block r k = (fun x => (x - P.site r k) / (((P.ρ * r : ℝ) : ℂ) * P.n)) ⁻¹'
      blockNorm P.α := by
    ext x
    simp only [block, mem_image, mem_preimage, modMap]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      rwa [add_sub_cancel_left, mul_div_cancel_left₀ _ hc]
    · intro hx
      refine ⟨_, hx, ?_⟩
      rw [mul_div_cancel₀ _ hc, add_sub_cancel]
  rw [hblock]
  apply IsOpen.preimage (by fun_prop)
  have h1 : IsOpen {ζ : ℂ | P.α < ‖ζ‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {ζ : ℂ | ‖ζ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have h3 : IsOpen {ζ : ℂ | 0 < ζ.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (h1.inter (h2.inter h3))

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
