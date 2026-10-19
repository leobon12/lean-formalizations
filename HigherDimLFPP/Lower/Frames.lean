import HigherDimLFPP.Core.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Orthogonal frames and similarities in `ℝ^d` (lower comparison, source §5.2–§5.3)

Deterministic geometry of the lower comparison (packet P-L1, target T2; ruling H6; audit HA4,
"Details for later use" D2, finding HA4-2).

* `horiz z = ⟪e₁, z⟫` and `transv z = z - horiz z • e₁`: horizontal coordinate and transverse
  part of a point of `ℝ^d`; `embedT : ℝ^{d-1} → ℝ^d`, `y ↦ (0, y)`, the transverse embedding.
* `edgeRot u`: the reflection in `(e₁ - u)ᗮ`.  It is a linear isometry of `ℝ^d` with
  `edgeRot u e₁ = u` for every unit vector `u` (Mathlib `Submodule.reflection_sub`), so every
  unit vector is the image of `e₁` under an orthogonal frame (`exists_frame`).  The source's
  "minimal rotation" is replaced by an arbitrary orthogonal frame with `O e₁ = u`: the only
  properties used are `‖O y‖ = ‖y‖` and the horizontal bound
  `|⟪e₁, O y⟫| ≤ ‖O e₁ - e₁‖ ‖y‖` for `y ⊥ e₁` (`abs_inner_map_le_of_inner_eq_zero`, HA4's
  Lean-checked `horiz_bound_of_orth`, here for every orthogonal map and every real inner
  product space).
* `SimD d`: similarities `z ↦ b + r • O z` of `ℝ^d`; `SimD.comp` composes them,
  `(S.comp T).app = S.app ∘ T.app` (`SimD.app_comp`), and the frame of a composite is
  `O_child = O_parent ∘ O_local` (`SimD.comp_O_apply`).  These are the recursive frames of
  source §5.3 (HA4 D7).
* `edgeSim q v i`: the similarity of ratio `q` carrying the unit segment `[0, e₁]` onto the
  edge `[v i, v (i+1)]` of a polygon whose edges have length `q`, with frame
  `edgeRot (q⁻¹ • (v (i+1) - v i))`.

2D source: `LQGDimension/LFPP/BlockConstructionAux1.lean` (`app`, `comp`, `app_comp`,
`app_sub`), where a similarity of `ℂ` is `z ↦ α z + β`.  In `ℝ^d` an edge determines its
frame only up to the stabilizer of `e₁`, so a frame is chosen per edge and frames are composed.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The unit vector `e₁` -/

theorem e₁_ofLp (i : Fin d) : (e₁ d).ofLp i = if (i : ℕ) = 0 then 1 else 0 := rfl

/-- `⟪e₁, z⟫ = z₁`. -/
theorem inner_e₁_left (hd : 0 < d) (z : Rd d) : ⟪e₁ d, z⟫ = z.ofLp ⟨0, hd⟩ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [e₁_ofLp]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [e₁_ofLp, hi']
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem norm_e₁ (hd : 0 < d) : ‖e₁ d‖ = 1 := by
  have h : ‖e₁ d‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_e₁_left hd, e₁_ofLp]
    simp
  have h0 : 0 ≤ ‖e₁ d‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖e₁ d‖ - 1), sq_nonneg (‖e₁ d‖ + 1)]

theorem inner_e₁_self (hd : 0 < d) : ⟪e₁ d, e₁ d⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₁ hd, one_pow]

/-! ## Horizontal and transverse parts -/

/-- Horizontal coordinate `z₁ = ⟪e₁, z⟫`. -/
def horiz (z : Rd d) : ℝ := ⟪e₁ d, z⟫

/-- Transverse part `z - z₁ e₁`. -/
def transv (z : Rd d) : Rd d := z - horiz z • e₁ d

theorem horiz_apply (hd : 0 < d) (z : Rd d) : horiz z = z.ofLp ⟨0, hd⟩ := inner_e₁_left hd z

theorem horiz_add (z w : Rd d) : horiz (z + w) = horiz z + horiz w := inner_add_right _ _ _

theorem horiz_sub (z w : Rd d) : horiz (z - w) = horiz z - horiz w := inner_sub_right _ _ _

theorem horiz_smul (c : ℝ) (z : Rd d) : horiz (c • z) = c * horiz z := real_inner_smul_right _ _ _

theorem horiz_neg (z : Rd d) : horiz (-z) = -horiz z := inner_neg_right _ _

theorem horiz_zero : horiz (0 : Rd d) = 0 := inner_zero_right _

theorem horiz_e₁ (hd : 0 < d) : horiz (e₁ d) = 1 := inner_e₁_self hd

theorem horiz_smul_e₁ (hd : 0 < d) (c : ℝ) : horiz (c • e₁ d) = c := by
  rw [horiz_smul, horiz_e₁ hd, mul_one]

theorem abs_horiz_le (z : Rd d) (hd : 0 < d) : |horiz z| ≤ ‖z‖ := by
  have := abs_real_inner_le_norm (e₁ d) z
  rwa [norm_e₁ hd, one_mul] at this

theorem transv_add (z w : Rd d) : transv (z + w) = transv z + transv w := by
  simp only [transv, horiz_add, add_smul]
  abel

theorem transv_sub (z w : Rd d) : transv (z - w) = transv z - transv w := by
  simp only [transv, horiz_sub, sub_smul]
  abel

theorem transv_smul (c : ℝ) (z : Rd d) : transv (c • z) = c • transv z := by
  simp only [transv, horiz_smul, smul_sub, smul_smul]

theorem transv_zero : transv (0 : Rd d) = 0 := by
  simp [transv, horiz_zero]

theorem transv_smul_e₁ (hd : 0 < d) (c : ℝ) : transv (c • e₁ d) = 0 := by
  rw [transv, horiz_smul_e₁ hd, sub_self]

theorem horiz_add_transv (z : Rd d) : horiz z • e₁ d + transv z = z := by
  simp only [transv]
  abel

theorem horiz_transv (hd : 0 < d) (z : Rd d) : horiz (transv z) = 0 := by
  rw [transv, horiz_sub, horiz_smul_e₁ hd, sub_self]

/-- Pythagoras: `‖z‖² = z₁² + ‖z_⊥‖²`. -/
theorem norm_sq_eq_horiz_sq_add (hd : 0 < d) (z : Rd d) :
    ‖z‖ ^ 2 = horiz z ^ 2 + ‖transv z‖ ^ 2 := by
  have h := norm_add_sq_real (horiz z • e₁ d) (transv z)
  rw [horiz_add_transv] at h
  have h0 : ⟪horiz z • e₁ d, transv z⟫ = 0 := by
    rw [real_inner_smul_left]
    have : ⟪e₁ d, transv z⟫ = 0 := horiz_transv hd z
    rw [this, mul_zero]
  rw [h, h0, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_transv_le (hd : 0 < d) (z : Rd d) : ‖transv z‖ ≤ ‖z‖ := by
  have h := norm_sq_eq_horiz_sq_add hd z
  have h1 : ‖transv z‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (horiz z)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- The transverse part of `x e₁ + w`, `w ⊥ e₁`, is `w`. -/
theorem transv_smul_e₁_add (hd : 0 < d) (c : ℝ) {w : Rd d} (hw : horiz w = 0) :
    transv (c • e₁ d + w) = w := by
  rw [transv, horiz_add, hw, horiz_smul_e₁ hd, add_zero]
  abel

/-- Off the first coordinate, a point and its transverse part agree. -/
theorem transv_ofLp (z : Rd d) {i : Fin d} (hi : (i : ℕ) ≠ 0) :
    (transv z).ofLp i = z.ofLp i := by
  simp only [transv, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, e₁_ofLp,
    hi, ↓reduceIte, smul_zero, sub_zero]

theorem abs_ofLp_le_norm_transv (z : Rd d) {i : Fin d} (hi : (i : ℕ) ≠ 0) :
    |z.ofLp i| ≤ ‖transv z‖ := by
  rw [← transv_ofLp z hi, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (transv z) i

/-! ## The transverse embedding `ℝ^{d-1} → ℝ^d` -/

/-- `y ↦ (0, y)`: the transverse embedding `ℝ^{d-1} → ℝ^d` (coordinate `0` is horizontal). -/
def embedT (y : Rd (d - 1)) : Rd d :=
  WithLp.toLp 2 (fun i : Fin d =>
    if h : (i : ℕ) = 0 then 0 else y.ofLp ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)

theorem embedT_ofLp (y : Rd (d - 1)) (i : Fin d) :
    (embedT y).ofLp i =
      if h : (i : ℕ) = 0 then 0 else y.ofLp ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := rfl

theorem embedT_add (y y' : Rd (d - 1)) : embedT (y + y') = (embedT y + embedT y' : Rd d) := by
  ext i
  simp only [embedT_ofLp, WithLp.ofLp_add, Pi.add_apply]
  split_ifs <;> simp

theorem embedT_smul (c : ℝ) (y : Rd (d - 1)) : embedT (c • y) = (c • embedT y : Rd d) := by
  ext i
  simp only [embedT_ofLp, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem embedT_zero : embedT (0 : Rd (d - 1)) = (0 : Rd d) := by
  have := embedT_smul (d := d) 0 0
  rwa [zero_smul, zero_smul] at this

theorem embedT_sub (y y' : Rd (d - 1)) : embedT (y - y') = (embedT y - embedT y' : Rd d) := by
  ext i
  simp only [embedT_ofLp, WithLp.ofLp_sub, Pi.sub_apply]
  split_ifs <;> simp

theorem horiz_embedT (hd : 0 < d) (y : Rd (d - 1)) : horiz (embedT y : Rd d) = 0 := by
  rw [horiz_apply hd, embedT_ofLp]
  simp

/-- `embedT` is an isometry. -/
theorem norm_embedT (y : Rd (d - 1)) : ‖(embedT y : Rd d)‖ = ‖y‖ := by
  have key : ‖(embedT y : Rd d)‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
      rw [Fin.sum_univ_succ]
      simp [embedT_ofLp, Fin.val_succ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

theorem transv_embedT (hd : 0 < d) (y : Rd (d - 1)) : transv (embedT y : Rd d) = embedT y := by
  rw [transv, horiz_embedT hd, zero_smul, sub_zero]

/-- A point `x e₁ + (0, y)`: its horizontal coordinate is `x` and its transverse part `(0, y)`. -/
theorem horiz_smul_e₁_add_embedT (hd : 0 < d) (x : ℝ) (y : Rd (d - 1)) :
    horiz (x • e₁ d + embedT y) = x := by
  rw [horiz_add, horiz_smul_e₁ hd, horiz_embedT hd, add_zero]

theorem transv_smul_e₁_add_embedT (hd : 0 < d) (x : ℝ) (y : Rd (d - 1)) :
    transv (x • e₁ d + embedT y) = embedT y :=
  transv_smul_e₁_add hd x (horiz_embedT hd y)

/-- `‖x e₁ + (0, y)‖² = x² + ‖y‖²`. -/
theorem norm_sq_smul_e₁_add_embedT (hd : 0 < d) (x : ℝ) (y : Rd (d - 1)) :
    ‖x • e₁ d + embedT y‖ ^ 2 = x ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_eq_horiz_sq_add hd, horiz_smul_e₁_add_embedT hd, transv_smul_e₁_add_embedT hd,
    norm_embedT]

/-- The coordinate form `(x, y) ↦ (x, y₁, …, y_{d-1})` used in source §3 (`Fin.cons`). -/
theorem toLp_cons_eq (m : ℕ) (x : ℝ) (y : Rd m) :
    (WithLp.toLp 2 (Fin.cons x y.ofLp : Fin (m + 1) → ℝ) : Rd (m + 1)) =
      x • e₁ (m + 1) + embedT (d := m + 1) y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [embedT_ofLp, e₁_ofLp]
  · simp [embedT_ofLp, e₁_ofLp, Fin.val_succ]

/-! ## The horizontal bound for orthogonal frames (HA4 D2) -/

/-- **Horizontal bound for an arbitrary orthogonal map** (HA4 D2, `horiz_bound_of_orth`): if
`‖e‖ = 1` and `y ⊥ e`, then `|⟪e, O y⟫| ≤ ‖O e - e‖ ‖y‖`. -/
theorem abs_inner_map_le_of_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (O : E ≃ₗᵢ[ℝ] E) {e y : E} (he : ‖e‖ = 1) (hy : ⟪e, y⟫ = 0) :
    |⟪e, O y⟫| ≤ ‖O e - e‖ * ‖y‖ := by
  set w := O.symm e with hw_def
  have key : ⟪e, O y⟫ = ⟪w, y⟫ := by
    have := O.inner_map_map w y
    rw [hw_def, LinearIsometryEquiv.apply_symm_apply] at this
    rw [this]
  have hw : ‖w‖ = 1 := by rw [hw_def, LinearIsometryEquiv.norm_map, he]
  set c := ⟪w, e⟫ with hc_def
  have hc : ⟪O e, e⟫ = c := by
    have := O.inner_map_map w e
    rw [hw_def, LinearIsometryEquiv.apply_symm_apply] at this
    rw [hc_def, ← this, real_inner_comm]
  have h1 : ⟪w, y⟫ = ⟪w - c • e, y⟫ := by
    rw [inner_sub_left, real_inner_smul_left, hy, mul_zero, sub_zero]
  have h2 : ‖w - c • e‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, hw, norm_smul, he, real_inner_smul_right, Real.norm_eq_abs, ← hc_def]
    rw [mul_one, sq_abs]
    ring
  have h3 : ‖O e - e‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, he, hc]
    ring
  have h4 : ‖w - c • e‖ ≤ ‖O e - e‖ := by
    have hc1 : c ≤ 1 := by
      have := real_inner_le_norm w e
      rw [hw, he] at this
      linarith
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [h2, h3]
    nlinarith [sq_nonneg (1 - c)]
  rw [key, h1]
  calc |⟪w - c • e, y⟫| ≤ ‖w - c • e‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖O e - e‖ * ‖y‖ := by gcongr

/-- The horizontal bound in `ℝ^d`: for `y ⊥ e₁`, `|(O y)₁| ≤ ‖O e₁ - e₁‖ ‖y‖`. -/
theorem abs_horiz_map_le (hd : 0 < d) (O : Rd d ≃ₗᵢ[ℝ] Rd d) {y : Rd d} (hy : horiz y = 0) :
    |horiz (O y)| ≤ ‖O (e₁ d) - e₁ d‖ * ‖y‖ :=
  abs_inner_map_le_of_inner_eq_zero O (norm_e₁ hd) hy

/-- The horizontal bound for a frame with `O e₁ = u` and `‖u - e₁‖ ≤ θ`, applied to a general
vector: `|(O w)₁ - w₁ u₁| ≤ θ ‖w_⊥‖`. -/
theorem abs_horiz_map_sub_le (hd : 0 < d) (O : Rd d ≃ₗᵢ[ℝ] Rd d) {u : Rd d}
    (hu : O (e₁ d) = u) {θ : ℝ} (hθ : ‖u - e₁ d‖ ≤ θ) (w : Rd d) :
    |horiz (O w) - horiz w * horiz u| ≤ θ * ‖transv w‖ := by
  have hw : O w = horiz w • u + O (transv w) := by
    conv_lhs => rw [← horiz_add_transv w]
    rw [map_add, map_smul, hu]
  have h1 : horiz (O w) - horiz w * horiz u = horiz (O (transv w)) := by
    rw [hw, horiz_add, horiz_smul]
    ring
  rw [h1]
  calc |horiz (O (transv w))| ≤ ‖O (e₁ d) - e₁ d‖ * ‖transv w‖ :=
        abs_horiz_map_le hd O (horiz_transv hd w)
    _ ≤ θ * ‖transv w‖ := by
        rw [hu]
        exact mul_le_mul_of_nonneg_right hθ (norm_nonneg _)

/-! ## Frames: `O e₁ = u` -/

/-- The frame `O_u`: the reflection in `(e₁ - u)ᗮ`. -/
def edgeRot (u : Rd d) : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (e₁ d - u))ᗮ.reflection

/-- `O_u e₁ = u` for every unit vector `u` (`Submodule.reflection_sub`). -/
theorem edgeRot_e₁ (hd : 0 < d) {u : Rd d} (hu : ‖u‖ = 1) : edgeRot u (e₁ d) = u :=
  Submodule.reflection_sub (by rw [norm_e₁ hd, hu])

/-- Every unit vector is the image of `e₁` under an orthogonal frame. -/
theorem exists_frame (hd : 0 < d) {u : Rd d} (hu : ‖u‖ = 1) :
    ∃ O : Rd d ≃ₗᵢ[ℝ] Rd d, O (e₁ d) = u :=
  ⟨edgeRot u, edgeRot_e₁ hd hu⟩

/-! ## Similarities `z ↦ b + r • O z` -/

/-- A similarity `z ↦ b + r • O z` of `ℝ^d` (frame `O`, ratio `r`, translation `b`). -/
structure SimD (d : ℕ) where
  /-- The orthogonal frame. -/
  O : Rd d ≃ₗᵢ[ℝ] Rd d
  /-- The dilation ratio. -/
  r : ℝ
  /-- The translation, i.e. the image of `0`. -/
  b : Rd d

namespace SimD

/-- The action `z ↦ b + r • O z`. -/
def app (S : SimD d) (z : Rd d) : Rd d := S.b + S.r • S.O z

/-- Composition: `(S.comp T).app = S.app ∘ T.app`; the frame of the composite is
`O_S ∘ O_T`. -/
def comp (S T : SimD d) : SimD d := ⟨T.O.trans S.O, S.r * T.r, S.b + S.r • S.O T.b⟩

/-- The identity similarity. -/
def id : SimD d := ⟨LinearIsometryEquiv.refl ℝ (Rd d), 1, 0⟩

theorem app_def (S : SimD d) (z : Rd d) : S.app z = S.b + S.r • S.O z := rfl

theorem app_zero (S : SimD d) : S.app 0 = S.b := by
  simp [app]

theorem app_comp (S T : SimD d) (z : Rd d) : (S.comp T).app z = S.app (T.app z) := by
  simp only [app, comp, LinearIsometryEquiv.coe_trans, Function.comp_apply, map_add, map_smul,
    smul_add, smul_smul]
  abel

theorem comp_O_apply (S T : SimD d) (z : Rd d) : (S.comp T).O z = S.O (T.O z) := rfl

theorem comp_r (S T : SimD d) : (S.comp T).r = S.r * T.r := rfl

theorem comp_b (S T : SimD d) : (S.comp T).b = S.b + S.r • S.O T.b := rfl

theorem app_id (z : Rd d) : (id : SimD d).app z = z := by
  simp [app, id]

theorem ext' {S T : SimD d} (hO : S.O = T.O) (hr : S.r = T.r) (hb : S.b = T.b) : S = T := by
  cases S
  cases T
  simp only at hO hr hb
  subst hO hr hb
  rfl

theorem comp_assoc (S T U : SimD d) : (S.comp T).comp U = S.comp (T.comp U) := by
  refine ext' ?_ ?_ ?_
  · rfl
  · simp only [comp]
    ring
  · simp only [comp, LinearIsometryEquiv.coe_trans, Function.comp_apply, map_add, map_smul,
      smul_add, smul_smul, add_assoc]

theorem id_comp (S : SimD d) : (id : SimD d).comp S = S := by
  refine ext' ?_ ?_ ?_
  · exact LinearIsometryEquiv.trans_refl S.O
  · simp [comp, id]
  · simp [comp, id]

theorem comp_id (S : SimD d) : S.comp (id : SimD d) = S := by
  refine ext' ?_ ?_ ?_
  · exact LinearIsometryEquiv.refl_trans S.O
  · simp [comp, id]
  · simp [comp, id]

theorem app_sub (S : SimD d) (z w : Rd d) : S.app z - S.app w = S.r • S.O (z - w) := by
  simp only [app, map_sub, smul_sub]
  abel

/-- A similarity multiplies distances by `|r|`. -/
theorem norm_app_sub (S : SimD d) (z w : Rd d) : ‖S.app z - S.app w‖ = |S.r| * ‖z - w‖ := by
  rw [app_sub, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]

/-- Similarities are affine: they preserve the segment parametrization. -/
theorem app_add_smul_sub (S : SimD d) (z w : Rd d) (t : ℝ) :
    S.app (z + t • (w - z)) = S.app z + t • (S.app w - S.app z) := by
  rw [app_sub]
  simp only [app, map_add, map_smul, smul_add, smul_smul, mul_comm t S.r]
  rw [← smul_smul, ← map_smul S.O t (w - z)]
  abel

theorem continuous_app (S : SimD d) : Continuous S.app := by
  unfold app
  fun_prop

end SimD

/-! ## Edge similarities of a polygon with common edge length `q` -/

/-- The similarity `T_i` of ratio `q` carrying `[0, e₁]` onto the edge `[v i, v (i+1)]`, with
frame `edgeRot (q⁻¹ • (v (i+1) - v i))`. -/
def edgeSim (q : ℝ) (v : ℕ → Rd d) (i : ℕ) : SimD d :=
  ⟨edgeRot (q⁻¹ • (v (i + 1) - v i)), q, v i⟩

theorem edgeSim_r (q : ℝ) (v : ℕ → Rd d) (i : ℕ) : (edgeSim q v i).r = q := rfl

theorem edgeSim_b (q : ℝ) (v : ℕ → Rd d) (i : ℕ) : (edgeSim q v i).b = v i := rfl

theorem edgeSim_app_zero (q : ℝ) (v : ℕ → Rd d) (i : ℕ) : (edgeSim q v i).app 0 = v i :=
  SimD.app_zero _

/-- The normalized edge direction is a unit vector. -/
theorem norm_edgeDir {q : ℝ} (hq : 0 < q) {v : ℕ → Rd d} {i : ℕ}
    (hlen : ‖v (i + 1) - v i‖ = q) : ‖q⁻¹ • (v (i + 1) - v i)‖ = 1 := by
  rw [norm_smul, hlen, Real.norm_eq_abs, abs_inv, abs_of_pos hq, inv_mul_cancel₀ hq.ne']

/-- The frame of `T_i` sends `e₁` to the edge direction. -/
theorem edgeSim_O_e₁ (hd : 0 < d) {q : ℝ} (hq : 0 < q) {v : ℕ → Rd d} {i : ℕ}
    (hlen : ‖v (i + 1) - v i‖ = q) :
    (edgeSim q v i).O (e₁ d) = q⁻¹ • (v (i + 1) - v i) :=
  edgeRot_e₁ hd (norm_edgeDir hq hlen)

/-- `T_i (t e₁) = v i + t (v (i+1) - v i)`. -/
theorem edgeSim_app_smul_e₁ (hd : 0 < d) {q : ℝ} (hq : 0 < q) {v : ℕ → Rd d} {i : ℕ}
    (hlen : ‖v (i + 1) - v i‖ = q) (t : ℝ) :
    (edgeSim q v i).app (t • e₁ d) = v i + t • (v (i + 1) - v i) := by
  rw [SimD.app_def, map_smul, edgeSim_O_e₁ hd hq hlen, edgeSim_r, edgeSim_b, smul_smul,
    smul_smul, mul_comm q t, mul_assoc, mul_inv_cancel₀ hq.ne', mul_one]

theorem edgeSim_app_e₁ (hd : 0 < d) {q : ℝ} (hq : 0 < q) {v : ℕ → Rd d} {i : ℕ}
    (hlen : ‖v (i + 1) - v i‖ = q) : (edgeSim q v i).app (e₁ d) = v (i + 1) := by
  have := edgeSim_app_smul_e₁ hd hq hlen 1
  rw [one_smul, one_smul] at this
  rw [this]
  abel

end HigherDimLFPP.Lower
