import MatedCRTHarmonic.GMSMain.T16DDirichlet

/-!
# The Tutte embedding of `G^ε(D)` with identity boundary data

Source: [18] , `[18]`: "let `Φ^ε_1` be the function `f_ε` from above
with `f(z) = Re z` and let `Φ^ε_2` be defined analogously with `f(z) = Im z`. Then `Φ^ε := (Φ^ε_1, Φ^ε_2) :
V(G^ε(D)) → ℝ²` is discrete harmonic on the interior of `G^ε(D)` and approximates the map `x ↦ η(x)` on
`V(G^ε(∂D))`. The function `Φ^ε` is called the Tutte embedding of `G^ε(D)` with identity boundary data."
We identify `ℝ²` with `ℂ` (the Euclidean norm of `ℝ²` is the modulus).

For a cellular embedding `H` of a locally finite multigraph `G` and `D ⊂ ℂ`:

* `tutteRe H D`, `tutteIm H D`: the walk solutions (`dirichletSol`) of (1.6) for `f = Re`, `f = Im`, and
  `tutte H D x = tutteRe H D x + i tutteIm H D x`.
* `isCellDirichletSolution_tutteRe`, `..._tutteIm`: they are the functions `f_ε` of (1.6) for `Re`, `Im`;
  `tutte_unique`: for a connected `G` and bounded open `D`, every `Φ' : V → ℂ` whose coordinates are such functions
  agrees with `tutte H D` on `V(G(D))` (so "the" Tutte embedding is well defined);
  `tutteRe_eq_integral`, `tutteIm_eq_integral`: the walk representation `Φ(x) = E_x[Φ(X_τ)]`, coordinatewise.
* `norm_tutte_sub_le` (**"approximates `x ↦ η(x)` on `V(G^ε(∂D))`"**): for `x` whose cell meets `∂D` and every
  `z ∈ H_x` (in the model, `z = η(x)`), `‖Φ(x) − z‖ ≤ 2 diam(H_x)`.
* `abs_tutteRe_le`, `abs_tutteIm_le`: for `D ⊂ B_ρ(0)`, both coordinates of `Φ` on `V(G(D))` lie in `[−ρ, ρ]`
  (maximum principle).
* `norm_tutte_sub_le_of_holder` (**deterministic core of [18] Corollary 1.6**): if both coordinates satisfy the Hölder
  bound (1.9) of [18] Theorem 1.5 on `V(G(D))` with marked points `p x ∈ H_x` and every cell of `V(G(D))` has diameter
  `≤ δ`, every edge `{x, y}` of `G(D)` has `‖Φ(x) − Φ(y)‖ ≤ (A₁ + A₂) max(ε, 2δ)^ξ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open LFMultigraph Harmonic HarmonicInfinity Markov GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- `Φ¹`: the function `f_ε` of [18] (1.6) for `f = Re` (the walk solution). -/
def tutteRe (D : Set ℂ) : V → ℝ := dirichletSol G (vBd H D) (bdryVal H D Complex.re)

/-- `Φ²`: the function `f_ε` of [18] (1.6) for `f = Im` (the walk solution). -/
def tutteIm (D : Set ℂ) : V → ℝ := dirichletSol G (vBd H D) (bdryVal H D Complex.im)

/-- **The Tutte embedding of `G(D)` with identity boundary data**, `Φ = Φ¹ + i Φ²`. -/
def tutte (D : Set ℂ) (x : V) : ℂ := ⟨tutteRe H D x, tutteIm H D x⟩

@[simp] theorem tutte_re (D : Set ℂ) (x : V) : (tutte H D x).re = tutteRe H D x := rfl

@[simp] theorem tutte_im (D : Set ℂ) (x : V) : (tutte H D x).im = tutteIm H D x := rfl

/-- `Φ¹` is the function `f_ε` of (1.6) for `f = Re`. -/
theorem isCellDirichletSolution_tutteRe (D : Set ℂ) :
    IsCellDirichletSolution H D (bdryVal H D Complex.re) (tutteRe H D) :=
  isCellDirichletSolution_dirichletSol H D _

/-- `Φ²` is the function `f_ε` of (1.6) for `f = Im`. -/
theorem isCellDirichletSolution_tutteIm (D : Set ℂ) :
    IsCellDirichletSolution H D (bdryVal H D Complex.im) (tutteIm H D) :=
  isCellDirichletSolution_dirichletSol H D _

/-- `Φ` is discrete harmonic at the interior vertices (both coordinates). -/
theorem lap_tutte {D : Set ℂ} {x : V} (hx : x ∉ vBd H D) :
    lap G (tutteRe H D) x = 0 ∧ lap G (tutteIm H D) x = 0 :=
  ⟨lap_dirichletSol G _ _ hx, lap_dirichletSol G _ _ hx⟩

/-- **Uniqueness of the Tutte embedding** on `V(G(D))`: any `Φ'` whose coordinates solve (1.6) for `Re` and `Im` is
`Φ` there. -/
theorem tutte_unique (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {Φ' : V → ℂ} (h₁ : IsCellDirichletSolution H D (bdryVal H D Complex.re) fun x => (Φ' x).re)
    (h₂ : IsCellDirichletSolution H D (bdryVal H D Complex.im) fun x => (Φ' x).im) :
    ∀ x ∈ vFin H D, Φ' x = tutte H D x := by
  intro x hx
  apply Complex.ext
  · exact cellDirichlet_eqOn H hconn hDo hDb h₁ (isCellDirichletSolution_tutteRe H D) x hx
  · exact cellDirichlet_eqOn H hconn hDo hDb h₂ (isCellDirichletSolution_tutteIm H D) x hx

/-- Walk representation of `Φ¹`: `Φ¹(x) = E_x[Φ¹(X_τ)]` on `V(G(D))`. -/
theorem tutteRe_eq_integral (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : x ∈ vFin H D) :
    tutteRe H D x =
      ∫ ω, tutteRe H D (hitVertex G (verticesMeeting H.cell (frontier D)) ω) ∂G.walkLaw x :=
  cellDirichlet_eq_integral H hconn hDo hDb (isCellDirichletSolution_tutteRe H D) hx

/-- Walk representation of `Φ²`: `Φ²(x) = E_x[Φ²(X_τ)]` on `V(G(D))`. -/
theorem tutteIm_eq_integral (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : x ∈ vFin H D) :
    tutteIm H D x =
      ∫ ω, tutteIm H D (hitVertex G (verticesMeeting H.cell (frontier D)) ω) ∂G.walkLaw x :=
  cellDirichlet_eq_integral H hconn hDo hDb (isCellDirichletSolution_tutteIm H D) hx

/-- On a vertex whose cell meets `∂D`, `Φ¹(x) = sup_{z ∈ H_x ∩ ∂D} Re z`, `Φ²(x) = sup_{z ∈ H_x ∩ ∂D} Im z`. -/
theorem tutte_of_mem_vBd {D : Set ℂ} {x : V} (hx : x ∈ vBd H D) :
    tutteRe H D x = bdryVal H D Complex.re x ∧ tutteIm H D x = bdryVal H D Complex.im x :=
  ⟨dirichletSol_of_mem G _ _ hx, dirichletSol_of_mem G _ _ hx⟩

/-- **`Φ` approximates `x ↦ η(x)` on `V(G(∂D))`**: if the cell of `x` meets `∂D`, then
`‖Φ(x) − z‖ ≤ 2 diam(H_x)` for every `z ∈ H_x` (in the model, `z = η(x)`). -/
theorem norm_tutte_sub_le {D : Set ℂ} (hDb : Bornology.IsBounded D) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) {z : ℂ} (hz : z ∈ H.cell x) :
    ‖tutte H D x - z‖ ≤ 2 * cellDiam H x := by
  have hxB : x ∈ vBd H D := (mem_vBd H hDb).mpr hx
  obtain ⟨hre, him⟩ := tutte_of_mem_vBd H hxB
  obtain ⟨z₁, hz₁, hval₁, -⟩ := exists_bdryVal_eq H Complex.continuous_re.continuousOn hx
  obtain ⟨z₂, hz₂, hval₂, -⟩ := exists_bdryVal_eq H Complex.continuous_im.continuousOn hx
  have h1 : |(tutte H D x - z).re| ≤ cellDiam H x := by
    rw [Complex.sub_re, tutte_re, hre, hval₁, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by rw [← dist_eq_norm]; exact dist_le_cellDiam H hz₁.1 hz)
  have h2 : |(tutte H D x - z).im| ≤ cellDiam H x := by
    rw [Complex.sub_im, tutte_im, him, hval₂, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (by rw [← dist_eq_norm]; exact dist_le_cellDiam H hz₂.1 hz)
  calc ‖tutte H D x - z‖ ≤ |(tutte H D x - z).re| + |(tutte H D x - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * cellDiam H x := by linarith

/-- The boundary data (1.6) of `Re` lie in `[−ρ, ρ]` when `D ⊂ B_ρ(0)`. -/
theorem abs_bdryVal_re_le {D : Set ℂ} {ρ : ℝ} (hDsub : D ⊆ ball (0 : ℂ) ρ) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) : |bdryVal H D Complex.re x| ≤ ρ := by
  obtain ⟨z, hz, hval, -⟩ := exists_bdryVal_eq H Complex.continuous_re.continuousOn hx
  rw [hval]
  have hzc : z ∈ closedBall (0 : ℂ) ρ :=
    (closure_mono hDsub |>.trans closure_ball_subset_closedBall) (frontier_subset_closure hz.2)
  rw [mem_closedBall, dist_zero_right] at hzc
  exact (Complex.abs_re_le_norm z).trans hzc

/-- The boundary data (1.6) of `Im` lie in `[−ρ, ρ]` when `D ⊂ B_ρ(0)`. -/
theorem abs_bdryVal_im_le {D : Set ℂ} {ρ : ℝ} (hDsub : D ⊆ ball (0 : ℂ) ρ) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) : |bdryVal H D Complex.im x| ≤ ρ := by
  obtain ⟨z, hz, hval, -⟩ := exists_bdryVal_eq H Complex.continuous_im.continuousOn hx
  rw [hval]
  have hzc : z ∈ closedBall (0 : ℂ) ρ :=
    (closure_mono hDsub |>.trans closure_ball_subset_closedBall) (frontier_subset_closure hz.2)
  rw [mem_closedBall, dist_zero_right] at hzc
  exact (Complex.abs_im_le_norm z).trans hzc

/-- A function with `|g| ≤ ρ` on the boundary vertices solving (1.6) has `|f| ≤ ρ` on `V(G(D))`. -/
theorem abs_le_of_cellDirichlet (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f : V → ℝ} (hf : IsCellDirichletSolution H D g f) {ρ : ℝ}
    (hg : ∀ x ∈ vFin H D, x ∈ vBd H D → |g x| ≤ ρ) : ∀ x ∈ vFin H D, |f x| ≤ ρ := by
  intro x hx
  rw [abs_le]
  exact ⟨cellDirichlet_ge H hconn hDo hDb hf (fun y hy hyB => (abs_le.mp (hg y hy hyB)).1) x hx,
    cellDirichlet_le H hconn hDo hDb hf (fun y hy hyB => (abs_le.mp (hg y hy hyB)).2) x hx⟩

/-- For `D ⊂ B_ρ(0)` open, `|Φ¹| ≤ ρ` on `V(G(D))`. -/
theorem abs_tutteRe_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D) {ρ : ℝ}
    (hDsub : D ⊆ ball (0 : ℂ) ρ) : ∀ x ∈ vFin H D, |tutteRe H D x| ≤ ρ :=
  abs_le_of_cellDirichlet H hconn hDo (isBounded_ball.subset hDsub) (isCellDirichletSolution_tutteRe H D)
    fun _ _ hyB => abs_bdryVal_re_le H hDsub ((mem_vBd H (isBounded_ball.subset hDsub)).mp hyB)

/-- For `D ⊂ B_ρ(0)` open, `|Φ²| ≤ ρ` on `V(G(D))`. -/
theorem abs_tutteIm_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D) {ρ : ℝ}
    (hDsub : D ⊆ ball (0 : ℂ) ρ) : ∀ x ∈ vFin H D, |tutteIm H D x| ≤ ρ :=
  abs_le_of_cellDirichlet H hconn hDo (isBounded_ball.subset hDsub) (isCellDirichletSolution_tutteIm H D)
    fun _ _ hyB => abs_bdryVal_im_le H hDsub ((mem_vBd H (isBounded_ball.subset hDsub)).mp hyB)

/-! ### Deterministic core of Corollary 1.6 -/

/-- The modulus of a difference is at most the sum of the coordinate differences. -/
theorem norm_tutte_sub_le_add (D : Set ℂ) (x y : V) :
    ‖tutte H D x - tutte H D y‖ ≤ |tutteRe H D x - tutteRe H D y| + |tutteIm H D x - tutteIm H D y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (tutte H D x - tutte H D y)
  rwa [Complex.sub_re, Complex.sub_im, tutte_re, tutte_re, tutte_im, tutte_im] at h

/-- **Deterministic core of [18] Corollary 1.6.** Let `p x ∈ H_x` be marked points (in the model `p x = η(x)`).
Suppose both coordinates of the Tutte embedding satisfy the Hölder bound (1.9) of [18] Theorem 1.5 on `V(G(D))`,
`|Φ^i(x) − Φ^i(y)| ≤ A_i (ε ∨ |p x − p y|)^ξ`, and every cell of `V(G(D))` has diameter at most `δ`. Then every edge
`e` of `G(D)` (both ends in `V(G(D))`, [18] (1.5)) has embedded length `‖Φ(x) − Φ(y)‖ ≤ (A₁ + A₂) (ε ∨ 2δ)^ξ`. -/
theorem norm_tutte_sub_le_of_holder {D : Set ℂ} {p : V → ℂ} (hp : ∀ x, p x ∈ H.cell x)
    {ε δ ξ A₁ A₂ : ℝ} (hε : 0 ≤ ε) (hξ : 0 < ξ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D,
      |tutteRe H D x - tutteRe H D y| ≤ A₁ * max ε ‖p x - p y‖ ^ ξ)
    (h₂ : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D,
      |tutteIm H D x - tutteIm H D y| ≤ A₂ * max ε ‖p x - p y‖ ^ ξ)
    (hdiam : ∀ x ∈ vFin H D, cellDiam H x ≤ δ) :
    ∀ e ∈ edgesIn G (vFin H D),
      ‖tutte H D (G.src e) - tutte H D (G.tgt e)‖ ≤ (A₁ + A₂) * max ε (2 * δ) ^ ξ := by
  intro e he
  rw [mem_edgesIn] at he
  obtain ⟨hs, ht⟩ := he
  have hbase : 0 ≤ max ε (2 * δ) := le_max_of_le_left hε
  have hRHS : 0 ≤ (A₁ + A₂) * max ε (2 * δ) ^ ξ :=
    mul_nonneg (add_nonneg hA₁ hA₂) (Real.rpow_nonneg hbase _)
  by_cases hloop : G.src e = G.tgt e
  · rw [hloop, sub_self, norm_zero]
    exact hRHS
  have hadj : G.adj.Adj (G.src e) (G.tgt e) := adj_of_edge G hloop
  have hpd : ‖p (G.src e) - p (G.tgt e)‖ ≤ 2 * δ := by
    rw [← dist_eq_norm]
    calc dist (p (G.src e)) (p (G.tgt e)) ≤ cellDiam H (G.src e) + cellDiam H (G.tgt e) :=
          dist_le_cellDiam_add_of_adj H hadj (hp _) (hp _)
      _ ≤ 2 * δ := by linarith [hdiam _ hs, hdiam _ ht]
  have hmono : max ε ‖p (G.src e) - p (G.tgt e)‖ ^ ξ ≤ max ε (2 * δ) ^ ξ :=
    Real.rpow_le_rpow (le_max_of_le_left hε) (max_le_max le_rfl hpd) hξ.le
  calc ‖tutte H D (G.src e) - tutte H D (G.tgt e)‖
      ≤ |tutteRe H D (G.src e) - tutteRe H D (G.tgt e)| +
          |tutteIm H D (G.src e) - tutteIm H D (G.tgt e)| := norm_tutte_sub_le_add H D _ _
    _ ≤ A₁ * max ε ‖p (G.src e) - p (G.tgt e)‖ ^ ξ + A₂ * max ε ‖p (G.src e) - p (G.tgt e)‖ ^ ξ :=
        add_le_add (h₁ _ hs _ ht) (h₂ _ hs _ ht)
    _ ≤ A₁ * max ε (2 * δ) ^ ξ + A₂ * max ε (2 * δ) ^ ξ :=
        add_le_add (mul_le_mul_of_nonneg_left hmono hA₁) (mul_le_mul_of_nonneg_left hmono hA₂)
    _ = (A₁ + A₂) * max ε (2 * δ) ^ ξ := by ring

/-- `max(ε, 2ε^q)^ξ = 2^ξ ε^{qξ}` for `0 < ε ≤ 1` and `q ≤ 1`: the exponent of Corollary 1.6 is `qξ`. -/
theorem max_mesh_rpow_eq {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq1 : q ≤ 1) (ξ : ℝ) :
    max ε (2 * ε ^ q) ^ ξ = 2 ^ ξ * ε ^ (q * ξ) := by
  have hεq : ε ≤ ε ^ q := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ q := Real.rpow_le_rpow_of_exponent_ge hε hε1 hq1
  have hmax : max ε (2 * ε ^ q) = 2 * ε ^ q :=
    max_eq_right (by linarith [Real.rpow_nonneg hε.le q])
  rw [hmax, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε.le q), ← Real.rpow_mul hε.le]

end MatedCRTHarmonic.GMSMain.T16D
