import HigherDimLFPP.Upper.LocalMeanShells

/-!
# Lemma 4.3, Step 1a and the energy expansion

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, proof of Lemma 4.3, Step 1 ((4.11) and
the parametrization `Q_δ(f)`), as completed by the planning audit HA3
(`planning/audits/HA3-section-4.md`), Details D5, Step 1a (fix F3) and the energy expansion;
packet P-U4.

* **Parametrization (Step 1a, fix F3)** (`qPoly_prof`): every `Q ∈ G_K(0, e₁)` is the polygon
  `Q_δ(f)` of `HigherDimLFPP.qPoly` for the profile `f = prof n δ Q ∈ V_{n,d}` interpolating the
  rescaled transverse vertex coordinates `δ⁻¹ (z_i)_⊥` (`unembedT`, `vInterp`).  Only this
  direction is needed.  If `E_δ(Q) ≤ R`, the profile lies in the vertex ball `B̂_{2√R}`
  (`prof_mem_vertBall`, HA3 D4 (c)).
* **Energy expansion** (`abs_eDelta_qPoly_sub_energy_le`): uniformly on `B̂_R`,
  `|E_δ(Q_δ(f)) - E(f)| ≤ C_{n,R} δ²` for small `δ`.  The first `K - 1` edges of `Q_δ(f)` have
  length `1/K` exactly (`norm_qVert_succ_sub`), so `len Q_δ(f) = (K-1)/K + √((1/K + σ)² + a_L)`
  with `σ = Σ_{l < K-1} (1/K - √(K⁻² - δ²|Δf_l|²))`; the square roots are expanded to second order
  (`sqrt_sq_sub_bounds`, `abs_sqrt_sq_add_sub_le`) and `|log(1+x) - x| ≤ x²`
  (`abs_log_one_add_sub_le`, `abs_log_excess_sub_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

variable {d : ℕ}

/-! ## Transverse coordinates and interpolation -/

section Interp

/-- The transverse coordinates `(z₂, …, z_d) ∈ ℝ^{d-1}` of `z ∈ ℝ^d`. -/
def unembedT (z : Rd d) : Rd (d - 1) :=
  WithLp.toLp 2 (fun j : Fin (d - 1) => z.ofLp ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)

theorem embedT_unembedT (hd : 0 < d) (z : Rd d) : (Lower.embedT (unembedT z) : Rd d) = Lower.transv z := by
  ext i
  rw [Lower.embedT_ofLp, Lower.transv, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul,
    Pi.smul_apply, Lower.e₁_ofLp, Lower.horiz_apply hd]
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, hd⟩ := Fin.ext hi
    subst hi'
    simp
  · rw [dite_eq_right hi, ite_eq_right hi, smul_zero, sub_zero]
    simp only [unembedT, WithLp.ofLp_toLp]
    exact congrArg (fun k => z.ofLp k) (Fin.ext (Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)))

theorem norm_unembedT (hd : 0 < d) (z : Rd d) : ‖unembedT z‖ = ‖Lower.transv z‖ := by
  rw [← embedT_unembedT hd, Lower.norm_embedT]

theorem unembedT_sub (z w : Rd d) : unembedT (z - w) = unembedT z - unembedT w := by
  ext j
  simp [unembedT]

theorem unembedT_smul (c : ℝ) (z : Rd d) : unembedT (c • z) = c • unembedT z := by
  ext j
  simp [unembedT]

theorem unembedT_e₁ : unembedT (e₁ d) = 0 := by
  ext j
  simp [unembedT, Lower.e₁_ofLp]

theorem unembedT_zero : unembedT (0 : Rd d) = 0 := by
  ext j
  simp [unembedT]

/-- The piecewise-linear interpolation on the mesh `2⁻ⁿ` of the values `v 0, …, v 2ⁿ`, extended by
`0` outside `[0,1]`. -/
def vInterp {m : ℕ} (n : ℕ) (v : ℕ → Rd m) (x : ℝ) : Rd m :=
  if x ∈ Icc (0 : ℝ) 1 then rampPath (2 ^ n) (fun i => (i : ℝ) / 2 ^ n) v x else 0

theorem mesh_lt (n i : ℕ) : (i : ℝ) / 2 ^ n < ((i + 1 : ℕ) : ℝ) / 2 ^ n := by
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  push_cast
  linarith

theorem vInterp_node {m : ℕ} (n : ℕ) (v : ℕ → Rd m) {i : ℕ} (hi : i ≤ 2 ^ n) :
    vInterp n v ((i : ℝ) / 2 ^ n) = v i := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hmem : (i : ℝ) / 2 ^ n ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hL]
    exact_mod_cast hi
  rw [vInterp, ite_eq_left hmem]
  have hT : ∀ j < 2 ^ n, (fun i : ℕ => (i : ℝ) / 2 ^ n) j < (fun i : ℕ => (i : ℝ) / 2 ^ n) (j + 1) :=
    fun j _ => mesh_lt n j
  rcases lt_or_eq_of_le hi with hlt | heq
  · rw [rampPath_eq v hT hlt ⟨le_rfl, (mesh_lt n i).le⟩]
    simp
  · have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hk : 2 ^ n - 1 < 2 ^ n := Nat.sub_lt hpos one_pos
    have e : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hpos
    have hmem' : (i : ℝ) / 2 ^ n ∈ Icc (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n)
        (((2 ^ n - 1 + 1 : ℕ) : ℝ) / 2 ^ n) := by
      rw [e, heq]
      exact ⟨(mesh_lt n (2 ^ n - 1)).le.trans (by rw [e]), le_rfl⟩
    rw [rampPath_eq v hT hk hmem', e, heq, div_self (by
      have := mesh_lt n (2 ^ n - 1)
      rw [e] at this
      linarith), one_smul]
    abel

/-- The interpolation of values vanishing at both ends lies in `V_n`. -/
theorem vInterp_mem_Vg {m : ℕ} (n : ℕ) {v : ℕ → Rd m} (hv0 : v 0 = 0) (hvK : v (2 ^ n) = 0) :
    vInterp n v ∈ Vg (Rd m) n := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := vInterp_node n v (Nat.zero_le (2 ^ n))
    simpa [hv0] using this
  · have := vInterp_node n v (le_refl (2 ^ n))
    rw [hvK] at this
    have e : ((2 ^ n : ℕ) : ℝ) / 2 ^ n = 1 := by push_cast; exact div_self hL.ne'
    rwa [e] at this
  · intro x hx
    rw [vInterp, ite_eq_right hx]
  · intro k hk
    have hT : ∀ j < 2 ^ n, (fun i : ℕ => (i : ℝ) / 2 ^ n) j <
        (fun i : ℕ => (i : ℝ) / 2 ^ n) (j + 1) := fun j _ => mesh_lt n j
    refine ⟨(2 : ℝ) ^ n • (v (k + 1) - v k), v k - (k : ℝ) • (v (k + 1) - v k), fun x hx => ?_⟩
    have hx01 : x ∈ Icc (0 : ℝ) 1 := by
      refine ⟨le_trans (by positivity) hx.1, hx.2.trans ?_⟩
      rw [div_le_one hL]
      exact_mod_cast hk
    have hx' : x ∈ Icc ((fun i : ℕ => (i : ℝ) / 2 ^ n) k) ((fun i : ℕ => (i : ℝ) / 2 ^ n) (k + 1)) := by
      simp only
      push_cast
      exact hx
    rw [vInterp, ite_eq_left hx01, rampPath_eq v hT hk hx']
    have e : (x - (k : ℝ) / 2 ^ n) / (((k + 1 : ℕ) : ℝ) / 2 ^ n - (k : ℝ) / 2 ^ n) =
        (2 : ℝ) ^ n * x - k := by
      push_cast
      field_simp
      ring
    rw [e]
    module

end Interp

/-! ## Step 1a: every good polygon of the unit chord is a polygon `Q_δ(f)` -/

section Param

/-- The profile `f ∈ V_{n,d}` of a polygon: the interpolation of `δ⁻¹ (z_i)_⊥`. -/
def prof (n : ℕ) (δ : ℝ) (Q : List (Rd d)) : ℝ → Rd (d - 1) :=
  vInterp n (fun i => δ⁻¹ • unembedT (vtx Q i))

theorem prof_node (n : ℕ) (δ : ℝ) (Q : List (Rd d)) {i : ℕ} (hi : i ≤ 2 ^ n) :
    prof n δ Q ((i : ℝ) / 2 ^ n) = δ⁻¹ • unembedT (vtx Q i) :=
  vInterp_node n _ hi

theorem prof_mem_Vg (hd : 0 < d) {n : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d)) (δ : ℝ) : prof n δ Q ∈ Vg (Rd (d - 1)) n := by
  obtain ⟨-, -, h0, hK, -⟩ := unitGood_facts hd ha₀ hQ
  exact vInterp_mem_Vg n (by simp [h0, unembedT_zero]) (by simp [hK, unembedT_e₁])

/-- **Step 1a (HA3 D5, fix F3)**: every `Q ∈ G_K(0, e₁)` is the polygon `Q_δ(f)` of its profile. -/
theorem qPoly_prof (hd : 0 < d) {n : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d)) {δ : ℝ} (hδ : δ ≠ 0) :
    qPoly d n δ (prof n δ Q) = Q := by
  obtain ⟨hK1, hQV, h0, hK, hedge, -⟩ := unitGood_facts hd ha₀ hQ
  obtain ⟨V, hQV', hV0, hVK, hreg, hfwd, -⟩ := goodFamily_vertex hQ
  set K := 2 ^ n with hKdef
  have hvV : ∀ i ≤ K, vtx Q i = V i := fun i hi => by rw [hQV']; exact vtx_range_map V hi
  have he : ‖e₁ d - 0‖ = 1 := by rw [sub_zero, Lower.norm_e₁ hd]
  -- the transverse increments
  have htr : ∀ l, l + 1 ≤ K → δ ^ 2 * ‖prof n δ Q (((l : ℝ) + 1) / 2 ^ n) -
      prof n δ Q ((l : ℝ) / 2 ^ n)‖ ^ 2 = ‖Lower.transv (vtx Q (l + 1) - vtx Q l)‖ ^ 2 := by
    intro l hl
    have e1 : ((l : ℝ) + 1) / 2 ^ n = ((l + 1 : ℕ) : ℝ) / 2 ^ n := by push_cast; ring
    rw [e1, prof_node n δ Q hl, prof_node n δ Q (by omega), ← smul_sub, ← unembedT_sub,
      norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 hδ), one_mul, norm_unembedT hd]
  -- the horizontal increments of the regular edges
  have hinc : ∀ l, l + 1 < K → qInc n δ (prof n δ Q) l =
      Lower.horiz (vtx Q (l + 1)) - Lower.horiz (vtx Q l) := by
    intro l hl
    rw [qInc, htr l hl.le, ← Lower.horiz_sub]
    have hnorm : ‖vtx Q (l + 1) - vtx Q l‖ = ((2 : ℝ) ^ n)⁻¹ := by
      rw [hvV (l + 1) hl.le, hvV l (by omega), hreg l hl, he, hKdef]
      push_cast
      ring
    have hpy := Lower.norm_sq_eq_horiz_sq_add hd (vtx Q (l + 1) - vtx Q l)
    rw [hnorm] at hpy
    have hfw : 0 ≤ Lower.horiz (vtx Q (l + 1) - vtx Q l) := by
      have h := hfwd l (by omega)
      rw [he, mul_one, sub_zero] at h
      rw [Lower.horiz, real_inner_comm, hvV (l + 1) hl.le, hvV l (by omega)]
      exact le_trans (mul_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by
        linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])) (norm_nonneg _)) h
    rw [show ((2 : ℝ) ^ n)⁻¹ ^ 2 - ‖Lower.transv (vtx Q (l + 1) - vtx Q l)‖ ^ 2 =
      Lower.horiz (vtx Q (l + 1) - vtx Q l) ^ 2 by linarith]
    exact Real.sqrt_sq hfw
  -- the knots
  have hknot : ∀ i, i < K → qKnot n δ (prof n δ Q) i = Lower.horiz (vtx Q i) := by
    intro i hi
    rw [qKnot, Finset.sum_congr rfl fun l hl => hinc l (by
      have := Finset.mem_range.1 hl; omega), Finset.sum_range_sub
      (fun j => Lower.horiz (vtx Q j)), h0, Lower.horiz_zero, sub_zero]
  -- the vertices
  have hvert : ∀ i ≤ K, qVert d n δ (prof n δ Q) i = vtx Q i := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · rw [qVert, ite_eq_left hlt, hknot i hlt, prof_node n δ Q hi, smul_smul,
        mul_inv_cancel₀ hδ, one_smul, embedT_unembedT hd, Lower.horiz_add_transv]
    · rw [qVert, ite_eq_right (lt_irrefl _), hK]
  rw [qPoly]
  conv_rhs => rw [hQV]
  exact List.map_congr_left fun i hi => hvert i (by have := List.mem_range.1 hi; omega)

/-- **The vertex ball** (HA3 D5, Step 1b): if `E_δ(Q) ≤ R`, the profile of `Q ∈ G_K(0, e₁)` lies in
`B̂_{2√R}`. -/
theorem prof_mem_vertBall (hd : 0 < d) {n : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d)) {δ R : ℝ} (hδ : 0 < δ) (hR : eDelta δ Q ≤ R) :
    prof n δ Q ∈ vertBall (Rd (d - 1)) n (2 * Real.sqrt R) := by
  refine ⟨prof_mem_Vg hd ha₀ hQ δ, fun i hi => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hclose⟩ := unitGood_facts hd ha₀ hQ
  rw [prof_node n δ Q hi, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ,
    norm_unembedT hd]
  have h1 : Lower.transv (vtx Q i) = Lower.transv (vtx Q i - ((i : ℝ) / (2 ^ n : ℕ)) • e₁ d) := by
    rw [Lower.transv_sub, Lower.transv_smul_e₁ hd, sub_zero]
  have h2 : Real.sqrt (Real.log (polyLen Q)) ≤ δ * Real.sqrt R := by
    have h4 : Real.log (polyLen Q) ≤ δ ^ 2 * R := by
      rw [eDelta, inv_mul_le_iff₀ (by positivity)] at hR
      exact hR
    calc Real.sqrt (Real.log (polyLen Q)) ≤ Real.sqrt (δ ^ 2 * R) := Real.sqrt_le_sqrt h4
      _ = δ * Real.sqrt R := by rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
  rw [h1, inv_mul_le_iff₀ hδ]
  calc ‖Lower.transv (vtx Q i - ((i : ℝ) / (2 ^ n : ℕ)) • e₁ d)‖
      ≤ ‖vtx Q i - ((i : ℝ) / (2 ^ n : ℕ)) • e₁ d‖ := Lower.norm_transv_le hd _
    _ ≤ 2 * Real.sqrt (Real.log (polyLen Q)) := hclose i hi
    _ ≤ δ * (2 * Real.sqrt R) := by linarith

end Param

/-! ## The energy expansion (HA3 D5, "Energy expansion") -/

section Energy

/-- Second-order expansion of the square root (as `HigherDimLFPP.Lower.sqrt_sub_bounds`):
`q - u/(2q) - u²/(2q³) ≤ √(q² - u) ≤ q - u/(2q)` for `q > 0`, `u ≤ q²`. -/
theorem sqrt_sq_sub_bounds {q u : ℝ} (hq : 0 < q) (huq : u ≤ q ^ 2) :
    q - u / (2 * q) - u ^ 2 / (2 * q ^ 3) ≤ Real.sqrt (q ^ 2 - u) ∧
      Real.sqrt (q ^ 2 - u) ≤ q - u / (2 * q) := by
  set r := Real.sqrt (q ^ 2 - u) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = q ^ 2 - u := Real.sq_sqrt (by linarith)
  have hu : u = q ^ 2 - r ^ 2 := by linarith
  have hq' : q ≠ 0 := hq.ne'
  constructor
  · have h : q - u / (2 * q) - u ^ 2 / (2 * q ^ 3) - r =
        -((q - r) ^ 2 * (2 * q * r + r ^ 2)) / (2 * q ^ 3) := by
      rw [hu]; field_simp; ring
    have h' : -((q - r) ^ 2 * (2 * q * r + r ^ 2)) / (2 * q ^ 3) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)
    linarith
  · have h : q - u / (2 * q) - r = (q - r) ^ 2 / (2 * q) := by
      rw [hu]; field_simp; ring
    have h' : 0 ≤ (q - r) ^ 2 / (2 * q) := by positivity
    linarith

/-- `|√(p² + a) - p - a/(2p)| ≤ a²/(8p³)` for `p > 0`, `a ≥ 0`. -/
theorem abs_sqrt_sq_add_sub_le {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) :
    |Real.sqrt (p ^ 2 + a) - p - a / (2 * p)| ≤ a ^ 2 / (8 * p ^ 3) := by
  set s := Real.sqrt (p ^ 2 + a) with hs
  have hs2 : s ^ 2 = p ^ 2 + a := Real.sq_sqrt (by positivity)
  have hsp : p ≤ s := by
    rw [hs, Real.le_sqrt hp.le (by positivity)]
    linarith
  have hsp0 : 0 < s + p := by linarith
  have e : s - p - a / (2 * p) = -(a ^ 2 / (2 * p * (s + p) ^ 2)) := by
    have h1 : s - p = a / (s + p) := by
      rw [eq_div_iff hsp0.ne']
      nlinarith
    rw [h1]
    field_simp
    nlinarith
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 4 * p ^ 2 ≤ (s + p) ^ 2 := by nlinarith
  nlinarith [sq_nonneg a, mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ a ^ 2 * (2 * p))]

/-- `|log(1 + x) - x| ≤ x²` for `x ≥ 0`. -/
theorem abs_log_one_add_sub_le {x : ℝ} (hx : 0 ≤ x) : |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have h1 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
    linarith
  have h2 : x - x ^ 2 ≤ Real.log (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
    have h3 : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [show (1 : ℝ) - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
    linarith
  rw [abs_le]
  constructor <;> linarith

variable (d)

/-- The regular edges of `Q_δ(f)` have length exactly `2⁻ⁿ` (if `δ |Δf| ≤ 2⁻ⁿ`). -/
theorem norm_qVert_succ_sub (hd : 0 < d) {n : ℕ} {δ : ℝ} {f : ℝ → Rd (d - 1)} {i : ℕ}
    (hi : i + 1 < 2 ^ n)
    (hsmall : δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ ^ 2) :
    ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ = ((2 : ℝ) ^ n)⁻¹ := by
  have e : qVert d n δ f (i + 1) - qVert d n δ f i =
      qInc n δ f i • e₁ d + Lower.embedT (δ • (f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n))) := by
    rw [qVert, qVert, ite_eq_left hi, ite_eq_left (by omega), qKnot, qKnot, Finset.sum_range_succ,
      smul_sub, Lower.embedT_sub]
    push_cast
    rw [add_smul]
    abel
  have hsq : ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ ^ 2 = ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
    rw [e, Lower.norm_sq_smul_e₁_add_embedT hd, qInc, Real.sq_sqrt (by linarith), norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The last edge of `Q_δ(f)`. -/
theorem norm_qVert_last_sq (hd : 0 < d) {n : ℕ} {δ : ℝ} {f : ℝ → Rd (d - 1)} :
    ‖qVert d n δ f (2 ^ n) - qVert d n δ f (2 ^ n - 1)‖ ^ 2 =
      (1 - qKnot n δ f (2 ^ n - 1)) ^ 2 + δ ^ 2 * ‖f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n)‖ ^ 2 := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have e : qVert d n δ f (2 ^ n) - qVert d n δ f (2 ^ n - 1) =
      (1 - qKnot n δ f (2 ^ n - 1)) • e₁ d +
        Lower.embedT (-(δ • f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n))) := by
    rw [qVert, qVert, ite_eq_right (lt_irrefl _), ite_eq_left (Nat.sub_lt hpos one_pos),
      sub_smul, one_smul]
    have : Lower.embedT (-(δ • f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n))) =
        -(Lower.embedT (δ • f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n)) : Rd d) := by
      rw [show -(δ • f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n)) =
        (0 : Rd (d - 1)) - δ • f (((2 ^ n - 1 : ℕ) : ℝ) / 2 ^ n) by abel, Lower.embedT_sub,
        Lower.embedT_zero, zero_sub]
    rw [this]
    abel
  rw [e, Lower.norm_sq_smul_e₁_add_embedT hd, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]

variable {d}

/-- The real-analysis tail of the energy expansion: if `x = √((q+σ)² + a_L) - q` is the excess of
`Q_δ(f)` and its parts satisfy the second-order bounds, then
`|δ⁻² log(1 + x) - E| ≤ ((E_m + C₁)² + C₁) δ²`, `C₁ = c⁴ K³ (K + 1)`. -/
theorem abs_log_excess_sub_le {q Kr t σ aL Sa E Em δ c : ℝ} (hq0 : 0 < q) (hqKr : q * Kr = 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : t = δ ^ 2 * c ^ 2) (hσ0 : 0 ≤ σ) (hσle : σ ≤ Kr * t * Kr) (hB1 : |σ - Sa| ≤ Kr * t ^ 2 * Kr ^ 3 / 2)
    (haL0 : 0 ≤ aL) (haLt : aL ≤ t) (hEa : δ ^ 2 * E = Sa + aL * Kr / 2) (hEm : E ≤ Em) :
    |(δ ^ 2)⁻¹ * Real.log (1 + (Real.sqrt ((q + σ) ^ 2 + aL) - q)) - E| ≤
      ((Em + c ^ 4 * Kr ^ 3 * (Kr + 1)) ^ 2 + c ^ 4 * Kr ^ 3 * (Kr + 1)) * δ ^ 2 := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = c ^ 4 * Kr ^ 3 * (Kr + 1) := ⟨_, rfl⟩
  rw [← hC₁]
  have hKr0 : 0 < Kr := by
    by_contra h
    have : q * Kr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le (not_lt.1 h)
    linarith
  have hKq : Kr * q = 1 := by rw [mul_comm]; exact hqKr
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  obtain ⟨p, hp⟩ : ∃ p, p = q + σ := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 < p := by linarith
  have hqp : q ≤ p := by linarith
  obtain ⟨sq, hsq⟩ : ∃ sq, sq = Real.sqrt (p ^ 2 + aL) := ⟨_, rfl⟩
  rw [← hsq]
  have hsp : p ≤ sq := by
    rw [hsq, Real.le_sqrt hp0.le (add_nonneg (sq_nonneg p) haL0)]
    linarith
  obtain ⟨x, hx⟩ : ∃ x, x = sq - q := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hB2 : |sq - p - aL / (2 * p)| ≤ t ^ 2 * Kr ^ 3 / 8 := by
    rw [hsq]
    refine (abs_sqrt_sq_add_sub_le hp0 haL0).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : aL ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ haL0 haLt 2
    have h2 : q ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ hq0.le hqp 3
    have h3 : Kr ^ 3 * q ^ 3 = 1 := by rw [← mul_pow, hKq, one_pow]
    have h4 : 1 ≤ Kr ^ 3 * p ^ 3 := by
      have := mul_le_mul_of_nonneg_left h2 (pow_nonneg hKr0.le 3)
      linarith
    have h5 : aL ^ 2 ≤ t ^ 2 * (Kr ^ 3 * p ^ 3) :=
      h1.trans (le_mul_of_one_le_right (sq_nonneg t) h4)
    exact h5.trans (le_of_eq (by ring))
  have hB3 : |aL / (2 * p) - aL * Kr / 2| ≤ t ^ 2 * Kr ^ 4 / 2 := by
    have hKq' : Kr = q⁻¹ := by rw [← mul_eq_one_iff_eq_inv₀ hq0.ne', mul_comm, hqKr]
    have e : aL / (2 * p) - aL * Kr / 2 = -(aL * σ * Kr / (2 * p)) := by
      rw [hp, hKq']
      field_simp
      ring
    rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : aL * σ ≤ t * (Kr * t * Kr) := mul_le_mul haLt hσle hσ0 ht0
    have h3 : 1 ≤ Kr * p := by
      have := mul_le_mul_of_nonneg_left hqp hKr0.le
      linarith
    have h4 : aL * σ * Kr ≤ t * (Kr * t * Kr) * Kr := mul_le_mul_of_nonneg_right h1 hKr0.le
    have h6 : t ^ 2 * Kr ^ 3 ≤ t ^ 2 * Kr ^ 4 / 2 * (2 * p) := by
      have e2 : t ^ 2 * Kr ^ 4 / 2 * (2 * p) = t ^ 2 * Kr ^ 3 * (Kr * p) := by ring
      rw [e2]
      exact le_mul_of_one_le_right (by positivity) h3
    have e3 : t * (Kr * t * Kr) * Kr = t ^ 2 * Kr ^ 3 := by ring
    linarith
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hxE : |x - δ ^ 2 * E| ≤ C₁ * δ ^ 4 := by
    have e : x - δ ^ 2 * E =
        (σ - Sa) + (sq - p - aL / (2 * p)) + (aL / (2 * p) - aL * Kr / 2) := by
      rw [hx, hEa, hp]; ring
    rw [e]
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    have ht2 : t ^ 2 = δ ^ 4 * c ^ 4 := by rw [ht]; ring
    have h8 : 0 ≤ δ ^ 4 * c ^ 4 * Kr ^ 3 := by positivity
    have h7 : Kr * t ^ 2 * Kr ^ 3 / 2 + t ^ 2 * Kr ^ 3 / 8 + t ^ 2 * Kr ^ 4 / 2 ≤
        C₁ * δ ^ 4 := by
      have e4 : Kr * t ^ 2 * Kr ^ 3 / 2 + t ^ 2 * Kr ^ 3 / 8 + t ^ 2 * Kr ^ 4 / 2 =
          δ ^ 4 * c ^ 4 * Kr ^ 3 * (Kr + 1 / 8) := by rw [ht2]; ring
      have e5 : C₁ * δ ^ 4 = δ ^ 4 * c ^ 4 * Kr ^ 3 * (Kr + 1) := by rw [hC₁]; ring
      rw [e4, e5]
      exact mul_le_mul_of_nonneg_left (by linarith) h8
    linarith
  have hE0 : δ ^ 2 * E ≤ δ ^ 2 * Em := mul_le_mul_of_nonneg_left hEm (sq_nonneg δ)
  have hxle : x ≤ δ ^ 2 * (Em + C₁) := by
    have h1 := (abs_le.1 hxE).2
    have hδ4 : δ ^ 4 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hδ4 hC₁0
    have e : δ ^ 2 * (Em + C₁) = δ ^ 2 * Em + C₁ * δ ^ 2 := by ring
    linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  have e : (δ ^ 2)⁻¹ * Real.log (1 + x) - E =
      (δ ^ 2)⁻¹ * ((Real.log (1 + x) - x) + (x - δ ^ 2 * E)) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hδ2), inv_mul_le_iff₀ hδ2]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_log_one_add_sub_le hx0
  have h2 : x ^ 2 ≤ (δ ^ 2 * (Em + C₁)) ^ 2 := pow_le_pow_left₀ hx0 hxle 2
  have e1 : (δ ^ 2 * (Em + C₁)) ^ 2 = δ ^ 4 * (Em + C₁) ^ 2 := by ring
  have e2 : δ ^ 2 * (((Em + C₁) ^ 2 + C₁) * δ ^ 2) = δ ^ 4 * (Em + C₁) ^ 2 + C₁ * δ ^ 4 := by
    ring
  linarith

/-- The defects `2⁻ⁿ - qInc` of the regular edges: `a K/2 ≤ q - qInc ≤ a K/2 + a² K³/2` with
`a = δ² |Δf|² ≤ q²`, `q = 2⁻ⁿ`, `K = 2ⁿ`. -/
theorem qInc_defect_bounds {E : Type*} [NormedAddCommGroup E] (n : ℕ) (δ : ℝ) (f : ℝ → E) (l : ℕ)
    (hsmall : δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ ^ 2) :
    δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * (2 : ℝ) ^ n / 2 ≤
        ((2 : ℝ) ^ n)⁻¹ - qInc n δ f l ∧
      ((2 : ℝ) ^ n)⁻¹ - qInc n δ f l ≤
        δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * (2 : ℝ) ^ n / 2 +
          (δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2) ^ 2 * ((2 : ℝ) ^ n) ^ 3 / 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 :=
    ⟨_, rfl⟩
  rw [← ha] at hsmall ⊢
  have hq0 : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  obtain ⟨b1, b2⟩ := sqrt_sq_sub_bounds hq0 hsmall
  have e1 : qInc n δ f l = Real.sqrt (((2 : ℝ) ^ n)⁻¹ ^ 2 - a) := by rw [qInc, ha]
  have e2 : a / (2 * ((2 : ℝ) ^ n)⁻¹) = a * (2 : ℝ) ^ n / 2 := by field_simp
  have e3 : a ^ 2 / (2 * ((2 : ℝ) ^ n)⁻¹ ^ 3) = a ^ 2 * ((2 : ℝ) ^ n) ^ 3 / 2 := by field_simp
  rw [e1]
  constructor <;> linarith

/-- **The energy expansion** (HA3 D5): uniformly on the vertex ball `B̂_R`,
`|E_δ(Q_δ(f)) - E(f)| ≤ C_{n,R} δ²` for `0 < δ ≤ δ₂(n, R)`. -/
theorem abs_eDelta_qPoly_sub_energy_le (hd : 0 < d) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Cn δ₂ : ℝ, 0 < δ₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ f ∈ vertBall (Rd (d - 1)) n R,
      |eDelta δ (qPoly d n δ f) - energy f| ≤ Cn * δ ^ 2 := by
  obtain ⟨Kr, hKr⟩ : ∃ Kr : ℝ, Kr = (2 : ℝ) ^ n := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Kr⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * R := ⟨_, rfl⟩
  have hKr1 : 1 ≤ Kr := by rw [hKr]; exact one_le_pow₀ (by norm_num)
  have hKr0 : 0 < Kr := by linarith
  have hq0 : 0 < q := by rw [hq]; exact inv_pos.2 hKr0
  have hqKr : q * Kr = 1 := by rw [hq]; exact inv_mul_cancel₀ hKr0.ne'
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  refine ⟨(Kr ^ 2 * c ^ 2 / 2 + c ^ 4 * Kr ^ 3 * (Kr + 1)) ^ 2 + c ^ 4 * Kr ^ 3 * (Kr + 1),
    min 1 (q / (2 * c + 2)), lt_min one_pos (by positivity), fun δ hδ hδ₂ f hf => ?_⟩
  obtain ⟨hfV, hfR⟩ := hf
  have hδ1 : δ ≤ 1 := hδ₂.trans (min_le_left _ _)
  have hδc : δ * c ≤ q / 2 := by
    have h := hδ₂.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hK1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hKcast : ((2 ^ n : ℕ) : ℝ) = Kr := by rw [hKr]; push_cast; ring
  -- increments
  have hΔc : ∀ l : ℕ, l < 2 ^ n → ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ≤ c := by
    intro l hl
    have h1 := hfR (l + 1) hl
    have h2 := hfR l hl.le
    rw [Nat.cast_add, Nat.cast_one] at h1
    exact (norm_sub_le _ _).trans (by rw [hc]; linarith)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ ^ 2 * c ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hdc : t ≤ q ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (by positivity) hδc 2
    rw [mul_pow, div_pow] at h
    rw [ht]; linarith
  have hal : ∀ l : ℕ, l < 2 ^ n → 0 ≤ δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 ∧
      δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 ≤ t := fun l hl =>
    ⟨by positivity, by
      rw [ht]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hΔc l hl) 2)
        (sq_nonneg δ)⟩
  have hal_q : ∀ l : ℕ, l < 2 ^ n →
      δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
    intro l hl
    have h1 := (hal l hl).2
    have h2 : q ^ 2 / 4 ≤ q ^ 2 := by nlinarith [sq_nonneg q]
    have hq' : q = ((2 : ℝ) ^ n)⁻¹ := by rw [hq, hKr]
    rw [← hq']
    linarith
  have htKr : t * Kr ^ 2 ≤ 1 / 4 := by
    have hqK2 : q ^ 2 * Kr ^ 2 = 1 := by rw [← mul_pow, hqKr, one_pow]
    nlinarith
  -- the regular edges have length `q`
  have hreg : ∀ i, i + 1 < 2 ^ n → ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ = q := by
    intro i hi
    rw [norm_qVert_succ_sub d hd hi (hal_q i (by omega)), hq, hKr]
  -- the defects and `σ`
  obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K' = 2 ^ n - 1 := ⟨_, rfl⟩
  have hKK' : 2 ^ n = K' + 1 := by rw [hK']; omega
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ∑ l ∈ Finset.range K', (q - qInc n δ f l) := ⟨_, rfl⟩
  have hdef : ∀ l : ℕ, l < K' → δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2 ≤
      q - qInc n δ f l ∧ q - qInc n δ f l ≤
        δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2 +
          (δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2) ^ 2 * Kr ^ 3 / 2 := by
    intro l hl
    have h := qInc_defect_bounds n δ f l (hal_q l (by omega))
    rw [hq, hKr]
    exact h
  have hσ0 : 0 ≤ σ := by
    rw [hσ]
    exact Finset.sum_nonneg fun l hl =>
      le_trans (by have := (hal l (by have := Finset.mem_range.1 hl; omega)).1; positivity)
        (hdef l (Finset.mem_range.1 hl)).1
  have hK'Kr : (K' : ℝ) ≤ Kr := by
    rw [← hKcast]; exact_mod_cast (show K' ≤ 2 ^ n by omega)
  have hσle : σ ≤ Kr * t * Kr := by
    have h1 : σ ≤ K' * (t * Kr / 2 + t ^ 2 * Kr ^ 3 / 2) := by
      rw [hσ]
      calc ∑ l ∈ Finset.range K', (q - qInc n δ f l)
          ≤ ∑ _l ∈ Finset.range K', (t * Kr / 2 + t ^ 2 * Kr ^ 3 / 2) := by
            refine Finset.sum_le_sum fun l hl => (hdef l (Finset.mem_range.1 hl)).2.trans ?_
            have h := hal l (by have := Finset.mem_range.1 hl; omega)
            have h1 := mul_le_mul_of_nonneg_right h.2 hKr0.le
            have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.1 h.2 2)
              (pow_nonneg hKr0.le 3)
            linarith
        _ = K' * (t * Kr / 2 + t ^ 2 * Kr ^ 3 / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : t ^ 2 * Kr ^ 3 / 2 ≤ t * Kr / 2 := by
      have h3 : t * Kr ^ 2 ≤ 1 := by linarith
      have h4 : t ^ 2 * Kr ^ 3 = (t * Kr) * (t * Kr ^ 2) := by ring
      have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg ht0 hKr0.le)
      linarith
    have h3 : K' * (t * Kr / 2 + t ^ 2 * Kr ^ 3 / 2) ≤ Kr * (t * Kr) :=
      mul_le_mul hK'Kr (by linarith) (by positivity) hKr0.le
    linarith
  have hB1 : |σ - ∑ l ∈ Finset.range K',
      δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2| ≤
      Kr * t ^ 2 * Kr ^ 3 / 2 := by
    rw [hσ, ← Finset.sum_sub_distrib, abs_le]
    constructor
    · have : 0 ≤ ∑ l ∈ Finset.range K', (q - qInc n δ f l -
          δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2) :=
        Finset.sum_nonneg fun l hl => sub_nonneg.2 (hdef l (Finset.mem_range.1 hl)).1
      have h0 : 0 ≤ Kr * t ^ 2 * Kr ^ 3 / 2 := by positivity
      linarith
    · calc ∑ l ∈ Finset.range K', (q - qInc n δ f l -
            δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2)
          ≤ ∑ _l ∈ Finset.range K', t ^ 2 * Kr ^ 3 / 2 := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hl' := Finset.mem_range.1 hl
            have h3 := (hdef l hl').2
            have h4 := hal l (by omega)
            have h5 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h4.1 h4.2 2)
              (pow_nonneg hKr0.le 3)
            linarith
        _ = K' * (t ^ 2 * Kr ^ 3 / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ Kr * t ^ 2 * Kr ^ 3 / 2 := by
            have := mul_le_mul_of_nonneg_right hK'Kr
              (by positivity : (0 : ℝ) ≤ t ^ 2 * Kr ^ 3 / 2)
            linarith
  -- the last edge
  obtain ⟨aL, haL⟩ : ∃ aL : ℝ, aL = δ ^ 2 * ‖f (((K' : ℕ) : ℝ) / 2 ^ n)‖ ^ 2 := ⟨_, rfl⟩
  have haL_eq : aL = δ ^ 2 * ‖f (((K' : ℝ) + 1) / 2 ^ n) - f ((K' : ℝ) / 2 ^ n)‖ ^ 2 := by
    have e1 : ((K' : ℝ) + 1) / 2 ^ n = 1 := by
      have : ((K' : ℝ) + 1) = (2 : ℝ) ^ n := by
        have := hKcast
        rw [hKK'] at this
        push_cast at this
        rw [this, hKr]
      rw [this, div_self (by positivity)]
    rw [haL, e1, hfV.2.1, zero_sub, norm_neg]
  have haL0 : 0 ≤ aL := by rw [haL]; positivity
  have haLt : aL ≤ t := by rw [haL_eq]; exact (hal K' (by omega)).2
  have hknot : 1 - qKnot n δ f K' = q + σ := by
    rw [hσ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, qKnot]
    have : (K' : ℝ) * q + q = 1 := by
      have h1 : ((2 ^ n : ℕ) : ℝ) = K' + 1 := by rw [hKK']; push_cast; ring
      rw [hKcast] at h1
      rw [← add_one_mul, ← h1, mul_comm, hqKr]
    linarith
  have hpoly : polyLen (qPoly d n δ f) = 1 + (Real.sqrt ((q + σ) ^ 2 + aL) - q) := by
    rw [qPoly, polyLen_range_map]
    change plen (qVert d n δ f) (2 ^ n) = _
    rw [hKK', plen_succ]
    have hsum : plen (qVert d n δ f) K' = K' * q := by
      unfold plen
      rw [Finset.sum_congr rfl fun i hi => hreg i (by have := Finset.mem_range.1 hi; omega),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hlast := norm_qVert_last_sq d hd (n := n) (δ := δ) (f := f)
    rw [← hK', hKK', hknot, ← haL] at hlast
    rw [hsum, ← Real.sqrt_sq (norm_nonneg (qVert d n δ f (K' + 1) - qVert d n δ f K')), hlast]
    have h1 : ((2 ^ n : ℕ) : ℝ) = K' + 1 := by rw [hKK']; push_cast; ring
    rw [hKcast] at h1
    have h2 : (K' : ℝ) * q = 1 - q := by
      have := hqKr
      rw [h1] at this
      linarith
    rw [h2]
    ring
  -- the energy
  have hEa : δ ^ 2 * energy f = ∑ l ∈ Finset.range K',
      δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 * Kr / 2 + aL * Kr / 2 := by
    rw [HigherDimLFPP.Var.Vg_energy hfV, hKK', Finset.sum_range_succ, haL_eq, hKr, mul_add,
      mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · ring
  have hEm : energy f ≤ Kr ^ 2 * c ^ 2 / 2 := by
    rw [HigherDimLFPP.Var.Vg_energy hfV]
    have hK2 : (2 : ℝ) ^ n = Kr := hKr.symm
    have h1 : ∑ k ∈ Finset.range (2 ^ n), ‖f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)‖ ^ 2 ≤
        Kr * c ^ 2 := by
      calc ∑ k ∈ Finset.range (2 ^ n), ‖f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)‖ ^ 2
          ≤ ∑ _k ∈ Finset.range (2 ^ n), c ^ 2 :=
            Finset.sum_le_sum fun k hk =>
              pow_le_pow_left₀ (norm_nonneg _) (hΔc k (Finset.mem_range.1 hk)) 2
        _ = Kr * c ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKcast]
    calc (2 : ℝ) ^ n / 2 * ∑ k ∈ Finset.range (2 ^ n),
          ‖f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)‖ ^ 2
        ≤ (2 : ℝ) ^ n / 2 * (Kr * c ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Kr ^ 2 * c ^ 2 / 2 := by rw [hK2]; ring
  rw [eDelta, hpoly]
  exact abs_log_excess_sub_le hq0 hqKr hδ hδ1 ht hσ0 hσle hB1 haL0 haLt hEa hEm

end Energy

end HigherDimLFPP.Upper
