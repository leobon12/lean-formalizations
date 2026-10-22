import HigherDimLQGContinuity.Routing.GeneralPosition
import HigherDimLQGContinuity.Topology.Polygonal

/-!
# Two leads in a reserved box: definitions, constants and box geometry

Packet Q2 (ruling N9). Sources: planning audit `planning/audits/NA2-section-4.md`, §1.4 and
Details (c) **R3**; blueprint Part B, Lemma `b:lem-leads` ([C] p. 11–12, l. 566–601).

* `resBox m L = m + [-L, L]^d` (the reserved box `R`) and `resBoxInt m L = m + (-L, L)^d` (its
  interior, `interior_resBox`).
* The constants of `b:lem-leads`: `leadU A β L t₀ = min {(t₀/(2A))^{1/β}, L/8}` (`u_lead`),
  `leadR A α β L t₀ = r` with `10 r = ½ c₄₁(2A, α, β) (u_lead/2)^{1/(αβ)²}` (`ten_leadR_eq`; in Lean
  `10 r = polygonalClearanceConst (2A) α β · u_lead^{1/(αβ)²}`), and
  `leadN d r = ⌊(16√d·5/(20r) + 2)^d⌋ + 5` (`N`; `leadN_le`: `N ≤ ((4√d + 2)^d + 5) r^{-d}`;
  `polygonal_count_le`: Q1's edge count at `u_lead` is `≤ (16√d·5/(20r) + 2)^d`).
* `IsLead`: the properties (L1)–(L5) of one lead (a grid sequence `y 0 = p, …, y n`), the output
  structure of `exists_leads` (file `Routing/Leads.lean`).
* Box geometry used by the construction: coordinates of segment points (`abs_coord_lineMap_sub_le`),
  the homothety `resHom m λ` pushing vertices inward, the displacement of a segment under moves of
  its endpoints (`exists_mem_segment_near`), and the port incidence (L5) in abstract form
  (`dist_port_le`, `mem_resBoxInt_of_near_segment`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGContinuity.Topology (ArcModuli clearanceConst polygonalClearanceConst
  polygonalConst)

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-! ### The reserved box -/

/-- The reserved box `m + [-L, L]^d`. -/
def resBox (m : Rd d) (L : ℝ) : Set (Rd d) := {x | ∀ k, |x k - m k| ≤ L}

/-- The open box `m + (-L, L)^d`, the interior of `resBox m L` (`interior_resBox`). -/
def resBoxInt (m : Rd d) (L : ℝ) : Set (Rd d) := {x | ∀ k, |x k - m k| < L}

/-- Coordinates are `1`-Lipschitz. -/
lemma abs_coord_sub_le_norm (x y : Rd d) (k : Fin d) : |x k - y k| ≤ ‖x - y‖ := by
  have := PiLp.norm_apply_le (x - y) k
  simpa [Real.norm_eq_abs] using this

lemma resBoxInt_subset_resBox (m : Rd d) (L : ℝ) : resBoxInt m L ⊆ resBox m L :=
  fun _ hx k => (hx k).le

lemma isOpen_resBoxInt (m : Rd d) (L : ℝ) : IsOpen (resBoxInt m L) := by
  have : resBoxInt m L = ⋂ k, {x : Rd d | |x k - m k| < L} := by
    ext x; simp [resBoxInt]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const

lemma isClosed_resBox (m : Rd d) (L : ℝ) : IsClosed (resBox m L) := by
  have : resBox m L = ⋂ k, {x : Rd d | |x k - m k| ≤ L} := by
    ext x; simp [resBox]
  rw [this]
  exact isClosed_iInter fun k => isClosed_le (by fun_prop) continuous_const

/-- The coordinates of `a + ς (b - a)` are convex combinations. -/
lemma abs_coord_lineMap_sub_le (a b m : Rd d) (k : Fin d) {ς : ℝ} (h0 : 0 ≤ ς) (h1 : ς ≤ 1) :
    |(a + ς • (b - a)) k - m k| ≤ (1 - ς) * |a k - m k| + ς * |b k - m k| := by
  have he : (a + ς • (b - a)) k - m k = (1 - ς) * (a k - m k) + ς * (b k - m k) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - ς), abs_of_nonneg h0]

/-- Coordinates of segment points are bounded by those of the endpoints. -/
lemma abs_coord_sub_le_of_mem_segment {a b x m : Rd d} (hx : x ∈ segment ℝ a b) (k : Fin d)
    {M : ℝ} (ha : |a k - m k| ≤ M) (hb : |b k - m k| ≤ M) : |x k - m k| ≤ M := by
  rw [segment_eq_image'] at hx
  obtain ⟨ς, ⟨h0, h1⟩, rfl⟩ := hx
  refine (abs_coord_lineMap_sub_le a b m k h0 h1).trans ?_
  nlinarith

lemma convex_resBox (m : Rd d) (L : ℝ) : Convex ℝ (resBox m L) := by
  intro x hx y hy a b ha hb hab k
  have hseg : a • x + b • y ∈ segment ℝ x y := ⟨a, b, ha, hb, hab, rfl⟩
  exact abs_coord_sub_le_of_mem_segment hseg k (hx k) (hy k)

lemma convex_resBoxInt (m : Rd d) (L : ℝ) : Convex ℝ (resBoxInt m L) := by
  intro x hx y hy a b ha hb hab k
  have hseg : a • x + b • y ∈ segment ℝ x y := ⟨a, b, ha, hb, hab, rfl⟩
  have hmax := abs_coord_sub_le_of_mem_segment hseg k (le_max_left (|x k - m k|) (|y k - m k|))
    (le_max_right _ _)
  exact hmax.trans_lt (max_lt (hx k) (hy k))

/-- The open box is the interior of the closed box. -/
lemma interior_resBox (m : Rd d) (L : ℝ) : interior (resBox m L) = resBoxInt m L := by
  apply Subset.antisymm
  · intro x hx k
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    by_contra hk
    push Not at hk
    -- move by `ε/2` along `e_k` away from `m`
    set s : ℝ := if 0 ≤ x k - m k then 1 else -1 with hs
    set z : Rd d := x + (ε / 2) • EuclideanSpace.single k s with hz
    have hzx : dist z x < ε := by
      rw [dist_eq_norm, hz, add_sub_cancel_left, norm_smul, PiLp.norm_single,
        Real.norm_of_nonneg (by positivity)]
      have : ‖s‖ = 1 := by rw [hs]; split_ifs <;> simp
      rw [this]; linarith
    have hzR := interior_subset (hball hzx) k
    have hzk : z k - m k = (x k - m k) + ε / 2 * s := by
      simp [hz]; ring
    rw [hzk] at hzR
    by_cases h0 : 0 ≤ x k - m k
    · have hs1 : s = 1 := by simp only [hs, h0, ↓reduceIte]
      rw [hs1, mul_one, abs_of_nonneg (by linarith)] at hzR
      rw [abs_of_nonneg h0] at hk
      linarith
    · have hs1 : s = -1 := by simp only [hs, h0, ↓reduceIte]
      push Not at h0
      rw [hs1, mul_neg_one, abs_of_neg (by linarith)] at hzR
      rw [abs_of_neg h0] at hk
      linarith
  · exact interior_maximal (resBoxInt_subset_resBox m L) (isOpen_resBoxInt m L)

/-- Points of the closed box are within `√d L` of the centre. -/
lemma norm_sub_le_of_mem_resBox {m x : Rd d} {L : ℝ} (hL : 0 ≤ L) (hx : x ∈ resBox m L) :
    ‖x - m‖ ≤ √(d : ℝ) * L :=
  norm_le_sqrt_mul_of_abs_le hL fun k => by simpa using hx k

/-- Two points of the closed box are within `√d (2L)` of each other. -/
lemma norm_sub_le_of_mem_resBox₂ {m x y : Rd d} {L : ℝ} (hL : 0 ≤ L) (hx : x ∈ resBox m L)
    (hy : y ∈ resBox m L) : ‖x - y‖ ≤ √(d : ℝ) * (2 * L) := by
  refine norm_le_sqrt_mul_of_abs_le (by linarith) fun k => ?_
  have h1 := hx k
  have h2 := hy k
  have : (x - y) k = (x k - m k) - (y k - m k) := by simp
  rw [this]
  exact (abs_sub _ _).trans (by linarith)

/-- A point at Euclidean distance `< L` from the centre lies in the open box. -/
lemma mem_resBoxInt_of_norm_lt {m x : Rd d} {L : ℝ} (hx : ‖x - m‖ < L) : x ∈ resBoxInt m L :=
  fun k => (abs_coord_sub_le_norm x m k).trans_lt hx

/-! ### Moves of vertices -/

/-- The homothety `z ↦ m + (1 - λ)(z - m)` (pushes the vertices of a lead inward). -/
def resHom (m : Rd d) (lam : ℝ) (z : Rd d) : Rd d := m + (1 - lam) • (z - m)

lemma resHom_coord (m : Rd d) (lam : ℝ) (z : Rd d) (k : Fin d) :
    resHom m lam z k - m k = (1 - lam) * (z k - m k) := by
  simp [resHom]

lemma norm_resHom_sub (m : Rd d) {lam : ℝ} (hlam : 0 ≤ lam) (z : Rd d) :
    ‖resHom m lam z - z‖ = lam * ‖z - m‖ := by
  have : resHom m lam z - z = (-lam) • (z - m) := by
    simp only [resHom]; module
  rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hlam]

/-- Moving the endpoints of a segment by at most `D` moves each of its points by at most `D`. -/
lemma exists_mem_segment_near {a b a' b' x : Rd d} {D : ℝ} (hx : x ∈ segment ℝ a b)
    (ha : ‖a' - a‖ ≤ D) (hb : ‖b' - b‖ ≤ D) : ∃ x' ∈ segment ℝ a' b', ‖x - x'‖ ≤ D := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  refine ⟨s • a' + t • b', ⟨s, t, hs, ht, hst, rfl⟩, ?_⟩
  have he : s • a + t • b - (s • a' + t • b') = s • (a - a') + t • (b - b') := by module
  rw [he]
  calc ‖s • (a - a') + t • (b - b')‖ ≤ ‖s • (a - a')‖ + ‖t • (b - b')‖ := norm_add_le _ _
    _ = s * ‖a' - a‖ + t * ‖b' - b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht,
          norm_sub_rev a, norm_sub_rev b]
    _ ≤ s * D + t * D := add_le_add (mul_le_mul_of_nonneg_left ha hs)
        (mul_le_mul_of_nonneg_left hb ht)
    _ = D := by rw [← add_mul, hst, one_mul]

/-! ### Port incidence (L5), abstract form -/

/-- Points near the first segment `[p, y]` (with `y` at coordinate margin `μ`) that lie outside the
open box are near the port `p`. -/
lemma dist_port_le {m p y : Rd d} {L μ ω : ℝ} (hp : p ∈ resBox m L)
    (hy : ∀ k, |y k - m k| + μ ≤ L) (hμ : 0 < μ) {x z : Rd d} (hx : x ∈ segment ℝ p y)
    (hzx : dist z x ≤ ω) (hz : z ∉ resBoxInt m L) : dist z p ≤ ω + ω / μ * ‖y - p‖ := by
  rw [segment_eq_image'] at hx
  obtain ⟨ς, ⟨h0, h1⟩, rfl⟩ := hx
  simp only [resBoxInt, Set.mem_ofPred_eq, not_forall, not_lt] at hz
  obtain ⟨k, hk⟩ := hz
  have h2 := abs_coord_lineMap_sub_le p y m k h0 h1
  have h3 := abs_coord_sub_le_norm z (p + ς • (y - p)) k
  rw [← dist_eq_norm] at h3
  have h4 : |z k - m k| ≤ |z k - (p + ς • (y - p)) k| + |(p + ς • (y - p)) k - m k| := by
    have := abs_add_le (z k - (p + ς • (y - p)) k) ((p + ς • (y - p)) k - m k)
    rwa [sub_add_sub_cancel] at this
  have hpk := hp k
  have hyk := hy k
  -- `ς μ ≤ ω`
  have hςμ : ς * μ ≤ ω := by nlinarith
  have hς : ς ≤ ω / μ := by rw [le_div_iff₀ hμ]; exact hςμ
  calc dist z p ≤ dist z (p + ς • (y - p)) + dist (p + ς • (y - p)) p := dist_triangle _ _ _
    _ ≤ ω + ς * ‖y - p‖ := by
        refine add_le_add hzx (le_of_eq ?_)
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h0]
    _ ≤ ω + ω / μ * ‖y - p‖ := by
        gcongr

/-- Points near a segment whose endpoints have coordinate margin `μ > ω` lie in the open box. -/
lemma mem_resBoxInt_of_near_segment {m a b : Rd d} {L μ ω : ℝ}
    (ha : ∀ k, |a k - m k| + μ ≤ L) (hb : ∀ k, |b k - m k| + μ ≤ L) (hωμ : ω < μ)
    {x z : Rd d} (hx : x ∈ segment ℝ a b) (hzx : dist z x ≤ ω) : z ∈ resBoxInt m L := by
  intro k
  have hxk := abs_coord_sub_le_of_mem_segment hx k (m := m) (M := L - μ)
    (by linarith [ha k]) (by linarith [hb k])
  have h3 := abs_coord_sub_le_norm z x k
  rw [← dist_eq_norm] at h3
  have h4 : |z k - m k| ≤ |z k - x k| + |x k - m k| := by
    have := abs_add_le (z k - x k) (x k - m k)
    rwa [sub_add_sub_cancel] at this
  linarith

/-! ### The constants of `b:lem-leads` -/

/-- `u_lead = min {(t₀/(2A))^{1/β}, L/8}`. -/
def leadU (A β L t₀ : ℝ) : ℝ := min ((t₀ / (2 * A)) ^ β⁻¹) (L / 8)

/-- The lead clearance unit `r`: `10 r = ½ c₄₁(2A, α, β) (u_lead/2)^{1/(αβ)²}` (`ten_leadR_eq`). -/
def leadR (A α β L t₀ : ℝ) : ℝ :=
  polygonalClearanceConst (2 * A) α β * leadU A β L t₀ ^ ((α * β) ^ 2)⁻¹ / 10

/-- The edge bound `N = ⌊(16√d·5/(20r) + 2)^d⌋ + 5`. -/
def leadN (d : ℕ) (r : ℝ) : ℕ := ⌊(16 * √(d : ℝ) * 5 / (20 * r) + 2) ^ d⌋₊ + 5

section Constants

variable {A α β L t₀ : ℝ}

lemma leadU_pos (hA : 0 < A) (ht₀ : 0 < t₀) (hL : 0 < L) : 0 < leadU A β L t₀ :=
  lt_min (Real.rpow_pos_of_pos (by positivity) _) (by positivity)

lemma leadU_le_L : leadU A β L t₀ ≤ L / 8 := min_le_right _ _

lemma leadU_le_pow : leadU A β L t₀ ≤ (t₀ / (2 * A)) ^ β⁻¹ := min_le_left _ _

lemma inv_sq_ge_one (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 ≤ ((α * β) ^ 2)⁻¹ := by
  have hab : 0 < α * β := mul_pos hα hβ
  have hab1 : α * β ≤ 1 := by nlinarith
  exact (one_le_inv₀ (pow_pos hab 2)).2 (pow_le_one₀ hab.le hab1)

lemma polygonalClearanceConst_le_half {A' : ℝ} (hA' : 1 ≤ A') (hα : 0 < α) (hβ : 0 < β) :
    polygonalClearanceConst A' α β ≤ 1 / 2 := by
  unfold polygonalClearanceConst
  have h1 := Topology.clearanceConst_le_one (α := α) (β := β) hA' hα hβ
  have h0 := Topology.clearanceConst_pos (α := α) (β := β) (by linarith : (0 : ℝ) < A')
  have h2 : (1 : ℝ) ≤ 2 ^ ((α * β) ^ 2)⁻¹ :=
    Real.one_le_rpow (by norm_num) (inv_nonneg.2 (sq_nonneg _))
  have h3 : clearanceConst A' α β / 2 ^ ((α * β) ^ 2)⁻¹ ≤ 1 :=
    (div_le_one (by linarith)).2 (h1.trans h2)
  linarith

lemma leadR_pos (hA : 1 ≤ A) (ht₀ : 0 < t₀) (hL : 0 < L) : 0 < leadR A α β L t₀ := by
  unfold leadR
  have := Topology.polygonalClearanceConst_pos (α := α) (β := β) (by linarith : (0 : ℝ) < 2 * A)
  have := leadU_pos (β := β) (by linarith : (0 : ℝ) < A) ht₀ hL
  positivity

/-- `10 r ≤ u_lead / 2`. -/
lemma ten_leadR_le (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ht₀ : 0 < t₀) (hL : 0 < L) (hL1 : L ≤ 1) :
    10 * leadR A α β L t₀ ≤ leadU A β L t₀ / 2 := by
  have hU := leadU_pos (β := β) (by linarith : (0 : ℝ) < A) ht₀ hL
  have hU1 : leadU A β L t₀ ≤ 1 := leadU_le_L.trans (by linarith)
  have hp := inv_sq_ge_one hα hα1 hβ hβ1
  have hpow : leadU A β L t₀ ^ ((α * β) ^ 2)⁻¹ ≤ leadU A β L t₀ := by
    have := Real.rpow_le_rpow_of_exponent_ge hU hU1 hp
    rwa [Real.rpow_one] at this
  have hc := polygonalClearanceConst_le_half (by linarith : (1 : ℝ) ≤ 2 * A) hα hβ
  have hc0 := Topology.polygonalClearanceConst_pos (α := α) (β := β)
    (by linarith : (0 : ℝ) < 2 * A)
  have hpow0 : 0 ≤ leadU A β L t₀ ^ ((α * β) ^ 2)⁻¹ := Real.rpow_nonneg hU.le _
  unfold leadR
  nlinarith

/-- The blueprint form of `r`: `10 r = ½ c₄₁(2A, α, β) (u_lead/2)^{1/(αβ)²}`. -/
lemma ten_leadR_eq (hA : 0 < A) (ht₀ : 0 < t₀) (hL : 0 < L) :
    10 * leadR A α β L t₀ =
      1 / 2 * clearanceConst (2 * A) α β * (leadU A β L t₀ / 2) ^ ((α * β) ^ 2)⁻¹ := by
  have hU := leadU_pos (β := β) hA ht₀ hL
  unfold leadR polygonalClearanceConst
  rw [Real.div_rpow hU.le (by norm_num)]
  have : (0 : ℝ) < 2 ^ ((α * β) ^ 2)⁻¹ := by positivity
  field_simp

lemma leadR_le_L (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ht₀ : 0 < t₀) (hL : 0 < L) (hL1 : L ≤ 1) : leadR A α β L t₀ ≤ L / 160 := by
  have := ten_leadR_le hA hα hα1 hβ hβ1 ht₀ hL hL1
  have := leadU_le_L (A := A) (β := β) (L := L) (t₀ := t₀)
  linarith

/-- The edge count of Lemma 4.1′ (polygonal form, constants `(2A, α, β)`, `R₀ = 4`) at
`u = u_lead` is at most `(16√d·5/(20r) + 2)^d`. -/
lemma polygonal_count_le (hd : 1 ≤ d) (hA : 1 ≤ A) (hα : 0 < α) (hβ : 0 < β) (ht₀ : 0 < t₀)
    (hL : 0 < L) :
    polygonalConst d (2 * A) α β 4 * leadU A β L t₀ ^ (-((d : ℝ) / (α * β) ^ 2)) ≤
      (16 * √(d : ℝ) * 5 / (20 * leadR A α β L t₀) + 2) ^ d := by
  set U := leadU A β L t₀ with hUdef
  have hU : 0 < U := leadU_pos (β := β) (by linarith : (0 : ℝ) < A) ht₀ hL
  set p := ((α * β) ^ 2)⁻¹ with hp
  set c' := clearanceConst (2 * A) α β / 2 ^ p with hc'
  have hc0 : 0 < clearanceConst (2 * A) α β :=
    Topology.clearanceConst_pos (by linarith : (0 : ℝ) < 2 * A)
  have hc1 : clearanceConst (2 * A) α β ≤ 1 :=
    Topology.clearanceConst_le_one (by linarith : (1 : ℝ) ≤ 2 * A) hα hβ
  have h2p : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) (inv_nonneg.2 (sq_nonneg _))
  have hc'0 : 0 < c' := by positivity
  have hc'1 : c' ≤ 1 := (div_le_one (by linarith)).2 (hc1.trans h2p)
  set V := U ^ p with hV
  have hV0 : 0 < V := Real.rpow_pos_of_pos hU _
  -- `20 r = c' V`
  have h20 : 20 * leadR A α β L t₀ = c' * V := by
    rw [leadR, polygonalClearanceConst, ← hUdef, ← hp, ← hc', ← hV]
    ring
  -- `U^{-(d/(αβ)²)} = (V⁻¹)^d`
  have hUd : U ^ (-((d : ℝ) / (α * β) ^ 2)) = V⁻¹ ^ d := by
    rw [div_eq_mul_inv, ← hp, mul_comm, neg_mul_eq_mul_neg, Real.rpow_mul hU.le, ← hV,
      Real.rpow_neg hV0.le, Real.rpow_natCast, inv_pow]
  rw [hUd, h20]
  unfold polygonalConst
  have hsd : 1 ≤ √(d : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  set a := (8 * √(d : ℝ) * 4 + 3) / (c' * V) with ha
  set b := 1 / (c' * V) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hd0 : d ≠ 0 := by omega
  have hlhs : (((8 * √(d : ℝ) * 4 + 3) / c') ^ d + 2) * V⁻¹ ^ d ≤ a ^ d + (2 * b) ^ d := by
    have e1 : ((8 * √(d : ℝ) * 4 + 3) / c') ^ d * V⁻¹ ^ d = a ^ d := by
      rw [← mul_pow, ha]; congr 1; field_simp
    have e2 : V⁻¹ ^ d ≤ b ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      rw [hb, one_div, mul_inv]
      calc V⁻¹ = 1 * V⁻¹ := (one_mul _).symm
        _ ≤ c'⁻¹ * V⁻¹ := mul_le_mul_of_nonneg_right ((one_le_inv₀ hc'0).2 hc'1)
            (by positivity)
    have e3 : 2 * b ^ d ≤ (2 * b) ^ d := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb0 _)
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (((8 * √(d : ℝ) * 4 + 3) / c') ^ d + 2) * V⁻¹ ^ d
        = ((8 * √(d : ℝ) * 4 + 3) / c') ^ d * V⁻¹ ^ d + 2 * V⁻¹ ^ d := by ring
      _ ≤ a ^ d + 2 * b ^ d := by rw [e1]; nlinarith
      _ ≤ a ^ d + (2 * b) ^ d := by linarith
  refine hlhs.trans ((pow_add_pow_le ha0 (by positivity) hd0).trans ?_)
  apply pow_le_pow_left₀ (by positivity)
  rw [ha, hb]
  have hcV : 0 < c' * V := by positivity
  have e : (8 * √(d : ℝ) * 4 + 3) / (c' * V) + 2 * (1 / (c' * V)) =
      (8 * √(d : ℝ) * 4 + 5) / (c' * V) := by
    field_simp; ring
  rw [e]
  have : (8 * √(d : ℝ) * 4 + 5) / (c' * V) ≤ 16 * √(d : ℝ) * 5 / (c' * V) :=
    div_le_div_of_nonneg_right (by nlinarith) hcV.le
  linarith

/-- The edge bound in the packet form `N ≤ C r^{-d}`, `C = (4√d + 2)^d + 5` (for `0 < r ≤ 1`). -/
lemma leadN_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (leadN d r : ℝ) ≤ ((4 * √(d : ℝ) + 2) ^ d + 5) * r⁻¹ ^ d := by
  have hX : 0 ≤ (16 * √(d : ℝ) * 5 / (20 * r) + 2) ^ d := by positivity
  have h1 : (⌊(16 * √(d : ℝ) * 5 / (20 * r) + 2) ^ d⌋₊ : ℝ) ≤
      (16 * √(d : ℝ) * 5 / (20 * r) + 2) ^ d := Nat.floor_le hX
  have hri : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 hr1
  have h2 : 16 * √(d : ℝ) * 5 / (20 * r) + 2 ≤ (4 * √(d : ℝ) + 2) * r⁻¹ := by
    have e : 16 * √(d : ℝ) * 5 / (20 * r) = 4 * √(d : ℝ) * r⁻¹ := by field_simp; ring
    rw [e]
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have h3 : (16 * √(d : ℝ) * 5 / (20 * r) + 2) ^ d ≤ ((4 * √(d : ℝ) + 2) * r⁻¹) ^ d :=
    pow_le_pow_left₀ (by positivity) h2 d
  have h4 : (1 : ℝ) ≤ r⁻¹ ^ d := one_le_pow₀ hri
  rw [mul_pow] at h3
  unfold leadN
  push_cast
  nlinarith

end Constants

/-! ### The output structure -/

/-- **One lead** (blueprint `b:lem-leads`, (L1)–(L5) for one port): a grid sequence
`y 0 = p, y 1, …, y n` in the box `R = resBox m L` with `2 ≤ n ≤ N`, last vertex within `√d ν/2` of
the arc endpoint `g` (L1), segments at distance `≥ 7r` from `γ(I)` (L2), non-port vertices at
coordinate margin `r/(4√d)` from `∂R` (L3), distinct vertices, nonconsecutive segments at distance
`≥ c₁ν³` (`c₁ = gpC1 4 = 1/100`) and consecutive ones meeting only at their common vertex (L4), and
the `ω`-neighbourhood of the polygon leaves the open box only within `(4dL + 1)ω/r` of the port
(L5). -/
structure IsLead (m : Rd d) (L : ℝ) (p g : Rd d) (I : Set ℝ) (γ : ℝ → Rd d) (r ν : ℝ)
    (o : Rd d) (N : ℕ) (n : ℕ) (y : ℕ → Rd d) : Prop where
  start : y 0 = p
  two_le : 2 ≤ n
  le_N : n ≤ N
  onGrid : ∀ j ≤ n, OnGrid ν o (y j)
  mem_box : ∀ j ≤ n, y j ∈ resBox m L
  attach : ‖y n - g‖ ≤ √(d : ℝ) * (ν / 2)
  clear : ∀ j < n, ∀ x ∈ segment ℝ (y j) (y (j + 1)), ∀ t ∈ I, 7 * r ≤ dist x (γ t)
  margin : ∀ j, 1 ≤ j → j ≤ n → ∀ k, |y j k - m k| + r / (4 * √(d : ℝ)) ≤ L
  injOn : ∀ j ≤ n, ∀ j' ≤ n, y j = y j' → j = j'
  sep : ∀ j j', j + 2 ≤ j' → j' < n → ∀ x ∈ segment ℝ (y j) (y (j + 1)),
    ∀ x' ∈ segment ℝ (y j') (y (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x'
  inc : ∀ j, j + 1 < n →
    segment ℝ (y j) (y (j + 1)) ∩ segment ℝ (y (j + 1)) (y (j + 2)) = {y (j + 1)}
  port : ∀ ω, 0 < ω → ω ≤ r / (8 * √(d : ℝ)) → ∀ z : Rd d,
    (∃ j < n, ∃ x ∈ segment ℝ (y j) (y (j + 1)), dist z x ≤ ω) → z ∉ resBoxInt m L →
      dist z p ≤ (4 * d * L + 1) * ω / r

end HigherDimLQGContinuity.Routing

end
