import HigherDimLFPP.Var.Lemma22

/-!
# Lemma 2.2, (2.9): the near-optimal finite family `F_{n,d}`

Paper §2, Lemma 2.2, (2.9) (`source/higher-dimensional-lfpp-limit.txt` l. 255–257 and 280–292),
in the Dudley-free form of audit HA1 (§3.4, finding HA1-F9, Details D10): for every `n ≥ 1` (not
only for large `n`) there is a finite `F ⊆ V_{n,d}` containing `0` with
`E(f) ≤ e_{n,d}` on `F`, `E max_F G_d ≥ 4 e_{n,d} - 1` and `log(2|F|) ≤ C n 2ⁿ`.

Proof (HA1 D10, with the rounding cells of `LQGDimension.L23.low_part`):
1. `W(e) = 4e` gives a finite `F₀` in the energy ball `{E ≤ e}` with `E max_{F₀} G > 4e - 1/2`.
2. Round the coordinates of the node values to the grid `aℤ` (`nodeLabel`); choose one
   representative `c_λ ∈ F₀` per label `λ` and put `F = {0} ∪ {c_λ}` (`exists_cover`).
3. Pointwise `max_{F₀} G ≤ max_F G + max_λ max_{f ∈ cell λ} (G(f) - G(c_λ))`.  Within a cell the
   node values differ by `≤ √m a`, so `Var(G(f) - G(c_λ)) ≤ 2π √m a` and `E(f - c_λ) ≤ 2·4ⁿ m a²`;
   by the translation identity (HA1 D2.6, `inner_sub_sub_of_gram`) the mean of the cell maximum is
   an energy-ball quantity `≤ W(2·4ⁿ m a²)`.  Gaussian concentration over the cells
   (`LQGDimension.L23.integral_fsup_fsup_le`) bounds the expected error by
   `log #labels / t + W(r) + π² t σ² / 8`.
4. With `a = u² / (4ⁿ (w+1)²)`, `u = 1/(256 π³ m²)`, `t = 8(log #labels + 1)` the error is
   `≤ 1/2`, and `log #labels ≤ C n 2ⁿ` (using `e ≤ C n` from (2.8)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-- **(2.9)** (HA1 Details (c); for all `n ≥ 1`, with `0 ∈ F`, HA1-F9). -/
def Lemma22b (d : ℕ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ F : Finset (Vg (Rd (d - 1)) n),
    (∃ f ∈ F, ∀ x, (f : ℝ → Rd (d - 1)) x = 0) ∧
    (∀ f ∈ F, energy (f : ℝ → Rd (d - 1)) ≤ eN n d) ∧
    4 * eN n d - 1 ≤
      LQGDimension.gaussianExpectedMax F (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 ∧
    Real.log (2 * F.card) ≤ C * n * 2 ^ n

namespace Var

/-! ## The canonical distance and the translation identity (HA1 D2.6) -/

section Translation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `gCov a b = π (∫‖a‖ + ∫‖b‖ - ∫‖a - b‖)` for continuous `a, b`. -/
lemma gCov_eq_of_continuous {a b : ℝ → E} (ha : Continuous a) (hb : Continuous b) :
    gCov a b = Real.pi * ((∫ x in (0 : ℝ)..1, ‖a x‖) + (∫ x in (0 : ℝ)..1, ‖b x‖) -
      ∫ x in (0 : ℝ)..1, ‖a x - b x‖) := by
  have ia := ha.norm.intervalIntegrable (μ := volume) 0 1
  have ib := hb.norm.intervalIntegrable (μ := volume) 0 1
  have iab : IntervalIntegrable (fun x => ‖a x - b x‖) volume 0 1 :=
    (ha.sub hb).norm.intervalIntegrable 0 1
  unfold gCov
  rw [intervalIntegral.integral_sub (ia.add ib) iab, intervalIntegral.integral_add ia ib]

/-- The canonical distance (2.2) for an indexed Gram realization of `gCov`:
`‖T a - T b‖² = 2π ∫₀¹ ‖φ a - φ b‖`. -/
lemma norm_sub_sq_of_gram {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ι → ℝ → E) (T : ι → H) {a b : ι} (ha : Continuous (φ a)) (hb : Continuous (φ b))
    (haa : ⟪T a, T a⟫ = gCov (φ a) (φ a)) (hbb : ⟪T b, T b⟫ = gCov (φ b) (φ b))
    (hab : ⟪T a, T b⟫ = gCov (φ a) (φ b)) :
    ‖T a - T b‖ ^ 2 = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖φ a x - φ b x‖ := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, haa, hbb,
    hab, gCov_self, gCov_self, gCov_eq_of_continuous ha hb]
  ring

/-- **Translation identity** (HA1 D2.6): for a Gram realization `T` of `gCov` on `{f, g, c}`,
`⟪T f - T c, T g - T c⟫ = gCov (f - c) (g - c)`; so `(G(f) - G(c))_f` has the law of
`(G(f - c))_f`. -/
lemma inner_sub_sub_of_gram {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ι → ℝ → E) (T : ι → H) {f g c : ι} (hf : Continuous (φ f)) (hg : Continuous (φ g))
    (hc : Continuous (φ c)) (hff : ⟪T f, T f⟫ = gCov (φ f) (φ f))
    (hgg : ⟪T g, T g⟫ = gCov (φ g) (φ g)) (hcc : ⟪T c, T c⟫ = gCov (φ c) (φ c))
    (hfg : ⟪T f, T g⟫ = gCov (φ f) (φ g)) (hfc : ⟪T f, T c⟫ = gCov (φ f) (φ c))
    (hgc : ⟪T g, T c⟫ = gCov (φ g) (φ c)) :
    ⟪T f - T c, T g - T c⟫ = gCov (φ f - φ c) (φ g - φ c) := by
  have h1 := norm_sub_sq_of_gram φ T hf hc hff hcc hfc
  have h2 := norm_sub_sq_of_gram φ T hg hc hgg hcc hgc
  have h3 := norm_sub_sq_of_gram φ T hf hg hff hgg hfg
  have hpol : ⟪T f - T c, T g - T c⟫ =
      (‖T f - T c‖ ^ 2 + ‖T g - T c‖ ^ 2 - ‖T f - T g‖ ^ 2) / 2 := by
    have e : T f - T g = (T f - T c) - (T g - T c) := by abel
    have h4 : ‖T f - T g‖ ^ 2 =
        ‖T f - T c‖ ^ 2 - 2 * ⟪T f - T c, T g - T c⟫ + ‖T g - T c‖ ^ 2 := by
      rw [e]
      exact norm_sub_sq_real _ _
    linarith
  have e2 : ∫ x in (0 : ℝ)..1, ‖(φ f - φ c) x - (φ g - φ c) x‖ =
      ∫ x in (0 : ℝ)..1, ‖φ f x - φ g x‖ := by
    congr 1
    funext x
    simp only [Pi.sub_apply]
    congr 1
    abel
  rw [hpol, h1, h2, h3, gCov_eq_of_continuous (hf.sub hc) (hg.sub hc), e2]
  simp only [Pi.sub_apply]
  ring

end Translation

/-! ## Energy of a profile that is small at the nodes -/

section EnergyNodes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A profile of `V_n(E)` bounded by `δ` at the mesh points has energy at most `2 · 4ⁿ δ²`.
(Port of `LQGDimension.L23.energy_le_of_nodes`.) -/
lemma energy_le_of_nodes {n : ℕ} {h : ℝ → E} (hh : h ∈ Vg E n) {δ : ℝ}
    (hnode : ∀ k : ℕ, k ≤ 2 ^ n → ‖h ((k : ℝ) / 2 ^ n)‖ ≤ δ) :
    energy h ≤ 2 * 4 ^ n * δ ^ 2 := by
  rw [Vg_energy hh]
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      ‖h (((k : ℝ) + 1) / 2 ^ n) - h ((k : ℝ) / 2 ^ n)‖ ^ 2 ≤ (2 * δ) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have h1 := hnode k hk'.le
    have h2 := hnode (k + 1) hk'
    push_cast at h2
    have h3 : ‖h (((k : ℝ) + 1) / 2 ^ n) - h ((k : ℝ) / 2 ^ n)‖ ≤ 2 * δ :=
      (norm_sub_le _ _).trans (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  calc (2 : ℝ) ^ n / 2 * ∑ k ∈ Finset.range (2 ^ n),
        ‖h (((k : ℝ) + 1) / 2 ^ n) - h ((k : ℝ) / 2 ^ n)‖ ^ 2
      ≤ (2 : ℝ) ^ n / 2 * ((2 : ℝ) ^ n * (2 * δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * 4 ^ n * δ ^ 2 := by
        rw [h4]
        ring

end EnergyNodes

/-! ## Rounding labels -/

section Labels

/-- The rounding label of `f : ℝ → ℝ^m` at level `n` and resolution `a`: the integer parts
`⌊f(j/2ⁿ)_i / a⌋` of the coordinates of the node values. -/
def nodeLabel (m n : ℕ) (a : ℝ) (f : ℝ → Rd m) : Fin (2 ^ n + 1) → Fin m → ℤ :=
  fun j i => ⌊(f (((j : ℕ) : ℝ) / (2 : ℝ) ^ n)) i / a⌋

/-- The box of labels with entries in `[-M, M]`. -/
def nodeLabelBox (m n M : ℕ) : Finset (Fin (2 ^ n + 1) → Fin m → ℤ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M

lemma card_nodeLabelBox (m n M : ℕ) :
    (nodeLabelBox m n M).card = (2 * M + 1) ^ (m * (2 ^ n + 1)) := by
  rw [nodeLabelBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  have e : ((M : ℤ) + 1 - -(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e, Int.toNat_natCast, ← pow_mul]

lemma abs_sub_lt_of_floor_div_eq {a x y : ℝ} (ha : 0 < a) (h : ⌊x / a⌋ = ⌊y / a⌋) :
    |x - y| < a := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos ha, div_lt_one ha] at h1
  exact h1

/-- A vector of `ℝ^m` whose coordinates are bounded by `a` has norm `≤ √m a`. -/
lemma norm_le_of_abs_coord_le {m : ℕ} (y : Rd m) {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, |y i| ≤ a) :
    ‖y‖ ≤ √(m : ℝ) * a := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ i, ‖y.ofLp i‖ ^ 2 ≤ ∑ _i : Fin m, a ^ 2 := Finset.sum_le_sum fun i _ => by
    rw [Real.norm_eq_abs, sq_abs]
    have := h i
    nlinarith [abs_nonneg (y i), sq_abs (y i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc √(∑ i, ‖y.ofLp i‖ ^ 2) ≤ √((m : ℝ) * a ^ 2) := Real.sqrt_le_sqrt hs
    _ = √(m : ℝ) * a := by rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq ha]

/-- Two profiles with the same label have node values within `√m a`. -/
lemma norm_sub_node_le_of_nodeLabel_eq {m n : ℕ} {a : ℝ} (ha : 0 < a) {f g : ℝ → Rd m}
    (h : nodeLabel m n a f = nodeLabel m n a g) {k : ℕ} (hk : k ≤ 2 ^ n) :
    ‖(f - g) ((k : ℝ) / 2 ^ n)‖ ≤ √(m : ℝ) * a := by
  refine norm_le_of_abs_coord_le _ ha.le fun i => ?_
  have h1 := congrFun (congrFun h ⟨k, Nat.lt_succ_of_le hk⟩) i
  simp only [nodeLabel] at h1
  have h2 := abs_sub_lt_of_floor_div_eq ha h1
  have e : ((f - g) ((k : ℝ) / 2 ^ n)) i = (f ((k : ℝ) / 2 ^ n)) i - (g ((k : ℝ) / 2 ^ n)) i :=
    by simp
  rw [e]
  exact h2.le

/-- Labels of profiles with node values of norm `≤ ρ` lie in the box `[-M, M]`,
`M = ⌈ρ/a⌉ + 1`. -/
lemma nodeLabel_mem_box {m n : ℕ} {a ρ : ℝ} (ha : 0 < a) {f : ℝ → Rd m}
    (hf : ∀ k : ℕ, k ≤ 2 ^ n → ‖f ((k : ℝ) / 2 ^ n)‖ ≤ ρ) :
    nodeLabel m n a f ∈ nodeLabelBox m n (⌈ρ / a⌉₊ + 1) := by
  simp only [nodeLabelBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j i
  have hy : |(f (((j : ℕ) : ℝ) / (2 : ℝ) ^ n)) i| ≤ ρ := by
    have h1 := PiLp.norm_apply_le (f (((j : ℕ) : ℝ) / (2 : ℝ) ^ n)) i
    have h2 := hf j (Nat.lt_succ_iff.1 j.2)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  simp only [nodeLabel]
  set y := (f (((j : ℕ) : ℝ) / (2 : ℝ) ^ n)) i with hydef
  have hc := Nat.le_ceil (ρ / a)
  have h1 : y / a ≤ ρ / a := div_le_div_of_nonneg_right (le_of_abs_le hy) ha.le
  have h2 : -(ρ / a) ≤ y / a := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (neg_le_of_abs_le hy) ha.le
  have hf1 := Int.floor_le (y / a)
  have hf2 := Int.lt_floor_add_one (y / a)
  constructor
  · have : ((-(((⌈ρ / a⌉₊ + 1 : ℕ) : ℤ)) : ℤ) : ℝ) ≤ ((⌊y / a⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((⌊y / a⌋ : ℤ) : ℝ) ≤ ((((⌈ρ / a⌉₊ + 1 : ℕ) : ℤ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this

end Labels

/-! ## The covering construction -/

/-- **Rounding cells** (HA1 D10, steps 2–5).  Let `F₀ ⊆ V_n(ℝ^m)` be finite with node values of
norm `≤ ρ`, `a > 0`, `t > 0`, and let `B ≥ 0` bound `𝕄_G(gCov, 0)` on the energy ball of radius
`r ≥ 2·4ⁿ (√m a)²`.  Then there is `F ⊆ {0} ∪ F₀` containing `0`, with at most `N + 1` elements,
`N = (2(⌈ρ/a⌉ + 1) + 1)^{m(2ⁿ + 1)}`, and
`𝕄_{F₀}(gCov, 0) ≤ 𝕄_F(gCov, 0) + log N / t + B + (π²/8) t · 2π √m a`. -/
theorem exists_cover {m n : ℕ} (F₀ : Finset (Vg (Rd m) n)) {ρ a r B t : ℝ} (ha : 0 < a)
    (ht : 0 < t) (hB0 : 0 ≤ B)
    (hnode : ∀ f ∈ F₀, ∀ k : ℕ, k ≤ 2 ^ n → ‖(f : ℝ → Rd m) ((k : ℝ) / 2 ^ n)‖ ≤ ρ)
    (hr : 2 * 4 ^ n * (√(m : ℝ) * a) ^ 2 ≤ r)
    (hB : ∀ G : Finset (Vg (Rd m) n), (∀ f ∈ G, energy (f : ℝ → Rd m) ≤ r) →
      gaussianExpectedMax G (fun f g => gCov (f : ℝ → Rd m) g) 0 ≤ B) :
    ∃ F : Finset (Vg (Rd m) n), (⟨0, zero_mem_Vg n⟩ : Vg (Rd m) n) ∈ F ∧
      (∀ g ∈ F, (g : ℝ → Rd m) = 0 ∨ g ∈ F₀) ∧
      (F.card : ℝ) ≤ (((2 * (⌈ρ / a⌉₊ + 1) + 1) ^ (m * (2 ^ n + 1)) : ℕ) : ℝ) + 1 ∧
      gaussianExpectedMax F₀ (fun f g => gCov (f : ℝ → Rd m) g) 0 ≤
        gaussianExpectedMax F (fun f g => gCov (f : ℝ → Rd m) g) 0 +
          (Real.log (((2 * (⌈ρ / a⌉₊ + 1) + 1) ^ (m * (2 ^ n + 1)) : ℕ) : ℝ) / t + B +
            Real.pi ^ 2 / 8 * t * (2 * Real.pi * (√(m : ℝ) * a))) := by
  classical
  set z : Vg (Rd m) n := ⟨0, zero_mem_Vg n⟩ with hz
  set Nb : ℕ := (2 * (⌈ρ / a⌉₊ + 1) + 1) ^ (m * (2 ^ n + 1)) with hNb
  set R : Vg (Rd m) n → (Fin (2 ^ n + 1) → Fin m → ℤ) := fun f => nodeLabel m n a f with hR
  set Λ := F₀.image R with hΛ
  have hΛbox : Λ ⊆ nodeLabelBox m n (⌈ρ / a⌉₊ + 1) := by
    intro l hl
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hl
    exact nodeLabel_mem_box ha (hnode f hf)
  have hΛcard : Λ.card ≤ Nb := by
    have h := Finset.card_le_card hΛbox
    rwa [card_nodeLabelBox] at h
  have hNb1 : 1 ≤ Nb := Nat.one_le_pow _ _ (by omega)
  let rep : (Fin (2 ^ n + 1) → Fin m → ℤ) → Vg (Rd m) n := fun l =>
    if h : ∃ f ∈ F₀, R f = l then h.choose else z
  have hrep : ∀ l ∈ Λ, rep l ∈ F₀ ∧ R (rep l) = l := by
    intro l hl
    have h : ∃ f ∈ F₀, R f = l := Finset.mem_image.1 hl
    have e : rep l = h.choose := dite_eq_left h
    rw [e]
    exact h.choose_spec
  set F := insert z (Λ.image rep) with hFdef
  set cell : (Fin (2 ^ n + 1) → Fin m → ℤ) → Finset (Vg (Rd m) n) :=
    fun l => F₀.filter (fun f => R f = l) with hcell
  set G := F₀ ∪ F with hG
  obtain ⟨v, hv, -⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax G
    (fun f g => gCov (f : ℝ → Rd m) g) (gCov_psdOn_Vg n G)
  have hF₀G : F₀ ⊆ G := Finset.subset_union_left
  have hFG : F ⊆ G := Finset.subset_union_right
  have hzF : z ∈ F := Finset.mem_insert_self _ _
  have hzG : z ∈ G := hFG hzF
  have hvz : v z = 0 := by
    have h := hv z hzG z hzG
    rw [real_inner_self_eq_norm_sq] at h
    have h00 : gCov ((z : Vg (Rd m) n) : ℝ → Rd m) z = 0 := by simp [hz, gCov]
    rw [h00] at h
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
  have hrepF : ∀ l ∈ Λ, rep l ∈ F := fun l hl =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem rep hl)
  have hcellF₀ : ∀ l, cell l ⊆ F₀ := fun l => Finset.filter_subset _ _
  have hrepcell : ∀ l ∈ Λ, rep l ∈ cell l := fun l hl => Finset.mem_filter.2 (hrep l hl)
  -- node values within a cell
  have hnodes : ∀ l ∈ Λ, ∀ f ∈ cell l, ∀ k : ℕ, k ≤ 2 ^ n →
      ‖((f : ℝ → Rd m) - (rep l : ℝ → Rd m)) ((k : ℝ) / 2 ^ n)‖ ≤ √(m : ℝ) * a := by
    intro l hl f hf k hk
    have h1 : R f = l := (Finset.mem_filter.1 hf).2
    have h2 : R (rep l) = l := (hrep l hl).2
    exact norm_sub_node_le_of_nodeLabel_eq ha (h1.trans h2.symm) hk
  have hdiff : ∀ l, ∀ f : Vg (Rd m) n,
      (f : ℝ → Rd m) - (rep l : ℝ → Rd m) ∈ Vg (Rd m) n := fun l f => sub_mem_Vg f.2 (rep l).2
  have hclose : ∀ l ∈ Λ, ∀ f ∈ cell l, ∀ x,
      ‖(f : ℝ → Rd m) x - (rep l : ℝ → Rd m) x‖ ≤ √(m : ℝ) * a := by
    intro l hl f hf x
    have h := norm_le_of_nodes (hdiff l f) (by positivity) (hnodes l hl f hf) x
    simpa using h
  -- the difference vectors are short
  have hnorm : ∀ l ∈ Λ, ∀ f ∈ cell l, ‖v f - v (rep l)‖ ≤ √(2 * Real.pi * (√(m : ℝ) * a)) := by
    intro l hl f hf
    have hfG := hF₀G (hcellF₀ l hf)
    have hcG := hF₀G (hrep l hl).1
    apply Real.le_sqrt_of_sq_le
    rw [norm_sub_sq_of_gram (fun f : Vg (Rd m) n => (f : ℝ → Rd m)) v (Vg_continuous f.2)
      (Vg_continuous (rep l).2) (hv f hfG f hfG) (hv _ hcG _ hcG) (hv f hfG _ hcG)]
    have hint : ∫ x in (0 : ℝ)..1, ‖(f : ℝ → Rd m) x - (rep l : ℝ → Rd m) x‖ ≤
        √(m : ℝ) * a := by
      have h := intervalIntegral.integral_mono_on zero_le_one
        (((Vg_continuous f.2).sub (Vg_continuous (rep l).2)).norm.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable (μ := volume) 0 1) (fun x _ => hclose l hl f hf x)
      simpa using h
    have h2 := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  -- the mean of each cell maximum is an energy-ball quantity
  have hmean : ∀ l ∈ Λ, vecExpectedMax (cell l) (fun f => v f - v (rep l)) (fun _ => 0) ≤ B := by
    intro l hl
    have hcG := hF₀G (hrep l hl).1
    let sub : Vg (Rd m) n → Vg (Rd m) n := fun f => ⟨(f : ℝ → Rd m) - (rep l : ℝ → Rd m), hdiff l f⟩
    have h1 : vecExpectedMax (cell l) (fun f => v f - v (rep l)) (fun _ => 0) =
        gaussianExpectedMax ((cell l).image sub) (fun f g => gCov (f : ℝ → Rd m) g) 0 := by
      rw [gEM_image (cell l) sub _ _ (gCov_psdOn_Vg n _),
        ← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
      refine LQGDimension.Subadd.gEM_congr (cell l) (fun f hf g hg => ?_) (fun f _ => rfl)
      have hfG := hF₀G (hcellF₀ l hf)
      have hgG := hF₀G (hcellF₀ l hg)
      exact inner_sub_sub_of_gram (fun f : Vg (Rd m) n => (f : ℝ → Rd m)) v (Vg_continuous f.2)
        (Vg_continuous g.2) (Vg_continuous (rep l).2) (hv f hfG f hfG) (hv g hgG g hgG)
        (hv _ hcG _ hcG) (hv f hfG g hgG) (hv f hfG _ hcG) (hv g hgG _ hcG)
    rw [h1]
    refine hB _ fun g hg => ?_
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    exact (energy_le_of_nodes (hdiff l f) (hnodes l hl f hf)).trans hr
  -- the Gaussian estimate over the cells
  have hmain := LQGDimension.L23.integral_fsup_fsup_le LQGDimension.maxConcentration Λ cell
    (fun l f => v f - v (rep l)) ht hB0 hnorm hmean
  have hσ2 : √(2 * Real.pi * (√(m : ℝ) * a)) ^ 2 = 2 * Real.pi * (√(m : ℝ) * a) :=
    Real.sq_sqrt (by positivity)
  rw [hσ2] at hmain
  have hlog : Real.log Λ.card ≤ Real.log (Nb : ℝ) := by
    rcases Nat.eq_zero_or_pos Λ.card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hNb1)
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hΛcard)
  -- pointwise
  have hpt : ∀ x : EuclideanSpace ℝ G, (⨆ f : F₀, ⟪v f, x⟫ + (0 : Vg (Rd m) n → ℝ) f) ≤
      (⨆ g : F, ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g) +
        ⨆ l : Λ, ⨆ f : cell l, ⟪v f - v (rep l), x⟫ := by
    intro x
    have hF0 : 0 ≤ ⨆ g : F, ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g := by
      have h := LQGDimension.L23.le_fsup (fun g => ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g) hzF
      simpa [hvz] using h
    have hC0 : 0 ≤ ⨆ l : Λ, ⨆ f : cell l, ⟪v f - v (rep l), x⟫ := by
      refine Real.iSup_nonneg fun l => ?_
      have h := LQGDimension.L23.le_fsup (fun f => ⟪v f - v (rep l), x⟫) (hrepcell l l.2)
      simpa using h
    refine LQGDimension.L23.fsup_le (g := fun f => ⟪v f, x⟫ + (0 : Vg (Rd m) n → ℝ) f)
      (by linarith) fun f hf => ?_
    have hl : R f ∈ Λ := Finset.mem_image_of_mem R hf
    have hfc : f ∈ cell (R f) := Finset.mem_filter.2 ⟨hf, rfl⟩
    have h1 := LQGDimension.L23.le_fsup (fun g => ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g)
      (hrepF _ hl)
    have h2 := LQGDimension.L23.le_fsup (fun f' => ⟪v f' - v (rep (R f)), x⟫) hfc
    have h3 := LQGDimension.L23.le_fsup (fun l => ⨆ f' : cell l, ⟪v f' - v (rep l), x⟫) hl
    have h4 : ⟪v f, x⟫ = ⟪v (rep (R f)), x⟫ + ⟪v f - v (rep (R f)), x⟫ := by
      rw [inner_sub_left]
      ring
    simp only [Pi.zero_apply, add_zero] at h1 ⊢
    linarith
  refine ⟨F, hzF, ?_, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_insert.1 hg with rfl | hg
    · exact Or.inl rfl
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hg
      exact Or.inr (hrep l hl).1
  · have h1 : F.card ≤ (Λ.image rep).card + 1 := Finset.card_insert_le _ _
    have h2 : (Λ.image rep).card ≤ Λ.card := Finset.card_image_le
    have h3 : F.card ≤ Nb + 1 := by omega
    exact_mod_cast h3
  · rw [gEM_eq_vec_of_subset hF₀G _ v hv 0, gEM_eq_vec_of_subset hFG _ v hv 0]
    unfold vecExpectedMax
    have hint₀ := LQGDimension.integrable_iSup_inner_add F₀ v 0
    have hintF := LQGDimension.integrable_iSup_inner_add F v 0
    have hintC := LQGDimension.L23.integrable_fsup Λ
      (fun l x => ⨆ f : cell l, ⟪v f - v (rep l), x⟫)
      (fun l _ => LQGDimension.L23.integrable_fsup_inner (cell l) (fun f => v f - v (rep l)))
    have hdiv : Real.log Λ.card / t ≤ Real.log (Nb : ℝ) / t :=
      div_le_div_of_nonneg_right hlog ht.le
    calc ∫ x, (⨆ f : F₀, ⟪v f, x⟫ + (0 : Vg (Rd m) n → ℝ) f) ∂(stdGaussian (EuclideanSpace ℝ G))
        ≤ ∫ x, ((⨆ g : F, ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g) +
            ⨆ l : Λ, ⨆ f : cell l, ⟪v f - v (rep l), x⟫) ∂(stdGaussian (EuclideanSpace ℝ G)) :=
          integral_mono hint₀ (hintF.add hintC) hpt
      _ = (∫ x, (⨆ g : F, ⟪v g, x⟫ + (0 : Vg (Rd m) n → ℝ) g)
            ∂(stdGaussian (EuclideanSpace ℝ G))) +
          ∫ x, (⨆ l : Λ, ⨆ f : cell l, ⟪v f - v (rep l), x⟫)
            ∂(stdGaussian (EuclideanSpace ℝ G)) := integral_add hintF hintC
      _ ≤ _ := by linarith

/-! ## The numeric choices -/

lemma pi_cube_ge : 27 ≤ Real.pi ^ 3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 3
  norm_num at h
  linarith

/-- The constant `u = 1/(256 π³ m²)` lies in `(0, 1]`, and `256 m u ≤ 1`. -/
lemma uConst_facts {m : ℕ} (hm : 1 ≤ m) :
    0 < 1 / (256 * Real.pi ^ 3 * (m : ℝ) ^ 2) ∧ 1 / (256 * Real.pi ^ 3 * (m : ℝ) ^ 2) ≤ 1 ∧
      1 / (256 * Real.pi ^ 3 * (m : ℝ) ^ 2) * (256 * (m : ℝ)) ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi3 := pi_cube_ge
  have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := le_self_pow₀ hm1 two_ne_zero
  have hD : 0 < 256 * Real.pi ^ 3 * (m : ℝ) ^ 2 := by positivity
  have h256 : 256 * (m : ℝ) ≤ 256 * Real.pi ^ 3 * (m : ℝ) ^ 2 := by
    have h1 : (m : ℝ) ^ 2 ≤ Real.pi ^ 3 * (m : ℝ) ^ 2 :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one hD]
    linarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_one hD]
    exact h256

lemma sq_le_four_mul_cube_add_one {q : ℝ} (hq : 0 ≤ q) : q ^ 2 ≤ 4 * q ^ 3 + 1 := by
  rcases le_total q 1 with h | h
  · have h1 : q ^ 2 ≤ 1 := pow_le_one₀ hq h
    have h2 : 0 ≤ q ^ 3 := pow_nonneg hq 3
    linarith
  · have h1 : q ^ 2 ≤ q ^ 3 := pow_le_pow_right₀ h (by norm_num)
    have h2 : 0 ≤ q ^ 3 := pow_nonneg hq 3
    linarith

lemma cube_le_pow_four_add_one {q : ℝ} (hq : 0 ≤ q) : q ^ 3 ≤ q ^ 4 + 1 := by
  rcases le_total q 1 with h | h
  · have h1 : q ^ 3 ≤ 1 := pow_le_one₀ hq h
    have h2 : 0 ≤ q ^ 4 := pow_nonneg hq 4
    linarith
  · have h1 : q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ h (by norm_num)
    linarith

/-- With `a = u²/(4ⁿ (w+1)²)`, `u ≤ 1` and `ρ ≤ w + 1`, the number of grid values per coordinate,
`N = 2(⌈ρ/a⌉ + 1) + 1`, satisfies `log N ≤ log 7 + n log 4 + 3 log(w+1) + 2 log(1/u)`. -/
lemma log_N_le {n : ℕ} {w ρ u a : ℝ} (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ w + 1) (hu0 : 0 < u)
    (hu1 : u ≤ 1) (ha : a = u ^ 2 / (4 ^ n * (w + 1) ^ 2)) :
    Real.log (((2 * (⌈ρ / a⌉₊ + 1) + 1 : ℕ) : ℝ)) ≤
      Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u) := by
  have hw1 : 1 ≤ w + 1 := by linarith
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hw2 : (1 : ℝ) ≤ (w + 1) ^ 2 := one_le_pow₀ hw1
  have hX1 : (1 : ℝ) ≤ 4 ^ n * (w + 1) ^ 2 := one_le_mul_of_one_le_of_one_le h4 hw2
  have ha0 : 0 < a := by rw [ha]; positivity
  have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ ρ / a by positivity)
  have hN : (((2 * (⌈ρ / a⌉₊ + 1) + 1 : ℕ) : ℝ)) ≤ 7 * 4 ^ n * (w + 1) ^ 3 * (1 / u) ^ 2 := by
    push_cast
    have e : 7 * 4 ^ n * (w + 1) ^ 3 * (1 / u) ^ 2 = 7 * ((w + 1) / a) := by
      rw [ha]
      field_simp
    rw [e]
    have h1 : ρ / a ≤ (w + 1) / a := div_le_div_of_nonneg_right hρ ha0.le
    have h2 : 1 ≤ (w + 1) / a := by
      rw [le_div_iff₀ ha0]
      linarith
    linarith
  have hpos : (0 : ℝ) < ((2 * (⌈ρ / a⌉₊ + 1) + 1 : ℕ) : ℝ) := by positivity
  calc Real.log (((2 * (⌈ρ / a⌉₊ + 1) + 1 : ℕ) : ℝ))
      ≤ Real.log (7 * 4 ^ n * (w + 1) ^ 3 * (1 / u) ^ 2) := Real.log_le_log hpos hN
    _ = Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
        push_cast
        ring

/-- `2^n + 1 ≤ 4^n` and `n (2^n + 1) ≤ 4^n` for `n ≥ 1`. -/
lemma two_pow_add_one_le {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n + 1 ≤ 4 ^ n ∧ (n : ℝ) * (2 ^ n + 1) ≤ 4 ^ n := by
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hQ : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have hbern : (n : ℝ) + 1 ≤ 2 ^ n := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) n
    norm_num at h
    linarith
  rw [hQ]
  constructor
  · have h1 : (2 : ℝ) ^ n * 2 ≤ 2 ^ n * 2 ^ n := mul_le_mul_of_nonneg_left h2n (by positivity)
    linarith
  · have h1 : (n : ℝ) ≤ 2 ^ n - 1 := by linarith
    have h2 : (n : ℝ) * (2 ^ n + 1) ≤ (2 ^ n - 1) * (2 ^ n + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((2 : ℝ) ^ n - 1) * (2 ^ n + 1) = 2 ^ n * 2 ^ n - 1 := by ring
    linarith

/-- The error budget of the covering: with `t = 8(L + 1)`, `L ≤ m(2ⁿ+1) log N` and
`u ≤ 1/(256 π³ m²)`, the three error terms of `exists_cover` add up to at most `1/2`
(with `B = 1/4`). -/
lemma cover_error_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {w u a L t : ℝ} (hw : 0 ≤ w)
    (hu0 : 0 < u) (hu : u ≤ 1 / (256 * Real.pi ^ 3 * (m : ℝ) ^ 2))
    (ha : a = u ^ 2 / (4 ^ n * (w + 1) ^ 2)) (hL0 : 0 ≤ L)
    (hL : L ≤ m * (2 ^ n + 1) *
      (Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u)))
    (ht : t = 8 * (L + 1)) :
    L / t + 1 / 4 + Real.pi ^ 2 / 8 * t * (2 * Real.pi * (√(m : ℝ) * a)) ≤ 1 / 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨-, hu1', -⟩ := uConst_facts hm
  have hu1 : u ≤ 1 := hu.trans hu1'
  have hD : 0 < 256 * Real.pi ^ 3 * (m : ℝ) ^ 2 := by positivity
  have hu' : u * (256 * Real.pi ^ 3 * (m : ℝ) ^ 2) ≤ 1 := by
    rw [le_div_iff₀ hD] at hu
    exact hu
  have hw1 : 1 ≤ w + 1 := by linarith
  obtain ⟨hPQ, hnPQ⟩ := two_pow_add_one_le hn
  have hX : 0 < (4 : ℝ) ^ n * (w + 1) ^ 2 := by positivity
  have hw2 : (1 : ℝ) ≤ (w + 1) ^ 2 := one_le_pow₀ hw1
  have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hX1 : (4 : ℝ) ^ n ≤ 4 ^ n * (w + 1) ^ 2 := le_mul_of_one_le_right (by positivity) hw2
  have hX0 : (1 : ℝ) ≤ 4 ^ n * (w + 1) ^ 2 := h4n.trans hX1
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haX : a * (4 ^ n * (w + 1) ^ 2) = u ^ 2 := by
    rw [ha]
    field_simp
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = a * m * (2 ^ n + 1) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκX : κ * (4 ^ n * (w + 1) ^ 2) = m * u ^ 2 * (2 ^ n + 1) := by
    rw [hκ, show a * m * (2 ^ n + 1) * (4 ^ n * (w + 1) ^ 2) =
      (a * (4 ^ n * (w + 1) ^ 2)) * m * (2 ^ n + 1) by ring, haX]
    ring
  have hmu : 0 ≤ (m : ℝ) * u ^ 2 := by positivity
  have hκ1 : κ ≤ m * u ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hX
    rw [hκX]
    calc (m : ℝ) * u ^ 2 * (2 ^ n + 1) ≤ m * u ^ 2 * 4 ^ n := mul_le_mul_of_nonneg_left hPQ hmu
      _ ≤ m * u ^ 2 * (4 ^ n * (w + 1) ^ 2) := mul_le_mul_of_nonneg_left hX1 hmu
  have hκ2 : κ * n ≤ m * u ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hX
    rw [show κ * n * (4 ^ n * (w + 1) ^ 2) = κ * (4 ^ n * (w + 1) ^ 2) * n by ring, hκX]
    calc (m : ℝ) * u ^ 2 * (2 ^ n + 1) * n = m * u ^ 2 * (n * (2 ^ n + 1)) := by ring
      _ ≤ m * u ^ 2 * 4 ^ n := mul_le_mul_of_nonneg_left hnPQ hmu
      _ ≤ m * u ^ 2 * (4 ^ n * (w + 1) ^ 2) := mul_le_mul_of_nonneg_left hX1 hmu
  have hlogw : Real.log (w + 1) ≤ (w + 1) ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < w + 1 by linarith)
    have h2 : w + 1 ≤ (w + 1) ^ 2 := le_self_pow₀ hw1 two_ne_zero
    linarith
  have hκ3 : κ * Real.log (w + 1) ≤ m * u ^ 2 := by
    have h1 : κ * Real.log (w + 1) ≤ κ * (w + 1) ^ 2 := mul_le_mul_of_nonneg_left hlogw hκ0
    have h2 : κ * (w + 1) ^ 2 ≤ m * u ^ 2 := by
      have h4 : (0 : ℝ) < 4 ^ n := by positivity
      refine le_of_mul_le_mul_right ?_ h4
      rw [show κ * (w + 1) ^ 2 * 4 ^ n = κ * (4 ^ n * (w + 1) ^ 2) by ring, hκX]
      exact mul_le_mul_of_nonneg_left hPQ hmu
    linarith
  have hlogu : Real.log (1 / u) ≤ 1 / u := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / u by positivity)
    linarith
  have hκ4 : κ * Real.log (1 / u) ≤ m * u := by
    have h1 : κ * Real.log (1 / u) ≤ κ * (1 / u) := mul_le_mul_of_nonneg_left hlogu hκ0
    have h2 : κ * (1 / u) ≤ m * u := by
      rw [mul_one_div, div_le_iff₀ hu0]
      have e : (m : ℝ) * u * u = m * u ^ 2 := by ring
      linarith
    linarith
  have hlog7 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
    linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have haL : a * L ≤ 12 * (m * u ^ 2) + 2 * (m * u) := by
    have h1 : a * L ≤ a * (m * (2 ^ n + 1) *
        (Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u))) :=
      mul_le_mul_of_nonneg_left hL ha0
    have h2 : a * (m * (2 ^ n + 1) *
        (Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u))) =
        κ * Real.log 7 + (κ * n) * Real.log 4 + 3 * (κ * Real.log (w + 1)) +
          2 * (κ * Real.log (1 / u)) := by
      rw [hκ]
      ring
    have h3 : κ * Real.log 7 ≤ κ * 6 := mul_le_mul_of_nonneg_left hlog7 hκ0
    have h4 : (κ * n) * Real.log 4 ≤ (κ * n) * 3 :=
      mul_le_mul_of_nonneg_left hlog4 (by positivity)
    linarith
  have hu2 : u ^ 2 ≤ u := by
    have h1 : u * u ≤ u * 1 := mul_le_mul_of_nonneg_left hu1 hu0.le
    rw [sq]
    linarith
  have ha_le : a ≤ u ^ 2 := by
    have h1 : a * 1 ≤ a * (4 ^ n * (w + 1) ^ 2) := mul_le_mul_of_nonneg_left hX0 ha0
    linarith
  have hmu1 : u ≤ m * u := le_mul_of_one_le_left hu0.le hm1
  have hmu2 : (m : ℝ) * u ^ 2 ≤ m * u := mul_le_mul_of_nonneg_left hu2 (by positivity)
  have haL1 : a * (L + 1) ≤ 15 * (m * u) := by
    have e : a * (L + 1) = a * L + a := by ring
    linarith
  have hsqrt : √(m : ℝ) ≤ m := by
    rw [Real.sqrt_le_left (by linarith)]
    exact le_self_pow₀ hm1 two_ne_zero
  have hmain : 2 * Real.pi ^ 3 * (√(m : ℝ) * (a * (L + 1))) ≤ 1 / 8 := by
    have h1 : √(m : ℝ) * (a * (L + 1)) ≤ m * (15 * (m * u)) :=
      mul_le_mul hsqrt haL1 (by positivity) (by positivity)
    have h2 : 2 * Real.pi ^ 3 * (√(m : ℝ) * (a * (L + 1))) ≤
        2 * Real.pi ^ 3 * (m * (15 * (m * u))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * Real.pi ^ 3 * ((m : ℝ) * (15 * (m * u))) =
        30 / 256 * (u * (256 * Real.pi ^ 3 * (m : ℝ) ^ 2)) := by ring
    linarith
  have hLt : L / t ≤ 1 / 8 := by
    rw [ht, div_le_iff₀ (by positivity)]
    linarith
  have e : Real.pi ^ 2 / 8 * t * (2 * Real.pi * (√(m : ℝ) * a)) =
      2 * Real.pi ^ 3 * (√(m : ℝ) * (a * (L + 1))) := by
    rw [ht]
    ring
  rw [e]
  linarith

/-- The energy radius of a rounding cell is at most `s⁴`, `s = 1/(4(w+1))`: with
`a = u²/(4ⁿ (w+1)²)` and `u = 1/(256 π³ m²)`, `2·4ⁿ (√m a)² ≤ s⁴`. -/
lemma energy_radius_le {m n : ℕ} (hm : 1 ≤ m) {w u a s : ℝ} (hw : 0 ≤ w)
    (hu : u = 1 / (256 * Real.pi ^ 3 * (m : ℝ) ^ 2)) (ha : a = u ^ 2 / (4 ^ n * (w + 1) ^ 2))
    (hs : s = 1 / (4 * (w + 1))) :
    2 * 4 ^ n * (√(m : ℝ) * a) ^ 2 ≤ s ^ 4 := by
  obtain ⟨hu0, hu1, hum⟩ := uConst_facts hm
  rw [← hu] at hu0 hu1 hum
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hu12 : u ≤ 1 / 2 := by
    have h1 : u * 256 ≤ u * (256 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0.le
    linarith
  have hu3 : u ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ hu0.le hu12 3
    norm_num at h
    linarith
  have hu4 : u ^ 4 ≤ u / 8 := by
    have e : u ^ 4 = u * u ^ 3 := by ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left hu3 hu0.le
    linarith
  have hcoef : 512 * (m : ℝ) * u ^ 4 / 4 ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have h1 : 512 * (m : ℝ) * u ^ 4 ≤ 512 * m * (u / 8) :=
      mul_le_mul_of_nonneg_left hu4 (by positivity)
    have h2 : 512 * (m : ℝ) * (u / 8) = 1 / 4 * (u * (256 * m)) := by ring
    linarith
  have e1 : 2 * 4 ^ n * (√(m : ℝ) * a) ^ 2 = (512 * (m : ℝ) * u ^ 4 / 4 ^ n) * s ^ 4 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ha, hs]
    field_simp
    ring
  rw [e1]
  calc (512 * (m : ℝ) * u ^ 4 / 4 ^ n) * s ^ 4 ≤ 1 * s ^ 4 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = s ^ 4 := one_mul _

/-- The cardinality bound: if `c ≤ log 4 + L`, `L ≤ m(2ⁿ+1)(log 7 + n log 4 + 3 log(w+1) +
2 log(1/u))` and `w ≤ 4(Kn + 1)`, then `c ≤ (3 + 2m(21 + 12K + 2 log(1/u))) n 2ⁿ`. -/
lemma log_card_le {n : ℕ} (hn : 1 ≤ n) {m w K u L c : ℝ} (hm : 0 ≤ m) (hK : 0 ≤ K)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hw : 0 ≤ w) (hwK : w ≤ 4 * (K * n + 1))
    (hL : L ≤ m * (2 ^ n + 1) *
      (Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u)))
    (hc : c ≤ Real.log 4 + L) :
    c ≤ (3 + 2 * m * (21 + 12 * K + 2 * Real.log (1 / u))) * n * 2 ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogw : Real.log (w + 1) ≤ w := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < w + 1)
    linarith
  have hlog7 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
    linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hlog70 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogw0 : 0 ≤ Real.log (w + 1) := Real.log_nonneg (by linarith)
  have hlogu0 : 0 ≤ Real.log (1 / u) := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbr : Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u) ≤
      (21 + 12 * K + 2 * Real.log (1 / u)) * n := by
    have h1 : (n : ℝ) * Real.log 4 ≤ n * 3 := mul_le_mul_of_nonneg_left hlog4 (by positivity)
    have h2 : K * 1 ≤ K * n := mul_le_mul_of_nonneg_left hn1 hK
    have h3 : Real.log (1 / u) * 1 ≤ Real.log (1 / u) * n :=
      mul_le_mul_of_nonneg_left hn1 hlogu0
    have e : (21 + 12 * K + 2 * Real.log (1 / u)) * n =
        21 * n + 12 * (K * n) + 2 * (Real.log (1 / u) * n) := by ring
    linarith
  have hbr0 : 0 ≤ Real.log 7 + n * Real.log 4 + 3 * Real.log (w + 1) + 2 * Real.log (1 / u) := by
    positivity
  have hP : (2 : ℝ) ^ n + 1 ≤ 2 * 2 ^ n := by linarith
  have hL2 : L ≤ m * (2 * 2 ^ n) * ((21 + 12 * K + 2 * Real.log (1 / u)) * n) := by
    refine hL.trans ?_
    apply mul_le_mul _ hbr hbr0 (by positivity)
    exact mul_le_mul_of_nonneg_left hP hm
  have hn2 : (1 : ℝ) ≤ n * 2 ^ n := one_le_mul_of_one_le_of_one_le hn1 h2n
  calc c ≤ Real.log 4 + L := hc
    _ ≤ 3 * (n * 2 ^ n) + m * (2 * 2 ^ n) * ((21 + 12 * K + 2 * Real.log (1 / u)) * n) := by
        linarith
    _ = (3 + 2 * m * (21 + 12 * K + 2 * Real.log (1 / u))) * n * 2 ^ n := by ring

end Var

open Var

/-- **Lemma 2.2, (2.9)** (HA1 D10), for every `d ≥ 2`: there is `C` such that for every `n ≥ 1`
there is a finite `F ⊆ V_{n,d}` containing `0`, with `E(f) ≤ e_{n,d}` on `F`,
`E max_F G_d ≥ 4 e_{n,d} - 1`, and `log(2|F|) ≤ C n 2ⁿ`. -/
theorem lemma22b (d : ℕ) (hd : 2 ≤ d) : Lemma22b d := by
  classical
  obtain ⟨K₀, hK₀⟩ := lemma22a d hd
  have hm : 1 ≤ d - 1 := by omega
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (256 * Real.pi ^ 3 * ((d - 1 : ℕ) : ℝ) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨hu0, hu1, -⟩ := uConst_facts hm
  rw [← hudef] at hu0 hu1
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max K₀ 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  refine ⟨3 + 2 * ((d - 1 : ℕ) : ℝ) * (21 + 12 * K + 2 * Real.log (1 / u)), fun n hn => ?_⟩
  have he0 : 0 < eN n d := eN_pos hd hn
  have hw0 : 0 ≤ wN n d := wN_nonneg n d
  have hweq : wN n d = 4 * qN n d ^ 3 := wN_eq n d
  have heeq : eN n d = qN n d ^ 4 := eN_eq n d
  have hq0 : 0 ≤ qN n d := qN_nonneg n d
  -- a finite family `F₀` in the energy ball `{E ≤ e}` with `E max_{F₀} G > 4e - 1/2`
  obtain ⟨F₀, hF₀E, hF₀⟩ : ∃ F₀ : Finset (Vg (Rd (d - 1)) n),
      (∀ f ∈ F₀, energy (f : ℝ → Rd (d - 1)) ≤ eN n d) ∧
      4 * eN n d - 1 / 2 <
        gaussianExpectedMax F₀ (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 := by
    have hW : W n d (eN n d) = ((4 * eN n d : ℝ) : EReal) := by
      rw [← W_eN_toReal hd n, W_coe_toReal hd n]
    have hlt : ((4 * eN n d - 1 / 2 : ℝ) : EReal) < W n d (eN n d) := by
      rw [hW]
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    obtain ⟨F, hF⟩ := lt_iSup_iff.1 hlt
    obtain ⟨hE, hF'⟩ := lt_iSup_iff.1 hF
    exact ⟨F, hE, EReal.coe_lt_coe_iff.1 hF'⟩
  -- the node bound `ρ = e^{1/2} ≤ w + 1`
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = √(eN n d) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Real.sqrt_nonneg _
  have hρq : ρ = qN n d ^ 2 := by
    rw [hρdef, heeq, show qN n d ^ 4 = (qN n d ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hρw : ρ ≤ wN n d + 1 := by
    rw [hρq, hweq]
    exact sq_le_four_mul_cube_add_one hq0
  have hnode : ∀ f ∈ F₀, ∀ k : ℕ, k ≤ 2 ^ n →
      ‖(f : ℝ → Rd (d - 1)) ((k : ℝ) / 2 ^ n)‖ ≤ ρ := by
    intro f hf k _
    rw [hρdef]
    exact (norm_le_sqrt_energy f.2 _).trans (Real.sqrt_le_sqrt (hF₀E f hf))
  -- the parameters
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = u ^ 2 / (4 ^ n * (wN n d + 1) ^ 2) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 1 / (4 * (wN n d + 1)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; positivity
  obtain ⟨Nb, hNb⟩ : ∃ Nb : ℕ, Nb = (2 * (⌈ρ / a⌉₊ + 1) + 1) ^ ((d - 1) * (2 ^ n + 1)) :=
    ⟨_, rfl⟩
  have hNb1 : 1 ≤ Nb := by rw [hNb]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (Nb : ℝ) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg (by exact_mod_cast hNb1)
  have hLle : L ≤ ((d - 1 : ℕ) : ℝ) * (2 ^ n + 1) * (Real.log 7 + n * Real.log 4 +
      3 * Real.log (wN n d + 1) + 2 * Real.log (1 / u)) := by
    have h := log_N_le (n := n) hw0 hρ0 hρw hu0 hu1 hadef
    rw [hLdef, hNb, Nat.cast_pow, Real.log_pow]
    have e : (((d - 1) * (2 ^ n + 1) : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) * (2 ^ n + 1) := by
      push_cast
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 8 * (L + 1) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  have hr := energy_radius_le (n := n) hm hw0 hudef hadef hsdef
  have hB : ∀ G : Finset (Vg (Rd (d - 1)) n), (∀ f ∈ G, energy (f : ℝ → Rd (d - 1)) ≤ s ^ 4) →
      gaussianExpectedMax G (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 ≤ 1 / 4 := by
    intro G hG
    refine (gEM_le_of_energy_le hd G hs0 hG).trans ?_
    rw [hsdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the covering
  obtain ⟨F, hzF, hFsub, hcard, hgem⟩ :=
    exists_cover F₀ ha0 ht0 (by norm_num : (0 : ℝ) ≤ 1 / 4) hnode hr hB
  rw [← hNb] at hcard hgem
  rw [← hLdef] at hgem
  have herr := cover_error_le hm hn hw0 hu0 hudef.le hadef hL0 hLle htdef
  refine ⟨F, ⟨_, hzF, fun x => rfl⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases hFsub g hg with h0 | h0
    · rw [h0, energy_zero]
      exact he0.le
    · exact hF₀E g h0
  · linarith
  · -- `log(2|F|) ≤ C n 2ⁿ`
    have hcard1 : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.2 ⟨_, hzF⟩
    have hNb1' : (1 : ℝ) ≤ (Nb : ℝ) := by exact_mod_cast hNb1
    have h2F : 2 * (F.card : ℝ) ≤ 4 * Nb := by linarith
    have hlog2F : Real.log (2 * F.card) ≤ Real.log 4 + L := by
      calc Real.log (2 * F.card) ≤ Real.log (4 * Nb) := Real.log_le_log (by positivity) h2F
        _ = Real.log 4 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
    have hwK : wN n d ≤ 4 * (K * n + 1) := by
      have h1 := cube_le_pow_four_add_one hq0
      have h2 : eN n d ≤ K * n :=
        (hK₀ n hn).2.2.trans (mul_le_mul_of_nonneg_right (by rw [hKdef]; exact le_max_left _ _)
          (Nat.cast_nonneg n))
      rw [heeq] at h2
      rw [hweq]
      linarith
    exact log_card_le hn (Nat.cast_nonneg _) hK0 hu0 hu1 hw0 hwK hLle hlog2F

/-- **(2.9), enumerated form** (the shape of HA4's `IsLemma22Family`, consumed by the §5 lower
comparison): for every `d ≥ 2` there is `C` such that for every `n ≥ 1` there are `J` and profiles
`f : Fin (J + 1) → V_{n,d}` with `f 0 = 0`, `E(f j) ≤ e_{n,d}`,
`E max_j G_d(f j) ≥ 4 e_{n,d} - 1` and `log(2(J + 1)) ≤ C n 2ⁿ`. -/
theorem lemma22b_fin (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∃ (J : ℕ) (f : Fin (J + 1) → (ℝ → Rd (d - 1))),
      f 0 = 0 ∧ (∀ j, f j ∈ Vg (Rd (d - 1)) n) ∧ (∀ j, energy (f j) ≤ eN n d) ∧
      4 * eN n d - 1 ≤ gaussianExpectedMax (Finset.univ : Finset (Fin (J + 1)))
        (fun j k => gCov (f j) (f k)) (fun _ => 0) ∧
      Real.log (2 * ((J : ℝ) + 1)) ≤ C * n * 2 ^ n := by
  classical
  obtain ⟨C, hC⟩ := lemma22b d hd
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨F, ⟨z, hzF, hz0⟩, hE, hgem, hlog⟩ := hC n hn
  set G := F.erase z with hGdef
  set e := G.equivFin with hedef
  set φ : Fin (G.card + 1) → Vg (Rd (d - 1)) n :=
    Fin.cons z (fun j => ((e.symm j : G) : Vg (Rd (d - 1)) n)) with hφdef
  have himage : Finset.univ.image φ = F := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [hφdef, Fin.cons_zero]
        exact hzF
      · simp only [hφdef, Fin.cons_succ]
        exact (Finset.mem_erase.1 (e.symm i).2).2
    · intro hg
      by_cases hgz : g = z
      · exact ⟨0, by simp only [hφdef, Fin.cons_zero, hgz]⟩
      · have hgG : g ∈ G := Finset.mem_erase.2 ⟨hgz, hg⟩
        refine ⟨(e ⟨g, hgG⟩).succ, ?_⟩
        simp only [hφdef, Fin.cons_succ, Equiv.symm_apply_apply]
  have hz : (z : ℝ → Rd (d - 1)) = 0 := funext hz0
  refine ⟨G.card, fun j => (φ j : ℝ → Rd (d - 1)), ?_, fun j => (φ j).2, fun j => ?_, ?_, ?_⟩
  · simp only [hφdef, Fin.cons_zero]
    exact hz
  · have hj : φ j ∈ F := by
      rw [← himage]
      exact Finset.mem_image_of_mem φ (Finset.mem_univ j)
    exact hE _ hj
  · rw [← himage, gEM_image Finset.univ φ _ _ (gCov_psdOn_Vg n _)] at hgem
    exact hgem
  · have hcard : ((G.card : ℕ) : ℝ) + 1 = (F.card : ℝ) := by
      rw [hGdef]
      exact_mod_cast Finset.card_erase_add_one hzF
    rw [hcard]
    exact hlog

end HigherDimLFPP
