import HigherDimLFPP.Var.Theorem11
import HigherDimLFPP.Var.Scaling
import HigherDimLFPP.Lower.Profiles
import LQGDimension.Section2.Lemma23Aux

/-!
# The energy-ball quantities of Lemma 2.2: `W`, `w`, `e`, `β`

Paper §2, (2.7) (`source/higher-dimensional-lfpp-limit.txt` l. 248–253; audit HA1 §3.4, Details
D9–D10 and the recommended Lean definitions of HA1 Details (c)):

`W_{n,d}(r) = E sup_{f ∈ V_{n,d}, E(f) ≤ r} G_d(f)`, `w_{n,d} = W_{n,d}(1)`,
`e_{n,d} = (w_{n,d}/4)^{4/3}`, `β_{n,d} = 3 e_{n,d}`.

As for `A` (HA1 D1), the expected supremum is the supremum over finite subfamilies of expected
maxima.  The definitions `W`, `wN`, `eN`, `betaN` are HA1's (Details (c)) with
`V n d = Vg (Rd (d - 1)) n`; `W n d r` is the specialization of the generic `Wg (Rd (d - 1)) n r`.

Main results (target T1 of packet P-V2):
* `Var.Wg_nonneg`, `Var.Wg_mono`: `W(r) ≥ 0`, monotone in `r`;
* `Var.Wg_le_Ag_add`: `W(r) ≤ A + r` for `r ≥ 0` (HA1 D9, step 1); hence `Var.W_ne_top` for `d ≥ 2`;
* `Var.Wg_pow_four`, `Var.Wg_rpow` (homogeneity, HA1 D4): `W(r) = r^{1/4} W(1)` for `r > 0`;
* `Var.wN_pos`: `0 < w_{n,d}` for `n ≥ 1`, `d ≥ 2` (the family `{0, tent}`);
* `Var.betaN_le_A`: `β_{n,d} ≤ A_{n,d}` (HA1 D9, step 1: `sup_r (w r^{1/4} - r) = 3e` at `r = e`);
* `energyBall_basic` packages these facts for every `d ≥ 2`.

Parametrization used by (2.8)–(2.9): `Var.qN n d = (w_{n,d}/4)^{1/3}`, so that `w = 4q³`
(`Var.wN_eq`), `e = q⁴` (`Var.eN_eq`) and `W_{n,d}(s⁴) = s w_{n,d}` (`Var.W_pow_four_eq`); in
particular `W_{n,d}(e_{n,d}) = 4 e_{n,d}` (`Var.W_eN_toReal`).

Auxiliary deterministic bounds on `V_n(E)` used by (2.8) and (2.9):
`Var.norm_le_of_nodes` (a profile bounded at the mesh points is bounded everywhere; port of
`LQGDimension.L23.abs_le_of_nodes`), `Var.norm_le_sqrt_energy` (`‖f(x)‖ ≤ E(f)^{1/2}`, from
`Lower.norm_node_le`), `Var.gCov_self_le` (`Var G(f) ≤ 2π E(f)^{1/2}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Definitions (2.7) -/

/-- `W_n(E)(r) = E sup_{f ∈ V_n(E), E(f) ≤ r} G(f)`, as the supremum over finite subfamilies of
the energy ball of the expected maxima of the centered Gaussian vector with covariance `gCov`.
The guarded `⨆` over a false proposition is `⊥`; the admissible `F = ∅` term keeps the value
`≥ 0`. -/
def Wg (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (r : ℝ) : EReal :=
  ⨆ (F : Finset (Vg E n)) (_ : ∀ f ∈ F, energy (f : ℝ → E) ≤ r),
    ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal)

/-- `W_{n,d}(r) = E sup_{f ∈ V_{n,d}, E(f) ≤ r} G_d(f)` (HA1 Details (c)). -/
def W (n d : ℕ) (r : ℝ) : EReal := Wg (Rd (d - 1)) n r

/-- `w_{n,d} = E sup_{f ∈ V_{n,d}, E(f) ≤ 1} G_d(f)` (2.7). -/
def wN (n d : ℕ) : ℝ := (W n d 1).toReal

/-- `e_{n,d} = (w_{n,d}/4)^{4/3}` (2.7). -/
def eN (n d : ℕ) : ℝ := (wN n d / 4) ^ (4 / 3 : ℝ)

/-- `β_{n,d} = 3 e_{n,d}` (2.7). -/
def betaN (n d : ℕ) : ℝ := 3 * eN n d

/-- `W` is literally HA1's definition (with `V n d = Vg (Rd (d - 1)) n`). -/
example (n d : ℕ) (r : ℝ) : W n d r =
    ⨆ (F : Finset (Vg (Rd (d - 1)) n)) (_ : ∀ f ∈ F, energy (f : ℝ → Rd (d - 1)) ≤ r),
      ((LQGDimension.gaussianExpectedMax F (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 : ℝ) :
        EReal) := rfl

namespace Var

/-! ## Finite Gaussian families: Gram realization on a subfamily, drift comparison -/

/-- Expected maxima over a subfamily `F ⊆ G` through a Gram realization on `G`. -/
lemma gEM_eq_vec_of_subset {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {G F : Finset ι} (hFG : F ⊆ G)
    (C : ι → ι → ℝ) (v : ι → H) (hv : ∀ i ∈ G, ∀ j ∈ G, ⟪v i, v j⟫ = C i j) (b : ι → ℝ) :
    gaussianExpectedMax F C b = vecExpectedMax F v b := by
  rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  exact LQGDimension.gaussianExpectedMax_congr F b fun i hi j hj => (hv i (hFG hi) j (hFG hj)).symm

/-- **Drift comparison**: if `b ≤ b' + c` on `F` with `c ≥ 0`, then
`𝕄_F(C, b) ≤ 𝕄_F(C, b') + c` (for `C` positive semidefinite on `F`). -/
theorem gEM_le_add_of_le {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) (hC : PSDOn F C)
    {b b' : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i ∈ F, b i ≤ b' i + c) :
    gaussianExpectedMax F C b ≤ gaussianExpectedMax F C b' + c := by
  obtain ⟨v, -, hv⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  rw [hv b, hv b']
  unfold vecExpectedMax
  have hint := LQGDimension.integrable_iSup_inner_add F v b
  have hint' := LQGDimension.integrable_iSup_inner_add F v b'
  have hpt : ∀ x : EuclideanSpace ℝ F,
      (⨆ i : F, ⟪v i, x⟫ + b i) ≤ (⨆ i : F, ⟪v i, x⟫ + b' i) + c := by
    intro x
    rcases F.eq_empty_or_nonempty with hF | hF
    · subst hF
      rw [LQGDimension.L23.fsup_empty (fun i => ⟪v i, x⟫ + b i),
        LQGDimension.L23.fsup_empty (fun i => ⟪v i, x⟫ + b' i)]
      linarith
    · refine LQGDimension.L23.fsup_le' hF (g := fun i => ⟪v i, x⟫ + b i) fun i hi => ?_
      have h1 := LQGDimension.L23.le_fsup (fun i => ⟪v i, x⟫ + b' i) hi
      linarith [h i hi]
  calc ∫ x, (⨆ i : F, ⟪v i, x⟫ + b i) ∂(stdGaussian (EuclideanSpace ℝ F))
      ≤ ∫ x, ((⨆ i : F, ⟪v i, x⟫ + b' i) + c) ∂(stdGaussian (EuclideanSpace ℝ F)) :=
        integral_mono hint (hint'.add (integrable_const c)) hpt
    _ = (∫ x, (⨆ i : F, ⟪v i, x⟫ + b' i) ∂(stdGaussian (EuclideanSpace ℝ F))) + c := by
        rw [integral_add hint' (integrable_const c), integral_const]
        simp

/-! ## Basic properties of `Wg` -/

section WgBasic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma le_Wg {n : ℕ} {r : ℝ} (F : Finset (Vg E n)) (hF : ∀ f ∈ F, energy (f : ℝ → E) ≤ r) :
    ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal) ≤ Wg E n r :=
  le_iSup₂_of_le (f := fun (F : Finset (Vg E n)) (_ : ∀ f ∈ F, energy (f : ℝ → E) ≤ r) =>
    ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal)) F hF le_rfl

lemma Wg_le_of_forall {n : ℕ} {r : ℝ} {B : EReal}
    (h : ∀ F : Finset (Vg E n), (∀ f ∈ F, energy (f : ℝ → E) ≤ r) →
      ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal) ≤ B) :
    Wg E n r ≤ B :=
  iSup₂_le h

/-- `W(r) ≥ 0`: the empty family is admissible. -/
lemma Wg_nonneg (n : ℕ) (r : ℝ) : 0 ≤ Wg E n r := by
  have h := le_Wg (E := E) (n := n) (r := r) ∅ (fun f hf => absurd hf (Finset.notMem_empty f))
  rwa [gEM_empty, EReal.coe_zero] at h

lemma Wg_ne_bot (n : ℕ) (r : ℝ) : Wg E n r ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (Wg_nonneg n r)

/-- `W` is monotone in the radius. -/
lemma Wg_mono {n : ℕ} {r r' : ℝ} (h : r ≤ r') : Wg E n r ≤ Wg E n r' :=
  Wg_le_of_forall fun F hF => le_Wg F fun f hf => (hF f hf).trans h

end WgBasic

section WgInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`W(r) ≤ A + r`** for `r ≥ 0` (HA1 D9, step 1): on the energy ball,
`max_F G ≤ max_F (G - E) + r`. -/
theorem Wg_le_Ag_add (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : Wg E n r ≤ Ag E n + (r : EReal) := by
  refine Wg_le_of_forall fun F hF => ?_
  have h := gEM_le_add_of_le F (fun f g => gCov (f : ℝ → E) g) (gCov_psdOn_Vg n F)
    (b := 0) (b' := fun f => -energy (f : ℝ → E)) hr (fun f hf => by
      have := hF f hf
      simp only [Pi.zero_apply]
      linarith)
  calc ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal)
      ≤ ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g)
          (fun f => -energy (f : ℝ → E)) + r : ℝ) : EReal) := EReal.coe_le_coe_iff.2 h
    _ = ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g)
          (fun f => -energy (f : ℝ → E)) : ℝ) : EReal) + (r : EReal) := EReal.coe_add _ _
    _ ≤ Ag E n + (r : EReal) := add_le_add (le_Ag F) le_rfl

/-- The finite-family identity behind the homogeneity of `W`:
`𝕄_{s² F}(gCov, 0) = s 𝕄_F(gCov, 0)` for `s ≥ 0`. -/
lemma gEM_dilate_sq (n : ℕ) [DecidableEq (Vg E n)] (G : Finset (Vg E n)) {s : ℝ} (hs : 0 ≤ s) :
    gaussianExpectedMax (G.image (dilate n (s ^ 2))) (fun f g => gCov (f : ℝ → E) g) 0 =
      s * gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g) 0 := by
  rw [gEM_image G (dilate n (s ^ 2)) _ _ (gCov_psdOn_Vg n _)]
  have h2 := gEM_smul G (fun f g => gCov (f : ℝ → E) g) (gCov_psdOn_Vg n G) 0 hs
  rw [← h2]
  refine LQGDimension.Subadd.gEM_congr G (fun f _ g _ => ?_) (fun f _ => ?_)
  · simp only [dilate_coe]
    rw [gCov_smul (sq_nonneg s)]
  · simp

/-- **Homogeneity** (HA1 D4): `W(s⁴) = s W(1)` for `s > 0`, through the bijection `f ↦ s² f` of
the unit energy ball onto the ball of radius `s⁴`. -/
theorem Wg_pow_four (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Wg E n (s ^ 4) = (s : EReal) * Wg E n 1 := by
  classical
  set lam : ℝ := s ^ 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam4 : lam ^ 2 = s ^ 4 := by rw [hlam]; ring
  apply le_antisymm
  · refine Wg_le_of_forall fun F hF => ?_
    set G := F.image (dilate n lam⁻¹) with hGdef
    have hFG : F = G.image (dilate n lam) := (image_dilate_dilate n hlam0.ne' F).symm
    have hG : ∀ g ∈ G, energy (g : ℝ → E) ≤ 1 := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      simp only [dilate_coe]
      rw [energy_smul f.2, inv_pow, hlam4]
      have h1 := hF f hf
      have h4 : 0 < s ^ 4 := by positivity
      rw [inv_mul_le_iff₀ h4, mul_one]
      exact h1
    rw [hFG, gEM_dilate_sq n G hs.le, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (le_Wg G hG) (EReal.coe_nonneg.2 hs.le)
  · have h : Wg E n 1 = ⨆ (F : Finset (Vg E n)), ⨆ (_ : ∀ f ∈ F, energy (f : ℝ → E) ≤ 1),
        ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) 0 : ℝ) : EReal) := rfl
    rw [h, LQGDimension.Bounds.EReal_coe_mul_iSup hs]
    refine iSup_le fun G => ?_
    by_cases hG : ∀ f ∈ G, energy (f : ℝ → E) ≤ 1
    · rw [iSup_pos hG, ← EReal.coe_mul, ← gEM_dilate_sq n G hs.le]
      refine le_Wg _ fun g hg => ?_
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      simp only [dilate_coe]
      rw [energy_smul f.2, hlam4]
      have h1 := hG f hf
      have h4 : 0 ≤ s ^ 4 := by positivity
      calc s ^ 4 * energy (f : ℝ → E) ≤ s ^ 4 * 1 := mul_le_mul_of_nonneg_left h1 h4
        _ = s ^ 4 := mul_one _
    · rw [iSup_neg hG, EReal.coe_mul_bot_of_pos hs]
      exact bot_le

/-- **Homogeneity** `W(r) = r^{1/4} W(1)` for `r > 0` (paper l. 263, "Homogeneity gives
`E M_n(r) = r^{1/4} w_{n,d}`"). -/
theorem Wg_rpow (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Wg E n r = ((r ^ (1 / 4 : ℝ) : ℝ) : EReal) * Wg E n 1 := by
  have hs : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr _
  have h4 : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
    have := Real.rpow_inv_natCast_pow (x := r) (n := 4) hr.le (by norm_num)
    rw [show ((4 : ℕ) : ℝ)⁻¹ = (1 / 4 : ℝ) by norm_num] at this
    exact this
  rw [← Wg_pow_four n hs, h4]

end WgInner

/-! ## Deterministic bounds on `V_n(E)` -/

section Nodes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every `x ∈ [0,1]` lies in a closed mesh interval `[k 2⁻ⁿ, (k+1) 2⁻ⁿ]`, `k < 2ⁿ`.  (Port of
`LQGDimension.L23.exists_piece`, mesh `16⁻ⁿ` replaced by `2⁻ⁿ`.) -/
lemma exists_dyadic_piece (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 2 ^ n ∧ x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 ≤ x := hx.1
  rcases lt_or_eq_of_le hx.2 with h1 | h1
  · have h0 : (0 : ℝ) ≤ 2 ^ n * x := by positivity
    refine ⟨⌊(2 : ℝ) ^ n * x⌋₊, ?_, ?_, ?_⟩
    · exact (Nat.floor_lt h0).2 (by push_cast; nlinarith)
    · rw [div_le_iff₀ hN]
      have := Nat.floor_le h0
      linarith
    · rw [le_div_iff₀ hN]
      have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * x)
      linarith
  · have hc : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast
      ring
    refine ⟨2 ^ n - 1, Nat.sub_lt (by positivity) one_pos, ?_, ?_⟩
    · rw [hc, h1, div_le_iff₀ hN]
      linarith
    · rw [hc, h1, le_div_iff₀ hN]
      linarith

/-- A profile of `V_n(E)` bounded by `δ` at the mesh points is bounded by `δ` everywhere (it is
affine on each mesh interval and zero off `[0,1]`).
(Port of `LQGDimension.L23.abs_le_of_nodes`.) -/
lemma norm_le_of_nodes {n : ℕ} {h : ℝ → E} (hh : h ∈ Vg E n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnode : ∀ k : ℕ, k ≤ 2 ^ n → ‖h ((k : ℝ) / 2 ^ n)‖ ≤ δ) (x : ℝ) : ‖h x‖ ≤ δ := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := exists_dyadic_piece n hx
    have hN : (0 : ℝ) < 2 ^ n := by positivity
    rw [Vg_piece hh hk hxk]
    have h1 := hnode k hk.le
    have h2 := hnode (k + 1) hk
    push_cast at h2
    have hθ0 : 0 ≤ (2 : ℝ) ^ n * x - k := by
      have := hxk.1
      rw [div_le_iff₀ hN] at this
      linarith
    have hθ1 : (2 : ℝ) ^ n * x - k ≤ 1 := by
      have := hxk.2
      rw [le_div_iff₀ hN] at this
      linarith
    have e : ∀ (θ : ℝ) (a b : E), a + θ • (b - a) = (1 - θ) • a + θ • b := fun θ a b => by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    set θ := (2 : ℝ) ^ n * x - k with hθ
    set a := h ((k : ℝ) / 2 ^ n) with ha
    set b := h (((k : ℝ) + 1) / 2 ^ n) with hb
    calc ‖(1 - θ) • a + θ • b‖ ≤ ‖(1 - θ) • a‖ + ‖θ • b‖ := norm_add_le _ _
      _ = (1 - θ) * ‖a‖ + θ * ‖b‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg hθ0]
      _ ≤ (1 - θ) * δ + θ * δ := by
          have h3 : 0 ≤ 1 - θ := by linarith
          gcongr
      _ = δ := by ring
  · rw [hh.2.2.1 x hx, norm_zero]
    exact hδ

end Nodes

section NodesInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖f(x)‖ ≤ E(f)^{1/2}` for `f ∈ V_n(E)` and every `x` (from the node bound
`Lower.norm_node_le`). -/
lemma norm_le_sqrt_energy {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) (x : ℝ) :
    ‖f x‖ ≤ √(energy f) := by
  refine norm_le_of_nodes hf (Real.sqrt_nonneg _) (fun k hk => ?_) x
  have h := Lower.norm_node_le (K := 2 ^ n) rfl hf hk
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

lemma integral_norm_le_sqrt_energy {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) :
    ∫ x in (0 : ℝ)..1, ‖f x‖ ≤ √(energy f) := by
  have h := intervalIntegral.integral_mono_on zero_le_one
    ((Vg_continuous hf).norm.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable (μ := volume) 0 1)
    (fun x _ => norm_le_sqrt_energy hf x)
  simpa using h

/-- **Variance bound**: `Var G(f) = gCov(f, f) ≤ 2π E(f)^{1/2}` for `f ∈ V_n(E)` (a Poincaré
bound; HA1 D3.2 has the sharper constant `4π/3`). -/
lemma gCov_self_le {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) :
    gCov f f ≤ 2 * Real.pi * √(energy f) := by
  rw [gCov_self]
  exact mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_energy hf) (by positivity)

end NodesInner

/-! ## `W_{n,d}` for `d ≥ 2`: finiteness, real values, `w = 4q³`, `e = q⁴` -/

lemma W_nonneg (n d : ℕ) (r : ℝ) : 0 ≤ W n d r := Wg_nonneg n r

lemma W_ne_bot (n d : ℕ) (r : ℝ) : W n d r ≠ ⊥ := Wg_ne_bot n r

/-- `W_{n,d}(r) ≤ A_{n,d} + r` for `r ≥ 0`. -/
lemma W_le_A_add (n d : ℕ) {r : ℝ} (hr : 0 ≤ r) : W n d r ≤ A n d + (r : EReal) :=
  Wg_le_Ag_add n hr

/-- **Finiteness**: `W_{n,d}(r) < ∞` for `d ≥ 2` (since `W(r) ≤ A + r` and `A_{n,d} < ∞`). -/
theorem W_ne_top {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (r : ℝ) : W n d r ≠ ⊤ := by
  have h1 : W n d r ≤ W n d (max r 0) := Wg_mono (le_max_left r 0)
  have h2 : W n d (max r 0) ≤ A n d + ((max r 0 : ℝ) : EReal) :=
    W_le_A_add n d (le_max_right r 0)
  rw [← A_coe_toReal hd n, ← EReal.coe_add] at h2
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (h1.trans h2)

lemma W_coe_toReal {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (r : ℝ) :
    (((W n d r).toReal : ℝ) : EReal) = W n d r :=
  EReal.coe_toReal (W_ne_top hd n r) (W_ne_bot n d r)

lemma wN_nonneg (n d : ℕ) : 0 ≤ wN n d := EReal.toReal_nonneg (W_nonneg n d 1)

lemma W_one_eq {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : W n d 1 = ((wN n d : ℝ) : EReal) :=
  (W_coe_toReal hd n 1).symm

/-- `W_{n,d}(s⁴) = s w_{n,d}` for `s > 0`. -/
lemma W_pow_four_eq {d : ℕ} (hd : 2 ≤ d) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    W n d (s ^ 4) = ((s * wN n d : ℝ) : EReal) := by
  rw [W, Wg_pow_four n hs, ← W, W_one_eq hd n, EReal.coe_mul]

/-- **Homogeneity** `W_{n,d}(r) = r^{1/4} w_{n,d}` for `r > 0`, as real numbers. -/
lemma W_toReal_eq {d : ℕ} (hd : 2 ≤ d) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (W n d r).toReal = r ^ (1 / 4 : ℝ) * wN n d := by
  rw [W, Wg_rpow n hr, ← W, W_one_eq hd n, ← EReal.coe_mul, EReal.toReal_coe]

/-- A finite family in the energy ball of radius `s⁴` has expected maximum `≤ s w_{n,d}`. -/
lemma gEM_le_of_energy_le {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (G : Finset (Vg (Rd (d - 1)) n))
    {s : ℝ} (hs : 0 < s) (hG : ∀ f ∈ G, energy (f : ℝ → Rd (d - 1)) ≤ s ^ 4) :
    gaussianExpectedMax G (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 ≤ s * wN n d := by
  have h := le_Wg G hG
  rw [show Wg (Rd (d - 1)) n (s ^ 4) = W n d (s ^ 4) from rfl, W_pow_four_eq hd n hs] at h
  exact EReal.coe_le_coe_iff.1 h

/-- `q_{n,d} = (w_{n,d}/4)^{1/3}`, so that `w_{n,d} = 4 q³` and `e_{n,d} = q⁴`. -/
def qN (n d : ℕ) : ℝ := (wN n d / 4) ^ (1 / 3 : ℝ)

lemma qN_nonneg (n d : ℕ) : 0 ≤ qN n d :=
  Real.rpow_nonneg (div_nonneg (wN_nonneg n d) (by norm_num)) _

lemma wN_eq (n d : ℕ) : wN n d = 4 * qN n d ^ 3 := by
  have h := Real.rpow_inv_natCast_pow (x := wN n d / 4) (n := 3)
    (div_nonneg (wN_nonneg n d) (by norm_num)) (by norm_num)
  rw [show ((3 : ℕ) : ℝ)⁻¹ = (1 / 3 : ℝ) by norm_num] at h
  rw [qN, h]
  ring

lemma eN_eq (n d : ℕ) : eN n d = qN n d ^ 4 := by
  rw [eN, qN, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (wN_nonneg n d) (by norm_num))]
  norm_num

lemma eN_nonneg (n d : ℕ) : 0 ≤ eN n d := by
  rw [eN_eq]
  positivity

lemma betaN_nonneg (n d : ℕ) : 0 ≤ betaN n d := by
  rw [betaN]
  linarith [eN_nonneg n d]

/-- `W_{n,d}(e_{n,d}) = 4 e_{n,d}` (paper l. 291: `E M_n(e_{n,d}) = 4 e_{n,d}`). -/
theorem W_eN_toReal {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : (W n d (eN n d)).toReal = 4 * eN n d := by
  rcases (qN_nonneg n d).eq_or_lt with hq | hq
  · have hw : wN n d = 0 := by rw [wN_eq, ← hq]; ring
    have he : eN n d = 0 := by rw [eN_eq, ← hq]; ring
    rw [he]
    have h1 : W n d 0 ≤ W n d 1 := Wg_mono zero_le_one
    rw [W_one_eq hd n, hw, EReal.coe_zero] at h1
    have h0 : W n d 0 = 0 := le_antisymm h1 (W_nonneg n d 0)
    rw [h0]
    simp
  · rw [eN_eq, W_pow_four_eq hd n hq, EReal.toReal_coe, wN_eq]
    ring

/-- **`β_{n,d} ≤ A_{n,d}`** (paper l. 264; HA1 D9, step 1): `A ≥ W(e) - e = 4e - e = 3e`. -/
theorem betaN_le_A {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : betaN n d ≤ (A n d).toReal := by
  have h := W_le_A_add n d (eN_nonneg n d)
  rw [← W_coe_toReal hd n, W_eN_toReal hd n, ← A_coe_toReal hd n, ← EReal.coe_add] at h
  have h' := EReal.coe_le_coe_iff.1 h
  rw [betaN]
  linarith

/-! ## Positivity of `w_{n,d}` -/

section Tent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tent profile `x ↦ max(0, min(x, 1 - x)) • u`, an element of `V_1(E)`. -/
def tentProf (u : E) (x : ℝ) : E := (max 0 (min x (1 - x))) • u

lemma tentProf_mem_Vg_one (u : E) : tentProf u ∈ Vg E 1 := by
  refine ⟨by simp [tentProf], by simp [tentProf], fun x hx => ?_, fun k hk => ?_⟩
  · simp only [tentProf]
    have : max 0 (min x (1 - x)) = 0 := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · exact max_eq_left (by have := min_le_left x (1 - x); linarith)
      · exact max_eq_left (by have := min_le_right x (1 - x); linarith)
    rw [this, zero_smul]
  · have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · refine ⟨u, 0, fun x hx => ?_⟩
      have hx1 : x ≤ 1 / 2 := by
        have := hx.2
        norm_num at this
        linarith
      have hx0 : 0 ≤ x := by
        have := hx.1
        norm_num at this
        linarith
      simp only [tentProf, add_zero]
      rw [min_eq_left (by linarith), max_eq_right hx0]
    · refine ⟨-u, u, fun x hx => ?_⟩
      have hx1 : 1 / 2 ≤ x := by
        have := hx.1
        norm_num at this
        linarith
      have hx2 : x ≤ 1 := by
        have := hx.2
        norm_num at this
        linarith
      simp only [tentProf]
      rw [min_eq_right (by linarith), max_eq_right (by linarith), sub_smul, one_smul,
        smul_neg]
      abel

lemma tentProf_mem_Vg (u : E) {n : ℕ} (hn : 1 ≤ n) : tentProf u ∈ Vg E n :=
  Vg_mono hn (tentProf_mem_Vg_one u)

end Tent

section TentInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `E(tent_u) = ‖u‖²/2`. -/
lemma energy_tentProf (u : E) : energy (tentProf u) = ‖u‖ ^ 2 / 2 := by
  rw [Vg_energy (tentProf_mem_Vg_one u)]
  have e0 : tentProf u (((0 : ℕ) : ℝ) / 2 ^ 1) = 0 := by simp [tentProf]
  have e1 : tentProf u ((((0 : ℕ) : ℝ) + 1) / 2 ^ 1) = (1 / 2 : ℝ) • u := by
    simp only [tentProf]
    norm_num
  have e1' : tentProf u (((1 : ℕ) : ℝ) / 2 ^ 1) = (1 / 2 : ℝ) • u := by
    simp only [tentProf]
    norm_num
  have e2 : tentProf u ((((1 : ℕ) : ℝ) + 1) / 2 ^ 1) = 0 := by
    simp only [tentProf]
    norm_num
  rw [show (2 : ℕ) ^ 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, e0, e1, e1', e2, sub_zero, zero_sub, norm_neg, norm_smul]
  norm_num
  ring

lemma integral_norm_tentProf_pos {u : E} (hu : u ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, ‖tentProf u x‖ := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Vg_continuous (tentProf_mem_Vg_one u)).norm.intervalIntegrable 0 1)
    (fun x hx => ?_) zero_lt_one
  simp only [tentProf, norm_smul, Real.norm_eq_abs]
  have h : 0 < min x (1 - x) := lt_min hx.1 (by linarith [hx.2])
  rw [max_eq_right h.le, abs_of_pos h]
  exact mul_pos h (norm_pos_iff.2 hu)

end TentInner

/-- `E (⟪v, γ⟫)⁺ = c₀ ‖v‖ / 2` for `γ ∼ stdGaussian H`. -/
lemma integral_max_inner_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] (v : H) :
    ∫ x, max ⟪v, x⟫ 0 ∂(stdGaussian H) = gaussAbsMean * ‖v‖ / 2 := by
  have hint : Integrable (fun x : H => ⟪v, x⟫) (stdGaussian H) :=
    IsGaussian.integrable_id.const_inner v
  have habs := integrable_abs_inner_stdGaussian v
  have e : ∀ x : H, max ⟪v, x⟫ 0 = (⟪v, x⟫ + |⟪v, x⟫|) / 2 := fun x => by
    rcases le_total 0 ⟪v, x⟫ with h | h
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
  simp_rw [e]
  rw [integral_div, integral_add hint habs, integral_abs_inner_stdGaussian]
  have h0 : ∫ x, ⟪v, x⟫ ∂(stdGaussian H) = 0 := by
    have h := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id (μ := stdGaussian H)) v
    simp only [id] at h
    rw [h, integral_id_stdGaussian, inner_zero_right]
  rw [h0]
  ring

/-- **`0 < w_{n,d}`** for `n ≥ 1` and `d ≥ 2`: the family `{0, tent}` lies in the unit energy
ball, and `E max(G(0), G(tent)) = E G(tent)⁺ = c₀ (Var G(tent))^{1/2} / 2 > 0`. -/
theorem wN_pos {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) : 0 < wN n d := by
  classical
  have hm : 0 < d - 1 := by omega
  set u : Rd (d - 1) := EuclideanSpace.single (⟨0, hm⟩ : Fin (d - 1)) (1 : ℝ) with hudef
  have hu1 : ‖u‖ = 1 := by simp [hudef]
  have hu : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    exact zero_ne_one hu1
  set f0 : Vg (Rd (d - 1)) n := ⟨0, zero_mem_Vg n⟩ with hf0
  set ft : Vg (Rd (d - 1)) n := ⟨tentProf u, tentProf_mem_Vg u hn⟩ with hft
  set G : Finset (Vg (Rd (d - 1)) n) := {f0, ft} with hGdef
  have h0G : f0 ∈ G := Finset.mem_insert_self _ _
  have htG : ft ∈ G := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hG : ∀ f ∈ G, energy (f : ℝ → Rd (d - 1)) ≤ 1 := by
    intro f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · show energy (0 : ℝ → Rd (d - 1)) ≤ 1
      rw [energy_zero]
      norm_num
    · rw [Finset.mem_singleton.1 hf]
      show energy (tentProf u) ≤ 1
      rw [energy_tentProf, hu1]
      norm_num
  have hpos : 0 < gaussianExpectedMax G (fun f g => gCov (f : ℝ → Rd (d - 1)) g) 0 := by
    obtain ⟨v, hv, hvb⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax G
      (fun f g => gCov (f : ℝ → Rd (d - 1)) g) (gCov_psdOn_Vg n G)
    rw [hvb]
    have hv0 : v f0 = 0 := by
      have h := hv f0 h0G f0 h0G
      rw [real_inner_self_eq_norm_sq] at h
      have h00 : gCov ((f0 : Vg (Rd (d - 1)) n) : ℝ → Rd (d - 1)) f0 = 0 := by
        simp [hf0, gCov]
      rw [h00] at h
      exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
    have hvt : 0 < ‖v ft‖ := by
      have h := hv ft htG ft htG
      rw [real_inner_self_eq_norm_sq, gCov_self] at h
      have hI := integral_norm_tentProf_pos hu
      have h2 : 0 < ‖v ft‖ ^ 2 := by
        rw [h]
        have : ((ft : Vg (Rd (d - 1)) n) : ℝ → Rd (d - 1)) = tentProf u := rfl
        rw [this]
        positivity
      rcases (norm_nonneg (v ft)).eq_or_lt with h0 | h0
      · rw [← h0] at h2
        norm_num at h2
      · exact h0
    unfold vecExpectedMax
    have hle : ∀ x, max ⟪v ft, x⟫ 0 ≤ ⨆ i : G, ⟪v i, x⟫ + (0 : Vg (Rd (d - 1)) n → ℝ) i := by
      intro x
      refine max_le ?_ ?_
      · have h := LQGDimension.L23.le_fsup
          (fun i => ⟪v i, x⟫ + (0 : Vg (Rd (d - 1)) n → ℝ) i) htG
        simpa using h
      · have h := LQGDimension.L23.le_fsup
          (fun i => ⟪v i, x⟫ + (0 : Vg (Rd (d - 1)) n → ℝ) i) h0G
        simpa [hv0] using h
    have hint : Integrable (fun x => max ⟪v ft, x⟫ 0) (stdGaussian (EuclideanSpace ℝ G)) :=
      (IsGaussian.integrable_id.const_inner (v ft)).pos_part
    calc (0 : ℝ) < gaussAbsMean * ‖v ft‖ / 2 := by
          have := gaussAbsMean_pos
          positivity
      _ = ∫ x, max ⟪v ft, x⟫ 0 ∂(stdGaussian (EuclideanSpace ℝ G)) :=
          (integral_max_inner_zero _).symm
      _ ≤ _ := integral_mono hint (LQGDimension.integrable_iSup_inner_add G v _) hle
  have hW := le_Wg G hG
  rw [show Wg (Rd (d - 1)) n 1 = W n d 1 from rfl, W_one_eq hd n] at hW
  exact hpos.trans_le (EReal.coe_le_coe_iff.1 hW)

/-- `0 < e_{n,d}` for `n ≥ 1` and `d ≥ 2`. -/
lemma eN_pos {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) : 0 < eN n d :=
  Real.rpow_pos_of_pos (div_pos (wN_pos hd hn) (by norm_num)) _

end Var

open Var

/-- **The energy-ball quantities** (packet P-V2, target T1), for every `d ≥ 2`:
`W_{n,d}(r) ≥ 0`; `W_{n,d}(r) ≤ A_{n,d} + r` for `r ≥ 0`; `W_{n,d}(r) < ∞`;
homogeneity `W_{n,d}(r) = r^{1/4} W_{n,d}(1)` for `r > 0`; and `0 < w_{n,d}` for `n ≥ 1`. -/
theorem energyBall_basic (d : ℕ) (hd : 2 ≤ d) :
    (∀ (n : ℕ) (r : ℝ), 0 ≤ W n d r) ∧
    (∀ (n : ℕ) (r : ℝ), 0 ≤ r → W n d r ≤ A n d + (r : EReal)) ∧
    (∀ (n : ℕ) (r : ℝ), W n d r ≠ ⊤) ∧
    (∀ (n : ℕ) (r : ℝ), 0 < r → W n d r = ((r ^ (1 / 4 : ℝ) : ℝ) : EReal) * W n d 1) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < wN n d) :=
  ⟨fun n r => W_nonneg n d r, fun n _ hr => W_le_A_add n d hr, fun n r => W_ne_top hd n r,
    fun n _ hr => Wg_rpow n hr, fun _ hn => wN_pos hd hn⟩

end HigherDimLFPP
