import QuantumZipper.Proofs.Zipper.SWCoreN2Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (2): uniform smallness of scale-indexed Gaussian families (boxes + Borel–Cantelli)

Assembly of `SWCoreN2Chain`: `swcn2_ae_eventually_small` (statement in the docstring of
`SWCoreN2Chain`). Sheffield–Wang, arXiv:1605.06171, Lemma 3.5 and the Borel–Cantelli step after
(3.23), p. 16. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif

theorem swcn2_rad_rpow_inv (x : ℝ) (k : ℕ) : (radius k ^ x)⁻¹ = ((2 : ℝ) ^ x) ^ k := by
  unfold radius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast, Real.inv_rpow (by norm_num), inv_pow, inv_inv]

theorem swcn2_radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Fixed

variable {d : ℕ} (Z : ℕ → (Fin d → ℝ) → Ω → ℝ) {D : Set (Fin d → ℝ)}

/-- The grid box of index `g` at side `s`. -/
def swcn2Box (D : Set (Fin d → ℝ)) (s : ℝ) (g : Fin d → ℤ) : Set (Fin d → ℝ) :=
  {θ | θ ∈ D ∧ ∀ i, |θ i - s * g i| ≤ s / 2}

theorem swcn2_box_diam {s : ℝ} (hs : 0 ≤ s) {g : Fin d → ℤ} {θ θ' : Fin d → ℝ}
    (hθ : θ ∈ swcn2Box D s g) (hθ' : θ' ∈ swcn2Box D s g) : ‖θ - θ'‖ ≤ s := by
  refine (pi_norm_le_iff_of_nonneg hs).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have h1 := hθ.2 i
  have h2 := hθ'.2 i
  calc |θ i - θ' i| = |(θ i - s * g i) - (θ' i - s * g i)| := by ring_nf
    _ ≤ |θ i - s * g i| + |θ' i - s * g i| := abs_sub _ _
    _ ≤ s := by linarith

theorem swcn2_mem_box {s : ℝ} (hs : 0 < s) {θ : Fin d → ℝ} (hθ : θ ∈ D) :
    θ ∈ swcn2Box D s (fun i => round (θ i / s)) := by
  refine ⟨hθ, fun i => ?_⟩
  have h := abs_sub_round (θ i / s)
  have e : θ i - s * (round (θ i / s) : ℝ) = s * (θ i / s - round (θ i / s)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hs]
  nlinarith

theorem swcn2_round_mem {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) {θ : Fin d → ℝ} (hθR : ‖θ‖ ≤ R) :
    (fun i => round (θ i / s)) ∈ Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-((⌈R / s⌉₊ + 1 : ℕ) : ℤ)) ((⌈R / s⌉₊ + 1 : ℕ) : ℤ) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hi : |θ i| ≤ R := by
    have := norm_le_pi_norm θ i
    rw [Real.norm_eq_abs] at this; linarith
  have hr := abs_sub_round (θ i / s)
  have hxs : |θ i / s| ≤ R / s := by
    rw [abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right hi hs.le
  have hceil : R / s ≤ (⌈R / s⌉₊ : ℝ) := Nat.le_ceil _
  have hb : |(round (θ i / s) : ℝ)| ≤ (⌈R / s⌉₊ : ℝ) + 1 := by
    have : |(round (θ i / s) : ℝ)| ≤ |θ i / s| + |θ i / s - round (θ i / s)| := by
      have := abs_sub_abs_le_abs_sub (round (θ i / s) : ℝ) (θ i / s)
      rw [abs_sub_comm (round (θ i / s) : ℝ)] at this
      linarith
    linarith
  rw [abs_le] at hb
  constructor
  · have : (-(((⌈R / s⌉₊ + 1 : ℕ) : ℤ)) : ℝ) ≤ (round (θ i / s) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · have : (round (θ i / s) : ℝ) ≤ (((⌈R / s⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this

theorem swcn2_rpow_facts {r : ℝ} (hr : 0 < r) (β : ℝ) :
    (r ^ 2) ^ (β / 2) = (r ^ (β / 2)) ^ 2 ∧ r ^ β = (r ^ (β / 2)) ^ 2 := by
  have h1 : (r ^ (β / 2)) ^ 2 = r ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  refine ⟨?_, h1.symm⟩
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring

/-- Variance of a negated difference. -/
theorem swcn2_var_neg_sub {Z₁ Z₂ : Ω → ℝ} :
    Var[fun ω => -Z₁ ω - -Z₂ ω; P] = Var[fun ω => Z₁ ω - Z₂ ω; P] := by
  have e : (fun ω => -Z₁ ω - -Z₂ ω) = fun ω => -(Z₁ ω - Z₂ ω) := by funext ω; ring
  rw [e, variance_fun_neg]

/-- **One grid box at scale `k`**: the probability that the family is not `η/3`-controlled on a box
(relative to its representative, and at the representative). -/
theorem swcn2_box_bound {d : ℕ} {Z : (Fin d → ℝ) → Ω → ℝ} {D : Set (Fin d → ℝ)}
    (hD : D.Countable) (hG : IsGaussianProcess Z P) (hc : ∀ θ, ∫ ω, Z θ ω ∂P = 0)
    (hZm : ∀ θ, Measurable (Z θ)) {V β₀ L β r η : ℝ} (hβ₀ : 0 < β₀) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hV : 0 ≤ V) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η)
    (hvar : ∀ θ ∈ D, Var[Z θ; P] ≤ V * r ^ β₀)
    (hmod : ∀ θ ∈ D, ∀ θ' ∈ D, ‖θ - θ'‖ ≤ r ^ 2 →
      Var[fun ω => Z θ ω - Z θ' ω; P] ≤ L ^ 2 * (‖θ - θ'‖ / r) ^ β)
    (g : Fin d → ℤ) (i₀ : Fin d → ℝ) (hi₀ : i₀ ∈ swcn2Box D (r ^ 2) g) :
    P (({ω | ∃ θ ∈ swcn2Box D (r ^ 2) g, η / 3 ≤ Z θ ω - Z i₀ ω} ∪
        {ω | ∃ θ ∈ swcn2Box D (r ^ 2) g, η / 3 ≤ -Z θ ω - -Z i₀ ω}) ∪
        ({ω | η / 3 ≤ Z i₀ ω} ∪ {ω | η / 3 ≤ -Z i₀ ω})) ≤
      ENNReal.ofReal (2 * Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 -
          η / 3 * (r ^ (β / 2))⁻¹) +
        2 * Real.exp (V / 2 - η / 3 * (r ^ (β₀ / 2))⁻¹)) := by
  haveI : Countable D := hD.to_subtype
  set A := swcn2Box D (r ^ 2) g with hA
  set u := r ^ (β / 2) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hr _
  obtain ⟨hs_u, hr_u⟩ := swcn2_rpow_facts hr β
  rw [← hu] at hs_u hr_u
  have hs0 : 0 ≤ r ^ 2 := by positivity
  have hsr : r ^ 2 ≤ r := by nlinarith
  -- the negated process
  have hGn : IsGaussianProcess (fun θ ω => -Z θ ω) P := by
    simpa using hG.smul (fun _ => (-1 : ℝ))
  have hcn : ∀ θ, ∫ ω, -Z θ ω ∂P = 0 := fun θ => by rw [integral_neg, hc, neg_zero]
  have hZmn : ∀ θ, Measurable fun ω => -Z θ ω := fun θ => (hZm θ).neg
  -- box tails for a process `W ∈ {Z, −Z}`
  have hboxW : ∀ W : (Fin d → ℝ) → Ω → ℝ, IsGaussianProcess W P → (∀ θ, ∫ ω, W θ ω ∂P = 0) →
      (∀ θ, Measurable (W θ)) →
      (∀ θ θ', Var[fun ω => W θ ω - W θ' ω; P] = Var[fun ω => Z θ ω - Z θ' ω; P]) →
      P {ω | ∃ θ ∈ A, η / 3 ≤ W θ ω - W i₀ ω} ≤
        ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 -
          η / 3 * u⁻¹)) := by
    intro W hW hWc hWm hWv
    have hWD : IsGaussianProcess (fun i : D => W i) P := hW.restrict D
    set A' : Set D := {i | (i : Fin d → ℝ) ∈ A} with hA'
    have hdiam : ∀ i ∈ A', ∀ j ∈ A', ‖(i : Fin d → ℝ) - j‖ ≤ r ^ 2 := fun i hi j hj =>
      swcn2_box_diam hs0 hi hj
    have hkey := swcn2_box_tail hWD (fun i => hWc i) (fun i => hWm i) (Subtype.val : D → _)
      (L := L / u) (a := r ^ 2) (σ := L * u) (t := u⁻¹) (η := η / 3) hβ hβ1
      (div_nonneg hL hu0.le) (mul_nonneg hL hu0.le) (inv_nonneg.2 hu0.le) ⟨i₀, hi₀.1⟩ A'
      hdiam (fun i hi j hj => by
        rw [hWv]
        refine (hmod i i.2 j j.2 (hdiam i hi j hj)).trans (le_of_eq ?_)
        rw [Real.div_rpow (norm_nonneg _) hr.le, hr_u]
        field_simp)
      (fun i hi => by
        rw [hWv]
        have hd := hdiam i hi ⟨i₀, hi₀.1⟩ hi₀
        refine (hmod i i.2 i₀ hi₀.1 hd).trans ?_
        have h1 : (‖(i : Fin d → ℝ) - i₀‖ / r) ^ β ≤ (r ^ 2 / r) ^ β :=
          Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hd hr.le) hβ.le
        have h2 : r ^ 2 / r = r := by field_simp
        rw [h2, hr_u] at h1
        calc L ^ 2 * (‖(i : Fin d → ℝ) - i₀‖ / r) ^ β ≤ L ^ 2 * u ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
          _ = (L * u) ^ 2 := by ring)
    refine (measure_mono fun ω hω => ?_).trans (hkey.trans (le_of_eq ?_))
    · obtain ⟨θ, hθ, hle⟩ := hω
      exact ⟨⟨θ, hθ.1⟩, hθ, hle⟩
    · congr 2
      rw [hs_u]
      field_simp
  have hU := hboxW Z hG hc hZm fun _ _ => rfl
  have hU' := hboxW (fun θ ω => -Z θ ω) hGn hcn hZmn fun θ θ' => swcn2_var_neg_sub
  -- point tails
  set w := r ^ (β₀ / 2) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  obtain ⟨-, hr_w⟩ := swcn2_rpow_facts hr β₀
  rw [← hw] at hr_w
  have hpt : ∀ U : Ω → ℝ, HasGaussianLaw U P → ∫ ω, U ω ∂P = 0 → Measurable U →
      Var[U; P] ≤ V * r ^ β₀ →
      P {ω | η / 3 ≤ U ω} ≤ ENNReal.ofReal (Real.exp (V / 2 - η / 3 * w⁻¹)) := by
    intro U hUg hUc hUm hUv
    refine (swcn2_point_tail hUg hUc hUm (t := w⁻¹) (η := η / 3) (inv_nonneg.2 hw0.le)).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    rw [hr_w] at hUv
    have : Var[U; P] * w⁻¹ ^ 2 / 2 ≤ V / 2 := by
      have h := mul_le_mul_of_nonneg_right hUv (sq_nonneg w⁻¹)
      have e : V * w ^ 2 * w⁻¹ ^ 2 = V := by field_simp
      rw [e] at h; linarith
    linarith [mul_comm w⁻¹ (η / 3)]
  have hW1 := hpt (Z i₀) (hG.hasGaussianLaw_eval i₀) (hc i₀) (hZm i₀) (hvar i₀ hi₀.1)
  have hW2 := hpt (fun ω => -Z i₀ ω) (hGn.hasGaussianLaw_eval i₀) (hcn i₀) (hZmn i₀)
    (by rw [variance_fun_neg]; exact hvar i₀ hi₀.1)
  calc _ ≤ (P {ω | ∃ θ ∈ A, η / 3 ≤ Z θ ω - Z i₀ ω} +
          P {ω | ∃ θ ∈ A, η / 3 ≤ -Z θ ω - -Z i₀ ω}) +
        (P {ω | η / 3 ≤ Z i₀ ω} + P {ω | η / 3 ≤ -Z i₀ ω}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ (ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 - η / 3 * u⁻¹)) +
          ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 - η / 3 * u⁻¹))) +
        (ENNReal.ofReal (Real.exp (V / 2 - η / 3 * w⁻¹)) +
          ENNReal.ofReal (Real.exp (V / 2 - η / 3 * w⁻¹))) :=
        add_le_add (add_le_add hU hU') (add_le_add hW1 hW2)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Fixed `η`**: box cover at side `r_k²`, per-box tails, Borel–Cantelli. The index sets `D k`
may depend on the scale (e.g. radii in `[r_k, 2 r_k]`). -/
theorem swcn2_fixed {d : ℕ} (Z : ℕ → (Fin d → ℝ) → Ω → ℝ) {D : ℕ → Set (Fin d → ℝ)}
    (hD : ∀ k, (D k).Countable) {R : ℝ} (hR : 0 ≤ R) (hDR : ∀ k, ∀ θ ∈ D k, ‖θ‖ ≤ R)
    (hG : ∀ k, IsGaussianProcess (Z k) P) (hc : ∀ k θ, ∫ ω, Z k θ ω ∂P = 0)
    (hZm : ∀ k θ, Measurable (Z k θ)) {V β₀ L β : ℝ} (hβ₀ : 0 < β₀) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hvar : ∀ k, ∀ θ ∈ D k, Var[Z k θ; P] ≤ V * radius k ^ β₀)
    (hmod : ∀ k, ∀ θ ∈ D k, ∀ θ' ∈ D k, ‖θ - θ'‖ ≤ radius k ^ 2 →
      Var[fun ω => Z k θ ω - Z k θ' ω; P] ≤ L ^ 2 * (‖θ - θ'‖ / radius k) ^ β)
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ D k, |Z k θ ω| ≤ η := by
  classical
  set r : ℕ → ℝ := fun k => radius k with hrdef
  have hr : ∀ k, 0 < r k := fun k => by simp only [hrdef]; unfold radius; positivity
  set N : ℕ → ℕ := fun k => ⌈R / r k ^ 2⌉₊ + 1 with hN
  set G : ℕ → Finset (Fin d → ℤ) := fun k =>
    Fintype.piFinset fun _ : Fin d => Finset.Icc (-((N k : ℕ) : ℤ)) ((N k : ℕ) : ℤ) with hGdef
  set A : ℕ → (Fin d → ℤ) → Set (Fin d → ℝ) := fun k g => swcn2Box (D k) (r k ^ 2) g with hA
  set i₀ : ℕ → (Fin d → ℤ) → (Fin d → ℝ) := fun k g =>
    if h : (A k g).Nonempty then h.some else 0 with hi₀
  set bad : ℕ → (Fin d → ℤ) → Set Ω := fun k g => if (A k g).Nonempty then
    (({ω | ∃ θ ∈ A k g, η / 3 ≤ Z k θ ω - Z k (i₀ k g) ω} ∪
      {ω | ∃ θ ∈ A k g, η / 3 ≤ -Z k θ ω - -Z k (i₀ k g) ω}) ∪
      ({ω | η / 3 ≤ Z k (i₀ k g) ω} ∪ {ω | η / 3 ≤ -Z k (i₀ k g) ω})) else ∅ with hbad
  set E : ℕ → Set Ω := fun k => ⋃ g ∈ G k, bad k g with hE
  set B1 : ℝ := (2 : ℝ) ^ (β / 2) with hB1
  set B2 : ℝ := (2 : ℝ) ^ (β₀ / 2) with hB2
  have hB1g : 1 < B1 := Real.one_lt_rpow (by norm_num) (by positivity)
  have hB2g : 1 < B2 := Real.one_lt_rpow (by norm_num) (by positivity)
  set C1 : ℝ := fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 with hC1
  set b : ℕ → ℝ := fun k => (2 * Real.exp (C1 - η / 3 * B1 ^ k) +
    2 * Real.exp (V / 2 - η / 3 * B2 ^ k)) with hb
  have hbad_le : ∀ k g, P (bad k g) ≤ ENNReal.ofReal (b k) := by
    intro k g
    by_cases hne : (A k g).Nonempty
    · have hmem : i₀ k g ∈ A k g := by simp only [hi₀, dif_pos hne]; exact hne.some_mem
      simp only [hbad, if_pos hne]
      have h := swcn2_box_bound (hD k) (hG k) (hc k) (hZm k) hβ₀ hβ hβ1 hL hV (hr k)
        (swcn2_radius_le_one k) hη (hvar k) (hmod k) g (i₀ k g) hmem (P := P)
      refine h.trans (le_of_eq ?_)
      rw [swcn2_rad_rpow_inv, swcn2_rad_rpow_inv]
    · simp only [hbad, if_neg hne, measure_empty]; exact bot_le
  have hcard : ∀ k, ((G k).card : ℝ) ≤ (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k := by
    intro k
    have hr2 : r k ^ 2 = ((4 : ℝ) ^ k)⁻¹ := by
      simp only [hrdef]; unfold radius
      rw [← pow_mul, inv_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    have hNk : (N k : ℝ) ≤ R * 4 ^ k + 2 := by
      have hc1 := Nat.ceil_lt_add_one (show 0 ≤ R / r k ^ 2 by positivity)
      rw [hr2, div_inv_eq_mul] at hc1
      have e : (N k : ℝ) = ((⌈R * 4 ^ k⌉₊ : ℕ) : ℝ) + 1 := by
        simp only [hN, hr2, div_inv_eq_mul]; push_cast; ring
      rw [e]; linarith
    rw [hGdef, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    push_cast
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hbase : ((((N k : ℤ) + 1 - -(N k : ℤ)).toNat : ℕ) : ℝ) ≤ (2 * R + 5) * 4 ^ k := by
      have e : ((N k : ℤ) + 1 - -(N k : ℤ)).toNat = 2 * N k + 1 := by omega
      rw [e]; push_cast; nlinarith
    calc ((((N k : ℤ) + 1 - -(N k : ℤ)).toNat : ℕ) : ℝ) ^ d ≤ ((2 * R + 5) * 4 ^ k) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase d
      _ = (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d]
  have hEk : ∀ k, P (E k) ≤ ENNReal.ofReal ((2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k * b k) := by
    intro k
    have hb0 : 0 ≤ b k := by simp only [hb]; positivity
    calc P (E k) ≤ ∑ g ∈ G k, P (bad k g) := measure_biUnion_finset_le _ _
      _ ≤ ∑ g ∈ G k, ENNReal.ofReal (b k) := Finset.sum_le_sum fun g _ => hbad_le k g
      _ = ENNReal.ofReal ((G k).card * b k) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcard k) hb0)
  have hsum : Summable fun k => (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k * b k := by
    have h1 := (swcn2_summable (A := (4 : ℝ) ^ d) (by positivity) (by positivity : 0 < η / 3)
      hB1g).mul_left ((2 * R + 5) ^ d * (2 * Real.exp C1))
    have h2 := (swcn2_summable (A := (4 : ℝ) ^ d) (by positivity) (by positivity : 0 < η / 3)
      hB2g).mul_left ((2 * R + 5) ^ d * (2 * Real.exp (V / 2)))
    refine (h1.add h2).congr fun k => ?_
    simp only [hb, sub_eq_add_neg, Real.exp_add]
    ring
  have htsum : (∑' k, P (E k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEk)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by simp only [hb]; positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω] with k hk θ hθ
  set g : Fin d → ℤ := fun i => round (θ i / r k ^ 2) with hg
  have hs : 0 < r k ^ 2 := pow_pos (hr k) 2
  have hθA : θ ∈ A k g := swcn2_mem_box hs hθ
  have hgG : g ∈ G k := swcn2_round_mem hs hR (hDR k θ hθ)
  have hne : (A k g).Nonempty := ⟨θ, hθA⟩
  have hnb : ω ∉ bad k g := fun h => hk (mem_biUnion hgG h)
  simp only [hbad, if_pos hne, mem_union, mem_ofPred_eq, not_or, not_exists, not_and,
    not_le] at hnb
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hnb
  have a1 := h1 θ hθA
  have a2 := h2 θ hθA
  rw [abs_le]
  constructor <;> linarith

/-- **SWC-N2**: centred Gaussian families at scale `r_k = 2^{-k}` with variance `≤ V r_k^{β₀}` and
modulus `L² (‖θ − θ'‖/r_k)^β` (for `‖θ − θ'‖ ≤ r_k²`) are almost surely uniformly small for large `k`. -/
theorem swcn2_ae_eventually_small {d : ℕ} (Z : ℕ → (Fin d → ℝ) → Ω → ℝ)
    {D : ℕ → Set (Fin d → ℝ)} (hD : ∀ k, (D k).Countable) {R : ℝ} (hR : 0 ≤ R)
    (hDR : ∀ k, ∀ θ ∈ D k, ‖θ‖ ≤ R)
    (hG : ∀ k, IsGaussianProcess (Z k) P) (hc : ∀ k θ, ∫ ω, Z k θ ω ∂P = 0)
    (hZm : ∀ k θ, Measurable (Z k θ)) {V β₀ L β : ℝ} (hβ₀ : 0 < β₀) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hvar : ∀ k, ∀ θ ∈ D k, Var[Z k θ; P] ≤ V * radius k ^ β₀)
    (hmod : ∀ k, ∀ θ ∈ D k, ∀ θ' ∈ D k, ‖θ - θ'‖ ≤ radius k ^ 2 →
      Var[fun ω => Z k θ ω - Z k θ' ω; P] ≤ L ^ 2 * (‖θ - θ'‖ / radius k) ^ β) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ θ ∈ D k, |Z k θ ω| ≤ η := by
  have h : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ D k, |Z k θ ω| ≤ 1 / ((j : ℝ) + 1) :=
    fun j => swcn2_fixed Z hD hR hDR hG hc hZm hβ₀ hβ hβ1 hL hV hvar hmod (by positivity)
  filter_upwards [ae_all_iff.2 h] with ω hω η hη
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω j] with k hk θ hθ
  exact (hk θ hθ).trans hj.le

end Fixed

end SWCore
end QuantumZipper
