/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsBeta
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finset.Sort

/-!
# The finite-dimensional moments of the stationary Jacobi process

Packet PROVE-YW-JACOBI. A polynomial `F ∈ MvPolynomial ℝ ℝ` in the variables `X_t` (one variable per
time `t ∈ ℝ`) is a polynomial function of finitely many values `U_t` of the process. Its expectation
under the stationary Jacobi law is computed by integrating out the latest time first:

* `slice t y F : ℝ[X]` is `F` as a polynomial in `X_t`, the other variables evaluated at `y`;
* `red s t F` replaces every power `X_t^n` by `(semi (t - s) X^n)(X_s)`: the conditional expectation
  of `U_t^n` given `U_s` (`eval_red`: `eval y (red s t F) = (semi (t - s) (slice t y F))(y s)`);
* `lamList L F` reduces along a list of times `t₁ > t₂ > ⋯ > t_k` and integrates the last variable
  against the invariant law `π` (`invLaw`); `lam F = lamList (vars F, decreasing) F`.

Main results:
* `lamList_erase`/`lamList_eq_lam`: the value does not depend on the decreasing list of times, as long
  as it contains the variables of `F` (the semigroup law, `semi t 1 = 1` and the invariance of `π`);
* `lamL`: `lam` is linear, `lam 1 = 1`;
* `lam_nonneg`: positivity on polynomials that are nonnegative on the cube `[0, 1]^ℝ`;
* `lam_mul_aeval`: the Markov property `E[G f(U_v)] = E[G (semi (v - w) f)(U_w)]` when `G` only
  involves times `≤ w ≤ v`;
* `lam_two`: the two-time formula;
* `hasDerivAt_lam_semi`: the derivative of `r ↦ E[G (semi r f)(U_w)]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

/-- The cube of configurations with values in `[0, 1]`. -/
def InCube (y : ℝ → ℝ) : Prop := ∀ d, y d ∈ Icc (0 : ℝ) 1

theorem inCube_zero : InCube 0 := fun _ => ⟨le_rfl, zero_le_one⟩

theorem InCube.update {y : ℝ → ℝ} (hy : InCube y) (t : ℝ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    InCube (Function.update y t z) := by
  intro d
  by_cases h : d = t
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact hy d

/-- `F` depends only on the coordinates in `S`. -/
def DepOn (F : MvPolynomial ℝ ℝ) (S : Set ℝ) : Prop :=
  ∀ y y' : ℝ → ℝ, (∀ d ∈ S, y d = y' d) → MvPolynomial.eval y F = MvPolynomial.eval y' F

theorem DepOn.mono {F : MvPolynomial ℝ ℝ} {S T : Set ℝ} (h : DepOn F S) (hST : S ⊆ T) : DepOn F T :=
  fun y y' hy => h y y' fun d hd => hy d (hST hd)

theorem depOn_vars (F : MvPolynomial ℝ ℝ) : DepOn F (F.vars : Set ℝ) := by
  intro y y' hy
  refine MvPolynomial.eval₂_congr _ _ _ fun {i c} hi hc => hy i ?_
  rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨c, MvPolynomial.mem_support_iff.2 hc, hi⟩

/-! ### Slices -/

/-- `F` as a polynomial in `X_t`, the other variables evaluated at `y`. -/
def slice (t : ℝ) (y : ℝ → ℝ) : MvPolynomial ℝ ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (Function.update (fun d => Polynomial.C (y d)) t Polynomial.X)

theorem slice_X (t : ℝ) (y : ℝ → ℝ) (n : ℝ) :
    slice t y (MvPolynomial.X n) = Function.update (fun d => Polynomial.C (y d)) t Polynomial.X n :=
  MvPolynomial.aeval_X _ _

theorem eval_slice (t : ℝ) (y : ℝ → ℝ) (F : MvPolynomial ℝ ℝ) (z : ℝ) :
    (slice t y F).eval z = MvPolynomial.eval (Function.update y t z) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [slice]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, slice_X, MvPolynomial.eval_X]
    by_cases h : n = t
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem slice_congr {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) {t : ℝ} {y y' : ℝ → ℝ}
    (hy : ∀ d ∈ S, d ≠ t → y d = y' d) : slice t y F = slice t y' F := by
  refine Polynomial.funext fun z => ?_
  rw [eval_slice, eval_slice]
  refine hF _ _ fun d hd => ?_
  by_cases h : d = t
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hy d hd h

theorem slice_eq_C {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) {t : ℝ} (ht : t ∉ S)
    (y : ℝ → ℝ) : slice t y F = Polynomial.C (MvPolynomial.eval y F) := by
  refine Polynomial.funext fun z => ?_
  rw [eval_slice, Polynomial.eval_C]
  refine hF _ _ fun d hd => ?_
  have : d ≠ t := fun h => ht (h ▸ hd)
  rw [Function.update_of_ne this]

theorem eval_aeval_X (y : ℝ → ℝ) (s : ℝ) (f : Polynomial ℝ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X s : MvPolynomial ℝ ℝ) f) = f.eval (y s) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval y)
    (MvPolynomial.X s : MvPolynomial ℝ ℝ) f
  rw [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

theorem slice_aeval_X (t : ℝ) (y : ℝ → ℝ) (f : Polynomial ℝ) :
    slice t y (Polynomial.aeval (MvPolynomial.X t : MvPolynomial ℝ ℝ) f) = f := by
  rw [← Polynomial.aeval_algHom_apply, slice, MvPolynomial.aeval_X, Function.update_self,
    Polynomial.aeval_X_left_apply]

/-! ### The one-step reduction -/

variable (κ a b : ℝ)

/-- `red s t` replaces `X_t^n` by `(semi (t - s) X^n)(X_s)`. -/
def red (s t : ℝ) : MvPolynomial ℝ ℝ →ₗ[ℝ] MvPolynomial ℝ ℝ :=
  (MvPolynomial.basisMonomials ℝ ℝ).constr ℝ fun m =>
    MvPolynomial.monomial (m.erase t) 1 *
      Polynomial.aeval (MvPolynomial.X s : MvPolynomial ℝ ℝ) (semi κ a b (t - s) (Polynomial.X ^ m t))

theorem red_monomial (s t : ℝ) (m : ℝ →₀ ℕ) (c : ℝ) :
    red κ a b s t (MvPolynomial.monomial m c) = c • (MvPolynomial.monomial (m.erase t) 1 *
      Polynomial.aeval (MvPolynomial.X s : MvPolynomial ℝ ℝ)
        (semi κ a b (t - s) (Polynomial.X ^ m t))) := by
  have e : MvPolynomial.monomial m c = c • (MvPolynomial.basisMonomials ℝ ℝ) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, red, Module.Basis.constr_basis]

/-- **The reduction in coordinates.** -/
theorem eval_red (s t : ℝ) (y : ℝ → ℝ) (F : MvPolynomial ℝ ℝ) :
    MvPolynomial.eval y (red κ a b s t F) = (semi κ a b (t - s) (slice t y F)).eval (y s) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    have hP : (Finsupp.erase t m).prod
        (fun d e => (Function.update (fun d => Polynomial.C (y d)) t Polynomial.X d) ^ e) =
        Polynomial.C ((Finsupp.erase t m).prod fun d e => y d ^ e) := by
      rw [map_finsuppProd]
      refine Finsupp.prod_congr fun d hd => ?_
      have : d ≠ t := by
        intro h; subst h; simp at hd
      rw [Function.update_of_ne this, map_pow]
    have hslice : slice t y (MvPolynomial.monomial m c) =
        Polynomial.C (c * (Finsupp.erase t m).prod fun d e => y d ^ e) * Polynomial.X ^ m t := by
      rw [slice, MvPolynomial.aeval_monomial, ← Finsupp.mul_prod_erase' m t _ (fun _ => pow_zero _),
        Function.update_self, hP, Polynomial.algebraMap_eq, Polynomial.C_mul]
      ring
    rw [hslice, semi_C_mul, Polynomial.eval_mul, Polynomial.eval_C, red_monomial,
      MvPolynomial.smul_eq_C_mul, map_mul, map_mul, MvPolynomial.eval_C, eval_aeval_X,
      MvPolynomial.eval_monomial, one_mul]
    ring
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, semi_add, Polynomial.eval_add]

theorem depOn_red {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) (s t : ℝ) :
    DepOn (red κ a b s t F) (insert s (S \ {t})) := by
  intro y y' hy
  rw [eval_red, eval_red, hy s (mem_insert s _),
    slice_congr hF fun d hd hdt => hy d (mem_insert_of_mem s ⟨hd, hdt⟩)]

theorem red_of_not_mem {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) {t : ℝ} (ht : t ∉ S)
    (s : ℝ) : red κ a b s t F = F :=
  MvPolynomial.funext fun y => by rw [eval_red, slice_eq_C hF ht, semi_C, Polynomial.eval_C]

theorem slice_red {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) {s t : ℝ} (hs : s ∉ S)
    (y : ℝ → ℝ) : slice s y (red κ a b s t F) = semi κ a b (t - s) (slice t y F) := by
  refine Polynomial.funext fun z => ?_
  rw [eval_slice, eval_red, Function.update_self]
  congr 2
  refine slice_congr hF fun d hd _ => ?_
  have : d ≠ s := fun h => hs (h ▸ hd)
  rw [Function.update_of_ne this]

theorem red_red {F : MvPolynomial ℝ ℝ} {S : Set ℝ} (hF : DepOn F S) {s t : ℝ} (hs : s ∉ S)
    (r : ℝ) : red κ a b r s (red κ a b s t F) = red κ a b r t F :=
  MvPolynomial.funext fun y => by
    rw [eval_red, eval_red, slice_red κ a b hF hs, semi_semi]
    congr 2
    ring

theorem red_mul_aeval {G : MvPolynomial ℝ ℝ} {S : Set ℝ} (hG : DepOn G S) {v : ℝ} (hv : v ∉ S)
    (w : ℝ) (f : Polynomial ℝ) :
    red κ a b w v (G * Polynomial.aeval (MvPolynomial.X v : MvPolynomial ℝ ℝ) f) =
      G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ) (semi κ a b (v - w) f) :=
  MvPolynomial.funext fun y => by
    rw [eval_red, map_mul, slice_eq_C hG hv, slice_aeval_X, semi_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, map_mul, eval_aeval_X]

/-! ### Reduction along a list of times -/

/-- Reduce along the list of times (latest first) and integrate the last variable against `π`. -/
def lamList : List ℝ → MvPolynomial ℝ ℝ → ℝ
  | [], F => MvPolynomial.eval 0 F
  | [t], F => ∫ z, (slice t 0 F).eval z ∂(invLaw κ a b)
  | t :: s :: rest, F => lamList (s :: rest) (red κ a b s t F)

variable {κ a b}

theorem lamList_add (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∀ (L : List ℝ) (F G : MvPolynomial ℝ ℝ),
      lamList κ a b L (F + G) = lamList κ a b L F + lamList κ a b L G
  | [], F, G => by simp [lamList]
  | [t], F, G => by
    simp only [lamList, map_add, Polynomial.eval_add]
    exact integral_add (integrable_eval_invLaw hκ ha hb _) (integrable_eval_invLaw hκ ha hb _)
  | t :: s :: rest, F, G => by
    simp only [lamList, map_add]
    exact lamList_add hκ ha hb (s :: rest) _ _

theorem lamList_smul : ∀ (L : List ℝ) (c : ℝ) (F : MvPolynomial ℝ ℝ),
    lamList κ a b L (c • F) = c * lamList κ a b L F
  | [], c, F => by simp [lamList]
  | [t], c, F => by
    simp only [lamList, map_smul, Polynomial.eval_smul, smul_eq_mul]
    exact integral_const_mul c _
  | t :: s :: rest, c, F => by
    simp only [lamList, map_smul]
    exact lamList_smul (s :: rest) c _

/-- **Removing a time on which `F` does not depend.** -/
theorem lamList_erase (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∀ (L : List ℝ) (F : MvPolynomial ℝ ℝ) (u : ℝ), u ∈ L → DepOn F {d | d ∈ L ∧ d ≠ u} →
      lamList κ a b L F = lamList κ a b (L.erase u) F
  | [], F, u, hu, _ => absurd hu List.not_mem_nil
  | [t], F, u, hu, hF => by
    have hut : u = t := List.mem_singleton.1 hu
    subst hut
    have hF' : DepOn F ∅ := hF.mono fun d hd => by
      simp only [List.mem_singleton, mem_ofPred_eq] at hd; exact absurd hd.1 hd.2
    have := isProbabilityMeasure_invLaw hκ ha hb
    rw [List.erase_cons_head]
    simp only [lamList]
    rw [slice_eq_C hF' (notMem_empty u)]
    simp only [Polynomial.eval_C, integral_const, probReal_univ, one_smul]
  | t :: s :: rest, F, u, hu, hF => by
    by_cases hut : u = t
    · subst hut
      rw [List.erase_cons_head]
      simp only [lamList]
      rw [red_of_not_mem κ a b hF (by simp)]
    by_cases hus : u = s
    · subst hus
      have hne : ¬ ((t == u) = true) := by simpa using Ne.symm hut
      rw [List.erase_cons_tail hne, List.erase_cons_head]
      have hsS : u ∉ {d | d ∈ t :: u :: rest ∧ d ≠ u} := by simp
      cases rest with
      | nil =>
        simp only [lamList]
        rw [show (fun z => (slice u 0 (red κ a b u t F)).eval z) =
            fun z => (semi κ a b (t - u) (slice t 0 F)).eval z by
          rw [slice_red κ a b hF hsS]]
        exact integral_semi_invLaw hκ ha hb _ _
      | cons r rest' =>
        simp only [lamList]
        rw [red_red κ a b hF hsS]
    · have hu' : u ∈ s :: rest := by
        rcases List.mem_cons.1 hu with h | h
        · exact absurd h hut
        · exact h
      have hne : ¬ ((t == u) = true) := by simpa using Ne.symm hut
      have hne' : ¬ ((s == u) = true) := by simpa using Ne.symm hus
      rw [List.erase_cons_tail hne, List.erase_cons_tail hne']
      simp only [lamList]
      have hG : DepOn (red κ a b s t F) {d | d ∈ s :: rest ∧ d ≠ u} := by
        refine (depOn_red κ a b hF s t).mono ?_
        intro d hd
        rcases hd with rfl | ⟨⟨hdL, hdu⟩, hdt⟩
        · exact ⟨List.mem_cons_self, Ne.symm hus⟩
        · refine ⟨?_, hdu⟩
          rcases List.mem_cons.1 hdL with h | h
          · exact absurd h hdt
          · exact h
      rw [lamList_erase hκ ha hb (s :: rest) _ u hu' hG, List.erase_cons_tail hne']

/-- The decreasing list of the elements of a finite set. -/
def sortDesc (S : Finset ℝ) : List ℝ := S.sort (· ≥ ·)

theorem pairwise_sortDesc (S : Finset ℝ) : (sortDesc S).Pairwise (· > ·) :=
  List.sortedGT_iff_pairwise.1 (Finset.sortedGT_sort S)

theorem mem_sortDesc {S : Finset ℝ} {d : ℝ} : d ∈ sortDesc S ↔ d ∈ S := Finset.mem_sort _

variable (κ a b)

/-- **The moment functional**: reduce along the decreasing list of the variables of `F`. -/
def lam (F : MvPolynomial ℝ ℝ) : ℝ := lamList κ a b (sortDesc F.vars) F

variable {κ a b}

/-- Two decreasing lists with the same elements are equal. -/
theorem eq_of_pairwise_of_mem_iff {L L' : List ℝ} (hL : L.Pairwise (· > ·))
    (hL' : L'.Pairwise (· > ·)) (h : ∀ d, d ∈ L ↔ d ∈ L') : L = L' :=
  (List.sortedGT_iff_pairwise.2 hL).eq_of_mem_iff (List.sortedGT_iff_pairwise.2 hL') h

/-- **Independence of the list of times.** -/
theorem lamList_eq_lam (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (F : MvPolynomial ℝ ℝ) :
    ∀ (n : ℕ) (L : List ℝ), L.length = n → L.Pairwise (· > ·) → (∀ d ∈ F.vars, d ∈ L) →
      lamList κ a b L F = lam κ a b F := by
  intro n
  induction n with
  | zero =>
    intro L hn hL hv
    have hL0 : L = [] := List.eq_nil_of_length_eq_zero hn
    subst hL0
    have : F.vars = ∅ := Finset.eq_empty_of_forall_notMem fun d hd => List.not_mem_nil (hv d hd)
    simp [lam, this, sortDesc]
  | succ n ih =>
    intro L hn hL hv
    by_cases hex : ∃ u ∈ L, u ∉ F.vars
    · obtain ⟨u, huL, huv⟩ := hex
      have hdep : DepOn F {d | d ∈ L ∧ d ≠ u} := (depOn_vars F).mono fun d hd =>
        ⟨hv d hd, fun h => huv (h ▸ hd)⟩
      rw [lamList_erase hκ ha hb L F u huL hdep]
      refine ih _ ?_ (hL.erase u) fun d hd => ?_
      · rw [List.length_erase_of_mem huL, hn]; rfl
      · have hdu : d ≠ u := fun h => huv (h ▸ hd)
        exact (List.mem_erase_of_ne hdu).2 (hv d hd)
    · push Not at hex
      have : L = sortDesc F.vars :=
        eq_of_pairwise_of_mem_iff hL (pairwise_sortDesc _) fun d =>
          ⟨fun h => mem_sortDesc.2 (hex d h), fun h => hv d (mem_sortDesc.1 h)⟩
      rw [this]
      rfl

theorem lamList_eq_lam' (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {F : MvPolynomial ℝ ℝ}
    {L : List ℝ} (hL : L.Pairwise (· > ·)) (hv : ∀ d ∈ F.vars, d ∈ L) :
    lamList κ a b L F = lam κ a b F :=
  lamList_eq_lam hκ ha hb F L.length L rfl hL hv

theorem lam_add (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (F G : MvPolynomial ℝ ℝ) :
    lam κ a b (F + G) = lam κ a b F + lam κ a b G := by
  classical
  set L := sortDesc (F.vars ∪ G.vars)
  have hL := pairwise_sortDesc (F.vars ∪ G.vars)
  rw [← lamList_eq_lam' hκ ha hb (L := L) hL (fun d hd => mem_sortDesc.2
      (MvPolynomial.vars_add_subset F G hd)),
    lamList_add hκ ha hb, lamList_eq_lam' hκ ha hb hL (fun d hd => mem_sortDesc.2
      (Finset.mem_union_left _ hd)),
    lamList_eq_lam' hκ ha hb hL (fun d hd => mem_sortDesc.2 (Finset.mem_union_right _ hd))]

theorem vars_smul_subset (c : ℝ) (p : MvPolynomial ℝ ℝ) : (c • p).vars ⊆ p.vars := by
  intro d hd
  rw [MvPolynomial.mem_vars_iff_mem_support] at hd ⊢
  obtain ⟨m, hm, hdm⟩ := hd
  exact ⟨m, MvPolynomial.support_smul hm, hdm⟩

theorem lam_smul (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (c : ℝ) (F : MvPolynomial ℝ ℝ) :
    lam κ a b (c • F) = c * lam κ a b F := by
  have hL := pairwise_sortDesc F.vars
  rw [← lamList_eq_lam' hκ ha hb (F := c • F) hL (fun d hd => mem_sortDesc.2
      (vars_smul_subset c F hd)), lamList_smul]
  rfl

variable (κ a b) in
/-- The moment functional as a linear map. -/
def lamL (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) : MvPolynomial ℝ ℝ →ₗ[ℝ] ℝ where
  toFun := lam κ a b
  map_add' := lam_add hκ ha hb
  map_smul' := lam_smul hκ ha hb

theorem lam_one : lam κ a b 1 = 1 := by
  simp [lam, MvPolynomial.vars_one, sortDesc, lamList]

/-! ### Positivity -/

theorem lamList_nonneg (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∀ (L : List ℝ), L.Pairwise (· > ·) → ∀ (F : MvPolynomial ℝ ℝ),
      (∀ y, InCube y → 0 ≤ MvPolynomial.eval y F) → 0 ≤ lamList κ a b L F
  | [], _, F, hF => hF 0 inCube_zero
  | [t], _, F, hF => by
    refine integral_eval_invLaw_nonneg fun z hz => ?_
    rw [eval_slice]
    exact hF _ (inCube_zero.update t hz)
  | t :: s :: rest, hL, F, hF => by
    simp only [lamList]
    have hst : s < t := List.rel_of_pairwise_cons hL List.mem_cons_self
    refine lamList_nonneg hκ ha hb (s :: rest) hL.of_cons _ fun y hy => ?_
    rw [eval_red]
    refine semi_eval_nonneg hκ.le ha.le hb.le (fun z hz => ?_) (by linarith) (hy s)
    rw [eval_slice]
    exact hF _ (hy.update t hz)

/-- **Positivity of the moment functional.** -/
theorem lam_nonneg (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {F : MvPolynomial ℝ ℝ}
    (hF : ∀ y, InCube y → 0 ≤ MvPolynomial.eval y F) : 0 ≤ lam κ a b F :=
  lamList_nonneg hκ ha hb _ (pairwise_sortDesc _) F hF

/-! ### The Markov property -/

theorem vars_aeval_X_subset (s : ℝ) (f : Polynomial ℝ) :
    (Polynomial.aeval (MvPolynomial.X s : MvPolynomial ℝ ℝ) f).vars ⊆ {s} := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  refine (MvPolynomial.vars_sum_subset _ _).trans ?_
  intro d hd
  simp only [Finset.mem_biUnion] at hd
  obtain ⟨i, -, hi⟩ := hd
  have h1 := vars_smul_subset (f.coeff i) ((MvPolynomial.X s : MvPolynomial ℝ ℝ) ^ i) hi
  have h2 := MvPolynomial.vars_pow (MvPolynomial.X s : MvPolynomial ℝ ℝ) i h1
  rwa [MvPolynomial.vars_X] at h2

theorem vars_mul_aeval_subset (G : MvPolynomial ℝ ℝ) (s : ℝ) (f : Polynomial ℝ) :
    (G * Polynomial.aeval (MvPolynomial.X s : MvPolynomial ℝ ℝ) f).vars ⊆ insert s G.vars := by
  classical
  intro d hd
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hd) with h | h
  · exact Finset.mem_insert_of_mem h
  · rw [Finset.mem_singleton.1 (vars_aeval_X_subset s f h)]; exact Finset.mem_insert_self _ _

/-- **The Markov property**: if `G` involves only times `≤ w ≤ v`, then
`E[G f(U_v)] = E[G (semi (v - w) f)(U_w)]`. -/
theorem lam_mul_aeval (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {G : MvPolynomial ℝ ℝ} {w v : ℝ}
    (hwv : w ≤ v) (hG : ∀ d ∈ G.vars, d ≤ w) (f : Polynomial ℝ) :
    lam κ a b (G * Polynomial.aeval (MvPolynomial.X v : MvPolynomial ℝ ℝ) f) =
      lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ)
        (semi κ a b (v - w) f)) := by
  classical
  rcases eq_or_lt_of_le hwv with h | hlt
  · subst h; rw [sub_self, semi_zero_time]
  set L₀ := w :: sortDesc (G.vars.erase w) with hL₀
  have hpair₀ : L₀.Pairwise (· > ·) := by
    refine List.Pairwise.cons (fun d hd => ?_) (pairwise_sortDesc _)
    have hd' := Finset.mem_erase.1 (mem_sortDesc.1 hd)
    exact lt_of_le_of_ne (hG d hd'.2) hd'.1
  have hpair : (v :: L₀).Pairwise (· > ·) := by
    refine List.Pairwise.cons (fun d hd => ?_) hpair₀
    rcases List.mem_cons.1 hd with h | h
    · rw [h]; exact hlt
    · have hd' := Finset.mem_erase.1 (mem_sortDesc.1 h)
      exact lt_of_le_of_lt (hG d hd'.2) hlt
  have hmemL₀ : ∀ d ∈ insert w G.vars, d ∈ L₀ := by
    intro d hd
    rcases Finset.mem_insert.1 hd with h | h
    · rw [h]; exact List.mem_cons_self
    · by_cases hdw : d = w
      · rw [hdw]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_sortDesc.2 (Finset.mem_erase.2 ⟨hdw, h⟩))
  have hS : DepOn G (G.vars : Set ℝ) := depOn_vars G
  have hvS : v ∉ (G.vars : Set ℝ) := fun h => absurd (hG v h) (not_le.2 hlt)
  rw [← lamList_eq_lam' hκ ha hb hpair (fun d hd => ?_),
    ← lamList_eq_lam' hκ ha hb hpair₀ (fun d hd => hmemL₀ d (vars_mul_aeval_subset G w _ hd))]
  · show lamList κ a b L₀ (red κ a b w v _) = _
    rw [red_mul_aeval κ a b hS hvS]
  · rcases Finset.mem_insert.1 (vars_mul_aeval_subset G v f hd) with h | h
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hmemL₀ d (Finset.mem_insert_of_mem h))

/-- **The two-time formula**: if `F` involves only the times `s < t`, then
`E[F] = ∫ (semi (t - s) (slice t (update 0 s z) F))(z) dπ(z)`. -/
theorem lam_two (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {F : MvPolynomial ℝ ℝ} {s t : ℝ}
    (hst : s < t) (hF : ∀ d ∈ F.vars, d = s ∨ d = t) :
    lam κ a b F = ∫ z, (semi κ a b (t - s) (slice t (Function.update 0 s z) F)).eval z
      ∂(invLaw κ a b) := by
  have hpair : [t, s].Pairwise (· > ·) := by simp [hst]
  rw [← lamList_eq_lam' hκ ha hb hpair (fun d hd => by
    rcases hF d hd with h | h <;> simp [h])]
  simp only [lamList]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [eval_slice, eval_red, Function.update_self]

/-- **The derivative of `r ↦ E[G (semi r f)(U_w)]`.** -/
theorem hasDerivAt_lam_semi (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (G : MvPolynomial ℝ ℝ)
    (w : ℝ) (f : Polynomial ℝ) (r : ℝ) :
    HasDerivAt (fun r => lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ)
        (semi κ a b r f)))
      (lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ)
        (genL κ a b (semi κ a b r f)))) r := by
  set N := f.natDegree + 1
  have hexp : ∀ q : Polynomial ℝ, q ∈ Polynomial.degreeLT ℝ N →
      lam κ a b (G * Polynomial.aeval (MvPolynomial.X w : MvPolynomial ℝ ℝ) q) =
        ∑ k ∈ Finset.range N, q.coeff k *
          lam κ a b (G * (MvPolynomial.X w : MvPolynomial ℝ ℝ) ^ k) := by
    intro q hq
    conv_lhs => rw [eq_sum_of_mem_degreeLT hq]
    simp only [map_sum, Finset.mul_sum, ← Polynomial.smul_eq_C_mul, map_smul, Polynomial.aeval_X_pow,
      mul_smul_comm]
    change lamL κ a b hκ ha hb _ = _
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  have hmem : ∀ s, semi κ a b s f ∈ Polynomial.degreeLT ℝ N := fun s =>
    semi_mem_degreeLT_succ κ a b s f
  simp only [hexp _ (hmem _)]
  rw [hexp _ (genL_mem_degreeLT κ a b (hmem r))]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_coeff_semi κ a b f r k).mul_const _

end JacobiExists

end Sec2

end InteractingSLE
