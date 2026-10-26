import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Real `C^∞` convergence on compact sets

Gwynne–Miller 1905.00384v2, proof of Lemma 2.4 (`coord-change-final.tex` l. 539–543): "if `f` is
smooth and compactly supported then `f ∘ φ_n` and all of its derivatives of all orders converge
uniformly". This file supplies the real-analytic transfer:

* `UConv A A₀ s k`: the `k`-th real Fréchet derivatives converge uniformly on every compact `K ⊆ s`;
* `uconv_of_holo`: for holomorphic maps on an open `s`, complex `iteratedDeriv` convergence gives
  real `UConv` (scalar restriction of the complex iterated derivative, an isometry);
* `uconv_bilin`: Leibniz rule (bounded bilinear maps preserve `UConv` up to order `k`);
* `uconv_comp`: chain rule (`g ∘ φ_n → g ∘ φ₀` in `C^∞` on compacts, for every smooth `g`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace SupercriticalConformalCovariance.GM24

/-- `k`-th real derivatives converge uniformly on every compact subset of `s`. -/
def UConv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℕ → ℂ → E) (A₀ : ℂ → E) (s : Set ℂ) (k : ℕ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ s →
    TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (A n)) (iteratedFDeriv ℝ k A₀) atTop K

/-- Uniform convergence transfers along eventual pointwise distance domination. -/
theorem tendstoUniformlyOn_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {u : ℕ → ℂ → X} {u₀ : ℂ → X} {v : ℕ → ℂ → Y} {v₀ : ℂ → Y} {K : Set ℂ}
    (h : TendstoUniformlyOn u u₀ atTop K)
    (hd : ∀ᶠ n in atTop, ∀ x ∈ K, dist (v₀ x) (v n x) ≤ dist (u₀ x) (u n x)) :
    TendstoUniformlyOn v v₀ atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε, hd] with n hn hdn x hx
  exact (hdn x hx).trans_lt (hn x hx)

/-! ## Holomorphic maps -/

theorem dist_restrictScalars {n : ℕ} (a b : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ) :
    dist (a.restrictScalars ℝ) (b.restrictScalars ℝ) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  exact ContinuousMultilinearMap.norm_restrictScalars (a - b)

/-- **Complex to real.** For maps holomorphic on an open `s`, uniform convergence of the complex
`k`-th derivatives on compacts gives `UConv` at order `k`. -/
theorem uconv_of_holo {s : Set ℂ} (hs : IsOpen s) {f : ℕ → ℂ → ℂ} {f₀ : ℂ → ℂ}
    (hf : ∀ᶠ n in atTop, DifferentiableOn ℂ (f n) s) (hf₀ : DifferentiableOn ℂ f₀ s) (k : ℕ)
    (hk : ∀ K : Set ℂ, IsCompact K → K ⊆ s →
      TendstoUniformlyOn (fun n => iteratedDeriv k (f n)) (iteratedDeriv k f₀) atTop K) :
    UConv f f₀ s k := by
  intro K hK hKs
  refine tendstoUniformlyOn_of_dist_le (hk K hK hKs) ?_
  filter_upwards [hf] with n hfn x hx
  have hxs : x ∈ s := hKs hx
  have h1 : ContDiffAt ℂ k (f n) x := (hfn.contDiffOn hs).contDiffAt (hs.mem_nhds hxs)
  have h0 : ContDiffAt ℂ k f₀ x := (hf₀.contDiffOn hs).contDiffAt (hs.mem_nhds hxs)
  rw [← h1.restrictScalars_iteratedFDeriv (𝕜 := ℝ), ← h0.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply]
  rw [dist_restrictScalars]
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.dist_map,
    le_refl]

/-! ## Leibniz rule -/

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem continuousOn_iteratedFDeriv_of_contDiffOn {A : ℂ → E} {s : Set ℂ} (hs : IsOpen s)
    (hA : ContDiffOn ℝ ∞ A s) (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i A) s :=
  (hA.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn).congr
    fun _ hx => (iteratedFDerivWithin_of_isOpen i hs hx).symm

/-- **Leibniz rule for `UConv`.** A continuous bilinear map preserves `UConv` up to order `k`. -/
theorem uconv_bilin (β : E →L[ℝ] F →L[ℝ] G) {s : Set ℂ} (hs : IsOpen s)
    {A : ℕ → ℂ → E} {A₀ : ℂ → E} {B : ℕ → ℂ → F} {B₀ : ℂ → F}
    (hA : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (A n) s) (hA₀ : ContDiffOn ℝ ∞ A₀ s)
    (hB : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (B n) s) (hB₀ : ContDiffOn ℝ ∞ B₀ s) (k : ℕ)
    (hAc : ∀ j ≤ k, UConv A A₀ s j) (hBc : ∀ j ≤ k, UConv B B₀ s j) :
    UConv (fun n y => β (A n y) (B n y)) (fun y => β (A₀ y) (B₀ y)) s k := by
  intro K hK hKs
  choose MA hMA using fun i : ℕ =>
    hK.exists_bound_of_continuousOn ((continuousOn_iteratedFDeriv_of_contDiffOn hs hA₀ i).mono hKs)
  choose MB hMB using fun i : ℕ =>
    hK.exists_bound_of_continuousOn ((continuousOn_iteratedFDeriv_of_contDiffOn hs hB₀ i).mono hKs)
  set S : ℝ := ‖β‖ * ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * ((|MB (k - i)| + 1) + |MA i|) with hSdef
  have hS : 0 ≤ S := by rw [hSdef]; positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := min 1 (ε / (2 * (S + 1))) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδS : δ * S < ε := by
    have h1 : δ ≤ ε / (2 * (S + 1)) := min_le_right _ _
    have h2 : δ * S ≤ ε / (2 * (S + 1)) * S := mul_le_mul_of_nonneg_right h1 hS
    have h3 : ε / (2 * (S + 1)) * S < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hAe : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1), ∀ x ∈ K,
      dist (iteratedFDeriv ℝ i A₀ x) (iteratedFDeriv ℝ i (A n) x) < δ :=
    (Filter.eventually_all_finset _).2 fun i hi =>
      Metric.tendstoUniformlyOn_iff.1
        (hAc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) K hK hKs) δ hδ
  have hBe : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1), ∀ x ∈ K,
      dist (iteratedFDeriv ℝ i B₀ x) (iteratedFDeriv ℝ i (B n) x) < δ :=
    (Filter.eventually_all_finset _).2 fun i hi =>
      Metric.tendstoUniformlyOn_iff.1
        (hBc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) K hK hKs) δ hδ
  filter_upwards [hAe, hBe, hA, hB] with n hAn hBn hAn' hBn' x hx
  have hxs : x ∈ s := hKs hx
  have hnx : s ∈ 𝓝 x := hs.mem_nhds hxs
  have hdA : ContDiffOn ℝ ∞ (A n - A₀) s := hAn'.sub hA₀
  have hdB : ContDiffOn ℝ ∞ (B n - B₀) s := hBn'.sub hB₀
  have hβc : ∀ {a : ℂ → E} {b : ℂ → F}, ContDiffOn ℝ ∞ a s → ContDiffOn ℝ ∞ b s →
      ContDiffAt ℝ k (fun y => β (a y) (b y)) x := fun ha hb =>
    ((β.contDiff.contDiffAt.comp x ((ha.contDiffAt hnx).of_le (by exact_mod_cast le_top))).clm_apply
      ((hb.contDiffAt hnx).of_le (by exact_mod_cast le_top)))
  have hsplit : (fun y => β (A n y) (B n y)) =
      ((fun y => β ((A n - A₀) y) (B n y)) + fun y => β (A₀ y) ((B n - B₀) y)) +
        fun y => β (A₀ y) (B₀ y) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, map_sub, sub_apply]
    abel
  have hsum12 : ContDiffAt ℝ k ((fun y => β ((A n - A₀) y) (B n y)) +
      fun y => β (A₀ y) ((B n - B₀) y)) x := (hβc hdA hBn').add (hβc hA₀ hdB)
  rw [hsplit, iteratedFDeriv_add_apply hsum12 (hβc hA₀ hB₀),
    iteratedFDeriv_add_apply (hβc hdA hBn') (hβc hA₀ hdB), dist_eq_norm]
  have hw : ∀ {a : ℂ → E} {b : ℂ → F}, ContDiffOn ℝ ∞ a s → ContDiffOn ℝ ∞ b s →
      ‖iteratedFDeriv ℝ k (fun y => β (a y) (b y)) x‖ ≤ ‖β‖ * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (k - i) b x‖ := by
    intro a b ha hb
    rw [← iteratedFDerivWithin_of_isOpen k hs hxs]
    refine (β.norm_iteratedFDerivWithin_le_of_bilinear ha hb hs.uniqueDiffOn hxs
      (by exact_mod_cast le_top)).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDerivWithin_of_isOpen i hs hxs, iteratedFDerivWithin_of_isOpen (k - i) hs hxs]
  have hsubA : ∀ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (A n - A₀) x‖ ≤ δ := by
    intro i hi
    rw [iteratedFDeriv_sub_apply ((hAn'.contDiffAt hnx).of_le (by exact_mod_cast le_top))
      ((hA₀.contDiffAt hnx).of_le (by exact_mod_cast le_top)), ← dist_eq_norm, dist_comm]
    exact (hAn i hi x hx).le
  have hsubB : ∀ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (B n - B₀) x‖ ≤ δ := by
    intro i hi
    rw [iteratedFDeriv_sub_apply ((hBn'.contDiffAt hnx).of_le (by exact_mod_cast le_top))
      ((hB₀.contDiffAt hnx).of_le (by exact_mod_cast le_top)), ← dist_eq_norm, dist_comm]
    exact (hBn i hi x hx).le
  have hBnb : ∀ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (B n) x‖ ≤ |MB i| + 1 := by
    intro i hi
    have h1 : ‖iteratedFDeriv ℝ i (B n) x‖ ≤ ‖iteratedFDeriv ℝ i B₀ x‖ + δ :=
      norm_le_of_mem_closedBall (by rw [mem_closedBall, dist_comm]; exact (hBn i hi x hx).le)
    linarith [hMB i x hx, le_abs_self (MB i)]
  have hmem : ∀ i ∈ Finset.range (k + 1), k - i ∈ Finset.range (k + 1) := fun i _ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.sub_le k i))
  have hT1 : ‖iteratedFDeriv ℝ k (fun y => β ((A n - A₀) y) (B n y)) x‖ ≤
      ‖β‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (δ * (|MB (k - i)| + 1)) := by
    refine (hw hdA hBn').trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_)
      (by positivity))
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hsubA i hi) (hBnb _ (hmem i hi))
      (norm_nonneg _) hδ.le) (by positivity)
  have hT2 : ‖iteratedFDeriv ℝ k (fun y => β (A₀ y) ((B n - B₀) y)) x‖ ≤
      ‖β‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (|MA i| * δ) := by
    refine (hw hA₀ hdB).trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_)
      (by positivity))
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul ((hMA i x hx).trans (le_abs_self _))
      (hsubB _ (hmem i hi)) (norm_nonneg _) (abs_nonneg _)) (by positivity)
  have hsum : ‖β‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (δ * (|MB (k - i)| + 1)) +
      ‖β‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (|MA i| * δ) = δ * S := by
    rw [hSdef, ← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc ‖iteratedFDeriv ℝ (k) (fun y => β (A₀ y) (B₀ y)) x -
        (iteratedFDeriv ℝ k (fun y => β ((A n - A₀) y) (B n y)) x +
          iteratedFDeriv ℝ k (fun y => β (A₀ y) ((B n - B₀) y)) x +
          iteratedFDeriv ℝ k (fun y => β (A₀ y) (B₀ y)) x)‖
      = ‖iteratedFDeriv ℝ k (fun y => β ((A n - A₀) y) (B n y)) x +
          iteratedFDeriv ℝ k (fun y => β (A₀ y) ((B n - B₀) y)) x‖ := by
        rw [← norm_neg]; congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hT1 hT2
    _ = δ * S := hsum
    _ < ε := hδS

/-! ## Chain rule -/

theorem uconv_zero_iff {A : ℕ → ℂ → E} {A₀ : ℂ → E} {s : Set ℂ} :
    UConv A A₀ s 0 ↔ ∀ K : Set ℂ, IsCompact K → K ⊆ s → TendstoUniformlyOn A A₀ atTop K := by
  have hd : ∀ (a b : ℂ → E) (x : ℂ),
      dist (iteratedFDeriv ℝ 0 a x) (iteratedFDeriv ℝ 0 b x) = dist (a x) (b x) := by
    intro a b x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.dist_map]
  constructor
  · intro h K hK hKs
    exact tendstoUniformlyOn_of_dist_le (h K hK hKs)
      (Eventually.of_forall fun n x _ => (hd _ _ x).ge)
  · intro h K hK hKs
    exact tendstoUniformlyOn_of_dist_le (h K hK hKs)
      (Eventually.of_forall fun n x _ => (hd _ _ x).le)

/-- `UConv` of the derivatives at order `j` is `UConv` of the maps at order `j + 1`. -/
theorem uconv_fderiv_iff {A : ℕ → ℂ → E} {A₀ : ℂ → E} {s : Set ℂ} (j : ℕ) :
    UConv (fun n => fderiv ℝ (A n)) (fderiv ℝ A₀) s j ↔ UConv A A₀ s (j + 1) := by
  have hd : ∀ (a b : ℂ → E) (x : ℂ),
      dist (iteratedFDeriv ℝ (j + 1) a x) (iteratedFDeriv ℝ (j + 1) b x) =
        dist (iteratedFDeriv ℝ j (fderiv ℝ a) x) (iteratedFDeriv ℝ j (fderiv ℝ b) x) := by
    intro a b x
    simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.dist_map]
  constructor
  · intro h K hK hKs
    exact tendstoUniformlyOn_of_dist_le (h K hK hKs)
      (Eventually.of_forall fun n x _ => (hd _ _ x).le)
  · intro h K hK hKs
    exact tendstoUniformlyOn_of_dist_le (h K hK hKs)
      (Eventually.of_forall fun n x _ => (hd _ _ x).ge)

/-- `UConv` only depends on the functions near `s`, eventually in `n`. -/
theorem uconv_congr {A A' : ℕ → ℂ → E} {A₀ A₀' : ℂ → E} {s : Set ℂ} (hs : IsOpen s) {k : ℕ}
    (h : UConv A A₀ s k) (he : ∀ᶠ n in atTop, EqOn (A n) (A' n) s) (he₀ : EqOn A₀ A₀' s) :
    UConv A' A₀' s k := by
  intro K hK hKs
  refine tendstoUniformlyOn_of_dist_le (h K hK hKs) ?_
  filter_upwards [he] with n hn x hx
  have hxs : x ∈ s := hKs hx
  have e1 : iteratedFDeriv ℝ k (A n) x = iteratedFDeriv ℝ k (A' n) x :=
    (Filter.eventuallyEq_of_mem (hs.mem_nhds hxs) hn).iteratedFDeriv ℝ k |>.eq_of_nhds
  have e0 : iteratedFDeriv ℝ k A₀ x = iteratedFDeriv ℝ k A₀' x :=
    (Filter.eventuallyEq_of_mem (hs.mem_nhds hxs) he₀).iteratedFDeriv ℝ k |>.eq_of_nhds
  rw [e1, e0]

/-- **Chain rule for `UConv`.** If `φ_n → φ₀` in `C^∞` on compact subsets of the open `s`, then so
does `g ∘ φ_n → g ∘ φ₀`, for every smooth `g`. -/
theorem uconv_comp {s : Set ℂ} (hs : IsOpen s) {φ : ℕ → ℂ → ℂ} {φ₀ : ℂ → ℂ}
    (hφ : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (φ n) s) (hφ₀ : ContDiffOn ℝ ∞ φ₀ s)
    (hc : ∀ k, UConv φ φ₀ s k) :
    ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℂ → F),
      ContDiff ℝ ∞ g → ∀ j ≤ k, UConv (fun n => g ∘ φ n) (g ∘ φ₀) s j := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g hg j hj
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rw [uconv_zero_iff]
    intro K hK hKs
    have h0 := (uconv_zero_iff.1 (hc 0)) K hK hKs
    have hL : IsCompact (cthickening 1 (φ₀ '' K)) :=
      (hK.image_of_continuousOn (hφ₀.continuousOn.mono hKs)).cthickening
    have hev : ∀ᶠ n in atTop, ∀ x ∈ K, φ n x ∈ cthickening 1 (φ₀ '' K) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 h0 1 one_pos] with n hn x hx
      exact Metric.mem_cthickening_of_dist_le _ _ _ _ (mem_image_of_mem φ₀ hx)
        (by rw [dist_comm]; exact (hn x hx).le)
    exact (hL.uniformContinuousOn_of_continuous hg.continuous.continuousOn).comp_tendstoUniformlyOn_eventually
      hev (fun x hx => self_subset_cthickening _ (mem_image_of_mem φ₀ hx)) h0
  | succ k ih =>
    intro F _ _ g hg j hj
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact ih g hg j (Nat.lt_succ_iff.1 hj)
    rw [← uconv_fderiv_iff]
    have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by exact_mod_cast le_rfl)
    have hA := ih (fderiv ℝ g) hg'
    have hBc : ∀ j ≤ k, UConv (fun n => fderiv ℝ (φ n)) (fderiv ℝ φ₀) s j :=
      fun j _ => (uconv_fderiv_iff j).2 (hc (j + 1))
    have hAs : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fderiv ℝ g ∘ φ n) s := by
      filter_upwards [hφ] with n hn
      exact hg'.comp_contDiffOn hn
    have hBs : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (φ n)) s := by
      filter_upwards [hφ] with n hn
      exact hn.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)
    have key := uconv_bilin (ContinuousLinearMap.compL ℝ ℂ ℂ F) hs hAs
      (hg'.comp_contDiffOn hφ₀) hBs (hφ₀.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)) k hA hBc
    have hchain : ∀ {ψ : ℂ → ℂ}, ContDiffOn ℝ ∞ ψ s → EqOn
        (fun y => ContinuousLinearMap.compL ℝ ℂ ℂ F ((fderiv ℝ g ∘ ψ) y) (fderiv ℝ ψ y))
        (fderiv ℝ (g ∘ ψ)) s := by
      intro ψ hψ y hy
      have hψd : DifferentiableAt ℝ ψ y :=
        ((hψ.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp))
      simp only [Function.comp_apply, ContinuousLinearMap.compL_apply]
      rw [fderiv_comp y (hg.differentiable (by simp) _) hψd]
    refine uconv_congr hs key ?_ (hchain hφ₀)
    filter_upwards [hφ] with n hn
    exact hchain hn

end SupercriticalConformalCovariance.GM24
