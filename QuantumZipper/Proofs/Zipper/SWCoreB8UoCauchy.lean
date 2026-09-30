import QuantumZipper.Proofs.Zipper.UnifSWDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (d), part 1: uniform Cauchy along a filter (offset form of the UNIF-SW reduction)

The dyadic off-tip chain (`UnifSWDense.ucs_of_fam`, `ucs_of_rat`) works with sequences indexed by
`k ∈ ℕ` (`atTop`). The offset form indexes the radii by `(k, c) ∈ ℕ × [1,2]` along `goodFilter`
(radius `c 2^{-k}`), so the same two reductions are redone here for an arbitrary index filter `p`:

* `OffCauchyOn p a S`: `a i s` is Cauchy along `p`, uniformly in `s ∈ S`;
* `offCauchy_of_rat`: from the rational points of `[q,T]` to all of `[q,T]`, given continuity in
  `s` at each index;
* **`offCauchy_of_fam`**: from the countable family `swFam` to every test function (Weierstrass
  approximation + linearity + domination by the trapezoid), as `ucs_of_fam`.

Source: Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4 (p. 12, before (3.5)): reduction to
countably many test functions and a countable dense parameter set. The adaptation (polynomial ×
trapezoid family, general index filter) is own bookkeeping, as in `UnifSWDense`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace RegUnif

/-- `a i s` is Cauchy along the filter `p`, uniformly in `s ∈ S`. -/
def OffCauchyOn {ι α : Type*} (p : Filter ι) (a : ι → α → ℝ) (S : Set α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ ij in p ×ˢ p, ∀ s ∈ S, |a ij.1 s - a ij.2 s| < ε

section generic

variable {ι α : Type*} {p : Filter ι} {S : Set α}

theorem offCauchy_add {a b : ι → α → ℝ} (ha : OffCauchyOn p a S) (hb : OffCauchyOn p b S) :
    OffCauchyOn p (fun i s => a i s + b i s) S := by
  intro ε hε
  filter_upwards [ha (ε / 2) (by linarith), hb (ε / 2) (by linarith)] with ij h1 h2 s hs
  have e : a ij.1 s + b ij.1 s - (a ij.2 s + b ij.2 s) =
      (a ij.1 s - a ij.2 s) + (b ij.1 s - b ij.2 s) := by ring
  rw [e]
  exact (abs_add_le _ _).trans_lt (by linarith [h1 s hs, h2 s hs])

theorem offCauchy_smul {a : ι → α → ℝ} (c : ℝ) (ha : OffCauchyOn p a S) :
    OffCauchyOn p (fun i s => c * a i s) S := by
  intro ε hε
  filter_upwards [ha (ε / (|c| + 1)) (by positivity)] with ij h s hs
  rw [← mul_sub, abs_mul]
  calc |c| * |a ij.1 s - a ij.2 s| ≤ |c| * (ε / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left (h s hs).le (abs_nonneg c)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]

theorem offCauchy_zero : OffCauchyOn p (fun (_ : ι) (_ : α) => (0 : ℝ)) S :=
  fun ε hε => Eventually.of_forall fun _ _ _ => by simpa using hε

theorem offCauchy_sum (N : ℕ) (c : ℕ → ℝ) {a : ℕ → ι → α → ℝ}
    (ha : ∀ i < N, OffCauchyOn p (a i) S) :
    OffCauchyOn p (fun k s => ∑ i ∈ Finset.range N, c i * a i k s) S := by
  induction N with
  | zero => simpa using (offCauchy_zero (p := p) (S := S))
  | succ N ih =>
    simp_rw [Finset.sum_range_succ]
    exact offCauchy_add (ih fun i hi => ha i (by omega)) (offCauchy_smul (c N) (ha N (by omega)))

end generic

/-- A function continuous on `[q,T]` (`q` rational) and `≤ δ` at the rational points of `[q,T]`
is `≤ δ` on `[q,T]`. -/
theorem le_of_rat_dense_off {q : ℚ} {T δ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (q : ℝ) T))
    (h : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → g r ≤ δ) : ∀ s ∈ Icc (q : ℝ) T, g s ≤ δ := by
  intro s hs
  rcases hs.1.eq_or_lt with h' | h'
  · rw [← h']; exact h q ⟨le_rfl, h'.le.trans hs.2⟩
  · refine le_of_forall_pos_lt_add fun η hη => ?_
    obtain ⟨ρ, hρ, hρc⟩ := Metric.continuousWithinAt_iff.1 (hg s hs) η hη
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt h' (sub_lt_self s hρ))
    have hrm : (r : ℝ) ∈ Icc (q : ℝ) T := ⟨(le_max_left _ _).trans hr1.le, hr2.le.trans hs.2⟩
    have hd : dist (r : ℝ) s < ρ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (q : ℝ) (s - ρ)]
    have h1 := hρc hrm hd
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.1, h r hrm]

/-- **From rational times to all times**, given continuity in `s` at each index. -/
theorem offCauchy_of_rat {ι : Type*} {p : Filter ι} {q : ℚ} {T : ℝ} {a : ι → ℝ → ℝ}
    (hc : ∀ᶠ i in p, ContinuousOn (a i) (Icc (q : ℝ) T))
    (hr : OffCauchyOn p a (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ))) :
    OffCauchyOn p a (Icc (q : ℝ) T) := by
  intro ε hε
  filter_upwards [hr (ε / 2) (by linarith), hc.prod_mk hc] with ij h hcij s hs
  have := le_of_rat_dense_off (g := fun s => |a ij.1 s - a ij.2 s|)
    ((hcij.1.sub hcij.2).abs) (fun r hr => (h r ⟨hr, r, rfl⟩).le) s hs
  linarith

/-- **Deterministic core (offset form of `ucs_of_fam`)**: Cauchy along `p` for the countable
family, plus boundedness in `s` at each index, gives Cauchy along `p` for every test function. -/
theorem offCauchy_of_fam {ι : Type*} {p : Filter ι} [p.NeBot] {S : Set ℝ} {u v : ℝ}
    {F : ℝ → ℝ → ℝ} {A : ℝ → ι → Measure ℝ}
    (hΦ : ∀ s ∈ S, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc u v, Φ y = F s y)
    (hfin : ∀ᶠ k in p, ∀ s ∈ S, IsLocallyFiniteMeasure (A s k))
    (hbd : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo u v →
      ∀ᶠ k in p, ∃ C : ℝ, ∀ s ∈ S, |∫ x, awTest (F s) u v f x ∂A s k| ≤ C)
    (hfam : ∀ i : ℕ, ∀ a b c d : ℚ, u < a → a < b → b < c → c < d → (d : ℝ) < v →
      OffCauchyOn p (fun k s => ∫ x, awTest (F s) u v (swFam i a b c d) x ∂A s k) S)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo u v) :
    OffCauchyOn p (fun k s => ∫ x, awTest (F s) u v f x ∂A s k) S := by
  set I : (ℝ → ℝ) → ι → ℝ → ℝ := fun φ k s => ∫ x, awTest (F s) u v φ x ∂A s k with hI
  change OffCauchyOn p (I f) S
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · have hf0 : ∀ x, f x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport (by rw [he]; exact notMem_empty x)
    have : I f = fun _ _ => 0 := by
      funext k s
      simp only [hI]
      have : ∀ x, awTest (F s) u v f x = 0 := fun x => by
        unfold awTest; split_ifs <;> simp [hf0]
      simp [this]
    rw [this]
    exact offCauchy_zero
  obtain ⟨m, hm⟩ := hfc.isCompact.exists_isLeast hne
  obtain ⟨M, hM⟩ := hfc.isCompact.exists_isGreatest hne
  have hum : u < m := (hfs hm.1).1
  have hMv : M < v := (hfs hM.1).2
  obtain ⟨a, hua, ham⟩ := exists_rat_btwn hum
  obtain ⟨b, hab, hbm⟩ := exists_rat_btwn ham
  obtain ⟨d, hMd, hdv⟩ := exists_rat_btwn hMv
  obtain ⟨c, hMc, hcd⟩ := exists_rat_btwn hMd
  have hbc : (b : ℝ) < c := hbm.trans ((hm.2 hM.1).trans_lt hMc)
  have hfbc : tsupport f ⊆ Icc (b : ℝ) c := fun x hx => ⟨(hbm.trans_le (hm.2 hx)).le,
    ((hM.2 hx).trans_lt hMc).le⟩
  have had : Icc (a : ℝ) d ⊆ Ioo u v := fun x hx => ⟨hua.trans_le hx.1, hx.2.trans_lt hdv⟩
  set E : Set ι := {k | ∀ s ∈ S, IsLocallyFiniteMeasure (A s k)} with hE
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → tsupport φ ⊆ Icc (a : ℝ) d → ∀ s ∈ S,
      ∀ k ∈ E, Integrable (awTest (F s) u v φ) (A s k) := by
    intro φ hφ hφs s hs k hk
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    have := hk s hs
    exact integrable_awTest hΦs hφ (hasCompactSupport_of_tsupport_Icc hφs) (hφs.trans had)
  have hfamI : ∀ i : ℕ, OffCauchyOn p (I (swFam i a b c d)) S :=
    fun i => hfam i a b c d hua (by exact_mod_cast hab) (by exact_mod_cast hbc)
      (by exact_mod_cast hcd) hdv
  set g := swFam 0 a b c d with hg
  have hg_eq : ∀ x, g x = swTrap a b c d x := fun x => by simp [hg, swFam]
  have hgs : tsupport g ⊆ Icc (a : ℝ) d := tsupport_swFam_subset hab hcd
  -- a uniform bound on `I g k s` for `k` eventually along `p`
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.1 (hfamI 0 1 one_pos)
  obtain ⟨j0, hj0, C0, hC0⟩ := (hpb.and (hbd g (continuous_swFam 0 a b c d)
    (hasCompactSupport_of_tsupport_Icc hgs) (hgs.trans had))).exists
  set C := |C0| + 1 with hC
  have hC1 : 1 ≤ C := by linarith [abs_nonneg C0]
  have hbdd : ∀ᶠ k in p, ∀ s ∈ S, |I g k s| ≤ C + 1 := by
    filter_upwards [hpa] with k hk s hs
    have h1 := hpab hk hj0 s hs
    have h2 := hC0 s hs
    have : |I g k s| ≤ |I g k s - I g j0 s| + |I g j0 s| := by
      have := abs_add_le (I g k s - I g j0 s) (I g j0 s)
      simpa using this
    simp only at h1
    linarith [le_abs_self C0]
  intro ε hε
  set η := ε / (4 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨pp, hp⟩ := exists_polynomial_near_of_continuousOn a d f hf.continuousOn η hη0
  set Np := pp.natDegree + 1
  set h : ℝ → ℝ := fun x => ∑ i ∈ Finset.range Np, pp.coeff i * swFam i a b c d x with hh
  have hh_eq : ∀ x, h x = pp.eval x * g x := by
    intro x
    rw [hh, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, swFam]
    ring
  have hIh : ∀ k ∈ E, ∀ s ∈ S,
      I h k s = ∑ i ∈ Finset.range Np, pp.coeff i * I (swFam i a b c d) k s := by
    intro k hk s hs
    simp only [hI, hh]
    simp_rw [awTest_sum']
    rw [integral_finsetSum _ fun i _ => (hint _ (continuous_swFam i a b c d)
      (tsupport_swFam_subset hab hcd) s hs k hk).const_mul _]
    simp_rw [integral_const_mul]
  have hucsh : OffCauchyOn p (fun k s => ∑ i ∈ Finset.range Np,
      pp.coeff i * I (swFam i a b c d) k s) S :=
    offCauchy_sum Np pp.coeff fun i _ => hfamI i
  have hdom : ∀ x, |f x - h x| ≤ η * g x := by
    intro x
    rw [hh_eq, hg_eq]
    by_cases hx : x ∈ Icc (a : ℝ) d
    · have hfx : f x = f x * swTrap a b c d x := by
        by_cases hx' : x ∈ tsupport f
        · rw [swTrap_eq_one hab hcd (hfbc hx'), mul_one]
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul]
      rw [hfx, show f x * swTrap a b c d x - pp.eval x * swTrap a b c d x =
        swTrap a b c d x * (f x - pp.eval x) by ring, abs_mul,
        abs_of_nonneg (swTrap_nonneg _ _ _ _ _), mul_comm η]
      refine mul_le_mul_of_nonneg_left ?_ (swTrap_nonneg _ _ _ _ _)
      rw [abs_sub_comm]
      exact (hp x hx).le
    · have h0 : swTrap a b c d x = 0 :=
        swTrap_eq_zero hab hcd fun h' => hx (Ioo_subset_Icc_self h')
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx
        ((hfbc h').elim fun h1 h2 => ⟨hab.le.trans h1, h2.trans hcd.le⟩)
      simp [h0, hf0]
  have hcomp : ∀ᶠ k in p, ∀ s ∈ S, |I f k s - I h k s| ≤ η * (C + 1) := by
    filter_upwards [hbdd, hfin] with k hk hkE s hs
    have hsub : I f k s - I h k s = ∫ x, awTest (F s) u v (fun y => f y - h y) x ∂A s k := by
      simp only [hI]
      simp_rw [awTest_sub']
      rw [integral_sub (hint f hf (hfbc.trans (Icc_subset_Icc hab.le hcd.le)) s hs k hkE)
        (hint h (continuous_finsetSum _ fun i _ => continuous_const.mul
          (continuous_swFam i a b c d)) ?_ s hs k hkE)]
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      by_contra hx'
      apply hx
      rw [hh_eq, hg_eq, swTrap_eq_zero hab hcd fun h' => hx' (Ioo_subset_Icc_self h'), mul_zero]
    rw [hsub]
    have hgI : ∫ x, awTest (F s) u v (fun y => η * g y) x ∂A s k = η * I g k s := by
      simp only [hI]
      simp_rw [awTest_const_mul']
      exact integral_const_mul _ _
    calc |∫ x, awTest (F s) u v (fun y => f y - h y) x ∂A s k|
        ≤ ∫ x, awTest (F s) u v (fun y => η * g y) x ∂A s k := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le ((hint g (continuous_swFam 0 a b c d) hgs s hs k hkE).const_mul η
            |>.congr (Eventually.of_forall fun x => (awTest_const_mul' _ _ _ _ _ _).symm)) ?_
          exact Eventually.of_forall fun x => abs_awTest_le' _ _ _ hdom x
      _ = η * I g k s := hgI
      _ ≤ η * |I g k s| := mul_le_mul_of_nonneg_left (le_abs_self _) hη0.le
      _ ≤ η * (C + 1) := mul_le_mul_of_nonneg_left (hk s hs) hη0.le
  filter_upwards [hucsh (ε / 2) (by linarith), hcomp.prod_mk hcomp, hfin.prod_mk hfin]
    with ij e3 e12 hEE s hs
  have e1 := e12.1 s hs
  have e2 := e12.2 s hs
  have e3 := e3 s hs
  rw [← hIh ij.1 hEE.1 s hs, ← hIh ij.2 hEE.2 s hs] at e3
  have hηC : η * (C + 1) = ε / 4 := by
    rw [hη]; field_simp
  calc |I f ij.1 s - I f ij.2 s| =
        |(I f ij.1 s - I h ij.1 s) + (I h ij.1 s - I h ij.2 s) - (I f ij.2 s - I h ij.2 s)| := by
        ring_nf
    _ ≤ |I f ij.1 s - I h ij.1 s| + |I h ij.1 s - I h ij.2 s| + |I f ij.2 s - I h ij.2 s| := by
        have hadd := abs_add_le (I f ij.1 s - I h ij.1 s) (I h ij.1 s - I h ij.2 s)
        exact (abs_sub _ _).trans (by linarith)
    _ < ε := by linarith

end RegUnif
end QuantumZipper
