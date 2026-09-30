import QuantumZipper.Proofs.Zipper.UnifSWCont
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# UNIF-SW (3): AC-unif from a countable family of test functions at rational times

Task UNIF-SW (decision D26). `AnchorUnifCauchyStmt` (AC-unif) asks, for **every** continuous
test function `f` with compact support in the window `(u,v)`, that the transported integrals
`awInt f s k` be uniformly Cauchy in `s ∈ [q,T]` as `k → ∞`. Here it is reduced to

* countably many test functions: `x ↦ x^i · swTrap a b c d x` (`i : ℕ`, `swTrap` the rational
  trapezoid, `1` on `[b,c]`, `0` off `(a,d)`), and
* the rational times `s ∈ [q,T] ∩ ℚ` (so that the supremum over `s` is measurable),

given AC-cont (`anchorApproxContStmt_holds`). Statement: `AnchorUnifFamStmt`; reduction:
**`anchorUnifCauchyStmt_of_fam`**.

Source: Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost surely
commutes with all conformal maps simultaneously*, arXiv:1605.06171, proof of Thm 1.4 (p. 12, just
before (3.5)): the uniform convergence is reduced to countably many test sets (dyadic squares),
and suprema over the parameter set are taken over a countable dense subset. **Adaptation (own
argument):** we use the countable family `x^i · trapezoid` (Weierstrass approximation
`exists_polynomial_near_of_continuousOn` + linearity of `awInt` in `f` + domination
`|f − p·g| ≤ η g`) in place of dyadic squares, and continuity in `s` at each fixed scale
(AC-cont) in place of their continuity argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

/-! ## Trapezoids -/

/-- The trapezoid `0` off `(a,d)`, `1` on `[b,c]`, linear in between. -/
def swTrap (a b c d : ℝ) (x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - a) / (b - a)) ((d - x) / (d - c))))

theorem continuous_swTrap (a b c d : ℝ) : Continuous (swTrap a b c d) :=
  continuous_const.max (continuous_const.min (((continuous_id.sub continuous_const).div_const _).min
    ((continuous_const.sub continuous_id).div_const _)))

theorem swTrap_nonneg (a b c d x : ℝ) : 0 ≤ swTrap a b c d x := le_max_left _ _

theorem swTrap_eq_one {a b c d x : ℝ} (hab : a < b) (hcd : c < d) (hx : x ∈ Icc b c) :
    swTrap a b c d x = 1 := by
  have h1 : 1 ≤ (x - a) / (b - a) := by rw [le_div_iff₀ (by linarith)]; linarith [hx.1]
  have h2 : 1 ≤ (d - x) / (d - c) := by rw [le_div_iff₀ (by linarith)]; linarith [hx.2]
  unfold swTrap
  rw [min_eq_left (le_min h1 h2)]
  exact max_eq_right zero_le_one

theorem swTrap_eq_zero {a b c d x : ℝ} (hab : a < b) (hcd : c < d) (hx : x ∉ Ioo a d) :
    swTrap a b c d x = 0 := by
  unfold swTrap
  refine max_eq_left ?_
  rcases le_or_gt x a with h | h
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)))
  · have : d ≤ x := by
      by_contra h'
      exact hx ⟨h, lt_of_not_ge h'⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)))

theorem tsupport_swTrap_subset {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    tsupport (swTrap a b c d) ⊆ Icc a d :=
  closure_minimal (fun x hx => Ioo_subset_Icc_self (by
    by_contra h
    exact hx (swTrap_eq_zero hab hcd h))) isClosed_Icc

/-- The countable family of test functions: `x^i · swTrap a b c d x`. -/
def swFam (i : ℕ) (a b c d : ℝ) (x : ℝ) : ℝ := x ^ i * swTrap a b c d x

theorem continuous_swFam (i : ℕ) (a b c d : ℝ) : Continuous (swFam i a b c d) :=
  (continuous_pow i).mul (continuous_swTrap a b c d)

theorem tsupport_swFam_subset {i : ℕ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    tsupport (swFam i a b c d) ⊆ Icc a d :=
  (tsupport_mul_subset_right).trans (tsupport_swTrap_subset hab hcd)

theorem hasCompactSupport_of_tsupport_Icc {f : ℝ → ℝ} {a d : ℝ} (h : tsupport f ⊆ Icc a d) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) h

/-! ## Uniform Cauchy sequences: closure properties and rational times -/

theorem ucs_add {S : Set ℝ} {a b : ℕ → ℝ → ℝ} (ha : UniformCauchySeqOn a atTop S)
    (hb : UniformCauchySeqOn b atTop S) : UniformCauchySeqOn (fun k s => a k s + b k s) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff] at *
  intro ε hε
  obtain ⟨N1, h1⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N2, h2⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun m hm n hn s hs => ?_⟩
  have e1 := h1 m (le_of_max_le_left hm) n (le_of_max_le_left hn) s hs
  have e2 := h2 m (le_of_max_le_right hm) n (le_of_max_le_right hn) s hs
  rw [Real.dist_eq] at *
  calc |a m s + b m s - (a n s + b n s)| = |(a m s - a n s) + (b m s - b n s)| := by ring_nf
    _ ≤ |a m s - a n s| + |b m s - b n s| := abs_add_le _ _
    _ < ε := by linarith

theorem ucs_smul {S : Set ℝ} {a : ℕ → ℝ → ℝ} (c : ℝ) (ha : UniformCauchySeqOn a atTop S) :
    UniformCauchySeqOn (fun k s => c * a k s) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff] at *
  intro ε hε
  obtain ⟨N, h⟩ := ha (ε / (|c| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn s hs => ?_⟩
  have e := h m hm n hn s hs
  rw [Real.dist_eq] at *
  rw [← mul_sub, abs_mul]
  calc |c| * |a m s - a n s| ≤ |c| * (ε / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left e.le (abs_nonneg c)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]

theorem ucs_const {S : Set ℝ} : UniformCauchySeqOn (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff]
  exact fun ε hε => ⟨0, fun _ _ _ _ _ _ => by simpa using hε⟩

/-- Uniform Cauchy on the rational points of `[q,T]` plus continuity in `s` of each term gives
uniform Cauchy on `[q,T]`. -/
theorem ucs_of_rat {q : ℚ} {T : ℝ} {a : ℕ → ℝ → ℝ}
    (hc : ∀ k, ContinuousOn (a k) (Icc (q : ℝ) T))
    (hr : UniformCauchySeqOn a atTop (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ))) :
    UniformCauchySeqOn a atTop (Icc (q : ℝ) T) := by
  rw [Metric.uniformCauchySeqOn_iff] at *
  intro ε hε
  obtain ⟨N, hN⟩ := hr (ε / 2) (by linarith)
  refine ⟨N, fun m hm n hn s hs => ?_⟩
  have hle : dist (a m s) (a n s) ≤ ε / 2 := by
    have hcl : ContinuousOn (fun t => dist (a m t) (a n t)) (Icc (q : ℝ) T) :=
      continuous_dist.comp_continuousOn ((hc m).prodMk (hc n))
    have hval : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → dist (a m r) (a n r) ≤ ε / 2 :=
      fun r hr => (hN m hm n hn r ⟨hr, r, rfl⟩).le
    rcases hs.1.eq_or_lt with h | h
    · rw [← h]; exact hval q ⟨le_rfl, h.le.trans hs.2⟩
    · refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.1 (hcl s hs) δ hδ
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt h (sub_lt_self s hη))
      have hrm : (r : ℝ) ∈ Icc (q : ℝ) T := ⟨(le_max_left _ _).trans hr1.le, hr2.le.trans hs.2⟩
      have hd : dist (r : ℝ) s < η := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [le_max_right (q : ℝ) (s - η)]
      have h1 := hηc hrm hd
      have h2 := hval r hrm
      rw [Real.dist_eq, abs_lt] at h1
      linarith [h1.1]
  linarith

/-! ## Linearity and domination of `awTest` -/

theorem awTest_sub' (F : ℝ → ℝ) (u v : ℝ) (φ ψ : ℝ → ℝ) (x : ℝ) :
    awTest F u v (fun y => φ y - ψ y) x = awTest F u v φ x - awTest F u v ψ x := by
  unfold awTest; split_ifs <;> simp

theorem awTest_const_mul' (F : ℝ → ℝ) (u v : ℝ) (c : ℝ) (φ : ℝ → ℝ) (x : ℝ) :
    awTest F u v (fun y => c * φ y) x = c * awTest F u v φ x := by
  unfold awTest; split_ifs <;> simp

theorem awTest_sum' (F : ℝ → ℝ) (u v : ℝ) (N : ℕ) (c : ℕ → ℝ) (φ : ℕ → ℝ → ℝ) (x : ℝ) :
    awTest F u v (fun y => ∑ i ∈ Finset.range N, c i * φ i y) x =
      ∑ i ∈ Finset.range N, c i * awTest F u v (φ i) x := by
  unfold awTest; split_ifs <;> simp

theorem abs_awTest_le' (F : ℝ → ℝ) (u v : ℝ) {φ ψ : ℝ → ℝ} (h : ∀ y, |φ y| ≤ ψ y) (x : ℝ) :
    |awTest F u v φ x| ≤ awTest F u v ψ x := by
  unfold awTest; split_ifs
  · exact h _
  · simp

theorem integrable_awTest {F : ℝ → ℝ} {u v : ℝ} {Φ : ℝ ≃o ℝ} (hΦ : ∀ y ∈ Icc u v, Φ y = F y)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo u v)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] : Integrable (awTest F u v f) μ := by
  rw [awTest_eq hΦ hfs]
  exact (hf.comp Φ.symm.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_comp_orderIso hfc Φ.symm)

theorem ucs_sum {S : Set ℝ} (N : ℕ) (c : ℕ → ℝ) {a : ℕ → ℕ → ℝ → ℝ}
    (ha : ∀ i < N, UniformCauchySeqOn (a i) atTop S) :
    UniformCauchySeqOn (fun k s => ∑ i ∈ Finset.range N, c i * a i k s) atTop S := by
  induction N with
  | zero => simpa using (ucs_const (S := S))
  | succ N ih =>
    simp_rw [Finset.sum_range_succ]
    exact ucs_add (ih fun i hi => ha i (by omega)) (ucs_smul (c N) (ha N (by omega)))

/-! ## The deterministic reduction -/

/-- **Deterministic core**: uniform Cauchy for the countable family at rational times, plus
continuity in `s` at each scale, gives uniform Cauchy for every test function. -/
theorem ucs_of_fam {q : ℚ} {T u v : ℝ} {F : ℝ → ℝ → ℝ} {A : ℝ → ℕ → Measure ℝ}
    (hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc u v, Φ y = F s y)
    (hfin : ∀ s ∈ Icc (q : ℝ) T, ∀ k, IsLocallyFiniteMeasure (A s k))
    (hcont : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo u v →
      ∀ k, ContinuousOn (fun s => ∫ x, awTest (F s) u v f x ∂A s k) (Icc (q : ℝ) T))
    (hfam : ∀ i : ℕ, ∀ a b c d : ℚ, u < a → a < b → b < c → c < d → (d : ℝ) < v →
      UniformCauchySeqOn (fun k s => ∫ x, awTest (F s) u v (swFam i a b c d) x ∂A s k) atTop
        (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo u v) :
    UniformCauchySeqOn (fun k s => ∫ x, awTest (F s) u v f x ∂A s k) atTop (Icc (q : ℝ) T) := by
  set I : (ℝ → ℝ) → ℕ → ℝ → ℝ := fun φ k s => ∫ x, awTest (F s) u v φ x ∂A s k with hI
  change UniformCauchySeqOn (I f) atTop (Icc (q : ℝ) T)
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
    exact ucs_const
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
  -- integrability of every relevant test function
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → tsupport φ ⊆ Icc (a : ℝ) d → ∀ s ∈ Icc (q : ℝ) T,
      ∀ k, Integrable (awTest (F s) u v φ) (A s k) := by
    intro φ hφ hφs s hs k
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    have := hfin s hs k
    exact integrable_awTest hΦs hφ (hasCompactSupport_of_tsupport_Icc hφs) (hφs.trans had)
  -- the family at all times
  have hfamI : ∀ i : ℕ, UniformCauchySeqOn (I (swFam i a b c d)) atTop (Icc (q : ℝ) T) :=
    fun i => ucs_of_rat (hcont _ (continuous_swFam i a b c d)
      (hasCompactSupport_of_tsupport_Icc (tsupport_swFam_subset hab (hcd)))
      ((tsupport_swFam_subset hab hcd).trans had)) (hfam i a b c d hua (by exact_mod_cast hab) (by exact_mod_cast hbc)
      (by exact_mod_cast hcd) hdv)
  set g := swFam 0 a b c d with hg
  have hg_eq : ∀ x, g x = swTrap a b c d x := fun x => by simp [hg, swFam]
  have hgs : tsupport g ⊆ Icc (a : ℝ) d := tsupport_swFam_subset hab hcd
  -- a uniform bound on `I g k s` for large `k`
  obtain ⟨N0, hN0⟩ := Metric.uniformCauchySeqOn_iff.1 (hfamI 0) 1 one_pos
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont g (continuous_swFam 0 a b c d) (hasCompactSupport_of_tsupport_Icc hgs) (hgs.trans had) N0)
  set C := |C0| + 1 with hC
  have hC1 : 1 ≤ C := by linarith [abs_nonneg C0]
  have hbd : ∀ k ≥ N0, ∀ s ∈ Icc (q : ℝ) T, |I g k s| ≤ C + 1 := by
    intro k hk s hs
    have h1 := hN0 k hk N0 le_rfl s hs
    have h2 := hC0 s hs
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2
    have : |I g k s| ≤ |I g k s - I g N0 s| + |I g N0 s| := by
      have := abs_add_le (I g k s - I g N0 s) (I g N0 s)
      simpa using this
    linarith [le_abs_self C0]
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set η := ε / (4 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a d f hf.continuousOn η hη0
  set Np := p.natDegree + 1
  set h : ℝ → ℝ := fun x => ∑ i ∈ Finset.range Np, p.coeff i * swFam i a b c d x with hh
  have hh_eq : ∀ x, h x = p.eval x * g x := by
    intro x
    rw [hh, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, swFam]
    ring
  -- `I h` is a finite combination of the family
  have hIh : ∀ k, ∀ s ∈ Icc (q : ℝ) T,
      I h k s = ∑ i ∈ Finset.range Np, p.coeff i * I (swFam i a b c d) k s := by
    intro k s hs
    simp only [hI, hh]
    simp_rw [awTest_sum']
    rw [integral_finsetSum _ fun i _ => (hint _ (continuous_swFam i a b c d)
      (tsupport_swFam_subset hab hcd) s hs k).const_mul _]
    simp_rw [integral_const_mul]
  have hucsh : UniformCauchySeqOn (fun k s => ∑ i ∈ Finset.range Np,
      p.coeff i * I (swFam i a b c d) k s) atTop (Icc (q : ℝ) T) :=
    ucs_sum Np p.coeff fun i _ => hfamI i
  obtain ⟨N1, hN1⟩ := Metric.uniformCauchySeqOn_iff.1 hucsh (ε / 2) (by linarith)
  -- domination `|f − h| ≤ η g`
  have hdom : ∀ x, |f x - h x| ≤ η * g x := by
    intro x
    rw [hh_eq, hg_eq]
    by_cases hx : x ∈ Icc (a : ℝ) d
    · have hfx : f x = f x * swTrap a b c d x := by
        by_cases hx' : x ∈ tsupport f
        · rw [swTrap_eq_one hab hcd (hfbc hx'), mul_one]
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul]
      rw [hfx, show f x * swTrap a b c d x - p.eval x * swTrap a b c d x =
        swTrap a b c d x * (f x - p.eval x) by ring, abs_mul,
        abs_of_nonneg (swTrap_nonneg _ _ _ _ _), mul_comm η]
      refine mul_le_mul_of_nonneg_left ?_ (swTrap_nonneg _ _ _ _ _)
      rw [abs_sub_comm]
      exact (hp x hx).le
    · have h0 : swTrap a b c d x = 0 := swTrap_eq_zero hab hcd fun h' => hx (Ioo_subset_Icc_self h')
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx
        ((hfbc h').elim fun h1 h2 => ⟨hab.le.trans h1, h2.trans hcd.le⟩)
      simp [h0, hf0]
  have hcomp : ∀ k ≥ N0, ∀ s ∈ Icc (q : ℝ) T, |I f k s - I h k s| ≤ η * (C + 1) := by
    intro k hk s hs
    have hsub : I f k s - I h k s = ∫ x, awTest (F s) u v (fun y => f y - h y) x ∂A s k := by
      simp only [hI]
      simp_rw [awTest_sub']
      rw [integral_sub (hint f hf (hfbc.trans (Icc_subset_Icc hab.le hcd.le)) s hs k)
        (hint h (continuous_finsetSum _ fun i _ => continuous_const.mul
          (continuous_swFam i a b c d)) ?_ s hs k)]
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
          refine norm_integral_le_of_norm_le ((hint g (continuous_swFam 0 a b c d) hgs s hs k).const_mul η
            |>.congr (Eventually.of_forall fun x => (awTest_const_mul' _ _ _ _ _ _).symm)) ?_
          exact Eventually.of_forall fun x => abs_awTest_le' _ _ _ hdom x
      _ = η * I g k s := hgI
      _ ≤ η * |I g k s| := mul_le_mul_of_nonneg_left (le_abs_self _) hη0.le
      _ ≤ η * (C + 1) := mul_le_mul_of_nonneg_left (hbd k hk s hs) hη0.le
  refine ⟨max N0 N1, fun m hm n hn s hs => ?_⟩
  have e1 := hcomp m (le_of_max_le_left hm) s hs
  have e2 := hcomp n (le_of_max_le_left hn) s hs
  have e3 := hN1 m (le_of_max_le_right hm) n (le_of_max_le_right hn) s hs
  rw [Real.dist_eq, ← hIh m s hs, ← hIh n s hs] at e3
  rw [Real.dist_eq]
  have hηC : η * (C + 1) = ε / 4 := by
    rw [hη]; field_simp
  calc |I f m s - I f n s| = |(I f m s - I h m s) + (I h m s - I h n s) - (I f n s - I h n s)| := by
        ring_nf
    _ ≤ |I f m s - I h m s| + |I h m s - I h n s| + |I f n s - I h n s| := by
        exact (abs_sub _ _).trans (by linarith [abs_add_le (I f m s - I h m s) (I h m s - I h n s)])
    _ < ε := by linarith

end RegUnif
end QuantumZipper
