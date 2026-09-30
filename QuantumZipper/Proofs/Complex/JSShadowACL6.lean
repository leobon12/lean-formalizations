import QuantumZipper.Proofs.Complex.JSShadowACL5
import QuantumZipper.Proofs.Complex.JSAreaChain
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# EXT-JS node B1, step 4: the chain estimate on one line

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 "(C0: SH ⇒ removable.)", step 4.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, pp. 270–272,
estimate (10): the segment `[x_j, y_j]` of the line is cut into intervals that either miss `K`
(where `f(u_{i+1}) - f(u_i) = ∫ ∂f`) or have both ends in one shadow (where the difference is
bounded by the charged cube weights).

Here, on the line at height `y` and a segment `[a,b]`, the one-dimensional chain lemma A5
(`chain1D`, `JSAreaChain.lean`) is applied to `E t = e(t + iy)`, `γ t = 1_{Kᶜ} e'(t + iy)`,
`S = {t ∈ [a,b] | t + iy ∈ K}`, and the closed sets `C_{i,j} = {t | t + iy ∈ F_i(I_{n,j})}`
(images of the bases of the level-`n` tents) which meet `S`. The oscillation of `E` on `C_{i,j}` is
at most `3 · descShadow` (`edist_le_three_descShadow`), and these add up over `j` to
`3 Φ_n^{(i)}(y)`; the convex hulls of the `C_{i,j} ∩ [a,b]` lie in the `δ`-neighbourhood of `K` as
soon as every level-`n` tent image has diameter `≤ δ`.

Main result: `norm_line_sub_le`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

/-- The distance between two points of one horizontal line. -/
lemma dist_line (s t y : ℝ) : dist ((s : ℂ) + y * I) ((t : ℂ) + y * I) = |s - t| := by
  rw [dist_add_right, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Chain estimate on one line (blueprint §2 step 4).** If every level-`n` tent image has
diameter `≤ δ` and the level-`n` line shadow functions are finite at `y`, then
`‖e(b+iy) - e(a+iy) - ∫_a^b γ‖ ≤ 3 Σ_i Φ_n^{(i)}(y) + ∫_{(a,b] ∩ {t + iy ∈ N_δ(K)}} ‖γ‖`. -/
theorem norm_line_sub_le {K : Set ℂ} (hK : IsCompact K) {ι : Type*} [Fintype ι] {R : ℝ}
    {F : ι → ℂ → ℂ} (hF : ∀ i, IsChart K R (F i))
    (hcov : K ⊆ ⋃ i, F i '' ((↑) '' Set.Icc (-R) R)) (e : ℂ ≃ₜ ℂ)
    (he : DifferentiableOn ℂ e Kᶜ) {y a b : ℝ} (hab : a ≤ b)
    (hγ : IntegrableOn (fun t : ℝ => Kᶜ.indicator (deriv e) ((t : ℂ) + y * I)) (Icc a b))
    {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiam : ∀ i, ∀ j < 2 ^ n, ediam (F i '' tent R n j) ≤ ENNReal.ofReal δ)
    (hfin : ∀ i, lineShadow R (e ∘ F i) (F i) n y ≠ ⊤) :
    ‖e (b + y * I) - e (a + y * I) - ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * I)‖ ≤
      ∑ i, 3 * (lineShadow R (e ∘ F i) (F i) n y).toReal +
        ∫ t in Ioc a b ∩ {t : ℝ | (t : ℂ) + y * I ∈ cthickening δ K},
          ‖Kᶜ.indicator (deriv e) ((t : ℂ) + y * I)‖ := by
  classical
  set γ : ℝ → ℂ := fun t => Kᶜ.indicator (deriv e) ((t : ℂ) + y * I) with hγdef
  set E : ℝ → ℂ := fun t => e ((t : ℂ) + y * I) with hEdef
  set D : ι → ℕ → ℝ≥0∞ := fun i j => descShadow R (e ∘ F i) (F i) n j y with hD
  have hDle : ∀ i, ∀ j < 2 ^ n, D i j ≤ lineShadow R (e ∘ F i) (F i) n y := fun i j hj => by
    rw [← sum_descShadow_eq]
    exact Finset.single_le_sum (f := fun j => D i j) (fun _ _ => zero_le)
      (Finset.mem_range.2 hj)
  have hDfin : ∀ i, ∀ j < 2 ^ n, D i j ≠ ⊤ := fun i j hj =>
    ne_top_of_le_ne_top (hfin i) (hDle i j hj)
  have hline : Continuous fun t : ℝ => (t : ℂ) + y * I := by fun_prop
  set C : ι × ℕ → Set ℝ := fun p => {t | (t : ℂ) + y * I ∈ F p.1 '' ((↑) '' dyI R n p.2)}
    with hCdef
  set S : Set ℝ := Icc a b ∩ {t | (t : ℂ) + y * I ∈ K} with hSdef
  set s : Finset (ι × ℕ) :=
    (Finset.univ ×ˢ Finset.range (2 ^ n)).filter fun p => (C p ∩ S).Nonempty with hsdef
  set ω : ι × ℕ → ℝ := fun p => 3 * (D p.1 p.2).toReal with hω
  have hmem : ∀ p ∈ s, p.2 < 2 ^ n ∧ (C p ∩ S).Nonempty := fun p hp => by
    rw [hsdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact ⟨hp.1.2, hp.2⟩
  -- points of `C p`
  have hCmem : ∀ p : ι × ℕ, ∀ t ∈ C p, ∃ x ∈ dyI R n p.2, F p.1 x = (t : ℂ) + y * I := by
    rintro p t ⟨_, ⟨x, hx, rfl⟩, hxt⟩
    exact ⟨x, hx, hxt⟩
  have hC : ∀ p ∈ s, IsClosed (C p) := by
    intro p hp
    have hR := (hF p.1).pos
    have hsub : ((↑) '' dyI R n p.2 : Set ℂ) ⊆ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      rintro _ ⟨x, hx, rfl⟩
      have := mem_chartBox_of_dyI hR (hmem p hp).1 hx le_rfl (by linarith : (0 : ℝ) ≤ 2 * R)
      rwa [show (x : ℂ) + ((0 : ℝ) : ℂ) * I = x by simp] at this
    have hcpt : IsCompact (F p.1 '' ((↑) '' dyI R n p.2)) :=
      ((isCompact_Icc.image continuous_ofReal).image_of_continuousOn ((hF p.1).cont.mono hsub))
    exact hcpt.isClosed.preimage hline
  have hSc : IsClosed S := isClosed_Icc.inter (hK.isClosed.preimage hline)
  have hloc : ∀ u v, a ≤ u → u ≤ v → v ≤ b → Ioo u v ∩ S = ∅ →
      E v - E u = ∫ t in u..v, γ t := by
    intro u v hu huv hv hempty
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
      ((e.continuous.comp hline).continuousOn) (fun x hx => ?_)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).2
        (hγ.mono_set (Icc_subset_Icc hu hv)))).symm
    have hxK : (x : ℂ) + y * I ∈ Kᶜ := fun hxK =>
      (eq_empty_iff_forall_notMem.1 hempty) x
        ⟨hx, ⟨hu.trans hx.1.le, hx.2.le.trans hv⟩, hxK⟩
    have hdiff := he.differentiableAt (hK.isClosed.isOpen_compl.mem_nhds hxK)
    have h1 : HasDerivAt (fun w : ℂ => e (w + y * I)) (deriv e ((x : ℂ) + y * I)) (x : ℂ) := by
      have := hdiff.hasDerivAt.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (y * I))
      rw [mul_one] at this
      exact this
    have h2 := h1.comp_ofReal
    rw [hγdef]
    simp only [indicator_of_mem hxK]
    exact h2
  have hcovS : S ⊆ ⋃ p ∈ s, C p := by
    intro t ht
    obtain ⟨_, ⟨i, rfl⟩, hti⟩ := hcov ht.2
    obtain ⟨_, ⟨x, hx, rfl⟩, hxt⟩ := hti
    obtain ⟨j, hj, hxj⟩ := exists_dyI_of_mem_Icc (hF i).pos.le hx n
    have htC : t ∈ C (i, j) := ⟨_, ⟨x, hxj, rfl⟩, hxt⟩
    refine mem_iUnion₂.2 ⟨(i, j), ?_, htC⟩
    rw [hsdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨Finset.mem_univ _, hj⟩, t, htC, ht⟩
  have hωC : ∀ p ∈ s, ∀ q ∈ C p ∩ Icc a b, ∀ r ∈ C p ∩ Icc a b, ‖E q - E r‖ ≤ ω p := by
    intro p hp q hq r hr
    have hR := (hF p.1).pos
    obtain ⟨x, hx, hxq⟩ := hCmem p q hq.1
    obtain ⟨x', hx', hxr⟩ := hCmem p r hr.1
    have hyx : (F p.1 x).im = y := by rw [hxq]; simp
    have hyx' : (F p.1 x').im = y := by rw [hxr]; simp
    have hed := edist_le_three_descShadow (g := e ∘ F p.1) (F := F p.1) hR
      (e.continuous.comp_continuousOn (hF p.1).cont) (hmem p hp).1 hx hx' hyx hyx'
    simp only [Function.comp_apply, hxq, hxr] at hed
    rw [← dist_eq_norm, dist_edist, hω]
    have hfin3 : 3 * D p.1 p.2 ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (hDfin _ _ (hmem p hp).1)
    calc (edist (E q) (E r)).toReal ≤ (3 * D p.1 p.2).toReal := ENNReal.toReal_mono hfin3 hed
      _ = 3 * (D p.1 p.2).toReal := by rw [ENNReal.toReal_mul]; norm_num
  have hchain := chain1D s C hC ω (fun p _ => by positivity) hab hγ hSc inter_subset_left hloc
    hcovS hωC
  -- the oscillation terms
  have hsum : ∑ p ∈ s, ω p ≤ ∑ i, 3 * (lineShadow R (e ∘ F i) (F i) n y).toReal := by
    calc ∑ p ∈ s, ω p ≤ ∑ p ∈ Finset.univ ×ˢ Finset.range (2 ^ n), ω p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun p _ _ => by positivity
      _ = ∑ i, ∑ j ∈ Finset.range (2 ^ n), 3 * (D i j).toReal := Finset.sum_product _ _ _
      _ = ∑ i, 3 * (lineShadow R (e ∘ F i) (F i) n y).toReal := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, ← ENNReal.toReal_sum fun j hj =>
            hDfin i j (Finset.mem_range.1 hj), hD, sum_descShadow_eq]
  -- the hulls lie in the `δ`-neighbourhood of `K`
  have hhull : Ioc a b ∩ ⋃ p ∈ s, convexHull ℝ (C p ∩ Icc a b) ⊆
      Ioc a b ∩ {t : ℝ | (t : ℂ) + y * I ∈ cthickening δ K} := by
    rintro t ⟨hta, ht⟩
    refine ⟨hta, ?_⟩
    obtain ⟨p, hp, htp⟩ := mem_iUnion₂.1 ht
    obtain ⟨t₀, ht₀C, ht₀S⟩ := (hmem p hp).2
    obtain ⟨x₀, hx₀, hx₀t⟩ := hCmem p t₀ ht₀C
    have hsub : C p ∩ Icc a b ⊆ Icc (t₀ - δ) (t₀ + δ) := by
      rintro r ⟨hrC, -⟩
      obtain ⟨x, hx, hxr⟩ := hCmem p r hrC
      have hd : edist (F p.1 x) (F p.1 x₀) ≤ ENNReal.ofReal δ :=
        (edist_le_ediam_of_mem (mem_image_of_mem _ (ofReal_mem_tent (hF p.1).pos.le hx))
          (mem_image_of_mem _ (ofReal_mem_tent (hF p.1).pos.le hx₀))).trans
          (hdiam p.1 p.2 (hmem p hp).1)
      rw [edist_le_ofReal hδ, hxr, hx₀t, dist_line] at hd
      exact ⟨by linarith [(abs_le.1 hd).1], by linarith [(abs_le.1 hd).2]⟩
    have ht' := convexHull_min hsub (convex_Icc _ _) htp
    refine mem_cthickening_of_dist_le _ _ δ K ht₀S.2 ?_
    rw [dist_line, abs_le]
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hint : IntegrableOn (fun t => ‖γ t‖)
      (Ioc a b ∩ {t : ℝ | (t : ℂ) + y * I ∈ cthickening δ K}) :=
    (show IntegrableOn (fun t => ‖γ t‖) (Icc a b) volume from hγ.norm).mono_set
      (inter_subset_left.trans Ioc_subset_Icc_self)
  have hmono := setIntegral_mono_set hint
    (Eventually.of_forall fun _ => norm_nonneg _) hhull.eventuallyLE
  calc _ ≤ _ := hchain
    _ ≤ _ := add_le_add hsum hmono

end QuantumZipper.JS
