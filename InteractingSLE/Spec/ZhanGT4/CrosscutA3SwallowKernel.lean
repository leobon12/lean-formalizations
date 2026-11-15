/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA2
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Strip.Horizontal
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import QuantumZipper.Proofs.Complex.KoebeDistortion
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.Complex.KernelChordK1

/-!
# The hull at a time `T` is the filled closure of the earlier hulls

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L679–L682, ruling R38): "The outer boundary of the closure of
preterminal hulls equals the active-domain boundary at `T_x`: by the kernel theorem, any new open component at the
swallowing time is precisely a bounded complementary component of that closure. Filling such components leaves its
outer boundary unchanged."

For a continuous driver `W` with `W 0 = 0` and `T > 0`, let `S = closure (⋃_{t < T} K_t)`. Then
`ℍ \ K_T = unbddPart S` (the part of `ℍ \ S` reachable from infinity), so `∂(ℍ \ K_T) ∩ ℍ = outerBoundary S`.

## Proof

`ℍ \ K_T` is open, preconnected, unbounded and disjoint from `S`, so it lies in `unbddPart S`. Conversely, a
preconnected unbounded `U ⊆ ℍ \ S` that met `K_T` would contain a point `p ∈ ∂(ℍ \ K_T)`; a disc `B(p, r)` misses every
`K_t`, `t < T`, and contains an alive point `q`. On `B(p, r)` the maps `f_t = g_t − W_t` (`t < T`) are univalent with
values in `ℍ`; Koebe's covering and growth estimates give `|f_t(q) − f_t(p)| ≤ C |f_t'(p)| r ≤ C' |f_t(p)|`, so the flow
of `p` stays at distance `≥ |f_t(q)|/(1 + C')` from `0`, and `p` is alive at `T` (`kernel_key`).

## Main results

* `not_mem_fwdHull_of_ball_disjoint` (`kernel_key`);
* **`compl_fwdHull_eq_unbddPart`** and **`frontier_compl_fwdHull_eq_outerBoundary`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A34

open QuantumZipper

variable {W : ℝ → ℝ}

/-- The union of the hulls strictly before `T`. -/
def hullBefore (W : ℝ → ℝ) (T : ℝ) : Set ℂ := ⋃ t ∈ Ico (0 : ℝ) T, fwdHull W t

/-- **Koebe comparison**: on a disc `B(p, r) ⊆ ℍ \ K_t`, a point `q` with `|q − p| < r/2` has
`‖f_t(q)‖ ≤ (1 + G/c) ‖f_t(p)‖`, with Koebe's growth and covering constants `G`, `c`. -/
theorem norm_fwdMap_le_of_ball (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {p q : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball p r ⊆ H \ fwdHull W t) (hq : dist q p < r / 2) :
    ‖fwdMap W t q‖ ≤ (1 + CA.Koebe.koebeGrowthConst / CA.Koebe.koebeCovConst) * ‖fwdMap W t p‖ := by
  set f := fwdMap W t with hf
  have hd : DifferentiableOn ℂ f (ball p r) := (FwdHolo.differentiableOn_fwdMap hW ht).mono hball
  have hinj : InjOn f (ball p r) := (FwdHolo.injOn_fwdMap hW ht).mono hball
  have hmaps : MapsTo f (ball p r) H := (FwdHolo.mapsTo_fwdMap hW ht).mono_left hball
  have hc := CA.Koebe.koebeCovConst_pos
  have hG := CA.Koebe.koebeGrowthConst_pos
  -- covering: `c r ‖f'(p)‖ ≤ Im f(p) ≤ ‖f(p)‖`
  have hcov := CA.Koebe.koebeCovConst_mul_le_infDist hr hd hinj
  have hre : ((f p).re : ℂ) ∈ (f '' ball p r)ᶜ := by
    rintro ⟨z, hz, hfz⟩
    have := hmaps hz
    rw [hfz] at this
    exact (lt_irrefl 0) (by simp [H] at this)
  have hinf : infDist (f p) (f '' ball p r)ᶜ ≤ ‖f p‖ := by
    refine (infDist_le_dist_of_mem hre).trans ?_
    rw [dist_eq_norm]
    have : f p - ((f p).re : ℂ) = ((f p).im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  have h1 : CA.Koebe.koebeCovConst * r * ‖deriv f p‖ ≤ ‖f p‖ := hcov.trans hinf
  -- growth: `‖f q − f p‖ ≤ G r ‖f'(p)‖`
  have hgr := CA.Koebe.norm_sub_le_growth hd hinj hr (w := q) (by linarith)
  have h2 : CA.Koebe.koebeGrowthConst * r * ‖deriv f p‖ ≤
      CA.Koebe.koebeGrowthConst / CA.Koebe.koebeCovConst * ‖f p‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  calc ‖f q‖ ≤ ‖f p‖ + ‖f q - f p‖ := by
        calc ‖f q‖ = ‖f p + (f q - f p)‖ := by ring_nf
          _ ≤ ‖f p‖ + ‖f q - f p‖ := norm_add_le _ _
    _ ≤ ‖f p‖ + CA.Koebe.koebeGrowthConst / CA.Koebe.koebeCovConst * ‖f p‖ := by linarith
    _ = (1 + CA.Koebe.koebeGrowthConst / CA.Koebe.koebeCovConst) * ‖f p‖ := by ring

/-- **The key step**: if a disc `B(p, r) ⊆ ℍ` misses every hull `K_t`, `t < T`, and contains a point `q` within `r/2` of
`p` that is alive at `T`, then `p` is alive at `T`. -/
theorem not_mem_fwdHull_of_ball_disjoint (hW : Continuous W) {T : ℝ} (hT : 0 < T) {p q : ℂ} {r : ℝ}
    (hr : 0 < r) (hpH : p ∈ H) (hball : ∀ t ∈ Ico (0 : ℝ) T, ball p r ⊆ H \ fwdHull W t)
    (hq : dist q p < r / 2) (hqT : q ∈ H \ fwdHull W T) : p ∉ fwdHull W T := by
  set C := 1 + CA.Koebe.koebeGrowthConst / CA.Koebe.koebeCovConst with hC
  have hC0 : 0 < C := by
    have := CA.Koebe.koebeGrowthConst_pos; have := CA.Koebe.koebeCovConst_pos; positivity
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_not_mem_fwdHull hT.le hqT.1 hqT.2
  obtain ⟨δ, hδ, hδq⟩ := exists_two_mul_le_norm_of_isForwardSol hT.le huq
  -- the flow of `p` stays at distance `2δ/C` from `0` before `T`
  have hlowp : ∀ t ∈ Ico (0 : ℝ) T, 2 * (δ / C) ≤ ‖fwdMap W t p‖ := by
    intro t ht
    have h1 := norm_fwdMap_le_of_ball hW ht.1 hr (hball t ht) hq
    have h2 : fwdMap W t q = uq t := fwdMap_eq_of_isForwardSol hW huq ⟨ht.1, ht.2.le⟩
    have h3 := hδq t ⟨ht.1, ht.2.le⟩
    rw [h2] at h1
    rw [mul_div_assoc', div_le_iff₀ hC0]
    linarith
  -- a solution of `p` on `[0, T]` keeps the bound at `T`
  have hlowsol : ∀ v : ℝ → ℂ, IsForwardSol W p T v → ∀ r ∈ Icc (0 : ℝ) T, 2 * (δ / C) ≤ ‖v r‖ := by
    intro v hv
    have hsub : Ico (0 : ℝ) T ⊆ {r | 2 * (δ / C) ≤ ‖v r‖} := fun r hr => by
      have := hlowp r hr
      rwa [fwdMap_eq_of_isForwardSol hW hv ⟨hr.1, hr.2.le⟩] at this
    have hcl : IsClosed (Icc (0 : ℝ) T ∩ {r | 2 * (δ / C) ≤ ‖v r‖}) :=
      hv.1.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    intro r hr
    have hmem : r ∈ closure (Ico (0 : ℝ) T) := by rw [closure_Ico hT.ne]; exact hr
    have hsub' : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) T ∩ {r | 2 * (δ / C) ≤ ‖v r‖} :=
      fun x hx => ⟨Ico_subset_Icc_self hx, hsub hx⟩
    exact (closure_minimal hsub' hcl hmem).2
  obtain ⟨vp, hvp⟩ := Strip.exists_isForwardSol_of_forall_le_norm hT.le hW.continuousOn ⟨hT.le, le_rfl⟩
    hpH (by positivity : 0 < 2 * (δ / C)) fun t ht ⟨v, hv⟩ => by
      rcases ht.2.lt_or_eq with hlt | heq
      · exact hlowp t ⟨ht.1, hlt⟩
      · subst heq
        rw [fwdMap_eq_of_isForwardSol hW hv ⟨ht.1, le_rfl⟩]
        exact hlowsol v hv t ht
  refine not_mem_fwdHull_of_isForwardSol hW hvp (by positivity : 0 < δ / C) (hlowsol vp hvp) hpH ?_
  rw [sub_self, norm_zero, zero_mul]
  positivity

/-- **The alive set at `T` is the part of the complement of the earlier hulls' closure reachable from `∞`.** -/
theorem compl_fwdHull_eq_unbddPart (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) :
    H \ fwdHull W T = unbddPart (closure (hullBefore W T)) := by
  set A := H \ fwdHull W T with hA
  have hAo : IsOpen A := FwdHolo.isOpen_compl_fwdHull hW hT.le
  have hAc : IsPreconnected A := RS.isPreconnected_compl_fwdHull hW hW0 hT.le
  have hKb : Bornology.IsBounded (fwdHull W T) := isBounded_fwdHull hW T
  have hdisj : Disjoint A (closure (hullBefore W T)) := by
    refine Disjoint.closure_right ?_ hAo
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    simp only [hullBefore, mem_iUnion] at hz'
    obtain ⟨t, ht, hzt⟩ := hz'
    exact hz.2 ((fwdHull_mono (W := W)).1 ht.2.le hzt)
  -- `ℍ` minus a bounded set is unbounded and meets every unbounded subset of `ℍ`
  obtain ⟨R, hR⟩ := hKb.subset_closedBall 0
  have hfar : ∀ z ∈ H, R < ‖z‖ → z ∈ A := fun z hz hzR => ⟨hz, fun hK => by
    have := hR hK; rw [mem_closedBall, dist_zero_right] at this; linarith⟩
  apply Subset.antisymm
  · refine subset_sUnion_of_mem ⟨hAc, fun z hz => ⟨hz.1, Set.disjoint_left.1 hdisj hz⟩, ?_⟩
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    set y : ℝ := max (max R M) 0 + 1 with hy
    have hy0 : 0 < y := by have := le_max_right (max R M) 0; linarith
    have hyH : ((y : ℂ) * I) ∈ H := by show 0 < ((y : ℂ) * I).im; simpa using hy0
    have hnorm : ‖(y : ℂ) * I‖ = y := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    have hRM := le_max_left (max R M) 0
    have hmem := hM (hfar _ hyH (by rw [hnorm]; linarith [le_max_left R M]))
    rw [mem_closedBall, dist_zero_right, hnorm] at hmem
    linarith [le_max_right R M]
  · rintro z ⟨U, ⟨hUc, hUsub, hUb⟩, hzU⟩
    by_contra hzA
    -- `U` meets `A`
    have hUA : (U ∩ A).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      apply hUb
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun u hu => ?_
      rw [mem_closedBall, dist_zero_right]
      by_contra hlt
      have : u ∈ U ∩ A := ⟨hu, hfar u (hUsub hu).1 (not_le.1 hlt)⟩
      rw [hne] at this; exact this
    obtain ⟨a, haU, haA⟩ := hUA
    obtain ⟨p, hpU, hpf⟩ := CA.Kernel.inter_frontier_nonempty_of_isPreconnected hUc hAo haU haA hzU hzA
    have hpH : p ∈ H := (hUsub hpU).1
    have hpA : p ∉ A := fun h => (hAo.frontier_eq ▸ hpf).2 h
    -- a disc around `p` misses the earlier hulls
    have hpS : p ∉ closure (hullBefore W T) := (hUsub hpU).2
    obtain ⟨r₁, hr₁, hr₁S⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpS
    obtain ⟨r₂, hr₂, hr₂H⟩ := Metric.isOpen_iff.1 isOpen_H p hpH
    set r := min r₁ r₂ with hr
    have hr0 : 0 < r := lt_min hr₁ hr₂
    have hball : ∀ t ∈ Ico (0 : ℝ) T, ball p r ⊆ H \ fwdHull W t := by
      intro t ht w hw
      refine ⟨hr₂H (ball_subset_ball (min_le_right _ _) hw), fun hwK => ?_⟩
      have hwS : w ∉ closure (hullBefore W T) := hr₁S (ball_subset_ball (min_le_left _ _) hw)
      exact hwS (subset_closure (mem_biUnion ht hwK))
    -- an alive point near `p`
    obtain ⟨q, hqA, hqp⟩ : ∃ q ∈ A, dist q p < r / 2 := by
      have hcl := frontier_subset_closure hpf
      rw [Metric.mem_closure_iff] at hcl
      obtain ⟨q, hq, hd⟩ := hcl (r / 2) (by positivity)
      exact ⟨q, hq, by rw [dist_comm]; exact hd⟩
    exact hpA ⟨hpH, not_mem_fwdHull_of_ball_disjoint hW hT hr0 hpH hball hqp hqA⟩

/-- **The active-domain boundary at `T` is the outer boundary of the closure of the earlier hulls.** -/
theorem frontier_compl_fwdHull_eq_outerBoundary (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) :
    frontier (H \ fwdHull W T) ∩ H = outerBoundary (closure (hullBefore W T)) := by
  rw [outerBoundary, ← compl_fwdHull_eq_unbddPart hW hW0 hT]

end InteractingSLE.ZhanGT4.A34
