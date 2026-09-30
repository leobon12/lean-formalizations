import QuantumZipper.Proofs.Zipper.FieldLawler3UnifC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (D): which parts of `ℝ ∪ η` form the frontier of `H_η`, and in which order

Let `f : ℝ → ℂ` be a continuous injective parametrization of `frontier H_η` that is unbounded at
both ends (the boundary map `Φ|ℝ` of `FieldLawler3UnifC.lean`). Then
(`fl3u_frontier_pieces`):
* no point of the open segment `(a, b)` lies on `frontier H_η`;
* there are `α < β` with `{f α, f β} = {a, b}`, `f((α, β)) ⊆ η`, and `f(x)` real outside
  `[a, b]` for `x ∉ [α, β]`.

Own elementary plane-topology argument (no source needed beyond the definitions): `frontier H_η`
lies in the graph `η̄ ∪ ℝ`; the top point of `η` lies on `frontier H_η` (the vertical ray above it
lies in `H_η`); a connected subset of `(η ∪ ℝ) \ {a, b}` meeting `η` (resp. `(a, b)`) stays in `η`
(resp. `(a, b)`); a pigeonhole on the two points `a, b`, each attained at most once by `f`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

section Graph

variable {A : Set ℂ} {a b : ℝ}

/-- A connected subset of `(A ∪ ℝ) \ {a, b}` meeting the open segment `(a, b)` stays in it. -/
lemma fl3u_sub_seg (hAH : A ⊆ H) (hAne : A.Nonempty)
    (hreal : ∀ x : ℂ, x.im = 0 → x ≠ a → x ≠ b → x ∉ closure A)
    {s : Set ℂ} (hs : IsPreconnected s) (hsub : ∀ z ∈ s, z ∈ A ∨ z.im = 0)
    (ha : (a : ℂ) ∉ s) (hb : (b : ℂ) ∉ s)
    (hmeet : ∃ z ∈ s, z.im = 0 ∧ a < z.re ∧ z.re < b) :
    ∀ z ∈ s, z.im = 0 ∧ a < z.re ∧ z.re < b := by
  set u : Set ℂ := {z | a < z.re} ∩ {z | z.re < b} ∩ {z | |z.im| < infDist z A} with hu
  have huo : IsOpen u :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).inter
      (isOpen_lt continuous_im.abs (continuous_infDist_pt A))
  have hcl : closure u ⊆ {z | a ≤ z.re} ∩ {z | z.re ≤ b} ∩ {z | |z.im| ≤ infDist z A} :=
    closure_minimal (fun z hz => by
      simp only [u, mem_inter_iff, mem_ofPred_eq] at hz ⊢
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.le⟩)
      (((isClosed_le continuous_const continuous_re).inter
        (isClosed_le continuous_re continuous_const)).inter
        (isClosed_le continuous_im.abs (continuous_infDist_pt A)))
  have hApos : ∀ z ∈ A, 0 < z.im := fun z hz => hAH hz
  have hrealu : ∀ z : ℂ, z.im = 0 → z ≠ a → z ≠ b → a ≤ z.re → z.re ≤ b → z ∈ u := by
    intro z h0 hza hzb h1 h2
    have hra : z.re ≠ a := fun h => hza (Complex.ext (by simp [h]) (by simp [h0]))
    have hrb : z.re ≠ b := fun h => hzb (Complex.ext (by simp [h]) (by simp [h0]))
    have hd : infDist z A ≠ 0 := fun h => hreal z h0 hza hzb ((mem_closure_iff_infDist_zero hAne).2 h)
    refine ⟨⟨lt_of_le_of_ne h1 (Ne.symm hra), lt_of_le_of_ne h2 hrb⟩, ?_⟩
    show |z.im| < infDist z A
    rw [h0, abs_zero]
    exact lt_of_le_of_ne infDist_nonneg (Ne.symm hd)
  have hsu : s ⊆ u := by
    obtain ⟨z, hz, h0, h1, h2⟩ := hmeet
    refine hs.subset_of_closure_inter_subset huo
      ⟨z, hz, hrealu z h0 (fun h => ha (h ▸ hz)) (fun h => hb (h ▸ hz)) h1.le h2.le⟩ ?_
    rintro p ⟨hp, hps⟩
    have hp' := hcl hp
    rcases hsub p hps with hpA | hp0
    · have : |p.im| ≤ 0 := by
        have h' : |p.im| ≤ infDist p A := hp'.2; rwa [infDist_zero_of_mem hpA] at h'
      have := hApos p hpA
      have := abs_nonneg p.im
      linarith [le_abs_self p.im]
    · exact hrealu p hp0 (fun h => ha (h ▸ hps)) (fun h => hb (h ▸ hps)) hp'.1.1 hp'.1.2
  intro z hz
  have hzu := hsu hz
  rcases hsub z hz with hzA | hz0
  · have : |z.im| < 0 := by have h' : |z.im| < infDist z A := hzu.2; rwa [infDist_zero_of_mem hzA] at h'
    exact absurd this (not_lt.2 (abs_nonneg _))
  · exact ⟨hz0, hzu.1.1, hzu.1.2⟩

/-- A connected subset of `(A ∪ ℝ) \ {a, b}` meeting `A` stays in `A`. -/
lemma fl3u_sub_arc (hAH : A ⊆ H)
    (hreal : ∀ x : ℂ, x.im = 0 → x ≠ a → x ≠ b → x ∉ closure A)
    {s : Set ℂ} (hs : IsPreconnected s) (hsub : ∀ z ∈ s, z ∈ A ∨ z.im = 0)
    (ha : (a : ℂ) ∉ s) (hb : (b : ℂ) ∉ s) (hmeet : ∃ z ∈ s, z ∈ A) : s ⊆ A := by
  have hAne : A.Nonempty := let ⟨z, _, hz⟩ := hmeet; ⟨z, hz⟩
  set u : Set ℂ := {z | infDist z A < z.im} with hu
  have huo : IsOpen u := isOpen_lt (continuous_infDist_pt A) continuous_im
  have hcl : closure u ⊆ {z | infDist z A ≤ z.im} :=
    closure_minimal (fun z (hz : infDist z A < z.im) => (le_of_lt hz : infDist z A ≤ z.im))
      (isClosed_le (continuous_infDist_pt A) continuous_im)
  have hAu : ∀ z ∈ A, z ∈ u := fun z hz => by
    show infDist z A < z.im
    rw [infDist_zero_of_mem hz]; exact hAH hz
  have hsu : s ⊆ u := by
    obtain ⟨z, hz, hzA⟩ := hmeet
    refine hs.subset_of_closure_inter_subset huo ⟨z, hz, hAu z hzA⟩ ?_
    rintro p ⟨hp, hps⟩
    rcases hsub p hps with hpA | hp0
    · exact hAu p hpA
    · exfalso
      have h1 : infDist p A ≤ 0 := by have := hcl hp; simp only [mem_ofPred_eq] at this; linarith
      have h2 : infDist p A = 0 := le_antisymm h1 infDist_nonneg
      exact hreal p hp0 (fun h => ha (h ▸ hps)) (fun h => hb (h ▸ hps))
        ((mem_closure_iff_infDist_zero hAne).2 h2)
  intro z hz
  rcases hsub z hz with hzA | hz0
  · exact hzA
  · have := hsu hz
    have h : infDist z A < 0 := by simpa [u, hz0] using this
    exact absurd h (not_lt.2 infDist_nonneg)

end Graph

/-- The highest point of `η` lies on `frontier H_η`. -/
lemma fl3u_top_mem_frontier {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) :
    ∃ w ∈ arcH η, w ∈ frontier (hullComp η) := by
  set K := lwArcExt η a b '' Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn (lwArcExt_contOn hη ha hb)
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨_, ⟨t, ht, rfl⟩, hmax⟩ :=
    hKc.exists_isMaxOn ⟨_, 0, left_mem_Icc.2 zero_le_one, rfl⟩ continuous_im.continuousOn
  have hpos : 0 < (η (1 / 2)).im := hη.2.2.1 hhalf
  have hle : (η (1 / 2)).im ≤ (lwArcExt η a b t).im :=
    hmax (show η (1 / 2) ∈ K from ⟨1 / 2, Ioo_subset_Icc_self hhalf, (lwArcExt_mem hη hhalf).1⟩)
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne ht.1 fun h => ?_, lt_of_le_of_ne ht.2 fun h => ?_⟩
    · subst h; norm_num [lwArcExt] at hle; linarith
    · subst h; norm_num [lwArcExt] at hle; linarith
  set w := lwArcExt η a b t with hw
  have hwpos : 0 < w.im := hpos.trans_le hle
  have hwA : w ∈ arcH η := ⟨t, ht', (lwArcExt_mem hη ht').1.symm⟩
  have hArcK : ∀ z ∈ arcH η, z.im ≤ w.im := by
    rintro z ⟨s, hs, rfl⟩
    exact hmax (show η s ∈ K from ⟨s, Ioo_subset_Icc_self hs, (lwArcExt_mem hη hs).1⟩)
  set r : ℝ → ℂ := fun s => w + (s : ℂ) * I with hr
  have hrc : Continuous r := by fun_prop
  have hrim : ∀ s, (r s).im = w.im + s := fun s => by simp [r]
  have hrS : ∀ s > (0 : ℝ), r s ∈ H \ arcH η := fun s hs =>
    ⟨show 0 < (r s).im by rw [hrim]; linarith, fun hA => by
      have := hArcK _ hA; rw [hrim] at this; linarith⟩
  have hray : ∀ s > (0 : ℝ), r s ∈ hullComp η := by
    intro s hs
    refine ⟨hrS s hs, fun hbd => ?_⟩
    have hsub : r '' Ioi 0 ⊆ connectedComponentIn (H \ arcH η) (r s) :=
      (isPreconnected_Ioi.image r hrc.continuousOn).subset_connectedComponentIn ⟨s, hs, rfl⟩
        (by rintro _ ⟨u, hu, rfl⟩; exact hrS u hu)
    obtain ⟨R, hR⟩ := (hbd.subset hsub).subset_closedBall 0
    have h1 := hR ⟨|R| + 1, show (0 : ℝ) < |R| + 1 by positivity, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 := Complex.abs_im_le_norm (r (|R| + 1))
    rw [hrim, abs_of_pos (by positivity)] at h2
    linarith [le_abs_self R]
  refine ⟨w, hwA, ?_⟩
  rw [(lwExc_hullComp_isOpen hη).frontier_eq]
  refine ⟨mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ)) ?_
    (eventually_nhdsWithin_of_forall fun s hs => hray s hs), fun h => h.1.2 hwA⟩
  have := (hrc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [r] using this

/-- **Boundary pieces of `H_η`.** For a continuous injective parametrization `f` of
`frontier H_η`, unbounded at both ends: the open segment `(a, b)` is off `frontier H_η`, and
there are `α < β` with `{f α, f β} = {a, b}`, `f((α, β)) ⊆ η` and `f(x) ∈ ℝ \ [a, b]` for
`x ∉ [α, β]`. -/
theorem fl3u_frontier_pieces {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    {f : ℝ → ℂ} (hfc : Continuous f) (hfi : Function.Injective f)
    (hfr : range f = frontier (hullComp η))
    (hunb : ∀ c : ℝ, ¬ Bornology.IsBounded (f '' Ici c) ∧ ¬ Bornology.IsBounded (f '' Iic c)) :
    (∀ z ∈ frontier (hullComp η), ¬ (z.im = 0 ∧ a < z.re ∧ z.re < b)) ∧
    ∃ α β : ℝ, α < β ∧ ((f α = a ∧ f β = b) ∨ (f α = b ∧ f β = a)) ∧
      f '' Ioo α β ⊆ arcH η ∧
      ∀ x, (x < α ∨ β < x) → (f x).im = 0 ∧ ((f x).re < a ∨ b < (f x).re) := by
  set A := arcH η with hA
  have hAH : A ⊆ H := by rintro _ ⟨s, hs, rfl⟩; exact hη.2.2.1 hs
  have hAne : A.Nonempty := ⟨_, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hreal : ∀ x : ℂ, x.im = 0 → x ≠ a → x ≠ b → x ∉ closure A :=
    fun x h1 h2 h3 => lw3_real_not_mem_closure hη ha hb h1 h2 h3
  have hAb : Bornology.IsBounded A := lwExc_arc_isBounded hη
  have hSb : Bornology.IsBounded {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b} := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b|)).subset fun z hz => ?_
    rw [mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    rw [hz.1, abs_zero, add_zero] at h1
    have : |z.re| ≤ |a| + |b| := abs_le.2
      ⟨by linarith [neg_abs_le a, abs_nonneg b, hz.2.1], by linarith [le_abs_self b, abs_nonneg a, hz.2.2]⟩
    linarith
  have hfrm : ∀ x, f x ∈ frontier (hullComp η) := fun x => hfr ▸ mem_range_self x
  have hL : ∀ x, f x ∈ A ∨ (f x).im = 0 := by
    intro x
    by_cases hxA : f x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (le_antisymm (lw3_frontier_hull_im hη (hfrm x) hxA)
        (fl3u_frontier_im (lwExc_hullComp_subset_H η) (hfrm x)))
  have kA : ∀ I : Set ℝ, IsPreconnected I → (∀ x ∈ I, f x ≠ a ∧ f x ≠ b) →
      (∃ x ∈ I, f x ∈ A) → f '' I ⊆ A := by
    intro I hI hT ⟨x, hx, hxA⟩
    refine fl3u_sub_arc hAH hreal (hI.image f hfc.continuousOn) ?_ ?_ ?_ ⟨f x, ⟨x, hx, rfl⟩, hxA⟩
    · rintro _ ⟨y, -, rfl⟩; exact hL y
    · rintro ⟨y, hy, hya⟩; exact (hT y hy).1 hya
    · rintro ⟨y, hy, hyb⟩; exact (hT y hy).2 hyb
  have kS : ∀ I : Set ℝ, IsPreconnected I → (∀ x ∈ I, f x ≠ a ∧ f x ≠ b) →
      (∃ x ∈ I, (f x).im = 0 ∧ a < (f x).re ∧ (f x).re < b) →
      ∀ x ∈ I, (f x).im = 0 ∧ a < (f x).re ∧ (f x).re < b := by
    intro I hI hT ⟨x, hx, hxS⟩ y hy
    refine fl3u_sub_seg hAH hAne hreal (hI.image f hfc.continuousOn) ?_ ?_ ?_
      ⟨f x, ⟨x, hx, rfl⟩, hxS⟩ (f y) ⟨y, hy, rfl⟩
    · rintro _ ⟨y, -, rfl⟩; exact hL y
    · rintro ⟨y, hy, hya⟩; exact (hT y hy).1 hya
    · rintro ⟨y, hy, hyb⟩; exact (hT y hy).2 hyb
  have exA : ∀ I : Set ℝ, IsPreconnected I → ¬ Bornology.IsBounded (f '' I) →
      (∃ x ∈ I, f x ∈ A) → ∃ y ∈ I, f y = a ∨ f y = b := by
    intro I hI hIb hx
    by_contra hcon
    push Not at hcon
    exact hIb (hAb.subset (kA I hI hcon hx))
  have exS : ∀ I : Set ℝ, IsPreconnected I → ¬ Bornology.IsBounded (f '' I) →
      (∃ x ∈ I, (f x).im = 0 ∧ a < (f x).re ∧ (f x).re < b) → ∃ y ∈ I, f y = a ∨ f y = b := by
    intro I hI hIb hx
    by_contra hcon
    push Not at hcon
    refine hIb (hSb.subset ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact kS I hI hcon hx y hy
  have exAS : ∀ I : Set ℝ, IsPreconnected I → (∃ x ∈ I, f x ∈ A) →
      (∃ x ∈ I, (f x).im = 0 ∧ a < (f x).re ∧ (f x).re < b) → ∃ y ∈ I, f y = a ∨ f y = b := by
    intro I hI ⟨x, hx, hxA⟩ hS
    by_contra hcon
    push Not at hcon
    have h1 := (kS I hI hcon hS x hx).1
    have h2 : 0 < (f x).im := hAH hxA
    linarith
  obtain ⟨w, hwA, hwfr⟩ := fl3u_top_mem_frontier hη ha hb
  obtain ⟨xs, hxs⟩ : w ∈ range f := hfr ▸ hwfr
  have hxsA : f xs ∈ A := hxs ▸ hwA
  have hne_s : ∀ y, (f y = a ∨ f y = b) → y ≠ xs := by
    rintro y hy rfl
    have : (0 : ℝ) < (f y).im := hAH hxsA
    rcases hy with h | h <;> rw [h] at this <;> simp at this
  have pig : ∀ y1 y2 y3 : ℝ, y1 < y2 → y2 < y3 → (f y1 = a ∨ f y1 = b) →
      (f y2 = a ∨ f y2 = b) → (f y3 = a ∨ f y3 = b) → False := by
    intro y1 y2 y3 h12 h23 h1 h2 h3
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first
    | exact (ne_of_lt h12) (hfi (h1.trans h2.symm))
    | exact (ne_of_lt h23) (hfi (h2.trans h3.symm))
    | exact (ne_of_lt (h12.trans h23)) (hfi (h1.trans h3.symm))
  have P1 : ∀ z ∈ frontier (hullComp η), ¬ (z.im = 0 ∧ a < z.re ∧ z.re < b) := by
    intro z hz hzS
    obtain ⟨xc, rfl⟩ : z ∈ range f := hfr ▸ hz
    have hne_c : ∀ y, (f y = a ∨ f y = b) → y ≠ xc := by
      rintro y hy rfl
      rcases hy with h | h <;> rw [h] at hzS <;> simp at hzS
    have hcs : xc ≠ xs := fun h => by
      have h2 := hAH hxsA
      rw [← h] at h2
      have h3 : (0 : ℝ) < (f xc).im := h2
      rw [hzS.1] at h3
      exact lt_irrefl _ h3
    rcases lt_or_gt_of_ne hcs with h | h
    · obtain ⟨y1, hy1, t1⟩ := exS (Iic xc) isPreconnected_Iic (hunb xc).2 ⟨xc, (mem_Iic.2 le_rfl), hzS⟩
      obtain ⟨y2, hy2, t2⟩ := exAS (Icc xc xs) isPreconnected_Icc
        ⟨xs, right_mem_Icc.2 h.le, hxsA⟩ ⟨xc, left_mem_Icc.2 h.le, hzS⟩
      obtain ⟨y3, hy3, t3⟩ := exA (Ici xs) isPreconnected_Ici (hunb xs).1 ⟨xs, (mem_Ici.2 le_rfl), hxsA⟩
      exact pig y1 y2 y3
        ((lt_of_le_of_ne hy1 (hne_c y1 t1)).trans (lt_of_le_of_ne hy2.1 (hne_c y2 t2).symm))
        ((lt_of_le_of_ne hy2.2 (hne_s y2 t2)).trans (lt_of_le_of_ne hy3 (hne_s y3 t3).symm))
        t1 t2 t3
    · obtain ⟨y1, hy1, t1⟩ := exA (Iic xs) isPreconnected_Iic (hunb xs).2 ⟨xs, (mem_Iic.2 le_rfl), hxsA⟩
      obtain ⟨y2, hy2, t2⟩ := exAS (Icc xs xc) isPreconnected_Icc
        ⟨xs, left_mem_Icc.2 h.le, hxsA⟩ ⟨xc, right_mem_Icc.2 h.le, hzS⟩
      obtain ⟨y3, hy3, t3⟩ := exS (Ici xc) isPreconnected_Ici (hunb xc).1 ⟨xc, (mem_Ici.2 le_rfl), hzS⟩
      exact pig y1 y2 y3
        ((lt_of_le_of_ne hy1 (hne_s y1 t1)).trans (lt_of_le_of_ne hy2.1 (hne_s y2 t2).symm))
        ((lt_of_le_of_ne hy2.2 (hne_c y2 t2)).trans (lt_of_le_of_ne hy3 (hne_c y3 t3).symm))
        t1 t2 t3
  obtain ⟨α, hα, tα⟩ := exA (Iic xs) isPreconnected_Iic (hunb xs).2 ⟨xs, (mem_Iic.2 le_rfl), hxsA⟩
  obtain ⟨β, hβ, tβ⟩ := exA (Ici xs) isPreconnected_Ici (hunb xs).1 ⟨xs, (mem_Ici.2 le_rfl), hxsA⟩
  have hαs : α < xs := lt_of_le_of_ne hα (hne_s α tα)
  have hsβ : xs < β := lt_of_le_of_ne hβ (hne_s β tβ).symm
  have hends : (f α = a ∧ f β = b) ∨ (f α = b ∧ f β = a) := by
    rcases tα with h1 | h1 <;> rcases tβ with h2 | h2
    · exact absurd (hfi (h1.trans h2.symm)) (ne_of_lt (hαs.trans hsβ))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (hfi (h1.trans h2.symm)) (ne_of_lt (hαs.trans hsβ))
  have uniq : ∀ y, (f y = a ∨ f y = b) → y = α ∨ y = β := by
    intro y hy
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with h | h
    · exact Or.inl (hfi (h.trans h1.symm))
    · exact Or.inr (hfi (h.trans h2.symm))
    · exact Or.inr (hfi (h.trans h2.symm))
    · exact Or.inl (hfi (h.trans h1.symm))
  have avoid : ∀ I : Set ℝ, α ∉ I → β ∉ I → ∀ x ∈ I, f x ≠ a ∧ f x ≠ b := by
    intro I hα' hβ' x hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases uniq x (Or.inl h) with rfl | rfl
      · exact hα' hx
      · exact hβ' hx
    · rcases uniq x (Or.inr h) with rfl | rfl
      · exact hα' hx
      · exact hβ' hx
  have outside : ∀ I : Set ℝ, IsPreconnected I → ¬ Bornology.IsBounded (f '' I) → α ∉ I →
      β ∉ I → ∀ x ∈ I, (f x).im = 0 ∧ ((f x).re < a ∨ b < (f x).re) := by
    intro I hI hIb hαI hβI x hx
    have hav := avoid I hαI hβI
    have him : (f x).im = 0 := by
      rcases hL x with hA' | h0
      · exact absurd (hAb.subset (kA I hI hav ⟨x, hx, hA'⟩)) hIb
      · exact h0
    refine ⟨him, ?_⟩
    have hra : (f x).re ≠ a := fun h => (hav x hx).1 (Complex.ext (by simp [h]) (by simp [him]))
    have hrb : (f x).re ≠ b := fun h => (hav x hx).2 (Complex.ext (by simp [h]) (by simp [him]))
    rcases lt_or_gt_of_ne hra with h1 | h1
    · exact Or.inl h1
    · rcases lt_or_gt_of_ne hrb with h2 | h2
      · exact absurd ⟨him, h1, h2⟩ (P1 _ (hfrm x))
      · exact Or.inr h2
  refine ⟨P1, α, β, hαs.trans hsβ, hends,
    kA (Ioo α β) isPreconnected_Ioo (avoid _ (fun h => lt_irrefl _ h.1) (fun h => lt_irrefl _ h.2))
      ⟨xs, ⟨hαs, hsβ⟩, hxsA⟩, ?_⟩
  rintro x (hx | hx)
  · exact outside (Iic x) isPreconnected_Iic (hunb x).2 (fun h => not_le.2 hx h)
      (fun h => not_le.2 (hx.trans (hαs.trans hsβ)) h) x (mem_Iic.2 le_rfl)
  · exact outside (Ici x) isPreconnected_Ici (hunb x).1
      (fun h => not_le.2 ((hαs.trans hsβ).trans hx) h) (fun h => not_le.2 hx h) x (mem_Ici.2 le_rfl)

end FieldLawler
end QuantumZipper
