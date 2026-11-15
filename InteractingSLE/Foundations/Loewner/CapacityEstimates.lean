import InteractingSLE.Foundations.Loewner.Hull
import InteractingSLE.Foundations.Harmonic.PoissonH

/-!
# Half-plane capacity: subadditivity, the increment inequality, diameter bounds

Packet GEO-HCAP-B (`planning/INFRA-GEO.md` §4), on top of the hull API of GEO-HCAP-A
(`Loewner/Hull.lean`).

* `IsMapOut.tendsto_im_nhdsWithin`: a mapping-out function sends the boundary of `ℍ \ A` to `ℝ`
  (`Im g_A(z) → 0` as `z` tends to any point outside `ℍ \ A`).
* `le_zero_of_harmonicOnNhd_of_subset_H`: Lindelöf's maximum principle on open subsets of `ℍ`.
* `HPHull.tendsto_mul_sub_im`: `hcap(A) = lim_{y→∞} y (y − Im g_A(iy))`.
* `HPHull.hcap_le_add_of_frontier_subset`, `hcapFill_union_le`: **subadditivity**
  `hcap(fill(A ∪ B)) ≤ hcap(fill A) + hcap(fill B)` ([Law05] Prop. 3.39; Specification p. 24, by
  "the maximum principle applied to the sum of the two corresponding harmonic functions").
* `hcapFill_union_union_sub_le`: the **increment inequality** of the proof of Lemma 2.5
  (Specification p. 24): `hcap(A ∪ B ∪ C) − hcap(A ∪ B) ≤ hcap(A ∪ C) − hcap(A)` for filled hulls
  (map out `A` and apply subadditivity to the images).
* `HPHull.hcap_le_diam_sq`, `HPHull.sqrt_hcap_le_diam`, `hcapFill_le_diam_sq`: the
  **diameter–capacity bound** `hcap(A) ≤ diam(A)²` ([Law05] (3.8); Specification p. 148 and
  p. 337).
* `hcapFill_le_of_subset_rect`, `tendsto_hcapFill_rect`: thin rectangles have small capacity
  (`hcap ≤ 2aδ + δ²` for `[−a, a] × [−δ, δ]`); this is the bound `hcap(S̄_δ) → 0` of the proof of
  Lemma 2.5 (Specification p. 24).
* `IsMapOut.im_sub_eq_poissonIntegralH`, `HPHull.hcap_eq_integral`: **Poisson representation**
  of `Im(z − g_A(z))` above a horizontal line `Im z = y₀` lying above `A`, and of the capacity,
  `hcap(A) = (1/π) ∫ Im((t + iy₀) − g_A(t + iy₀)) dt` ([Law05] (3.5)–(3.6), line form).
* `IsHPHull.fillH_eq`, `HPHull.hcapFill_eq`, `HPHull.hcapFill_union_le`, `hcapFill_union_eq_add`:
  compact `ℍ`-hulls are their own fillings (so the filling API applies to them), and the
  composition rule for fillings.

The design's names map as follows: `hcapOf_union_sub_le` ↦ `hcapFill_union_union_sub_le`
(`hcapOf` was replaced by `hcapFill` in GEO-HCAP-A), `hcap_le_diam_sq` ↦ `HPHull.hcap_le_diam_sq`,
`diam_ge_sqrt_hcap` ↦ `HPHull.sqrt_hcap_le_diam`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-! ### Boundary behaviour of mapping-out functions -/

/-- **Mapping-out functions send the boundary to `ℝ`**: as `z → q` inside `ℍ \ A`, where `q` is
any point outside `ℍ \ A` (a real point, or a point of `A`), `Im g_A(z) → 0`. (The inverse map
sends the compact set `{Im ≥ ε} ∩ B̄(0, R)` of `ℍ` to a compact subset of `ℍ \ A`, which stays away
from `q`.) -/
theorem IsMapOut.tendsto_im_nhdsWithin {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A)
    (hg : IsMapOut A g) {q : ℂ} (hq : q ∉ H \ A) :
    Tendsto (fun z => (g z).im) (𝓝[H \ A] q) (𝓝 0) := by
  obtain ⟨h, hhd, hright, hleft⟩ := hg.exists_symm hA
  obtain ⟨C, hC⟩ := hg.exists_norm_le hA
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact ha.trans (show 0 < (g z).im from hg.1.2.mapsTo hz)
  · set R := ‖q‖ + 1 + C with hRdef
    set S : Set ℂ := {w : ℂ | ε ≤ w.im} ∩ closedBall 0 R with hSdef
    have hSc : IsCompact S :=
      (isCompact_closedBall (0 : ℂ) R).inter_left (isClosed_le continuous_const continuous_im)
    have hSH : S ⊆ H := fun w hw => show 0 < w.im from hε.trans_le hw.1
    have hhS : IsCompact (h '' S) := hSc.image_of_continuousOn (hhd.continuousOn.mono hSH)
    have hqS : q ∉ h '' S := by
      rintro ⟨w, hw, rfl⟩
      exact hq (hright w (hSH hw)).1
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hhS.isClosed.isOpen_compl.mem_nhds hqS),
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds q one_pos), self_mem_nhdsWithin]
      with z hz1 hz2 hz3
    by_contra hcon
    apply hz1
    refine ⟨g z, ⟨not_lt.1 hcon, ?_⟩, hleft z hz3⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hC z hz3
    have h2 : ‖z - q‖ < 1 := by rw [← dist_eq_norm]; exact hz2
    have h3 : ‖z‖ ≤ ‖q‖ + ‖z - q‖ := by
      calc ‖z‖ = ‖q + (z - q)‖ := by ring_nf
        _ ≤ ‖q‖ + ‖z - q‖ := norm_add_le _ _
    linarith

/-! ### The maximum principle on open subsets of `ℍ` -/

/-- The barrier `log ‖z + i‖` is harmonic on `ℍ`. -/
theorem harmonicOnNhd_log_norm_add_I_H :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖z + I‖) H := by
  intro z hz
  have hz' : z + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hz0 : 0 < z.im := hz
    linarith
  exact (analyticAt_id.add analyticAt_const).harmonicAt_log_norm hz'

theorem one_le_norm_add_I_of_mem_H {z : ℂ} (hz : z ∈ H) : 1 ≤ ‖z + I‖ := by
  have hz0 : 0 < z.im := hz
  calc (1 : ℝ) ≤ |(z + I).im| := by
        simp only [add_im, I_im]
        rw [abs_of_pos (by linarith)]
        linarith
    _ ≤ ‖z + I‖ := Complex.abs_im_le_norm _

/-- **Lindelöf's maximum principle on open subsets of `ℍ`**: a harmonic function on an open
`U ⊆ ℍ`, bounded above, with `limsup ≤ 0` at every point of `closure U \ U`, is `≤ 0` on `U`
(no condition at `∞`; the barrier is `log ‖z + i‖`). -/
theorem le_zero_of_harmonicOnNhd_of_subset_H {U : Set ℂ} {f : ℂ → ℝ} (hU : IsOpen U)
    (hUH : U ⊆ H) (hf : InnerProductSpace.HarmonicOnNhd f U) (hbd : BddAbove (f '' U))
    (hfr : ∀ q ∈ closure U, q ∉ U → ∀ ε > 0, ∀ᶠ z in 𝓝[U] q, f z ≤ ε) :
    ∀ z ∈ U, f z ≤ 0 := by
  refine harmonic_le_zero_of_barrier ∅ hU hf hbd (fun q hq _ => ?_)
    (fun z hz => harmonicOnNhd_log_norm_add_I_H z (hUH hz))
    (fun y hy => Real.log_nonneg (one_le_norm_add_I_of_mem_H (hUH hy))) ?_
  · rw [hU.frontier_eq] at hq
    exact hfr q hq.1 hq.2
  · intro M
    refine ⟨Real.exp M + 1, fun y _ hRy => ?_⟩
    have h1 : Real.exp M ≤ ‖y + I‖ := by
      have := norm_sub_norm_le y (-I)
      simp only [sub_neg_eq_add, norm_neg, Complex.norm_I] at this
      linarith
    exact (Real.le_log_iff_exp_le ((Real.exp_pos M).trans_le h1)).2 h1

/-! ### Capacity as a limit along the imaginary axis -/

/-- `hcap(A) = lim_{y → ∞} y (y − Im g_A(iy))` ([Law05] (3.5)). -/
theorem HPHull.tendsto_mul_sub_im (A : HPHull) {g : ℂ → ℂ} (hg : IsMapOut A.1 g) :
    Tendsto (fun y : ℝ => y * (y - (g (y * I)).im)) atTop (𝓝 A.hcap) := by
  have hT := (Complex.continuous_re.tendsto _).comp
    ((A.tendsto_hcap hg).comp A.2.tendsto_ofReal_mul_I)
  rw [ofReal_re] at hT
  refine hT.congr fun y => ?_
  simp only [Function.comp_apply, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_im, zero_sub, mul_im, sub_re, add_zero]
  ring

/-! ### Subadditivity -/

/-- **Subadditivity of half-plane capacity** in its general form: if the hulls `A, B ⊆ D` cover
every point of `D` adherent to `ℍ \ D`, then `hcap(D) ≤ hcap(A) + hcap(B)`. The function
`Im g_A + Im g_B − Im z − Im g_D` is harmonic and bounded on `ℍ \ D`, with `limsup ≤ 0` on the
boundary, hence `≤ 0` (maximum principle); then take `y (y − Im g(iy))` to the limit. -/
theorem HPHull.hcap_le_add_of_frontier_subset (A B D : HPHull) (hAD : A.1 ⊆ D.1)
    (hBD : B.1 ⊆ D.1) (hfr : ∀ q ∈ D.1, q ∈ closure (H \ D.1) → q ∈ A.1 ∪ B.1) :
    D.hcap ≤ A.hcap + B.hcap := by
  obtain ⟨gA, hgA⟩ := A.2.exists_isMapOut
  obtain ⟨gB, hgB⟩ := B.2.exists_isMapOut
  obtain ⟨gD, hgD⟩ := D.2.exists_isMapOut
  have hDA : H \ D.1 ⊆ H \ A.1 := fun z hz => ⟨hz.1, fun h => hz.2 (hAD h)⟩
  have hDB : H \ D.1 ⊆ H \ B.1 := fun z hz => ⟨hz.1, fun h => hz.2 (hBD h)⟩
  obtain ⟨MA, hMA⟩ := hgA.exists_norm_sub_le A.2
  obtain ⟨MB, hMB⟩ := hgB.exists_norm_sub_le B.2
  obtain ⟨MD, hMD⟩ := hgD.exists_norm_sub_le D.2
  set f : ℂ → ℝ := fun z => (gA z + gB z - z - gD z).im with hfdef
  have hf : InnerProductSpace.HarmonicOnNhd f (H \ D.1) := by
    intro z hz
    have hAz := hgA.1.1.analyticAt (A.2.isOpen.mem_nhds (hDA hz))
    have hBz := hgB.1.1.analyticAt (B.2.isOpen.mem_nhds (hDB hz))
    have hDz := hgD.1.1.analyticAt (D.2.isOpen.mem_nhds hz)
    exact (((hAz.add hBz).sub analyticAt_id).sub hDz).harmonicAt_im
  have hfA : ∀ z ∈ H \ D.1, f z ≤ (gA z).im := by
    intro z hz
    have h1 := hgB.im_le B.2 (hDB hz)
    have h2 : 0 < (gD z).im := hgD.1.2.mapsTo hz
    simp only [hfdef, sub_im, add_im]
    linarith
  have hfB : ∀ z ∈ H \ D.1, f z ≤ (gB z).im := by
    intro z hz
    have h1 := hgA.im_le A.2 (hDA hz)
    have h2 : 0 < (gD z).im := hgD.1.2.mapsTo hz
    simp only [hfdef, sub_im, add_im]
    linarith
  have hbd : BddAbove (f '' (H \ D.1)) := by
    refine ⟨MA + MB + MD, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 := (Complex.abs_im_le_norm (gA z - z)).trans (hMA z (hDA hz))
    have h2 := (Complex.abs_im_le_norm (gB z - z)).trans (hMB z (hDB hz))
    have h3 := (Complex.abs_im_le_norm (gD z - z)).trans (hMD z hz)
    have e : f z = (gA z - z).im + (gB z - z).im - (gD z - z).im := by
      simp only [hfdef, sub_im, add_im]; ring
    rw [e]
    linarith [le_abs_self (gA z - z).im, le_abs_self (gB z - z).im,
      neg_abs_le (gD z - z).im]
  have hfr' : ∀ q ∈ closure (H \ D.1), q ∉ H \ D.1 → ∀ ε > 0,
      ∀ᶠ z in 𝓝[H \ D.1] q, f z ≤ ε := by
    intro q hqc hq ε hε
    have hcase : q ∉ H \ A.1 ∨ q ∉ H \ B.1 := by
      by_cases hqH : q ∈ H
      · have hqD : q ∈ D.1 := by
          by_contra h
          exact hq ⟨hqH, h⟩
        rcases hfr q hqD hqc with h | h
        · exact Or.inl fun h' => h'.2 h
        · exact Or.inr fun h' => h'.2 h
      · exact Or.inl fun h' => hqH h'.1
    rcases hcase with hqA | hqB
    · have hT := (hgA.tendsto_im_nhdsWithin A.2 hqA).mono_left (nhdsWithin_mono q hDA)
      filter_upwards [hT.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with z hz hzD
      exact (hfA z hzD).trans hz.le
    · have hT := (hgB.tendsto_im_nhdsWithin B.2 hqB).mono_left (nhdsWithin_mono q hDB)
      filter_upwards [hT.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with z hz hzD
      exact (hfB z hzD).trans hz.le
  have hle := le_zero_of_harmonicOnNhd_of_subset_H D.2.isOpen (fun z hz => hz.1) hf hbd hfr'
  refine le_of_tendsto_of_tendsto (D.tendsto_mul_sub_im hgD)
    ((A.tendsto_mul_sub_im hgA).add (B.tendsto_mul_sub_im hgB)) ?_
  filter_upwards [D.2.tendsto_ofReal_mul_I.eventually (mem_inf_of_right (mem_principal_self _)),
    eventually_ge_atTop (0 : ℝ)] with y hy hy0
  have h1 := hle _ hy
  simp only [hfdef, sub_im, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
    mul_zero, add_zero] at h1
  have h2 : y - (gD (y * I)).im ≤ (y - (gA (y * I)).im) + (y - (gB (y * I)).im) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hy0
  linarith

/-! ### Fillings -/

/-- The filling is monotone. -/
theorem fillH_mono {A B : Set ℂ} (hAB : A ⊆ B) : fillH A ⊆ fillH B := by
  rintro z ⟨hz, h | h⟩
  · exact ⟨hz, Or.inl (closure_mono hAB h)⟩
  · by_cases hzB : z ∈ closure B
    · exact ⟨hz, Or.inl hzB⟩
    · refine ⟨hz, Or.inr (h.subset (connectedComponentIn_mono z ?_))⟩
      exact fun w hw => ⟨hw.1, fun h' => hw.2 (closure_mono hAB h')⟩

/-- Points of `ℍ ∩ closure A` belong to the filling. -/
theorem mem_fillH_of_mem_closure {A : Set ℂ} {z : ℂ} (hz : z ∈ H) (hzA : z ∈ closure A) :
    z ∈ fillH A :=
  ⟨hz, Or.inl hzA⟩

/-- A point of the filling adherent to its complement in `ℍ` lies in `closure A` (points of
bounded components of `ℍ \ closure A` are interior points of the filling). -/
theorem mem_closure_of_mem_fillH_of_mem_closure {A : Set ℂ} {z : ℂ} (hz : z ∈ fillH A)
    (hzc : z ∈ closure (H \ fillH A)) : z ∈ closure A := by
  by_contra hzA
  have hb : Bornology.IsBounded (connectedComponentIn (H \ closure A) z) := hz.2.resolve_left hzA
  have hzF : z ∈ H \ closure A := ⟨hz.1, hzA⟩
  set W := connectedComponentIn (H \ closure A) z with hWdef
  have hWo : IsOpen W := (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  have hWf : W ⊆ fillH A := by
    intro w hw
    have hwF := connectedComponentIn_subset _ _ hw
    refine ⟨hwF.1, Or.inr ?_⟩
    rw [← connectedComponentIn_eq hw]
    exact hb
  obtain ⟨w, hwW, hw⟩ := mem_closure_iff.1 hzc W hWo (mem_connectedComponentIn hzF)
  exact hw.2 (hWf hwW)

/-- `A ∪ {Im ≤ 0}` and `B ∪ {Im ≤ 0}` preconnected imply `A ∪ B ∪ {Im ≤ 0}` preconnected. -/
theorem isPreconnected_union_lowerHalf {A B : Set ℂ}
    (hA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) :
    IsPreconnected (A ∪ B ∪ {z : ℂ | z.im ≤ 0}) := by
  have h0 : (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} := show (0 : ℂ).im ≤ 0 by simp
  have := hA.union (0 : ℂ) (Or.inr h0) (Or.inr h0) hB
  convert this using 1
  ext z
  simp only [mem_union]
  tauto

/-- `hcapFill` only depends on the set. -/
theorem hcapFill_congr {A B : Set ℂ} (h : A = B) (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hB : Bornology.IsBounded B)
    (hcB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) : hcapFill A hA hcA = hcapFill B hB hcB := by
  subst h
  rfl

/-- **Monotonicity of the capacity of fillings.** -/
theorem hcapFill_mono {A B : Set ℂ} (hAB : A ⊆ B) (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hB : Bornology.IsBounded B)
    (hcB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) : hcapFill A hA hcA ≤ hcapFill B hB hcB :=
  HPHull.hcap_mono (A := ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hcA⟩)
    (B := ⟨fillH B, isHPHull_fillH_of_isPreconnected hB hcB⟩) (fillH_mono hAB)

/-- **Subadditivity of half-plane capacity** ([Law05] Prop. 3.39; Specification p. 24):
`hcap(fill(A ∪ B)) ≤ hcap(fill A) + hcap(fill B)`. -/
theorem hcapFill_union_le {A B : Set ℂ} (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hB : Bornology.IsBounded B)
    (hcB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) :
    hcapFill (A ∪ B) (hA.union hB) (isPreconnected_union_lowerHalf hcA hcB) ≤
      hcapFill A hA hcA + hcapFill B hB hcB := by
  refine HPHull.hcap_le_add_of_frontier_subset
    ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hcA⟩
    ⟨fillH B, isHPHull_fillH_of_isPreconnected hB hcB⟩
    ⟨fillH (A ∪ B), isHPHull_fillH_of_isPreconnected (hA.union hB)
      (isPreconnected_union_lowerHalf hcA hcB)⟩
    (fillH_mono subset_union_left) (fillH_mono subset_union_right) ?_
  intro q hq hqc
  have h := mem_closure_of_mem_fillH_of_mem_closure hq hqc
  rw [closure_union] at h
  rcases h with h | h
  · exact Or.inl (mem_fillH_of_mem_closure hq.1 h)
  · exact Or.inr (mem_fillH_of_mem_closure hq.1 h)

/-! ### The increment inequality (Specification p. 24) -/

/-- **The capacity increment inequality** of the proof of Lemma 2.5 (Specification p. 24): for
bounded sets attached to `ℝ` (filled hulls taken when writing capacity),
`hcap(A ∪ B ∪ C) − hcap(A ∪ B) ≤ hcap(A ∪ C) − hcap(A)`. Map out `fill A` by `g`; by the
composition rule each side is a difference of capacities of images under `g`, and the images of
`fill(A ∪ B) \ fill A` and `fill(A ∪ C) \ fill A` cover the boundary points of the image of
`fill(A ∪ B ∪ C) \ fill A`, so subadditivity applies. (No inclusion `A ⊆ B` is needed.) -/
theorem hcapFill_union_union_sub_le {A B C : Set ℂ} (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hB : Bornology.IsBounded B)
    (hcB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) (hC : Bornology.IsBounded C)
    (hcC : IsPreconnected (C ∪ {z : ℂ | z.im ≤ 0})) :
    hcapFill (A ∪ B ∪ C) ((hA.union hB).union hC)
        (isPreconnected_union_lowerHalf (isPreconnected_union_lowerHalf hcA hcB) hcC) -
      hcapFill (A ∪ B) (hA.union hB) (isPreconnected_union_lowerHalf hcA hcB) ≤
    hcapFill (A ∪ C) (hA.union hC) (isPreconnected_union_lowerHalf hcA hcC) -
      hcapFill A hA hcA := by
  set A₀ : HPHull := ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hcA⟩ with hA₀
  set B₀ : HPHull := ⟨fillH (A ∪ B), isHPHull_fillH_of_isPreconnected (hA.union hB)
    (isPreconnected_union_lowerHalf hcA hcB)⟩ with hB₀
  set C₀ : HPHull := ⟨fillH (A ∪ C), isHPHull_fillH_of_isPreconnected (hA.union hC)
    (isPreconnected_union_lowerHalf hcA hcC)⟩ with hC₀
  set D₀ : HPHull := ⟨fillH (A ∪ B ∪ C), isHPHull_fillH_of_isPreconnected
    ((hA.union hB).union hC)
    (isPreconnected_union_lowerHalf (isPreconnected_union_lowerHalf hcA hcB) hcC)⟩ with hD₀
  show D₀.hcap - B₀.hcap ≤ C₀.hcap - A₀.hcap
  obtain ⟨g, hg⟩ := A₀.2.exists_isMapOut
  have hAB : A₀.1 ⊆ B₀.1 := fillH_mono subset_union_left
  have hAC : A₀.1 ⊆ C₀.1 := fillH_mono subset_union_left
  have hAD : A₀.1 ⊆ D₀.1 := fillH_mono (subset_union_left.trans subset_union_left)
  have hBD : B₀.1 ⊆ D₀.1 := fillH_mono subset_union_left
  have hCD : C₀.1 ⊆ D₀.1 := fillH_mono (union_subset_union_left _ subset_union_left)
  have eB := HPHull.hcap_eq_add hAB hg
  have eC := HPHull.hcap_eq_add hAC hg
  have eD := HPHull.hcap_eq_add hAD hg
  have key := HPHull.hcap_le_add_of_frontier_subset
    ⟨g '' (B₀.1 \ A₀.1), hg.isHPHull_image A₀.2 B₀.2 hAB⟩
    ⟨g '' (C₀.1 \ A₀.1), hg.isHPHull_image A₀.2 C₀.2 hAC⟩
    ⟨g '' (D₀.1 \ A₀.1), hg.isHPHull_image A₀.2 D₀.2 hAD⟩
    (image_mono (sdiff_subset_sdiff_left hBD)) (image_mono (sdiff_subset_sdiff_left hCD)) ?_
  · linarith
  rintro q ⟨p, ⟨hpD, hpA⟩, rfl⟩ hqc
  change g p ∈ closure (H \ g '' (D₀.1 \ A₀.1)) at hqc
  rw [hg.H_diff_image hAD D₀.2.1] at hqc
  obtain ⟨h, hhd, -, hleft⟩ := hg.exists_symm A₀.2
  have hpH : p ∈ H \ A₀.1 := ⟨D₀.2.1 hpD, hpA⟩
  have hgp : g p ∈ H := hg.1.2.mapsTo hpH
  have hcont : ContinuousAt h (g p) :=
    hhd.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hgp)
  have h1 := mem_closure_image hcont hqc
  rw [hleft p hpH, image_image,
    image_congr (fun z hz => hleft z ⟨hz.1, fun h' => hz.2 (hAD h')⟩), image_id'] at h1
  have h3 := mem_closure_of_mem_fillH_of_mem_closure hpD h1
  rw [closure_union, closure_union] at h3
  rcases h3 with (h3 | h3) | h3
  · exact absurd (mem_fillH_of_mem_closure hpH.1 h3) hpA
  · refine Or.inl ⟨p, ⟨mem_fillH_of_mem_closure hpH.1 ?_, hpA⟩, rfl⟩
    exact closure_mono subset_union_right h3
  · refine Or.inr ⟨p, ⟨mem_fillH_of_mem_closure hpH.1 ?_, hpA⟩, rfl⟩
    exact closure_mono subset_union_right h3

/-! ### Diameter bounds -/

/-- A nonempty compact `ℍ`-hull touches `ℝ`: its closure contains a real point. (Otherwise the
hull is a compact subset of `ℍ`, and the component of one of its points in the complement of
`ℍ \ A` is bounded, contradicting simple connectivity.) -/
theorem IsHPHull.exists_ofReal_mem_closure {A : Set ℂ} (hA : IsHPHull A) (hne : A.Nonempty) :
    ∃ x : ℝ, (x : ℂ) ∈ closure A := by
  by_contra hcon
  have hcon' : ∀ x : ℝ, (x : ℂ) ∉ closure A := fun x hx => hcon ⟨x, hx⟩
  have hcl : closure A ⊆ A := by
    intro z hz
    have hz0 : 0 ≤ z.im := closure_minimal (t := {b : ℂ | 0 ≤ b.im})
      (fun w hw => show (0 : ℝ) ≤ w.im from (show (0 : ℝ) < w.im from hA.1 hw).le)
      (isClosed_le continuous_const continuous_im) hz
    have hzH : z ∈ H := by
      rcases hz0.lt_or_eq with h | h
      · exact h
      · have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [h])
        exact absurd (hz'.symm ▸ hz) (hcon' z.re)
    by_contra hzA
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hz _ hA.isOpen ⟨hzH, hzA⟩
    exact hw1.2 hw2
  have hAc : IsClosed A := closure_subset_iff_isClosed.1 hcl
  obtain ⟨a, ha⟩ := hne
  apply not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hA.isOpen hA.2.2.2
    (a := a) (fun h => h.2 ha)
  rw [compl_H_diff]
  refine hA.2.1.subset ?_
  have hQ := isPreconnected_connectedComponentIn (x := a) (F := A ∪ {z : ℂ | z.im ≤ 0})
  have hdisj : connectedComponentIn (A ∪ {z : ℂ | z.im ≤ 0}) a ∩
      (A ∩ {z : ℂ | z.im ≤ 0}) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro _ hzA hz
    exact absurd (show 0 < z.im from hA.1 hzA) (not_lt.2 hz)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hQ A _ hAc isClosed_lowerHalf
      (connectedComponentIn_subset _ _) hdisj with h | h
  · exact h
  · exfalso
    have := h (mem_connectedComponentIn (Or.inl ha))
    exact absurd (show 0 < a.im from hA.1 ha) (not_lt.2 this)

/-- **The diameter–capacity bound** `hcap(A) ≤ diam(A)²` ([Law05] (3.8); Specification p. 148,
"the diameter-capacity bound", and p. 337): a nonempty hull lies in the closed disc of radius
`diam A` around a real point of its closure. -/
theorem HPHull.hcap_le_diam_sq (A : HPHull) : A.hcap ≤ diam A.1 ^ 2 := by
  rcases A.1.eq_empty_or_nonempty with h | h
  · rw [A.hcap_eq_zero_of_eq_empty h]
    positivity
  obtain ⟨x, hx⟩ := A.2.exists_ofReal_mem_closure h
  refine A.hcap_le_rad_sq (x := x) fun z hz => ?_
  rw [mem_closedBall, ← diam_closure]
  exact dist_le_diam_of_mem A.2.2.1.closure (subset_closure hz) hx

/-- **`diam(A) ≥ √hcap(A)`** (Specification p. 148: `diam(K_s) ≥ c √hcap(K_s)`, here with
`c = 1`). -/
theorem HPHull.sqrt_hcap_le_diam (A : HPHull) : √A.hcap ≤ diam A.1 := by
  calc √A.hcap ≤ √(diam A.1 ^ 2) := Real.sqrt_le_sqrt A.hcap_le_diam_sq
    _ = diam A.1 := Real.sqrt_sq diam_nonneg

/-! ### Fillings inside discs centred on `ℝ` -/

/-- The filling of a set in `B̄(0, r)` stays in `B̄(0, r)`. -/
theorem fillH_subset_closedBall_zero {A : Set ℂ} {r : ℝ} (hA : closure A ⊆ closedBall 0 r) :
    fillH A ⊆ closedBall 0 r := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  rw [not_le] at hlt
  have hz0 : 0 < ‖z‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := show 0 < z.im from hz.1
    rw [h, zero_im] at this
    exact lt_irrefl _ this
  set R := (max r 0 + ‖z‖) / 2 with hRdef
  have hmax : max r 0 < ‖z‖ := max_lt hlt hz0
  have hR : 0 < R := by
    have := le_max_right r 0
    rw [hRdef]
    linarith
  have hAR : closure A ⊆ ball 0 R := by
    intro w hw
    rw [mem_ball_zero_iff]
    have h1 := mem_closedBall_zero_iff.1 (hA hw)
    have := le_max_left r 0
    rw [hRdef]
    linarith
  have := mem_ball_zero_iff.1 (fillH_subset_ball hR hAR hz)
  rw [hRdef] at this
  linarith

/-- **The filling of a set in a closed disc centred on `ℝ` stays in that disc.** -/
theorem fillH_subset_closedBall {A : Set ℂ} {x r : ℝ} (hA : closure A ⊆ closedBall (x : ℂ) r) :
    fillH A ⊆ closedBall (x : ℂ) r := by
  set e := affHomeo 1 one_pos (-x) with hedef
  have he : ∀ z, e z = z - x := fun z => by
    rw [hedef, coe_affHomeo]
    push_cast
    ring
  have h1 : closure (e '' A) ⊆ closedBall 0 r := by
    rw [← e.image_closure]
    rintro _ ⟨w, hw, rfl⟩
    have := hA hw
    rw [mem_closedBall, dist_eq_norm] at this
    rw [mem_closedBall_zero_iff, he]
    exact this
  have h2 := fillH_subset_closedBall_zero h1
  rw [fillH_image_affHomeo] at h2
  intro z hz
  have := mem_closedBall_zero_iff.1 (h2 ⟨z, hz, rfl⟩)
  rw [he] at this
  rw [mem_closedBall, dist_eq_norm]
  exact this

/-- `hcap(fill A) ≤ r²` for `A` in a closed disc of radius `r` centred on `ℝ` ([Law05] (3.8)). -/
theorem hcapFill_le_sq_of_subset_closedBall {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) {x r : ℝ}
    (hAx : A ⊆ closedBall (x : ℂ) r) : hcapFill A hA hc ≤ r ^ 2 :=
  HPHull.hcap_le_rad_sq _ (fillH_subset_closedBall (closure_minimal hAx isClosed_closedBall))

/-- **The diameter–capacity bound for fillings**: `hcap(fill A) ≤ diam(A)²` for a bounded set
`A ⊆ ℍ̄` attached to `ℝ` (Specification p. 148, p. 337). -/
theorem hcapFill_le_diam_sq {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hAH : A ⊆ Hbar) :
    hcapFill A hA hc ≤ diam A ^ 2 := by
  rcases A.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · subst h
    exact (hcapFill_le_sq_of_subset_closedBall hA hc (x := 0) (r := 0) (empty_subset _)).trans
      (by rw [diam_empty])
  have hcl : closure A ⊆ {z : ℂ | 0 ≤ z.im} :=
    closure_minimal hAH (isClosed_le continuous_const continuous_im)
  obtain ⟨p, hpA, hpL⟩ : (closure A ∩ {z : ℂ | z.im ≤ 0}).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hP := hc.closure
    rw [closure_union, isClosed_lowerHalf.closure_eq] at hP
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hP (closure A) _ isClosed_closure
        isClosed_lowerHalf subset_rfl (by rw [hne, inter_empty]) with h | h
    · have hI : -I ∈ closure A := h (Or.inr (show (-I).im ≤ 0 by simp))
      have := hcl hI
      simp only [mem_ofPred_eq, neg_im, I_im] at this
      norm_num at this
    · have := h (Or.inl (subset_closure ha))
      exact (eq_empty_iff_forall_notMem.1 hne) a ⟨subset_closure ha, this⟩
  have hp0 : p.im = 0 := le_antisymm hpL (hcl hpA)
  have hp' : ((p.re : ℝ) : ℂ) = p := Complex.ext (by simp) (by simp [hp0])
  refine hcapFill_le_sq_of_subset_closedBall hA hc (x := p.re) fun z hz => ?_
  rw [mem_closedBall, hp', ← diam_closure]
  exact dist_le_diam_of_mem hA.closure (subset_closure hz) hpA

/-! ### Finite unions and thin rectangles -/

/-- **Subadditivity over finite unions**: `hcap(fill ⋃_{k<n} Y_k) ≤ ∑_{k<n} hcap(fill Y_k)`. -/
theorem hcapFill_biUnion_range_le (Y : ℕ → Set ℂ) (hY : ∀ k, Bornology.IsBounded (Y k))
    (hcY : ∀ k, IsPreconnected (Y k ∪ {z : ℂ | z.im ≤ 0})) (n : ℕ) :
    ∃ (hb : Bornology.IsBounded (⋃ k ∈ Finset.range n, Y k))
      (hc : IsPreconnected ((⋃ k ∈ Finset.range n, Y k) ∪ {z : ℂ | z.im ≤ 0})),
      hcapFill _ hb hc ≤ ∑ k ∈ Finset.range n, hcapFill (Y k) (hY k) (hcY k) := by
  induction n with
  | zero =>
    have h0 : (⋃ k ∈ Finset.range 0, Y k) = ∅ := by simp
    rw [h0]
    refine ⟨Bornology.isBounded_empty, by simpa using isPreconnected_lowerHalf, ?_⟩
    rw [Finset.sum_range_zero]
    refine (hcapFill_le_sq_of_subset_closedBall _ _ (x := 0) (r := 0) (empty_subset _)).trans ?_
    norm_num
  | succ n ih =>
    obtain ⟨hb, hc, hle⟩ := ih
    have hU : (⋃ k ∈ Finset.range (n + 1), Y k) = (⋃ k ∈ Finset.range n, Y k) ∪ Y n := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    rw [hU]
    refine ⟨hb.union (hY n), isPreconnected_union_lowerHalf hc (hcY n), ?_⟩
    rw [Finset.sum_range_succ]
    exact (hcapFill_union_le hb hc (hY n) (hcY n)).trans (by linarith)

/-- Grid covering: with `n ≥ 1` columns of half-width `w = a/n`, every point with `|Re z| ≤ a`
and `|Im z| ≤ δ` lies in the disc of radius `√(w² + δ²)` around the centre of its column. -/
theorem exists_mem_closedBall_grid {a δ : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hre : |z.re| ≤ a) (him : |z.im| ≤ δ) :
    ∃ k < n, z ∈ closedBall (((-a + (2 * k + 1) * (a / n) : ℝ)) : ℂ)
      (√((a / n) ^ 2 + δ ^ 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set w := a / n with hwdef
  have hw : 0 < w := div_pos ha hnpos
  have hnw : (n : ℝ) * w = a := by rw [hwdef]; field_simp
  -- the column index
  have hcol : ∃ k < n, |z.re - (-a + (2 * k + 1) * w)| ≤ w := by
    set t := (z.re + a) / (2 * w) with htdef
    have ht0 : 0 ≤ t := div_nonneg (by linarith [neg_abs_le z.re]) (by positivity)
    have htn : t ≤ n := by
      rw [htdef, div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self z.re]
    have hte : z.re + a = 2 * w * t := by rw [htdef]; field_simp
    by_cases hm : ⌊t⌋₊ < n
    · refine ⟨⌊t⌋₊, hm, ?_⟩
      have h1 := Nat.floor_le ht0
      have h2 := Nat.lt_floor_add_one t
      rw [abs_le]
      constructor <;> nlinarith
    · refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_⟩
      have h1 : (n : ℝ) ≤ t := (Nat.cast_le.2 (not_lt.1 hm)).trans (Nat.floor_le ht0)
      have htn' : t = n := le_antisymm htn h1
      have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn.ne'), Nat.cast_one]
      rw [hcast, abs_le]
      rw [htn'] at hte
      constructor <;> nlinarith
  obtain ⟨k, hk, hkw⟩ := hcol
  refine ⟨k, hk, ?_⟩
  rw [mem_closedBall, dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have h1 : ((z - ((-a + (2 * k + 1) * w : ℝ) : ℂ)).re) ^ 2 ≤ w ^ 2 := by
    rw [sub_re, ofReal_re]
    exact sq_le_sq' (abs_le.1 hkw).1 (abs_le.1 hkw).2
  have h2 : ((z - ((-a + (2 * k + 1) * w : ℝ) : ℂ)).im) ^ 2 ≤ δ ^ 2 := by
    rw [sub_im, ofReal_im, sub_zero]
    exact sq_le_sq' (abs_le.1 him).1 (abs_le.1 him).2
  linarith

/-- **Thin sets attached to `ℝ` have small capacity**: if `A ⊆ [−a, a] × [−δ, δ]` then
`hcap(fill A) ≤ 2aδ + δ²` (cover by `⌈a/δ⌉` discs centred on `ℝ` and use subadditivity). -/
theorem hcapFill_le_of_subset_rect {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hsub : A ⊆ {z : ℂ | |z.re| ≤ a ∧ |z.im| ≤ δ}) :
    hcapFill A hA hc ≤ 2 * a * δ + δ ^ 2 := by
  set n := ⌈a / δ⌉₊ with hndef
  have hn : 0 < n := Nat.ceil_pos.2 (div_pos ha hδ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set w := a / n with hwdef
  set ρ := √(w ^ 2 + δ ^ 2) with hρdef
  set Y : ℕ → Set ℂ := fun k => closedBall (((-a + (2 * k + 1) * w : ℝ)) : ℂ) ρ with hYdef
  have hY : ∀ k, Bornology.IsBounded (Y k) := fun k => isBounded_closedBall
  have hcY : ∀ k, IsPreconnected (Y k ∪ {z : ℂ | z.im ≤ 0}) := fun k =>
    (convex_closedBall _ _).isPreconnected.union _ (mem_closedBall_self (Real.sqrt_nonneg _))
      (show (((-a + (2 * k + 1) * w : ℝ)) : ℂ).im ≤ 0 by simp) isPreconnected_lowerHalf
  obtain ⟨hb, hcU, hle⟩ := hcapFill_biUnion_range_le Y hY hcY n
  have hsubU : A ⊆ ⋃ k ∈ Finset.range n, Y k := fun z hz => by
    obtain ⟨k, hk, hzk⟩ := exists_mem_closedBall_grid ha hn (hsub hz).1 (hsub hz).2
    exact mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hk, hzk⟩
  have h1 := hcapFill_mono hsubU hA hc hb hcU
  have h3 : ∑ k ∈ Finset.range n, hcapFill (Y k) (hY k) (hcY k) ≤ n * ρ ^ 2 := by
    calc _ ≤ ∑ _k ∈ Finset.range n, ρ ^ 2 :=
          Finset.sum_le_sum fun k _ => hcapFill_le_sq_of_subset_closedBall _ _ subset_rfl
      _ = n * ρ ^ 2 := by simp
  have hρ : ρ ^ 2 = w ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hn1 : a / δ ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < a / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hwδ : w ≤ δ := by
    rw [hwdef, div_le_iff₀ hnpos]
    rw [div_le_iff₀ hδ] at hn1
    linarith
  have e1 : (n : ℝ) * w ^ 2 = a * w := by rw [hwdef]; field_simp
  have e2 : (n : ℝ) * δ ^ 2 ≤ a * δ + δ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hn2.le (sq_nonneg δ)
    have e : (a / δ + 1) * δ ^ 2 = a * δ + δ ^ 2 := by field_simp
    linarith
  have e3 : a * w ≤ a * δ := mul_le_mul_of_nonneg_left hwδ ha.le
  calc hcapFill A hA hc ≤ _ := h1
    _ ≤ _ := hle
    _ ≤ n * ρ ^ 2 := h3
    _ = n * w ^ 2 + n * δ ^ 2 := by rw [hρ]; ring
    _ ≤ 2 * a * δ + δ ^ 2 := by linarith

/-- The closed rectangle `[−a, a] × [0, δ]` (the set `S̄_δ` of the proof of Lemma 2.5,
Specification p. 24). -/
def rectH (a δ : ℝ) : Set ℂ := {z : ℂ | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ δ}

theorem isBounded_rectH (a δ : ℝ) : Bornology.IsBounded (rectH a δ) := by
  refine (isBounded_iff_forall_norm_le.2 ⟨|a| + |δ|, fun z hz => ?_⟩)
  have h1 : |z.re| ≤ |a| := hz.1.trans (le_abs_self a)
  have h2 : |z.im| ≤ |δ| := by
    rw [abs_of_nonneg hz.2.1]
    exact hz.2.2.trans (le_abs_self δ)
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

theorem isPreconnected_rectH_union (a δ : ℝ) :
    IsPreconnected (rectH a δ ∪ {z : ℂ | z.im ≤ 0}) := by
  have hconv : Convex ℝ (rectH a δ) := by
    have e : rectH a δ = {z : ℂ | |z.re| ≤ a} ∩ ({z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | z.im ≤ δ}) := rfl
    rw [e]
    refine Convex.inter ?_ ((convex_halfSpace_ge (f := fun z : ℂ => z.im)
      Complex.imLm.isLinear 0).inter (convex_halfSpace_le (f := fun z : ℂ => z.im)
      Complex.imLm.isLinear δ))
    have e2 : {z : ℂ | |z.re| ≤ a} = {z : ℂ | z.re ≤ a} ∩ {z : ℂ | -a ≤ z.re} := by
      ext z
      simp only [mem_ofPred_eq, mem_inter_iff, abs_le]
      tauto
    rw [e2]
    exact (convex_halfSpace_le (f := fun z : ℂ => z.re) Complex.reLm.isLinear a).inter
      (convex_halfSpace_ge (f := fun z : ℂ => z.re) Complex.reLm.isLinear (-a))
  rcases (rectH a δ).eq_empty_or_nonempty with h | ⟨z, hz⟩
  · rw [h, empty_union]
    exact isPreconnected_lowerHalf
  · refine IsPreconnected.union' ⟨(z.re : ℂ), ?_, show ((z.re : ℂ)).im ≤ 0 by simp⟩
      hconv.isPreconnected isPreconnected_lowerHalf
    refine ⟨by simpa using hz.1, by simp, ?_⟩
    simp only [ofReal_im]
    exact hz.2.1.trans hz.2.2

/-- **`hcap(S̄_δ) → 0` as `δ ↓ 0`** for the rectangles `S̄_δ = [−a, a] × [0, δ]` (Specification
p. 24, end of the proof of Lemma 2.5). -/
theorem tendsto_hcapFill_rectH (a : ℝ) :
    Tendsto (fun δ => hcapFill (rectH a δ) (isBounded_rectH a δ) (isPreconnected_rectH_union a δ))
      (𝓝[>] 0) (𝓝 0) := by
  set a' := |a| + 1 with ha'
  have ha' : 0 < a' := by positivity
  have hup : Tendsto (fun δ : ℝ => 2 * a' * δ + δ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => 2 * a' * δ + δ ^ 2) (𝓝 0) (𝓝 (2 * a' * 0 + 0 ^ 2)) :=
      ((continuous_const.mul continuous_id).add (continuous_pow 2)).tendsto 0
    rw [mul_zero, zero_add, zero_pow two_ne_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun δ => HPHull.hcap_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  refine hcapFill_le_of_subset_rect _ _ ha' hδ fun z hz => ⟨?_, ?_⟩
  · exact hz.1.trans (by linarith [le_abs_self a])
  · rw [abs_of_nonneg hz.2.1]
    exact hz.2.2

/-! ### Poisson representation of the capacity -/

section Poisson

open MeasureTheory
open scoped ENNReal Real

variable {A : Set ℂ} {g : ℂ → ℂ} {y₀ : ℝ}

/-- Points on or above the line `Im z = y₀` lie in `ℍ \ A` when `A ⊆ {Im < y₀}`, `y₀ > 0`. -/
theorem add_mul_I_mem_H_diff (hy₀ : 0 < y₀) (hAy : ∀ z ∈ A, z.im < y₀) {w : ℂ}
    (hw : 0 ≤ w.im) : w + y₀ * I ∈ H \ A := by
  have him : (w + y₀ * I).im = w.im + y₀ := by simp
  refine ⟨show 0 < (w + y₀ * I).im by rw [him]; linarith, fun h => ?_⟩
  have := hAy _ h
  rw [him] at this
  linarith

theorem IsMapOut.continuousAt {A : Set ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) {z : ℂ}
    (hz : z ∈ H \ A) : ContinuousAt g z :=
  (hg.1.1.differentiableAt (hA.isOpen.mem_nhds hz)).continuousAt

/-- `w ↦ Im((w + iy₀) − g(w + iy₀))` is continuous at every point of the closed half-plane
`Im w ≥ 0`. -/
theorem IsMapOut.continuousAt_im_sub_shift (hA : IsHPHull A) (hg : IsMapOut A g) (hy₀ : 0 < y₀)
    (hAy : ∀ z ∈ A, z.im < y₀) {w : ℂ} (hw : 0 ≤ w.im) :
    ContinuousAt (fun w : ℂ => (w + y₀ * I - g (w + y₀ * I)).im) w := by
  have hs : ContinuousAt (fun w : ℂ => w + y₀ * I) w := continuousAt_id.add continuousAt_const
  have hgs : ContinuousAt (fun w : ℂ => g (w + y₀ * I)) w :=
    ContinuousAt.comp (g := g) (hg.continuousAt hA (add_mul_I_mem_H_diff hy₀ hAy hw)) hs
  exact continuous_im.continuousAt.comp (hs.sub hgs)

/-- The boundary function `t ↦ Im((t + iy₀) − g(t + iy₀))` on the line `Im z = y₀` is
essentially bounded. -/
theorem IsMapOut.memLp_top_im_sub_line (hA : IsHPHull A) (hg : IsMapOut A g) (hy₀ : 0 < y₀)
    (hAy : ∀ z ∈ A, z.im < y₀) :
    MemLp (fun t : ℝ => ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im) ∞ (volume : Measure ℝ) := by
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  have hc : Continuous (fun t : ℝ => ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (hg.continuousAt_im_sub_shift hA hy₀ hAy (w := (t : ℂ)) (by simp)).comp
      continuous_ofReal.continuousAt
  refine memLp_top_of_bound hc.aestronglyMeasurable M (ae_of_all _ fun t => ?_)
  have h := hM _ (add_mul_I_mem_H_diff hy₀ hAy (w := (t : ℂ)) (by simp))
  rw [Real.norm_eq_abs]
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [← norm_neg, neg_sub]
  exact h

/-- **Poisson representation of `Im(z − g_A(z))`** above a horizontal line: if
`A ⊆ {Im < y₀}` (`y₀ > 0`) and `φ` is an `L^∞` representative of the boundary function
`t ↦ Im((t + iy₀) − g(t + iy₀))`, then `Im((w + iy₀) − g(w + iy₀)) = ∫ P(w, t) φ(t) dt` on `ℍ`
(both sides are bounded harmonic with the same continuous boundary values). -/
theorem IsMapOut.im_sub_eq_poissonIntegralH (hA : IsHPHull A) (hg : IsMapOut A g)
    (hy₀ : 0 < y₀) (hAy : ∀ z ∈ A, z.im < y₀) {φ : Lp ℝ ∞ (volume : Measure ℝ)}
    (hφ : ⇑φ =ᵐ[volume] fun t : ℝ => ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im) {w : ℂ}
    (hw : w ∈ H) : (w + y₀ * I - g (w + y₀ * I)).im = poissonIntegralH φ w := by
  set u : ℂ → ℝ := fun w => (w + y₀ * I - g (w + y₀ * I)).im with hudef
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  have hu : InnerProductSpace.HarmonicOnNhd u H := by
    intro w hw
    have hz := add_mul_I_mem_H_diff hy₀ hAy (w := w) (le_of_lt hw)
    have hgA := hg.1.1.analyticAt (hA.isOpen.mem_nhds hz)
    have hs : AnalyticAt ℂ (fun w : ℂ => w + y₀ * I) w := analyticAt_id.add analyticAt_const
    have hF : AnalyticAt ℂ (fun w : ℂ => w + y₀ * I - g (w + y₀ * I)) w :=
      hs.sub (AnalyticAt.comp (g := g) hgA hs)
    exact hF.harmonicAt_im
  have hub : Bornology.IsBounded (u '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h := hM _ (add_mul_I_mem_H_diff hy₀ hAy (w := w) (le_of_lt hw))
    rw [Real.norm_eq_abs]
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [← norm_neg, neg_sub]
    exact h
  have hPb : Bornology.IsBounded (poissonIntegralH φ '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖φ‖, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [Real.norm_eq_abs]
    exact abs_poissonIntegralH_le φ hw
  refine eqOn_of_tendsto_sub_H ∅ hu (harmonicOnNhd_poissonIntegralH φ) hub hPb
    (fun t _ => ?_) hw
  have hct := hg.continuousAt_im_sub_shift hA hy₀ hAy (w := (t : ℂ)) (by simp)
  have h1 : Tendsto u (𝓝[H] (t : ℂ)) (𝓝 (u t)) := hct.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_poissonIntegralH hφ (x := t)
    (hct.comp continuous_ofReal.continuousAt)
  have := h1.sub h2
  rw [sub_self] at this
  exact this

/-- The Poisson kernel on the imaginary axis: `y P(iy, t) = y² / (π (t² + y²))`. -/
theorem mul_poissonKernelH_mul_I (y t : ℝ) :
    y * poissonKernelH (y * I) t = y ^ 2 / (π * (t ^ 2 + y ^ 2)) := by
  have hn : ‖(y : ℂ) * I - t‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [PoissonH.norm_sub_ofReal_sq]
    simp
  rw [poissonKernelH, hn]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  ring

/-- **Poisson representation of the half-plane capacity** ([Law05] (3.5)–(3.6), in the form
of a horizontal line): if `A ⊆ {Im < y₀}` with `y₀ > 0`, the function
`t ↦ Im((t + iy₀) − g_A(t + iy₀))` is integrable on `ℝ` and
`hcap(A) = (1/π) ∫ Im((t + iy₀) − g_A(t + iy₀)) dt`. (By the Poisson representation,
`y Im(iy + iy₀ − g_A(iy + iy₀)) = ∫ y²/(π(t² + y²)) φ(t) dt`; the left side tends to `hcap(A)`, the
integrand increases to `φ(t)/π`, and monotone convergence applies.) -/
theorem HPHull.hcap_eq_integral (A : HPHull) {g : ℂ → ℂ} (hg : IsMapOut A.1 g) {y₀ : ℝ}
    (hy₀ : 0 < y₀) (hAy : ∀ z ∈ A.1, z.im < y₀) :
    Integrable (fun t : ℝ => ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im) ∧
      A.hcap = (∫ t : ℝ, ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im) / π := by
  set φf : ℝ → ℝ := fun t => ((t : ℂ) + y₀ * I - g ((t : ℂ) + y₀ * I)).im with hφfdef
  have hmem := hg.memLp_top_im_sub_line A.2 hy₀ hAy
  set φ := hmem.toLp φf with hφdef
  have hφ : ⇑φ =ᵐ[volume] φf := hmem.coeFn_toLp
  have hφm : AEStronglyMeasurable φf volume := hmem.aestronglyMeasurable
  have hφ0 : ∀ t, 0 ≤ φf t := by
    intro t
    have h := hg.im_le A.2 (add_mul_I_mem_H_diff hy₀ hAy (w := (t : ℂ)) (by simp))
    simp only [hφfdef, sub_im]
    linarith
  -- the Poisson representation on the imaginary axis
  have hrep : ∀ y : ℝ, 0 < y →
      y * ((y : ℂ) * I + y₀ * I - g ((y : ℂ) * I + y₀ * I)).im =
        ∫ t, y ^ 2 / (π * (t ^ 2 + y ^ 2)) * φf t := by
    intro y hy
    have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
    rw [IsMapOut.im_sub_eq_poissonIntegralH A.2 hg hy₀ hAy hφ hyH, poissonIntegralH,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hφ] with t ht
    rw [ht, ← mul_poissonKernelH_mul_I]
    ring
  have hint : ∀ y : ℝ, 0 < y → Integrable fun t => y ^ 2 / (π * (t ^ 2 + y ^ 2)) * φf t := by
    intro y hy
    have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
    have h := (integrable_poissonKernelH_mul hyH φ).const_mul y
    refine h.congr ?_
    filter_upwards [hφ] with t ht
    rw [ht, ← mul_poissonKernelH_mul_I]
    ring
  -- the left side tends to `hcap`
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) * I + y₀ * I - g ((((n : ℝ) + 1 : ℝ) : ℂ) * I + y₀ * I)).im)
      atTop (𝓝 A.hcap) := by
    have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1 + y₀) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop)
    have h1 := (A.tendsto_mul_sub_im hg).comp hs
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 1 + y₀)) atTop (𝓝 1) := by
      have h3 : Tendsto (fun n : ℕ => y₀ / ((n : ℝ) + 1 + y₀)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hs
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub h3
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      have hpos : (0 : ℝ) < (n : ℝ) + 1 + y₀ := by positivity
      field_simp
      ring
    have := h2.mul h1
    rw [one_mul] at this
    refine this.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 + y₀ := by positivity
    have e : (((n : ℝ) + 1 : ℝ) : ℂ) * I + y₀ * I = (((n : ℝ) + 1 + y₀ : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [Function.comp_apply]
    rw [e]
    have e2 : ((((n : ℝ) + 1 + y₀ : ℝ) : ℂ) * I - g ((((n : ℝ) + 1 + y₀ : ℝ) : ℂ) * I)).im =
        ((n : ℝ) + 1 + y₀) - (g ((((n : ℝ) + 1 + y₀ : ℝ) : ℂ) * I)).im := by
      simp
    rw [e2]
    field_simp
  -- monotone convergence
  set f : ℕ → ℝ → ENNReal := fun n t =>
    ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (π * (t ^ 2 + ((n : ℝ) + 1) ^ 2)) * φf t) with hfdef
  have hfm : ∀ n, AEMeasurable (f n) volume := fun n =>
    ((Continuous.aestronglyMeasurable (continuous_const.div (by fun_prop)
      fun t => by positivity)).mul hφm).aemeasurable.ennreal_ofReal
  have hmono : ∀ t, Monotone fun n => f n t := by
    intro t
    refine monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_right ?_ (hφ0 t)
    have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := pow_le_pow_left₀ ha.le hb 2
    nlinarith [sq_nonneg t, Real.pi_pos, mul_le_mul_of_nonneg_left h1 (sq_nonneg t)]
  have htend : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (ENNReal.ofReal (φf t / π))) := by
    intro t
    refine ENNReal.tendsto_ofReal ?_
    have hk : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 / (π * (t ^ 2 + ((n : ℝ) + 1) ^ 2)))
        atTop (𝓝 (1 / π)) := by
      have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ _
          tendsto_natCast_atTop_atTop)
      have h3 : Tendsto (fun n : ℕ => t ^ 2 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ hs)
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h3).div_const π
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      have hpos : 0 < t ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
      field_simp
      ring
    have := hk.mul_const (φf t)
    rw [one_div, inv_mul_eq_div] at this
    exact this
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hfm (ae_of_all _ hmono)
    (ae_of_all _ htend)
  have hval : ∀ n : ℕ, ∫⁻ t, f n t = ENNReal.ofReal (((n : ℝ) + 1) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) * I + y₀ * I - g ((((n : ℝ) + 1 : ℝ) : ℂ) * I + y₀ * I)).im) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hrep _ hpos, ofReal_integral_eq_lintegral_ofReal (hint _ hpos)
      (ae_of_all _ fun t => mul_nonneg (by positivity) (hφ0 t))]
  simp_rw [hval] at hMCT
  have hL : ∫⁻ t, ENNReal.ofReal (φf t / π) = ENNReal.ofReal A.hcap :=
    tendsto_nhds_unique hMCT (ENNReal.tendsto_ofReal hlim)
  have hfin : ∫⁻ t, ENNReal.ofReal (φf t / π) ≠ ⊤ := by rw [hL]; exact ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (fun t => ENNReal.ofReal (φf t / π)) volume :=
    (hφm.aemeasurable.div_const π).ennreal_ofReal
  have hint' : Integrable (fun t => φf t / π) := by
    refine (integrable_toReal_of_lintegral_ne_top hmeas hfin).congr (ae_of_all _ fun t => ?_)
    exact ENNReal.toReal_ofReal (div_nonneg (hφ0 t) Real.pi_pos.le)
  have hintφ : Integrable φf := by
    refine (hint'.const_mul π).congr (ae_of_all _ fun t => ?_)
    field_simp
  refine ⟨hintφ, ?_⟩
  rw [← integral_div, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun t => div_nonneg (hφ0 t) Real.pi_pos.le)
    (hφm.aemeasurable.div_const π).aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal A.hcap_nonneg]

end Poisson

/-! ### Hulls are their own fillings; the composition rule for fillings -/

/-- A compact `ℍ`-hull together with the lower half-plane is preconnected (every complementary
component of the simply connected `ℍ \ A` is unbounded, hence meets `{Im ≤ 0}`). -/
theorem IsHPHull.isPreconnected_union_lowerHalf {A : Set ℂ} (hA : IsHPHull A) :
    IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) := by
  have h0 : (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} := show (0 : ℂ).im ≤ 0 by simp
  refine isPreconnected_of_forall (0 : ℂ) fun y hy => ?_
  set Q := connectedComponentIn (A ∪ {z : ℂ | z.im ≤ 0}) y with hQdef
  have hQ : IsPreconnected Q := isPreconnected_connectedComponentIn
  have hQsub : Q ⊆ A ∪ {z : ℂ | z.im ≤ 0} := connectedComponentIn_subset _ _
  have hyQ : y ∈ Q := mem_connectedComponentIn hy
  obtain ⟨q, hqQ, hqL⟩ : (Q ∩ {z : ℂ | z.im ≤ 0}).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hQA : Q ⊆ A := by
      intro z hz
      rcases hQsub hz with h | h
      · exact h
      · exact absurd ⟨hz, h⟩ ((eq_empty_iff_forall_notMem.1 hne) z)
    have hyU : y ∉ H \ A := by
      rintro ⟨-, hyA⟩
      exact hyA (hQA hyQ)
    have hb := not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hA.isOpen
      hA.2.2.2 hyU
    rw [compl_H_diff] at hb
    exact hb (hA.2.1.subset hQA)
  refine ⟨Q ∪ {z : ℂ | z.im ≤ 0}, union_subset hQsub subset_union_right, Or.inr h0,
    Or.inl hyQ, hQ.union q hqQ hqL isPreconnected_lowerHalf⟩

/-- `closure A ∩ ℍ = A` for a compact `ℍ`-hull. -/
theorem IsHPHull.mem_of_mem_closure {A : Set ℂ} (hA : IsHPHull A) {z : ℂ} (hz : z ∈ H)
    (hzA : z ∈ closure A) : z ∈ A := by
  by_contra h
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hzA _ hA.isOpen ⟨hz, h⟩
  exact hw1.2 hw2

/-- **A compact `ℍ`-hull is its own filling.** -/
theorem IsHPHull.fillH_eq {A : Set ℂ} (hA : IsHPHull A) : fillH A = A := by
  ext z
  refine ⟨fun hz => ?_, fun hz => mem_fillH_of_mem_closure (hA.1 hz) (subset_closure hz)⟩
  rcases hz.2 with h | h
  · exact hA.mem_of_mem_closure hz.1 h
  · by_contra hzA
    have hcl : H \ closure A = H \ A := by
      ext w
      refine ⟨fun hw => ⟨hw.1, fun h' => hw.2 (subset_closure h')⟩,
        fun hw => ⟨hw.1, fun h' => hw.2 (hA.mem_of_mem_closure hw.1 h')⟩⟩
    rw [hcl] at h
    have hcc : connectedComponentIn (H \ A) z = H \ A :=
      hA.isConnected.isPreconnected.connectedComponentIn ⟨hz.1, hzA⟩
    rw [hcc] at h
    obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
    refine not_isBounded_setOf_lt_im R (h.subset fun w hw => ⟨?_, fun hwA => ?_⟩)
    · exact show 0 < w.im from hR.trans hw
    · have h1 := mem_ball_zero_iff.1 (hAR hwA)
      have h2 := Complex.abs_im_le_norm w
      have h3 : R < w.im := hw
      linarith [le_abs_self w.im]

/-- For a compact `ℍ`-hull, the capacity of its filling is its capacity. -/
theorem HPHull.hcapFill_eq (A : HPHull) :
    hcapFill A.1 A.2.2.1 A.2.isPreconnected_union_lowerHalf = A.hcap :=
  HPHull.hcap_congr A.2.fillH_eq

/-- **Subadditivity for compact `ℍ`-hulls**: `hcap(fill(A ∪ B)) ≤ hcap(A) + hcap(B)`. -/
theorem HPHull.hcapFill_union_le (A B : HPHull) :
    hcapFill (A.1 ∪ B.1) (A.2.2.1.union B.2.2.1)
        (isPreconnected_union_lowerHalf A.2.isPreconnected_union_lowerHalf
          B.2.isPreconnected_union_lowerHalf) ≤ A.hcap + B.hcap := by
  rw [← A.hcapFill_eq, ← B.hcapFill_eq]
  exact InteractingSLE.hcapFill_union_le _ _ _ _

/-- **The composition rule for fillings** ([Law05] (3.7); Specification p. 24, "map out `A`"):
`hcap(fill(A ∪ X)) = hcap(g(fill(A ∪ X) \ fill A)) + hcap(fill A)` for the mapping-out function
`g` of `fill A`. -/
theorem hcapFill_union_eq_add {A X : Set ℂ} (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hX : Bornology.IsBounded X)
    (hcX : IsPreconnected (X ∪ {z : ℂ | z.im ≤ 0})) {g : ℂ → ℂ} (hg : IsMapOut (fillH A) g) :
    hcapFill (A ∪ X) (hA.union hX) (isPreconnected_union_lowerHalf hcA hcX) =
      HPHull.hcap ⟨g '' (fillH (A ∪ X) \ fillH A),
        hg.isHPHull_image (isHPHull_fillH_of_isPreconnected hA hcA)
          (isHPHull_fillH_of_isPreconnected (hA.union hX)
            (isPreconnected_union_lowerHalf hcA hcX)) (fillH_mono subset_union_left)⟩ +
      hcapFill A hA hcA :=
  HPHull.hcap_eq_add (A := ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hcA⟩)
    (B := ⟨fillH (A ∪ X), isHPHull_fillH_of_isPreconnected (hA.union hX)
      (isPreconnected_union_lowerHalf hcA hcX)⟩) (fillH_mono subset_union_left) hg

end InteractingSLE
