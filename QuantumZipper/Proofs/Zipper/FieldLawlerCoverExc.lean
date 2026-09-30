import QuantumZipper.Proofs.Thm18.LWExc2Refl
import QuantumZipper.Proofs.Zipper.FieldLawlerCover
import QuantumZipper.Proofs.Thm18.LWExc3Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: the excursion lower bound `ℰ_ℍ(η, [0,∞)) ≥ c (diam η ∧ 1)`, normalized

**Source.** Field–Lawler, arXiv:1407.3314, proof of Prop. 3.1 (p. 7):
`ℰ_ℍ(η, ℝ₋) ≥ c (diam η / dist(0, η) ∧ 1)`, which FL take from their Corollary 5.2 (pp. 12–13).
We prove it in the normalization `η(0+) = −1`, `η(1−) = b < 0` (so the half-line is `[0, ∞)`)
by following the proof of **Lawler–Werness Lemma 4.3** (LW p. 24) already formalized in
`Thm18/LWExc3Key.lean` (`lw3_circle`, `lw3_outer`: `h_η(z) ≥ c₀ r Im z / |z + 1|²` outside
`B̄(−1, r)` for a radius `r ≍ diam η ∧ 1/2`), which does not use `diam η ≤ 1/2` except to put the
half-disks over `[0, ∞)` inside `H_η`. That membership is `flExc_halfDisk` below (own elementary
argument: a thin rectangle over `[x, x + M + 1]` misses `closure η` and meets the connected
unbounded set `ℍ \ B̄(0, M)`), which replaces LW's `diam η ≤ 1/2` and yields FL's `∧ 1` regime.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Half-disks over `[0, ∞)` lie in `H_η`** when both endpoints of `η` are negative. -/
theorem flExc_halfDisk {η : ℝ → ℂ} {b : ℝ} (hη : IsCrosscutH η)
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ))) (h1 : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) (hb : b < 0)
    {x : ℝ} (hx : 0 ≤ x) : ∃ r : ℝ, 0 < r ∧ H ∩ ball (x : ℂ) r ⊆ hullComp η ∧
      ∀ w ∈ ball (x : ℂ) r, w.im = 0 → w ∉ closure (arcH η) := by
  set K := closure (arcH η) with hKdef
  obtain ⟨M₀, hM₀⟩ := (lwExc_arc_isBounded hη).exists_norm_le
  set M := |M₀| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg _
  have hMK : ∀ z ∈ arcH η, ‖z‖ ≤ M := fun z hz => le_trans (hM₀ z hz) (le_abs_self _)
  set S : Set ℂ := (fun s : ℝ => (s : ℂ)) '' Icc x (x + M + 1) with hSdef
  have hSc : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hSK : S ⊆ Kᶜ := by
    rintro _ ⟨s, hs, rfl⟩
    exact lw3_real_not_mem_closure hη h0 h1 (by simp)
      (fun he => by have := congrArg Complex.re he; simp at this; linarith [hs.1])
      (fun he => by have := congrArg Complex.re he; simp at this; linarith [hs.1])
  obtain ⟨δ, hδ, hδS⟩ := hSc.exists_thickening_subset_open isClosed_closure.isOpen_compl hSK
  set e := min (δ / 2) 1 with hedef
  have he0 : 0 < e := lt_min (by linarith) one_pos
  have heδ : e ≤ δ / 2 := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  -- the thin rectangle `P`
  set P : Set ℂ := {z | x - e < z.re} ∩ {z | z.re < x + M + 1} ∩ {z | 0 < z.im} ∩ {z | z.im < e}
    with hPdef
  have hPconv : Convex ℝ P :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      (convex_halfSpace_im_gt _) |>.inter (convex_halfSpace_im_lt _)
  have hPK : ∀ z ∈ P, z ∉ K := by
    rintro z ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    simp only [mem_ofPred_eq] at h1' h2' h3' h4'
    set s := max x z.re
    have hsS : (s : ℂ) ∈ S := ⟨s, ⟨le_max_left _ _, max_le (by linarith) h2'.le⟩, rfl⟩
    have hre : |z.re - s| < e := by
      rcases le_total x z.re with hxz | hxz
      · simp [s, max_eq_right hxz]; exact he0
      · rw [show s = x from max_eq_left hxz, abs_lt]; constructor <;> linarith
    have hd : dist z (s : ℂ) < δ := by
      rw [dist_eq_norm]
      have := norm_le_abs_re_add_abs_im (z - (s : ℂ))
      simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at this
      rw [abs_of_pos h3'] at this
      linarith
    exact hδS (mem_thickening_iff.2 ⟨_, hsS, hd⟩)
  have hPH : P ⊆ H := fun z hz => hz.1.2
  -- the outer region and the connecting point
  set O := flCoverOuter (0 : ℂ) M with hOdef
  have hOS : O ⊆ H \ arcH η := by
    intro z hz
    have hz' := flCoverOuter_norm hM0 hz
    refine ⟨by simpa [H] using hz'.2, fun hza => ?_⟩
    have := hMK z hza
    simp at hz'
    linarith [hz'.1]
  set p₀ : ℂ := ((x + M + 1 / 2 : ℝ) : ℂ) + ((e / 2 : ℝ) : ℂ) * I with hp₀
  have hp₀re : p₀.re = x + M + 1 / 2 := by simp [hp₀]
  have hp₀im : p₀.im = e / 2 := by simp [hp₀]
  have hp₀P : p₀ ∈ P := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp only [mem_ofPred_eq, hp₀re, hp₀im] <;> linarith
  have hp₀O : p₀ ∈ O := by
    refine flCoverOuter_mem (a := 0) (show 0 < p₀.im by rw [hp₀im]; linarith) ?_
    have := Complex.re_le_norm p₀
    simp only [ofReal_zero, sub_zero]
    rw [hp₀re] at this
    linarith
  have hU : IsPreconnected (P ∪ O) :=
    hPconv.isPreconnected.union p₀ hp₀P hp₀O (flCoverOuter_isPreconnected 0 M)
  have hUS : P ∪ O ⊆ H \ arcH η := by
    rintro z (hz | hz)
    · exact ⟨hPH hz, fun hza => hPK z hz (subset_closure hza)⟩
    · exact hOS hz
  refine ⟨e, he0, ?_, ?_⟩
  · intro z ⟨hzH, hzB⟩
    have hzH' : 0 < z.im := hzH
    rw [mem_ball, dist_eq_norm] at hzB
    have hr := (abs_lt.1 (lt_of_le_of_lt (Complex.abs_re_le_norm (z - x)) hzB))
    have hi := lt_of_le_of_lt (Complex.abs_im_le_norm (z - x)) hzB
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hr hi
    have hzP : z ∈ P := by
      refine ⟨⟨⟨?_, ?_⟩, hzH'⟩, ?_⟩ <;> simp only [mem_ofPred_eq]
      · linarith [hr.1]
      · linarith [hr.2]
      · linarith [le_abs_self z.im]
    have hcc := hU.subset_connectedComponentIn (Or.inl hzP) hUS
    exact ⟨hUS (Or.inl hzP), fun hbd =>
      flCoverOuter_unbounded (0 : ℂ) M (hbd.subset (subset_union_right.trans hcc))⟩
  · intro w hw _
    have hxS : (x : ℂ) ∈ S := ⟨x, ⟨le_rfl, by linarith⟩, rfl⟩
    exact hδS (mem_thickening_iff.2 ⟨_, hxS, by rw [mem_ball] at hw; linarith⟩)

end FieldLawler
end QuantumZipper
