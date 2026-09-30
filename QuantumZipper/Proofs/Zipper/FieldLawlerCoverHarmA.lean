import QuantumZipper.Proofs.Zipper.FieldLawlerCover
import QuantumZipper.Proofs.Thm18.LWHarmCross
import QuantumZipper.Proofs.Complex.UniformizerComp
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: topology of `H_η` (unbounded component of `ℍ \ η`) and the map `z ↦ 1/(z + i)`

Inputs of `FieldLawlerCoverHarm.lean` (existence of harmonic measure in `H_η`):
* `flH_hullComp_eq`: `hullComp η` is a single connected component of `ℍ \ η` (all unbounded
  components contain the connected set `ℍ \ B̄(0, M)`), hence preconnected;
* `flH_compl_unbounded`: every component of `(hullComp η)ᶜ` is unbounded (as in
  `lwCrosscutJordanStmt_of_jct`: bounded components of `ℍ \ η` are glued along a frontier point to
  the connected unbounded set `{Im ≤ 0} ∪ η̄`);
* elementary facts on `flMob z = (z + i)⁻¹` (maps `ℍ̄` into `B̄(0,1)`, `ℝ` onto the circle
  `|w + i/2| = 1/2` minus `0`).
Own elementary arguments (standard plane topology; the analogous bounded-part facts are in
`Thm18/LWHarmJordan.lean`).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- `hullComp η` is the connected component of `ℍ \ η` containing a far point. -/
theorem flH_hullComp_eq {η : ℝ → ℂ} (hη : IsCrosscutH η) :
    ∃ p₀ ∈ hullComp η, hullComp η = connectedComponentIn (H \ arcH η) p₀ := by
  obtain ⟨M₀, hM₀⟩ := (lwExc_arc_isBounded hη).exists_norm_le
  set M := |M₀| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg _
  set S := H \ arcH η with hSdef
  set O := flCoverOuter (0 : ℂ) M with hOdef
  have hOS : O ⊆ S := by
    intro z hz
    have hz' := flCoverOuter_norm hM0 hz
    refine ⟨by simpa [H] using hz'.2, fun hza => ?_⟩
    have := le_trans (hM₀ z hza) (le_abs_self M₀)
    simp at hz'
    linarith [hz'.1]
  have hfar : ∀ w ∈ S, M < ‖w‖ → w ∈ O := fun w hw hwM =>
    flCoverOuter_mem (a := 0) hw.1 (by simpa using hwM)
  set p₀ : ℂ := ((M + 1 : ℝ) : ℂ) * I with hp₀
  have hp₀S : p₀ ∈ S := by
    refine ⟨by simp [H, hp₀]; linarith, fun hza => ?_⟩
    have h1 := le_trans (hM₀ p₀ hza) (le_abs_self M₀)
    have h2 : ‖p₀‖ = M + 1 := by
      rw [hp₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    linarith
  have hp₀O : p₀ ∈ O := hfar p₀ hp₀S (by
    rw [hp₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]; linarith)
  have hOC : O ⊆ connectedComponentIn S p₀ :=
    (flCoverOuter_isPreconnected 0 M).subset_connectedComponentIn hp₀O hOS
  have hCunb : ¬ Bornology.IsBounded (connectedComponentIn S p₀) := fun hb =>
    flCoverOuter_unbounded 0 M (hb.subset hOC)
  refine ⟨p₀, ⟨hp₀S, hCunb⟩, ?_⟩
  ext z
  constructor
  · rintro ⟨hzS, hzu⟩
    have : ¬ connectedComponentIn S z ⊆ closedBall 0 M := fun h =>
      hzu (isBounded_closedBall.subset h)
    obtain ⟨w, hwC, hwM⟩ := not_subset.1 this
    have hwS : w ∈ S := connectedComponentIn_subset _ _ hwC
    have hwM' : M < ‖w‖ := by simpa [mem_closedBall, dist_zero_right] using hwM
    have hwp : w ∈ connectedComponentIn S p₀ := hOC (hfar w hwS hwM')
    rw [connectedComponentIn_eq hwp, ← connectedComponentIn_eq hwC]
    exact mem_connectedComponentIn hzS
  · intro hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hCunb

/-- Every component of `(hullComp η)ᶜ` is unbounded. -/
theorem flH_compl_unbounded {η : ℝ → ℂ} {a b : ℝ} (hη : IsCrosscutH η)
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) :
    ∀ a' ∉ hullComp η, ¬ Bornology.IsBounded (connectedComponentIn (hullComp η)ᶜ a') := by
  set S := H \ arcH η with hSdef
  set U := hullComp η with hUdef
  have hSo : IsOpen S := lwExc_isOpen_H_diff_arc hη
  have hUo : IsOpen U := lwExc_hullComp_isOpen hη
  have hUS : U ⊆ S := fun z hz => hz.1
  set E₀ : Set ℂ := {z : ℂ | z.im ≤ 0} ∪ lwArcExt η a b '' Icc 0 1 with hE₀def
  have ha0 : lwArcExt η a b 0 = a := by simp [lwArcExt]
  have hE₀c : IsPreconnected E₀ := by
    refine IsPreconnected.union (a : ℂ) (by simp) ⟨0, ⟨le_rfl, zero_le_one⟩, ha0⟩
      (convex_halfSpace_im_le 0).isPreconnected
      (isPreconnected_Icc.image _ (lwArcExt_contOn hη ha hb))
  have hE₀S : E₀ ⊆ Sᶜ := by
    rintro z (hz | ⟨t, ht, rfl⟩) hzS
    · have : (0 : ℝ) < z.im := hzS.1
      simp only [mem_setOf_eq] at hz
      linarith
    · unfold lwArcExt at hzS
      split_ifs at hzS with h0 h1'
      · have : (0 : ℝ) < ((a : ℂ)).im := hzS.1
        simp at this
      · have : (0 : ℝ) < ((b : ℂ)).im := hzS.1
        simp at this
      · exact hzS.2 ⟨t, ⟨not_le.1 h0, not_le.1 h1'⟩, rfl⟩
  have hE₀U : E₀ ⊆ Uᶜ := fun z hz hzU => hE₀S hz (hUS hzU)
  have hE₀u : ¬ Bornology.IsBounded E₀ := fun hb' =>
    Uniformizer.not_isBounded_lowerHalf (hb'.subset subset_union_left)
  have hSc : Sᶜ ⊆ E₀ := by
    intro z hz
    by_cases hH : z ∈ H
    · have harc : z ∈ arcH η := by
        by_contra h; exact hz ⟨hH, h⟩
      obtain ⟨s, hs, rfl⟩ := harc
      right
      exact ⟨s, Ioo_subset_Icc_self hs, (lwArcExt_mem (a := a) (b := b) hη hs).1⟩
    · left
      exact not_lt.1 (show ¬ (0 < z.im) from hH)
  intro a' ha'
  by_cases h1 : a' ∈ S
  · set C := connectedComponentIn S a' with hCdef
    have hCb : Bornology.IsBounded C := by
      by_contra hC; exact ha' ⟨h1, hC⟩
    have hCo : IsOpen C := hSo.connectedComponentIn
    have hCne : C.Nonempty := ⟨a', mem_connectedComponentIn h1⟩
    have hCuniv : C ≠ univ := fun h => Uniformizer.not_isBounded_lowerHalf
      (hCb.subset (by rw [h]; exact subset_univ _))
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.2 ⟨hCne, hCuniv⟩
    have hqS : q ∉ S := by
      intro hqS
      have hqC : q ∈ closure C := frontier_subset_closure hq
      obtain ⟨y, hyq, hyC⟩ := mem_closure_iff.1 hqC _ hSo.connectedComponentIn
        (mem_connectedComponentIn hqS)
      have e1 := connectedComponentIn_eq hyq
      have e2 := connectedComponentIn_eq hyC
      have : q ∈ C := by
        rw [hCdef, e2, ← e1]; exact mem_connectedComponentIn hqS
      rw [hCo.frontier_eq] at hq
      exact hq.2 this
    have hqE : q ∈ E₀ := hSc hqS
    have hCU : closure C ⊆ Uᶜ := by
      intro z hz hzU
      obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.1 hz U hUo hzU
      have e2 := connectedComponentIn_eq hyC
      exact hyU.2 (by rw [← e2]; exact hCb)
    have hT : IsPreconnected (closure C ∪ E₀) :=
      IsPreconnected.union q (frontier_subset_closure hq) hqE
        isPreconnected_connectedComponentIn.closure hE₀c
    exact Uniformizer.not_isBounded_of_subset hT
      (Or.inl (subset_closure (mem_connectedComponentIn h1)))
      (union_subset hCU hE₀U) fun hb' => hE₀u (hb'.subset subset_union_right)
  · exact Uniformizer.not_isBounded_of_subset hE₀c (hSc h1) hE₀U hE₀u

/-- The Möbius map `z ↦ 1/(z + i)` and its inverse `w ↦ 1/w − i`. -/
def flMob (z : ℂ) : ℂ := (z + I)⁻¹

/-- Inverse of `flMob`. -/
def flMobInv (w : ℂ) : ℂ := w⁻¹ - I

lemma flMobInv_flMob {z : ℂ} : flMobInv (flMob z) = z := by
  simp [flMob, flMobInv]

lemma flMob_flMobInv {w : ℂ} : flMob (flMobInv w) = w := by
  simp [flMob, flMobInv]

lemma flMob_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : flMob z ≠ 0 :=
  inv_ne_zero (add_I_ne_zero_of_im_nonneg hz)

lemma flMob_norm_le {z : ℂ} (hz : 0 ≤ z.im) : ‖flMob z‖ ≤ 1 := by
  have h1 : 1 ≤ ‖z + I‖ := by
    have := Complex.abs_im_le_norm (z + I)
    simp at this
    linarith [le_abs_self (z.im + 1)]
  rw [flMob, norm_inv]
  exact inv_le_one_of_one_le₀ h1

lemma flMob_norm_lt {z : ℂ} (hz : 0 < z.im) : ‖flMob z‖ < 1 := by
  have h1 : 1 < ‖z + I‖ := by
    have := Complex.abs_im_le_norm (z + I)
    simp at this
    linarith [le_abs_self (z.im + 1)]
  rw [flMob, norm_inv]
  exact inv_lt_one_of_one_lt₀ h1

/-- Real points go to the circle `|w + i/2| = 1/2`. -/
lemma flMob_real_mem_sphere (x : ℝ) : flMob x ∈ sphere (-I / 2) (1 / 2) := by
  have hne : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have e : flMob x - (-I / 2) = I * ((x : ℂ) - I) / (2 * ((x : ℂ) + I)) := by
    rw [flMob]; field_simp; ring_nf; simp [Complex.I_sq]; ring
  have hc : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
    rw [← Complex.norm_conj ((x : ℂ) + I)]; simp [map_add, Complex.conj_ofReal, sub_eq_add_neg]
  rw [mem_sphere, dist_eq_norm, e, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, hc]
  have : ‖(x : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.2 hne
  simp only [RCLike.norm_ofNat]
  field_simp

/-- Points of the circle `|w + i/2| = 1/2` other than `0` come from real points. -/
lemma flMobInv_im_of_sphere {w : ℂ} (hw : w ∈ sphere (-I / 2) (1 / 2)) (hw0 : w ≠ 0) :
    (flMobInv w).im = 0 := by
  rw [mem_sphere, dist_eq_norm] at hw
  have h2 : Complex.normSq (w - -I / 2) = 1 / 4 := by
    rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  have hn : Complex.normSq w ≠ 0 := by simpa using hw0
  rw [Complex.normSq_apply] at h2 hn
  simp at h2
  have hq : w.re * w.re + w.im * w.im = - w.im := by nlinarith [h2]
  have him : w.im ≠ 0 := fun h => hn (by rw [hq, h, neg_zero])
  rw [flMobInv, sub_im, inv_im, Complex.normSq_apply, I_im, hq, div_self (neg_ne_zero.2 him)]
  ring

end FieldLawler
end QuantumZipper
