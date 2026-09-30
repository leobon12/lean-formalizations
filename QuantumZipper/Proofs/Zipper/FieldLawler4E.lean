import QuantumZipper.Proofs.Zipper.FieldLawler4EBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-E: the boundary-set hypotheses of `fl3Wd_FL3Unif_of_car` for the Loewner configuration

Setting: `γ` continuous and injective on `[0, t]`, `γ 0 = 0`, `γ((0, t]) ⊆ ℍ`, `|γ| < R` on
`[0, t)`, `|γ t| = R`, `K = γ([0, t])`; an open arc `η = C_ε(α, β)` (`0 < ε < R`,
`0 < α < β < π`) with end points in `K ∪ ℝ`; the frame `E = fl4eE γ t R ε α β`.
* `fl4eE_diff_preconnected`: `E \ {q}` is preconnected for every `q` (hypothesis `hE`);
* `fl4e_hcomp`: for an open `D ⊆ ℍ ∩ B(0, R)` disjoint from `E` which is a union of components
  of `U = (ℍ ∩ B(0, R)) \ (K ∪ closure η)`, every complementary component of `D` is unbounded
  (hypothesis `hcomp`).
Together with `fl4eE_isClosed`, `fl4eE_sub_closedBall`, `fl4eE_ulc` (FieldLawler4EBasic.lean)
these are the boundary-set hypotheses of `fl3Wd_FL3Unif_of_car` (Carathéodory, Pommerenke 1992,
Thm 2.6, p. 24). Own elementary point-set arguments (as in `flExist_loewner`,
FieldLawler3ExistLoew.lean); no published source states them for this configuration.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

variable {γ : ℝ → ℂ} {t R ε α β : ℝ}

/-- Every complementary component of `D` is unbounded, for `D` open, disjoint from `E`, inside
`ℍ ∩ B(0, R)`, and a union of components of `U = (ℍ ∩ B(0, R)) \ (K ∪ closure η)`.
Own elementary proof (as `flExist_loewner` and `flExist_compl_unbdd`). -/
theorem fl4e_hcomp (ht : 0 ≤ t) (hγc : ContinuousOn γ (Icc 0 t)) (hγ0 : γ 0 = 0)
    (hαβ : α < β)
    (hend : (ε : ℂ) * exp (α * I) ∈ γ '' Icc 0 t ∪ range ((↑) : ℝ → ℂ))
    {D : Set ℂ} (hDo : IsOpen D) (hDE : Disjoint D (fl4eE γ t R ε α β))
    (hDsub : D ⊆ H ∩ ball 0 R)
    (hDU : ∀ z ∈ D, connectedComponentIn
      ((H ∩ ball 0 R) \ (γ '' Icc 0 t ∪ closure (flCircArc ε α β))) z ⊆ D) :
    ∀ a ∉ D, ¬ Bornology.IsBounded (connectedComponentIn Dᶜ a) := by
  set K := γ '' Icc 0 t with hKdef
  set A := flClArc ε α β with hAdef
  set L := {z : ℂ | z.im ≤ 0} with hLdef
  rw [fl4e_closure_arc hαβ] at hDU
  set U := (H ∩ ball 0 R) \ (K ∪ A) with hUdef
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hγc
  have hAc : IsCompact A := isCompact_Icc.image (flClArc_cont ε)
  have hUo : IsOpen U := (isOpen_H.inter isOpen_ball).sdiff (hKc.isClosed.union hAc.isClosed)
  have hUb : Bornology.IsBounded U := isBounded_ball.subset fun z hz => hz.1.2
  have hDU' : D ⊆ U := by
    intro z hz
    refine ⟨hDsub hz, fun h => Set.disjoint_left.1 hDE hz ?_⟩
    rw [fl4eE, fl4e_closure_arc hαβ]
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  have hLH : ∀ z ∈ L, z ∉ H := fun z hz hH => by
    simp only [hLdef, mem_ofPred_eq] at hz
    exact absurd (hH : (0 : ℝ) < z.im) (not_lt.2 hz)
  have hΓ : IsPreconnected (K ∪ L) :=
    (isPreconnected_Icc.image γ hγc).union 0 ⟨0, ⟨le_rfl, ht⟩, hγ0⟩ (by simp [hLdef])
      flExist_lower_preconn
  have hΓU : K ∪ L ⊆ Uᶜ := by
    rintro z (hk | hl) hzU
    · exact hzU.2 (Or.inl hk)
    · exact hLH z hl hzU.1.1
  have hΓb : ¬ Bornology.IsBounded (K ∪ L) := fun h =>
    flExist_lower_unbdd (h.subset subset_union_right)
  have hendα : (ε : ℂ) * exp (α * I) ∈ K ∪ L := by
    rcases hend with h | ⟨x, hx⟩
    · exact Or.inl h
    · exact Or.inr (by rw [← hx]; simp [hLdef])
  have hcompU : ∀ a ∉ U, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Uᶜ ∧
      ¬ Bornology.IsBounded C := by
    intro a haU
    by_cases hKA : a ∈ K ∪ A
    · rcases hKA with hk | hc
      · exact ⟨K ∪ L, hΓ, Or.inl hk, hΓU, hΓb⟩
      · refine ⟨A ∪ (K ∪ L),
          (isPreconnected_Icc.image _ (flClArc_cont ε).continuousOn).union _
            ⟨α, left_mem_Icc.2 hαβ.le, rfl⟩ hendα hΓ, Or.inl hc, ?_,
          fun h => hΓb (h.subset subset_union_right)⟩
        exact union_subset (fun w hw hwU => hwU.2 (Or.inr hw)) hΓU
    · by_cases hH : a ∈ H
      · have hb : a ∉ ball 0 R := fun h => haU ⟨⟨hH, h⟩, hKA⟩
        have ha0 : a ≠ 0 := fun h => by simp [h, H] at hH
        refine ⟨_, flExist_ray_preconn a, ⟨1, show (1 : ℝ) ≤ 1 from le_rfl, by simp⟩, ?_,
          flExist_ray_unbdd ha0⟩
        rintro _ ⟨s, hs, rfl⟩ hwU
        have h1 := hwU.1.2
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
        rw [mem_ball, dist_zero_right, not_lt] at hb
        simp only [mem_Ici] at hs
        rw [abs_of_pos (by linarith)] at h1
        nlinarith [norm_nonneg a]
      · exact ⟨K ∪ L, hΓ, Or.inr (show a.im ≤ 0 from not_lt.1 hH), hΓU, hΓb⟩
  intro a haD
  suffices h : ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Dᶜ ∧
      ¬ Bornology.IsBounded C by
    obtain ⟨C, hC, haC, hCD, hCb⟩ := h
    exact fun hb => hCb (hb.subset (hC.subset_connectedComponentIn haC hCD))
  by_cases haU : a ∈ U
  · set V' := connectedComponentIn U a
    have hV'U : V' ⊆ U := connectedComponentIn_subset U a
    obtain ⟨b, hb⟩ : (frontier V').Nonempty := nonempty_frontier_iff.2
      ⟨⟨a, mem_connectedComponentIn haU⟩, fun h =>
        NormedSpace.unbounded_univ ℝ ℂ (hUb.subset (h ▸ hV'U))⟩
    have hbU : b ∉ U := by
      have := flExist_frontier_comp hUo a hb
      rw [hUo.frontier_eq] at this
      exact this.2
    obtain ⟨C, hC, hbC, hCU, hCb⟩ := hcompU b hbU
    have hdisj : Disjoint V' D := by
      rw [Set.disjoint_left]
      intro y hyV hyD
      apply haD
      refine hDU y hyD ?_
      rw [← connectedComponentIn_eq hyV]
      exact mem_connectedComponentIn haU
    have hdc : Disjoint (closure V') D := hdisj.closure_left hDo
    refine ⟨closure V' ∪ C, isPreconnected_connectedComponentIn.closure.union b
      (frontier_subset_closure hb) hbC hC, Or.inl (subset_closure (mem_connectedComponentIn haU)),
      union_subset (fun x hx hxD => Set.disjoint_left.1 hdc hx hxD)
        (hCU.trans (compl_subset_compl.2 hDU')),
      fun h => hCb (h.subset subset_union_right)⟩
  · obtain ⟨C, hC, haC, hCU, hCb⟩ := hcompU a haU
    exact ⟨C, hC, haC, hCU.trans (compl_subset_compl.2 hDU'), hCb⟩

end FieldLawler
end QuantumZipper
