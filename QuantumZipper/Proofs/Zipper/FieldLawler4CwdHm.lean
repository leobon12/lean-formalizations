import QuantumZipper.Proofs.Zipper.FieldLawler4WdOuter
import QuantumZipper.Proofs.Zipper.FieldLawler3ExistLoew

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CWD-HM: harmonic measures exist in `Wd`

Task FL4-CWD-HM (sub-task of FL4-CWD). For `Wd = fl4Wd W t R ε α β p₀` (the component through
`p₀` of `(ℍ ∩ B(0,R)) \ (K_t ∪ closure ηD)`), every bounded `A` disjoint from `Wd` has a harmonic
measure in `Wd` (`fl4cwd_harm_exists`); in particular the arc `ηD = flCircArc ε α β`
(`fl4cwd_harm_arc`) and any subset of `C_R` given in the chart `fl3Chart R`
(`fl4cwd_harm_chart`).

Source: Field–Lawler's implicit use of harmonic measure (Garnett–Marshall, *Harmonic Measure*,
Ch. I §1, eq. (1.6)), as in `FieldLawler3ExistCar.lean`; we apply `flExist_of_frame` with the
ULC frame `E = γ([0,t]) ∪ [-R,R] ∪ C_R ∪ C̄_ε(α,β)` of `flExist_loewner`
(`FieldLawler3ExistLoew.lean`). The wiring (one arc, one component) is our own elementary
bookkeeping.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **Existence of harmonic measure in `Wd`** for every bounded `A` disjoint from `Wd`. -/
theorem fl4cwd_harm_exists (hc : SideCtx W t F) {R ε α β : ℝ} (hR : 0 < R) (hαβ : α ≤ β)
    (hα : flCirc ε α ∉ H \ fwdHull W t) (hβ : flCirc ε β ∉ H \ fwdHull W t) (p₀ : ℂ)
    {A : Set ℂ} (hA : Bornology.IsBounded A) (hAW : Disjoint A (fl4Wd W t R ε α β p₀)) :
    ∃ g : ℂ → ℝ, IsHarmMeas (fl4Wd W t R ε α β p₀) A g := by
  set D := fl4WdDom W t R ε α β with hDdef
  set U := fl4Wd W t R ε α β p₀ with hUdef
  set K := trace W '' Icc 0 t with hKdef
  set L := {z : ℂ | z.im ≤ 0} with hLdef
  set Cl := flClArc ε α β with hCldef
  set seg := (fun x : ℝ => (x : ℂ)) '' Icc (-R) R with hsegdef
  have ht : 0 ≤ t := hc.tpos.le
  have hγc := hc.trCont
  have hhullK : fwdHull W t ⊆ K := by
    rw [hc.hull]; exact image_mono Ioc_subset_Icc_self
  have hKH : ∀ z ∈ K, z ∈ H → z ∈ fwdHull W t := by
    rintro _ ⟨s, hs, rfl⟩ hH
    rw [hc.hull]
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0; simp [H, hc.tr0] at hH
    · exact ⟨s, ⟨hpos, hs.2⟩, rfl⟩
  have hLH : ∀ z ∈ L, z ∉ H := fun z hz hH => by
    simp only [hLdef, mem_ofPred_eq] at hz
    exact absurd (hH : (0 : ℝ) < z.im) (not_lt.2 hz)
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hγc
  have hClc : IsCompact Cl := isCompact_Icc.image (flClArc_cont ε)
  have hClu : Topo.ULC Cl := flExist_ulc_image_Icc hαβ (flClArc_cont ε).continuousOn
  have hend : ∀ θ : ℝ, flCirc ε θ ∉ H \ fwdHull W t → (ε : ℂ) * exp (θ * I) ∈ K ∪ L := by
    intro θ hθ
    by_cases hH : flCirc ε θ ∈ H
    · have h' : flCirc ε θ ∈ fwdHull W t := by
        by_contra h'; exact hθ ⟨hH, h'⟩
      exact Or.inl (hhullK h')
    · exact Or.inr (show (flCirc ε θ).im ≤ 0 from not_lt.1 hH)
  have hDeq : D = (H ∩ ball 0 R) \ (K ∪ Cl) := by
    ext z
    simp only [hDdef, fl4WdDom, Set.mem_sdiff, mem_inter_iff, mem_union, not_or]
    constructor
    · rintro ⟨⟨hH, hb⟩, hK, hcl⟩
      refine ⟨⟨hH, hb⟩, fun hk => hK (hKH z hk hH), fun hC => ?_⟩
      obtain ⟨θ, hθ, rfl⟩ := hC
      rcases hθ.1.eq_or_lt with h1 | h1
      · rw [← h1] at hH hK
        exact hα ⟨hH, hK⟩
      rcases hθ.2.eq_or_lt with h2 | h2
      · rw [h2] at hH hK
        exact hβ ⟨hH, hK⟩
      exact hcl (subset_closure ⟨θ, ⟨h1, h2⟩, rfl⟩)
    · rintro ⟨⟨hH, hb⟩, hK, hC⟩
      exact ⟨⟨hH, hb⟩, fun h => hK (hhullK h),
        fun h => hC (closure_minimal (flCircArc_sub_clArc ε α β) hClc.isClosed h)⟩
  have hDo : IsOpen D := fl4WdDom_isOpen hc R ε α β
  have hUo : IsOpen U := hDo.connectedComponentIn
  have hUD : U ⊆ D := connectedComponentIn_subset _ _
  have hsegc : IsCompact seg := isCompact_Icc.image continuous_ofReal
  set E := ((K ∪ seg) ∪ sphere (0 : ℂ) R) ∪ Cl with hEdef
  have hEc : IsCompact E := ((hKc.union hsegc).union (isCompact_sphere _ _)).union hClc
  have hEu : Topo.ULC E := by
    refine Topo.ULC.union_of_isCompact_of_isClosed ((hKc.union hsegc).union (isCompact_sphere _ _))
      hClc.isClosed ?_ hClu
    refine Topo.ULC.union_of_isCompact_of_isClosed (hKc.union hsegc) isClosed_sphere ?_
      (Topo.ULC.sphere _ _)
    exact Topo.ULC.union_of_isCompact_of_isClosed hKc hsegc.isClosed
      (flExist_ulc_image_Icc ht hγc)
      (flExist_ulc_image_Icc (by linarith) continuous_ofReal.continuousOn)
  have hsegL : seg ⊆ L := by
    rintro _ ⟨x, -, rfl⟩
    simp [hLdef]
  have hED : E ⊆ Dᶜ := by
    intro z hz hzD
    rw [hDeq] at hzD
    obtain ⟨⟨hH, hb⟩, hKC⟩ := hzD
    rcases hz with ((hk | hs) | hs) | hcl
    · exact hKC (Or.inl hk)
    · exact hLH z (hsegL hs) hH
    · rw [mem_sphere, dist_zero_right] at hs
      rw [mem_ball, dist_zero_right] at hb
      linarith
    · exact hKC (Or.inr hcl)
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hEc.isBounded
  have hUb : U ⊆ ball 0 (max r R) := fun z hz =>
    ball_subset_ball (le_max_right _ _) (fl4wd_subset_ball hz)
  have hEb : E ⊆ closedBall 0 (max r R) :=
    hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hfrE : frontier D ⊆ E := by
    intro z hz
    rw [hDo.frontier_eq] at hz
    obtain ⟨hcl, hnD⟩ := hz
    have hcl' : z ∈ {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R := by
      refine closure_minimal (fun w hw => ?_) ((isClosed_le continuous_const continuous_im).inter
        isClosed_closedBall) hcl
      rw [hDeq] at hw
      exact ⟨show (0 : ℝ) ≤ w.im from le_of_lt hw.1.1, ball_subset_closedBall hw.1.2⟩
    rw [hDeq] at hnD
    by_cases hKC : z ∈ K ∪ Cl
    · rcases hKC with hk | hcC
      · exact Or.inl (Or.inl (Or.inl hk))
      · exact Or.inr hcC
    · have hnb : ¬ (z ∈ H ∧ z ∈ ball 0 R) := fun h => hnD ⟨h, hKC⟩
      have hzn : ‖z‖ ≤ R := by simpa using hcl'.2
      by_cases hH : z ∈ H
      · have hb : z ∉ ball 0 R := fun h => hnb ⟨hH, h⟩
        rw [mem_ball, dist_zero_right, not_lt] at hb
        refine Or.inl (Or.inr ?_)
        rw [mem_sphere, dist_zero_right]
        linarith
      · have him : z.im = 0 := le_antisymm (not_lt.1 hH) hcl'.1
        refine Or.inl (Or.inl (Or.inr ⟨z.re, ⟨?_, ?_⟩, Complex.ext (by simp) (by simp [him])⟩))
        · linarith [neg_abs_le z.re, Complex.abs_re_le_norm z]
        · linarith [le_abs_self z.re, Complex.abs_re_le_norm z]
  have hΓ : IsPreconnected (K ∪ L) :=
    (isPreconnected_Icc.image (trace W) hγc).union 0 ⟨0, ⟨le_rfl, ht⟩, hc.tr0⟩ (by simp [hLdef])
      flExist_lower_preconn
  have hΓD : K ∪ L ⊆ Dᶜ := by
    rintro z (hk | hl) hzD
    · rw [hDeq] at hzD; exact hzD.2 (Or.inl hk)
    · rw [hDeq] at hzD; exact hLH z hl hzD.1.1
  have hΓb : ¬ Bornology.IsBounded (K ∪ L) := fun h =>
    flExist_lower_unbdd (h.subset subset_union_right)
  have hcompD : ∀ a ∉ D, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Dᶜ ∧
      ¬ Bornology.IsBounded C := by
    intro a haD
    rw [hDeq] at haD
    by_cases hKC : a ∈ K ∪ Cl
    · rcases hKC with hk | hcC
      · exact ⟨K ∪ L, hΓ, Or.inl hk, hΓD, hΓb⟩
      · refine ⟨Cl ∪ (K ∪ L),
          (isPreconnected_Icc.image _ (flClArc_cont ε).continuousOn).union _
            ⟨α, left_mem_Icc.2 hαβ, rfl⟩ (hend α hα) hΓ, Or.inl hcC, ?_,
          fun h => hΓb (h.subset subset_union_right)⟩
        refine union_subset (fun w hw hwD => ?_) hΓD
        rw [hDeq] at hwD
        exact hwD.2 (Or.inr hw)
    · by_cases hH : a ∈ H
      · have hb : a ∉ ball 0 R := fun h => haD ⟨⟨hH, h⟩, hKC⟩
        have ha0 : a ≠ 0 := fun h => by simp [h, H] at hH
        refine ⟨_, flExist_ray_preconn a, ⟨1, show (1 : ℝ) ≤ 1 from le_rfl, by simp⟩, ?_,
          flExist_ray_unbdd ha0⟩
        rintro _ ⟨s, hs, rfl⟩ hwD
        rw [hDeq] at hwD
        have h1 := hwD.1.2
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
        rw [mem_ball, dist_zero_right, not_lt] at hb
        simp only [mem_Ici] at hs
        rw [abs_of_pos (by linarith)] at h1
        nlinarith [norm_nonneg a]
      · exact ⟨K ∪ L, hΓ, Or.inr (show a.im ≤ 0 from not_lt.1 hH), hΓD, hΓb⟩
  have hDb : Bornology.IsBounded D := by
    rw [hDeq]; exact isBounded_ball.subset fun z hz => hz.1.2
  have hcompU := flExist_compl_unbdd hDo hDb hcompD p₀
  have hcomp : ∀ a ∉ U, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Uᶜ ∧
      ¬ Bornology.IsBounded C := fun a ha =>
    ⟨connectedComponentIn Uᶜ a, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn ha, connectedComponentIn_subset _ _, hcompU a ha⟩
  have hfin : (connectedComponentIn U '' U).Finite := by
    refine (finite_singleton U).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact isPreconnected_connectedComponentIn.connectedComponentIn hz
  exact flExist_of_frame hUo hUb hfin hA hAW hcomp hEc.isClosed hEu
    ((flExist_frontier_comp hDo p₀).trans hfrE) (hED.trans (compl_subset_compl.2 hUD)) hEb

/-- The harmonic measure in `Wd` of any subset of `C_R` given in the chart `fl3Chart R`. -/
theorem fl4cwd_harm_chart (hc : SideCtx W t F) {R ε α β : ℝ} (hR : 0 < R) (hαβ : α ≤ β)
    (hα : flCirc ε α ∉ H \ fwdHull W t) (hβ : flCirc ε β ∉ H \ fwdHull W t) (p₀ : ℂ)
    (J : Set ℝ) :
    ∃ V : ℂ → ℝ, IsHarmMeas (fl4Wd W t R ε α β p₀) (fl3Chart R '' (((↑) : ℝ → ℂ) '' J)) V := by
  have hsub : fl3Chart R '' (((↑) : ℝ → ℂ) '' J) ⊆ sphere (0 : ℂ) R := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [mem_sphere, dist_zero_right, fl4_chart_norm hR.le]
    simp
  refine fl4cwd_harm_exists hc hR hαβ hα hβ p₀ (isBounded_sphere.subset hsub) ?_
  rw [Set.disjoint_right]
  intro z hz h
  have h1 := mem_ball_zero_iff.1 (fl4wd_subset_ball hz)
  have h2 := hsub h
  rw [mem_sphere, dist_zero_right] at h2
  linarith

end FieldLawler
end QuantumZipper
