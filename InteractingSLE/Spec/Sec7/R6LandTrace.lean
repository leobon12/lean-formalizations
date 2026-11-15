/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnLanding
import InteractingSLE.Spec.Supplement.Q3KernelTip
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# R.6: physical trace witnesses for force-mark landings

PROVE-R6-LANDING. A real inverse landing on the closed hull is a point of
its generating trace, by the existing boundary theorem for filled paths.
Transporting this fact through an injective initial boundary coordinate
identifies the physical landing with a visited point. The left force
landing minimizes the initial coordinate among real trace contacts.

Only committed dependencies are used. In particular, this file does not
import the concurrent `R6Fd` development or use Theorems 1.2--1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec7.R6Land

open WangWu (chartAL chartAR)

/-- A real inverse landing on the closed hull belongs to the generating
trace, including real contacts and multiply accessed trace points. -/
theorem real_landing_mem_trace {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {q x : ℝ} (hq : 0 ≤ q)
    (him : (extendFrom H (fwdMapInv W q) (x : ℂ)).im = 0)
    (hK : extendFrom H (fwdMapInv W q) (x : ℂ) ∈ closure (fwdHull W q)) :
    extendFrom H (fwdMapInv W q) (x : ℂ) ∈ η '' Icc 0 q := by
  have := R6Fc.neBot_nhdsWithin_H_real x
  have hlim := (hη.hasBdryLimits hW hW0 hq).tendsto (R6Fc.real_mem_Hbar x)
  have hcl : extendFrom H (fwdMapInv W q) (x : ℂ) ∈ closure (H \ fwdHull W q) :=
    mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz =>
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hq hz)
  have hfr : extendFrom H (fwdMapInv W q) (x : ℂ) ∈ frontier (H \ fwdHull W q) := by
    rw [(isHPHull_fwdHull hW hq).isOpen.frontier_eq]
    refine ⟨hcl, fun hz => ?_⟩
    have hpos : 0 < (extendFrom H (fwdMapInv W q) (x : ℂ)).im := hz.1
    exact (lt_irrefl (0 : ℝ)) (him ▸ hpos)
  rw [hη.2.2 q hq] at hK hfr
  exact YuanCharacterisation.mem_of_mem_closure_of_mem_frontier
    (hη.isCompact_image q).isClosed him hK hfr

/-- Pull a real closed-hull landing back to a visited physical point.
`P` may be the finite-pole boundary closure or the full finite closure
of a pocket whose outgoing pole is infinity. -/
theorem physical_landing_mem_trace {P : Set ℂ} {O : Chart} {ψ E₀ : ℂ → ℂ}
    {W : ℝ → ℝ} {η Γ : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q x : ℝ} (hq : 0 ≤ q)
    (hinj : InjOn ψ P) (hΓ : MapsTo Γ (Icc 0 q) P)
    (hcode : ∀ t ∈ Icc 0 q, η t = ψ (Γ t))
    (hE₀ : MapsTo E₀ Hbar P) (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar)
    (him : (extendFrom H (fwdMapInv W q) (x : ℂ)).im = 0)
    (hK : extendFrom H (fwdMapInv W q) (x : ℂ) ∈ closure (fwdHull W q)) :
    extendFrom H O.2.1 (x : ℂ) ∈ Γ '' Icc 0 q := by
  have hp : extendFrom H O.2.1 (x : ℂ) =
      E₀ (extendFrom H (fwdMapInv W q) (x : ℂ)) :=
    extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar x)
      (R6Fc.tendsto_of_extension hE hEc x)
  obtain ⟨t, ht, heq⟩ := real_landing_mem_trace hη hW hW0 hq him hK
  refine ⟨t, ht, ?_⟩
  rw [hp]
  apply hinj (hΓ ht) (hE₀ ((R6Fc.extendFrom_props hη hW hW0 hq).2.2 (R6Fc.real_mem_Hbar x)))
  rw [hcomp _ ((R6Fc.extendFrom_props hη hW hW0 hq).2.2 (R6Fc.real_mem_Hbar x)),
    ← hcode t ht]
  exact heq

/-- The physical left force landing is a visited point and minimizes
the initial real coordinate among all visited boundary contacts. -/
theorem physical_left_force_spec {P : Set ℂ} {O : Chart} {ψ E₀ : ℂ → ℂ}
    {W : ℝ → ℝ} {η Γ : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 < q)
    (hgap : chartAL W q < chartAR W q)
    (hinj : InjOn ψ P) (hΓ : MapsTo Γ (Icc 0 q) P)
    (hcode : ∀ t ∈ Icc 0 q, η t = ψ (Γ t))
    (hE₀ : MapsTo E₀ Hbar P) (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar) :
    extendFrom H O.2.1 (chartAL W q : ℂ) ∈ Γ '' Icc 0 q ∧
      IsLeast {y : ℝ | ∃ t ∈ Icc 0 q, (ψ (Γ t)).im = 0 ∧ y = (ψ (Γ t)).re}
        (ψ (extendFrom H O.2.1 (chartAL W q : ℂ))).re := by
  have hreal := (R6Tn.left_boundary_real_nonpos hη hW hW0 hq.le (le_refl (chartAL W q))).1
  have hK := Supp8.RelTrans.Icc_subset_hullImage hη hW hW0 hq hgap ⟨le_rfl, hgap.le⟩
  have hmem := physical_landing_mem_trace hη hW hW0 hq.le hinj hΓ hcode hE₀ hcomp hE hEc hreal hK
  have hcoord := R6Tn.initial_coord_left_force hη hW hW0 hq.le hcomp hE hEc
  refine ⟨hmem, ?_, ?_⟩
  · obtain ⟨t, ht, heq⟩ := hmem
    refine ⟨t, ht, ?_, ?_⟩
    · rw [heq, hcoord]
      exact hreal
    · rw [heq]
  · rintro y ⟨t, ht, him, rfl⟩
    have htK : η t ∈ closure (fwdHull W q) := by
      rcases ht.1.lt_or_eq with hpos | hzero
      · exact closure_mono (fwdHull_mono' ht.2)
          (Supp8.Q3Kernel.trace_mem_closure_fwdHull hη hW hW0 hpos)
      · rw [← hzero, hη.1]
        exact ConformalImageFull.zero_mem_closure_fwdHull hW hW0 hq
    have heq : (((ψ (Γ t)).re : ℝ) : ℂ) = η t := by
      rw [hcode t ht]
      apply Complex.ext
      · exact Complex.ofReal_re _
      · simpa only [Complex.ofReal_im] using him.symm
    rw [hcoord]
    exact (R6Tn.left_force_landing_isLeast hη hW hW0 hq hgap).2 (by
      change (((ψ (Γ t)).re : ℝ) : ℂ) ∈ closure (fwdHull W q)
      rwa [heq])

end InteractingSLE.Sec7.R6Land
