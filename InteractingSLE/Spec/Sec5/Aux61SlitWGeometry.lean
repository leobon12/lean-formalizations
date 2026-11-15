/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmCover

/-!
# Rational comparison hulls cover the physical slit

Packet PROVE-AUX61-SLITW. A point of the fresh slit has a rational later own time
strictly before the current stop. Injectivity and compactness remove the tail
from a small ball. The physical force-word extension has the basic heights on
the two sides of each comparison hull, by CONFIG's geometric-mark theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open Aux61Conf2 Aux61Asm Aux61Fib

/-- Nonnegative rational own times, indexed by all rationals. -/
def rationalTime (q : ℚ) : ℝ≥0 := (q : ℝ).toNNReal

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ}
  {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}

/-- The marked complement geometry forces the part of the union inside the
retained component to lie on the fresh physical slit. -/
theorem inter_domain_subset_trace (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
    {A : Set ℂ} (hgeo : H \ A = c.2.1 '' (H \ fwdHull w t)) :
    A ∩ D ⊆ η '' Icc 0 (r + τ) := by
  intro z hz
  have hzdom := hg.mem_dom hz.2
  have hzc : c.1 z ∈ H := hg.conf.fwd_mem hzdom
  have hzK : c.1 z ∈ fwdHull w t := by
    by_contra hzK
    have hzout : z ∈ H \ A := by
      rw [hgeo]
      exact ⟨c.1 z, ⟨hzc, hzK⟩, hg.conf.inv_fwd hzdom⟩
    exact hzout.2 hz.1
  rw [hg.hull] at hzK
  obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := hzK
  have hηdom := hg.mem_dom (hg.cont u hu)
  have he' : η (r + u) = z := by
    rw [← hg.conf.inv_fwd hηdom, ← hg.conf.inv_fwd hzdom, he]
  exact ⟨r + u, ⟨(add_pos hg.rpos hu.1).le, add_le_add le_rfl hu.2⟩, he'⟩

/-- The rational comparison hulls give the slit cover required by the mean identification. -/
theorem exists_rational_comparison (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
    {A : Set ℂ} (hAH : A ⊆ H) (hAD : A ∩ D ⊆ η '' Icc 0 (r + τ))
    {u : ℝ} (hu : u ∈ Ioo 0 τ) :
    ∃ q : ℚ, r + u < (rationalTime q : ℝ) ∧ (rationalTime q : ℝ) < r + τ ∧
      η (r + u) ∈ fwdHull Wph (rationalTime q) ∧
      ∃ ε > 0, A ∩ ball (η (r + u)) ε ⊆ fwdHull Wph (rationalTime q) := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r + u < r + τ by linarith only [hu.2])
  have hq0 : 0 ≤ (q : ℝ) := (add_pos hg.rpos hu.1).le.trans hq1.le
  have htime : (rationalTime q : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
  have htip : η (r + u) ∈ H := hg.mem_H _ ⟨add_pos hg.rpos hu.1, by linarith only [hu.2]⟩
  have hsub : η '' Icc 0 (q : ℝ) ∩ H ⊆ fwdHull Wph (q : ℝ) := by
    intro z hz
    rw [hg.trace.2.2 _ hq0]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure hz.1)
  obtain ⟨ε, hε, hball⟩ := Aux61TwoS.exists_ball_inter_subset_curve (ρ := (q : ℝ)) hg.isOpen_D
    (hg.cont u ⟨hu.1, hu.2.le⟩) (hg.trace.2.1.mono (fun _ hz => hq0.trans hz.1)) hg.inj
    (add_pos hg.rpos hu.1).le hq1 hq2.le hAD
  refine ⟨q, by rwa [htime], by rwa [htime], ?_, ε, hε, ?_⟩
  · rw [htime]
    exact hsub ⟨⟨r + u, ⟨(add_pos hg.rpos hu.1).le, hq1.le⟩, rfl⟩, htip⟩
  · rw [htime]
    exact fun z hz => hsub ⟨hball hz, hAH hz.1⟩

/-- All the comparison cover and height clauses of `GluedSlitFacts` follow from
the physical hulls and their force-word extensions. -/
theorem gluedSlitFacts_of_bhe {s : FibCode} {q : ℝ≥0}
    (hg : IsGluedSlit Wph η r τ c D (fun u : ℝ => s.driver u.toNNReal) γ Tc q)
    {κ : ℝ} {A : Set ℂ} (hAH : A ⊆ H) (hAD : A ∩ D ⊆ η '' Icc 0 (r + τ))
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {uph : ℚ → ℂ → ℝ}
    (hb : ∀ j, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (Restart.FlowStopIdentCMI.geomL Wph (rationalTime j) ∘ xL)
        (Restart.FlowStopIdentCMI.geomR Wph (rationalTime j) ∘ xR))
      (forceJumpSet (Restart.FlowStopIdentCMI.geomL Wph (rationalTime j) ∘ xL)
        (Restart.FlowStopIdentCMI.geomR Wph (rationalTime j) ∘ xR)) (uph j)) :
    GluedSlitFacts κ s q Wph η r τ c D γ Tc
      (fun j => (rationalTime j : ℝ)) (fun j => fwdHull Wph (rationalTime j)) A
      (fun j => couplingMean κ Wph (rationalTime j) (uph j)) uph := by
  refine ⟨hg, fun u hu => exists_rational_comparison hg hAH hAD hu, fun _ _ _ => rfl, ?_, ?_⟩
  · intro j
    exact (tendsto_bhe_of_mem hg.trace hg.hW hg.hW0 (rationalTime j).coe_nonneg hxL hxR (hb j)).1
  · intro j
    exact (tendsto_bhe_of_mem hg.trace hg.hW hg.hW0 (rationalTime j).coe_nonneg hxL hxR (hb j)).2

end InteractingSLE.Sec5.Aux61SlitW
