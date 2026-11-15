/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillFamily
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Compact boundary supports for proper prefix charts

A bounded interval of the continuous inverse boundary map contains every
nonreal frontier value. Its endpoints can be chosen on the real line.
The resulting compact path is a uniformly locally connected support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA.Topo (ULC)

namespace InteractingSLE.Theorem14.WalkIntExtend

open WalkIntCanon

/-- Compact boundary data suitable for the existing ULC extension theorem.
Only the part in H must lie in the hull; real connector values are allowed. -/
structure CompactBoundarySupport {c : Chart} (M : HullModel c) where
  carrier : Set ℂ
  compact : IsCompact carrier
  upper : carrier ⊆ Hbar
  ulc : ULC carrier
  attached : IsPreconnected ({z : ℂ | z.im = 0} ∪ carrier)
  frontier : frontier (H \ M.hull) ∩ H ⊆ carrier
  hull : carrier ∩ H ⊆ M.hull

/-- Properness supplies a compact continuous boundary path carrying every
frontier point in H, without any finiteness assumption on real contacts. -/
theorem exists_compactBoundarySupport {c : Chart} (M : HullModel c)
    (hc : c.IsConformal) (hproper : GW1P.HasProperBdryExt c) :
    Nonempty (CompactBoundarySupport M) := by
  obtain ⟨E, C, hE, hC⟩ := hproper
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 M.isHull.2.1
  let R : ℝ := max B 0 + max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hBC : B + C < R := by
    dsimp [R]
    have := le_max_left B 0
    have := le_max_left C 0
    linarith
  have hEc := GW1P.continuousOn_of_tendsto hE
  have hEH : ∀ p ∈ Hbar, E p ∈ Hbar := fun p hp =>
    GW1P.mem_Hbar_of_tendsto hp hc.2.1 (hE p hp)
  have hrealHull : ∀ x : ℝ, E x ∈ H → E x ∈ M.hull := by
    intro x hx
    have hn := Sec7.PocketStopSide.inverse_real_landing_notMem_dom hc
      (hE (x : ℂ) (by simp [Hbar]))
    by_contra hnot
    apply hn
    change E (x : ℂ) ∈ (c.dom : Set ℂ)
    rw [M.dom_eq]
    exact ⟨hx, hnot⟩
  have hparam : ∀ x : ℝ, E x ∈ H → |x| < R := by
    intro x hx
    have h1 := hB _ (hrealHull x hx)
    have h2 := hC (x : ℂ) (by simp [Hbar])
    have h3 := norm_le_norm_add_norm_sub' (x : ℂ) (E x)
    rw [norm_sub_rev] at h3
    simp only [norm_real, Real.norm_eq_abs] at h3
    linarith
  let γ : ℝ → ℂ := fun t => E ((t - R : ℝ) : ℂ)
  have hγc : ContinuousOn γ (Icc 0 (2 * R)) :=
    hEc.comp (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousOn
      (fun t _ => by simp [Hbar])
  have hγH : MapsTo γ (Icc 0 (2 * R)) Hbar := fun t _ =>
    hEH _ (by simp [Hbar])
  have hzero : (γ 0).im = 0 := by
    have hu := hγH (show (0 : ℝ) ∈ Icc 0 (2 * R) from ⟨le_rfl, by linarith⟩)
    have hn : γ 0 ∉ H := by
      intro hh
      have hb := hparam (-R) (by simpa [γ] using hh)
      rw [abs_neg, abs_of_pos hR] at hb
      exact (lt_irrefl R) hb
    exact le_antisymm (not_lt.1 hn) hu
  have hboundary : GW1RestartFinal.HasBoundaryRange c (γ '' Icc 0 (2 * R)) := by
    refine ⟨E, hE, fun p hpbar hp => ?_⟩
    by_cases hEp : E p ∈ H
    · left
      have hp0 : p.im = 0 := by
        exact le_antisymm (not_lt.1 hp) hpbar
      have hpr : (p.re : ℂ) = p := (eq_ofReal_re_of_im_eq_zero hp0).symm
      have hb := abs_lt.1 (hparam p.re (by rwa [hpr]))
      refine ⟨p.re + R, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [γ, add_sub_cancel_right, hpr]
    · exact Or.inr hEp
  refine ⟨⟨γ '' Icc 0 (2 * R), isCompact_Icc.image_of_continuousOn hγc,
    hγH.image_subset, ulc_image_Icc hγc, ?_, ?_, ?_⟩⟩
  · exact QuantumZipper.CA.Uniformizer.isPreconnected_setOf_im_eq_zero.union'
      ⟨γ 0, hzero, ⟨0, ⟨le_rfl, by linarith⟩, rfl⟩⟩
      (isPreconnected_Icc.image _ hγc)
  · rintro z ⟨hzfr, hzH⟩
    rw [← M.dom_eq, c.dom.isOpen.frontier_eq] at hzfr
    exact WalkLeaf.mem_of_frontier_dom hc ⟨E, C, hE, hC⟩ hboundary hzH hzfr.1 hzfr.2
  · rintro z ⟨⟨t, -, rfl⟩, hzH⟩
    exact hrealHull (t - R) hzH

end InteractingSLE.Theorem14.WalkIntExtend
