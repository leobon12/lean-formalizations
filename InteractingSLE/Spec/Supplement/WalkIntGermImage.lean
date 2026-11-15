/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.R6RefPhase
import Mathlib.Analysis.Complex.OpenMapping

/-!
# A reflected boundary interval contains an image half-disc

PROVE-T14-WALKINT continuation. Real-boundary conformality gives a full
upper half-disc in the image near each real boundary value. This uses the
existing open mapping theorem and the signs of Schwarz reflection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real
open QuantumZipper (H)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Theorem14.WalkIntGerm

/-- The image of an incident upper half-disc contains an upper half-disc
about its central real boundary value. -/
theorem exists_halfdisc_subset_image {φ : ℂ → ℂ} {x r : ℝ}
    (h : R16.IsRealBoundaryConformal φ x r) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      H ∩ ball (φ (x : ℂ)) δ ⊆ φ '' (H ∩ ball (x : ℂ) r) := by
  have hx : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hd := h.differentiableOn_schwarzReflect
  have ha := hd.analyticOnNhd isOpen_ball (x : ℂ) hx
  have hne : deriv (schwarzReflect φ) (x : ℂ) ≠ 0 := by
    intro he
    have hp := (h.deriv_schwarzReflect_pos hx).2
    rw [he, zero_re] at hp
    exact (lt_irrefl 0) hp
  have hopen : 𝓝 (schwarzReflect φ (x : ℂ)) ≤
      map (schwarzReflect φ) (𝓝 (x : ℂ)) := by
    refine ha.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro he
    have heq : schwarzReflect φ =ᶠ[𝓝 (x : ℂ)]
        fun _ => schwarzReflect φ (x : ℂ) := he
    have hz := heq.deriv_eq
    simp only [deriv_const] at hz
    exact hne hz
  have himage : schwarzReflect φ '' ball (x : ℂ) r ∈
      𝓝 (schwarzReflect φ (x : ℂ)) :=
    hopen (image_mem_map (ball_mem_nhds (x : ℂ) hr))
  have hbase : schwarzReflect φ (x : ℂ) = φ (x : ℂ) := by simp [schwarzReflect]
  rw [hbase] at himage
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 himage
  refine ⟨δ, hδ, ?_⟩
  rintro w ⟨hwH, hwb⟩
  obtain ⟨z, hzb, he⟩ := hsub hwb
  have hzH : z ∈ H := by
    change 0 < z.im
    rcases lt_trichotomy z.im 0 with hn | hz | hp
    · have hi := (h.im_schwarzReflect hzb).2.2 hn
      rw [he] at hi
      exact (not_lt_of_ge (le_of_lt hwH) hi).elim
    · have hi := (h.im_schwarzReflect hzb).2.1 hz
      rw [he] at hi
      exact (ne_of_gt hwH hi).elim
    · exact hp
  refine ⟨z, ⟨hzH, hzb⟩, ?_⟩
  simpa only [schwarzReflect, show 0 ≤ z.im from le_of_lt hzH,
    ite_true] using he

end InteractingSLE.Theorem14.WalkIntGerm
