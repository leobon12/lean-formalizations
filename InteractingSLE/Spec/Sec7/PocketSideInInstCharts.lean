/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFaceAnchor
import InteractingSLE.Spec.Jordan.Chart

/-!
# The transition between two actual current pocket charts

PROVE-POCKET-SIDEIN. The transition is constructed from the two current
charts, including their inherited lifts. Physical containment proves its
conformality. Its coordinate mean identity is algebraic and does not equate
the two physical conditional means.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The inner chart written in the outer chart's current coordinate. The
derivative argument is the inherited difference in the same physical frame. -/
def pocketTransitionChart (outer inner : Chart) : Chart :=
  (fun z => inner.1 (outer.2.1 z), fun z => outer.1 (inner.2.1 z),
    fun z => inner.2.2 (outer.2.1 z) - outer.2.2 (outer.2.1 z))

/-- The complex inherited transition logarithm, formed from the two physical
chart logarithms before taking their imaginary parts. -/
def pocketTransitionLog (outer : Chart) (LOuter LInner : ℂ → ℂ) : ℂ → ℂ :=
  fun z => LInner (outer.2.1 z) - LOuter (outer.2.1 z)

/-- Physical inclusion of the two current domains gives a conformal
transition; it does not by itself assert any shared real interval. -/
theorem isConformal_pocketTransitionChart {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    (pocketTransitionChart outer inner).IsConformal := by
  refine ⟨hO.differentiableOn_fwd.comp hI.1
    (fun z hz => hCurrentInclusion (hI.inv_mem_dom hz)),
    fun z hz => hO.fwd_mem (hCurrentInclusion (hI.inv_mem_dom hz)), ?_⟩
  intro z hz
  change inner.1 (outer.2.1 (outer.1 (inner.2.1 z))) = z
  rw [hO.inv_fwd (hCurrentInclusion (hI.inv_mem_dom hz)), hI.2.2 z hz]

/-- The current transition domain is exactly the image of the current inner
domain, not the image of its initial pocket. -/
theorem dom_pocketTransitionChart {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    ((pocketTransitionChart outer inner).dom : Set ℂ) = outer.1 '' (inner.dom : Set ℂ) := by
  rw [(isConformal_pocketTransitionChart hO hI hCurrentInclusion).coe_dom, hI.coe_dom,
    image_image]
  rfl

/-- A transition point is precisely an outer coordinate of a point still
active in the inner pocket. -/
theorem mem_dom_pocketTransitionChart {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) {z : ℂ} :
    z ∈ (pocketTransitionChart outer inner).dom ↔ z ∈ H ∧ outer.2.1 z ∈ inner.dom := by
  change z ∈ ((pocketTransitionChart outer inner).dom : Set ℂ) ↔ _
  rw [dom_pocketTransitionChart hO hI hCurrentInclusion]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hO.fwd_mem (hCurrentInclusion hp), ?_⟩
    rw [hO.inv_fwd (hCurrentInclusion hp)]
    exact hp
  · rintro ⟨hz, hp⟩
    exact ⟨outer.2.1 z, hp, hO.2.2 z hz⟩

/-- Existing physical log/lift identities supply the transition's inherited
log identity; no new coordinate normalization is required. -/
theorem im_pocketTransitionLog {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) {LOuter LInner : ℂ → ℂ}
    (hOuterLift : ∀ p ∈ (outer.dom : Set ℂ), outer.2.2 p = (LOuter p).im)
    (hInnerLift : ∀ p ∈ (inner.dom : Set ℂ), inner.2.2 p = (LInner p).im) :
    ∀ z ∈ (pocketTransitionChart outer inner).dom,
      (pocketTransitionLog outer LOuter LInner z).im =
        (pocketTransitionChart outer inner).2.2 z := by
  intro z hz
  have hp := (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 hz
  change (LInner (outer.2.1 z) - LOuter (outer.2.1 z)).im =
    inner.2.2 (outer.2.1 z) - outer.2.2 (outer.2.1 z)
  rw [Complex.sub_im, hInnerLift _ hp.2, hOuterLift _ (hCurrentInclusion hp.2)]

/-- In two actual current domains cut by the same ambient hull, containment
of the initial physical pockets implies containment of the current domains.
The common-stop identities are still required at the selected visit. -/
theorem current_domain_inclusion_of_common_hull {outer inner : Chart}
    {C U F : Set ℂ} (hUC : U ⊆ C)
    (hOuterCurrent : (outer.dom : Set ℂ) = C ∩ (H \ F))
    (hInnerCurrent : (inner.dom : Set ℂ) = U ∩ (H \ F)) :
    (inner.dom : Set ℂ) ⊆ outer.dom := by
  rw [hOuterCurrent, hInnerCurrent]
  exact inter_subset_inter_left _ hUC

/-- The corrected-coordinate difference is exactly the physical conditional
mean difference. The deterministic mean and the inherited lift cancel,
while the two physical means remain distinct. -/
theorem sideMean_transition_sub {κ : ℝ} {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    (u vOuter vInner : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ (pocketTransitionChart outer inner).dom) :
    sideMean κ inner u vInner ((pocketTransitionChart outer inner).1 z) -
      sideMean κ outer u vOuter z - chiC κ * (pocketTransitionChart outer inner).2.2 z =
        vInner (outer.2.1 z) - vOuter (outer.2.1 z) := by
  have hp := (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 hz
  change (vInner (inner.2.1 (inner.1 (outer.2.1 z))) +
      u (inner.2.1 (inner.1 (outer.2.1 z))) +
      chiC κ * inner.2.2 (inner.2.1 (inner.1 (outer.2.1 z)))) -
    (vOuter (outer.2.1 z) + u (outer.2.1 z) + chiC κ * outer.2.2 (outer.2.1 z)) -
    chiC κ * (inner.2.2 (outer.2.1 z) - outer.2.2 (outer.2.1 z)) = _
  rw [hI.inv_fwd hp.2]
  ring

/-- A shared upper half-disc makes the preceding identity eventual at its
real centre. This discharges the coordinate-increment premise of phase transfer. -/
theorem eventually_sideMean_transition_sub {κ : ℝ} {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    (u vOuter vInner : ℂ → ℝ) {ξ r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ Metric.ball (ξ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ)) :
    ∀ᶠ z in 𝓝[H] (ξ : ℂ),
      sideMean κ inner u vInner ((pocketTransitionChart outer inner).1 z) -
        sideMean κ outer u vOuter z - chiC κ * (pocketTransitionChart outer inner).2.2 z =
          vInner (outer.2.1 z) - vOuter (outer.2.1 z) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (ξ : ℂ) hr)] with z hzH hzball
  exact sideMean_transition_sub hO hI hCurrentInclusion u vOuter vInner (hCollar ⟨hzH, hzball⟩)

end InteractingSLE.Sec7.PocketStopSide
