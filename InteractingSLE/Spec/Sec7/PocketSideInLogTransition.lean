/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInLogExtension
import InteractingSLE.Spec.Sec7.Lemma71OLocal

/-!
# The actual current transition carries the inherited analytic logarithm

PROVE-POCKET-SIDEIN. Physical derivative logarithms give the transition
logarithm by the analytic chain rule. The constructed boundary extension
therefore has the actual transition lift, rather than a newly chosen branch.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The difference of the physical chart logarithms is an analytic
derivative logarithm of the constructed current transition. -/
theorem isDerivLog_pocketTransitionLog {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {LOuter LInner : ℂ → ℂ}
    (hLO : IsDerivLog outer.1 LOuter outer.dom)
    (hLI : IsDerivLog inner.1 LInner inner.dom) :
    IsDerivLog (pocketTransitionChart outer inner).1
      (pocketTransitionLog outer LOuter LInner) (pocketTransitionChart outer inner).dom := by
  have hT := isConformal_pocketTransitionChart hO hI hCurrentInclusion
  have hm : MapsTo outer.2.1 ((pocketTransitionChart outer inner).dom : Set ℂ)
      (inner.dom : Set ℂ) := fun z hz =>
    (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 hz |>.2
  have hi := hO.1.mono hT.dom_subset
  refine ⟨(hLI.1.comp hi hm).sub (hLO.1.comp hi (fun z hz => hCurrentInclusion (hm hz))), ?_⟩
  intro z hz
  have hzH := hT.dom_subset hz
  have hpI := hm hz
  have hpO := hCurrentInclusion hpI
  have hdI := hI.differentiableOn_fwd.differentiableAt (inner.dom.isOpen.mem_nhds hpI)
  have hdi := hO.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hzH)
  have hne : deriv outer.1 (outer.2.1 z) ≠ 0 := by
    rw [← hLO.2 _ hpO]
    exact exp_ne_zero _
  have hmul := Lemma71O.deriv_fwd_mul_deriv_inv hO hzH
  change exp (LInner (outer.2.1 z) - LOuter (outer.2.1 z)) =
    deriv (inner.1 ∘ outer.2.1) z
  rw [exp_sub, hLI.2 _ hpI, hLO.2 _ hpO, deriv_comp z hdI hdi, div_eq_iff hne]
  calc
    deriv inner.1 (outer.2.1 z) =
        deriv inner.1 (outer.2.1 z) * (deriv outer.1 (outer.2.1 z) * deriv outer.2.1 z) := by
      rw [hmul, mul_one]
    _ = _ := by ring

/-- For two actual current charts, a reflected shared side supplies all
boundary-log conditions needed by R.6. The two physical lift identities
ensure that the extension retains precisely the current inherited lift. -/
theorem exists_current_pocket_log_extension {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {LOuter LInner : ℂ → ℂ}
    (hLO : IsDerivLog outer.1 LOuter outer.dom)
    (hLI : IsDerivLog inner.1 LInner inner.dom)
    (hOuterLift : ∀ p ∈ (outer.dom : Set ℂ), outer.2.2 p = (LOuter p).im)
    (hInnerLift : ∀ p ∈ (inner.dom : Set ℂ), inner.2.2 p = (LInner p).im)
    {G : ℂ → ℂ}
    (hExtensionEq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hReflect : ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) :
    ∃ Lbar : ℂ → ℂ,
      EqOn Lbar (pocketTransitionLog outer LOuter LInner) (pocketTransitionChart outer inner).dom ∧
      (∀ z ∈ (pocketTransitionChart outer inner).dom,
        (Lbar z).im = (pocketTransitionChart outer inner).2.2 z) ∧
      ContinuousOn (fun x : ℝ => Lbar x) J ∧
      (∀ x ∈ J, ContinuousWithinAt Lbar Hbar (x : ℂ)) ∧
      (∀ x ∈ J, exp (Lbar x) = deriv (schwarzReflect G) x) := by
  obtain ⟨Lbar, heq, hc, hbar, hexp⟩ := exists_inherited_log_extension
    (isConformal_pocketTransitionChart hO hI hCurrentInclusion)
    (isDerivLog_pocketTransitionLog hO hI hCurrentInclusion hLO hLI)
    hExtensionEq hJo hCollars hReflect
  refine ⟨Lbar, heq, ?_, ?_, hbar, hexp⟩
  · intro z hz
    rw [heq hz]
    exact im_pocketTransitionLog hO hI hCurrentInclusion hOuterLift hInnerLift z hz
  · exact hc.comp continuous_ofReal.continuousOn (fun x hx => Or.inr (mem_image_of_mem _ hx))

end InteractingSLE.Sec7.PocketStopSide
