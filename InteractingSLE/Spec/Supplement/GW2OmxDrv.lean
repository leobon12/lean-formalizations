/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil8
import InteractingSLE.Spec.Supplement.GW2SdmDrv
import InteractingSLE.Spec.Supplement.GB6LMeanChain

/-!
# GW2's open lines: the stage driver is the Brownian rescaling of the kernel's relative driver

Packet PROVE-GW2-STAGEMEAN, R120 round (the driver relation). Deterministic, per sample: with the stage-start dilation
`relMap (Uk, t₀) ∘ cL.1 = λ · cs.1`, the stage shape at every stage time `u ≤ t`, the launch union identity and the
kernel chain's hull identity (`HullsUpTo`), the two charts read the same domains at all stage times, so
(`GW2Sdm.driver_scale_of_domains`):

* **`sample_driver_scale`**: the stage driver equals `s ↦ Rk(λ² s)/λ` on `[0, Q]` (`Q` = the stage clock at `t`), and
  the kernel's relative clock at `t` is `λ² Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap relClock)
open Supp8.Q3Rel (invHull)

/-- **The stage driver is the Brownian rescaling of the kernel's relative driver.** -/
theorem sample_driver_scale {cL c₀ : Chart} (hconf : cL.IsConformal) (hc₀ : c₀.IsConformal) {R : ℝ≥0 → ℝ}
    (hR : Continuous R) (hR0 : R 0 = 0) {a₀ : ℝ≥0} {Uk : ℝ → ℝ} (hUk : Continuous Uk) (hUk0 : Uk 0 = 0)
    {t₀ : ℝ≥0} {lam : ℝ} (hlam : 0 < lam)
    (hdil : ∀ x ∈ ((GW2Rd.stgChart c₀ R a₀).dom : Set ℂ),
      relMap Uk t₀ (cL.1 x) = (lam : ℂ) * (GW2Rd.stgChart c₀ R a₀).1 x)
    {B : ℝ≥0 → Set ℂ} {t : ℝ≥0} {A : ℝ≥0 → ℝ≥0} (hA0 : A 0 = a₀) (hAa : ∀ u, a₀ ≤ A u)
    (hAc : ContinuousOn A (Icc 0 t))
    (hshape : ∀ u ≤ t, H \ B u = c₀.2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {KT : Set ℂ} (hdomL : (cL.dom : Set ℂ) = H \ KT) (hKB : ∀ u ≤ t, KT ⊆ B u)
    {Wc Rk : ℝ → ℝ} (hRk : Continuous Rk) (hRk0 : Rk 0 = 0)
    (hhull : ∀ u : ℝ≥0, u ≤ t → relMap Uk t₀ '' fwdHull Wc u = fwdHull Rk (relClock Uk t₀ Wc u))
    (hdisj : ∀ u : ℝ≥0, u ≤ t → fwdHull Wc u ⊆ H \ invHull Uk t₀)
    (hunion : ∀ u : ℝ≥0, u ≤ t → cL.1 '' (B u ∩ (cL.dom : Set ℂ)) = invHull Uk t₀ ∪ fwdHull Wc u) :
    EqOn (Ito.rpath (GW2Rd.stgDrv R a₀)) (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 ((A t : ℝ) - a₀)) ∧
      relClock Uk t₀ Wc t = lam ^ 2 * ((A t : ℝ) - a₀) := by
  have hcapnn : ∀ K : Set ℂ, 0 ≤ ConformalImage.hcapSet K := fun K => by
    unfold ConformalImage.hcapSet
    split_ifs
    · exact HPHull.hcap_nonneg _
    · exact le_rfl
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set ca := cL.trans (GW2JointKernel.jointChart Uk t₀) with hcadef
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart hc₀ hR hR0 a₀
  have hj := Supp8.Q3Rel.isDomainChart_rel hUk hUk0 t₀.coe_nonneg
  have hjc : (GW2JointKernel.jointChart Uk t₀).IsConformal := hj.isConformal
  have hca : ca.IsConformal := hconf.trans hjc
  have hjH : (GW2JointKernel.jointChart Uk t₀).2.1 '' H = H \ invHull Uk t₀ := by
    rw [← hjc.coe_dom, hjc.coe_dom, hj.image_eq]
  have hLH : cL.2.1 '' H = H \ KT := by rw [← hconf.coe_dom, hdomL]
  have hfwd : ∀ x ∈ cs.2.1 '' H, ca.1 x = (lam : ℂ) * cs.1 x := by
    intro x hx
    rw [← hcs.coe_dom] at hx
    exact hdil x hx
  have hS : Continuous (Ito.rpath (GW2Rd.stgDrv R a₀)) :=
    (GW2Rd.continuous_stgDrv hR a₀).comp continuous_real_toNNReal
  have hS0 : Ito.rpath (GW2Rd.stgDrv R a₀) 0 = 0 := by simp [Ito.rpath, GW2Rd.stgDrv_zero]
  -- the two charts read the same complement at every stage time
  have hsame : ∀ u : ℝ≥0, u ≤ t →
      cs.2.1 '' (H \ fwdHull (Ito.rpath (GW2Rd.stgDrv R a₀)) ((A u : ℝ) - a₀)) =
        ca.2.1 '' (H \ fwdHull Rk (relClock Uk t₀ Wc u)) := by
    intro u hu
    have hAu : ((A u : ℝ) - a₀) = ((A u - a₀ : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub (hAa u)]
    have hstg := GW2Rd.stgChart_inv_image c₀ hR hR0 a₀ (A u - a₀)
    rw [add_tsub_cancel_of_le (hAa u)] at hstg
    rw [hAu, hstg, ← hshape u hu]
    -- the kernel side
    have e1 : ca.2.1 '' (H \ fwdHull Rk (relClock Uk t₀ Wc u)) =
        cL.2.1 '' ((GW2JointKernel.jointChart Uk t₀).2.1 '' (H \ fwdHull Rk (relClock Uk t₀ Wc u))) := by
      rw [Set.image_image]
      rfl
    rw [e1, ← hhull u hu]
    have e2 : (GW2JointKernel.jointChart Uk t₀).2.1 '' (H \ relMap Uk t₀ '' fwdHull Wc u) =
        (H \ invHull Uk t₀) \ fwdHull Wc u :=
      Supp8.RelSafeS.image_inv_compl_image_fwd hjc hjH (hdisj u hu)
    rw [e2]
    have e3 : (H \ invHull Uk t₀) \ fwdHull Wc u = H \ cL.1 '' (B u ∩ (cL.dom : Set ℂ)) := by
      rw [hunion u hu]
      ext z
      simp only [Set.mem_sdiff, Set.mem_union]
      tauto
    rw [e3]
    have hKsub : B u ∩ (cL.dom : Set ℂ) ⊆ H \ KT := by
      rw [← hdomL]
      exact inter_subset_right
    rw [Supp8.RelSafeS.image_inv_compl_image_fwd hconf hLH hKsub]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hzH, hzB⟩
      exact ⟨⟨hzH, fun h => hzB (hKB u hu h)⟩, fun h => hzB h.1⟩
    · rintro ⟨⟨hzH, hzK⟩, hzB⟩
      refine ⟨hzH, fun h => hzB ⟨h, ?_⟩⟩
      rw [hdomL]
      exact ⟨hzH, hzK⟩
  -- every stage clock value is reached
  have hD : ∀ q ∈ Icc (0 : ℝ) ((A t : ℝ) - a₀), ∃ q' : ℝ, 0 ≤ q' ∧
      cs.2.1 '' (H \ fwdHull (Ito.rpath (GW2Rd.stgDrv R a₀)) q) = ca.2.1 '' (H \ fwdHull Rk q') := by
    intro q hq
    have hq' : A 0 ≤ (a₀ + q.toNNReal) ∧ a₀ + q.toNNReal ≤ A t := by
      refine ⟨by rw [hA0]; exact le_self_add, ?_⟩
      have : (q.toNNReal : ℝ) ≤ (A t : ℝ) - a₀ := by
        rw [Real.coe_toNNReal _ hq.1]
        exact hq.2
      have h2 : ((a₀ + q.toNNReal : ℝ≥0) : ℝ) ≤ A t := by
        push_cast
        linarith
      exact_mod_cast h2
    obtain ⟨u, hu, hAu⟩ := intermediate_value_Icc (zero_le (a := t)) hAc hq'
    have hqA : q = (A u : ℝ) - a₀ := by
      rw [hAu]
      push_cast
      rw [Real.coe_toNNReal _ hq.1]
      ring
    refine ⟨relClock Uk t₀ Wc u, ?_, ?_⟩
    · exact div_nonneg (hcapnn _) (by norm_num)
    · rw [hqA]
      exact hsame u hu.2
  have hQ : (0 : ℝ) ≤ (A t : ℝ) - a₀ := sub_nonneg.2 (by exact_mod_cast hAa t)
  refine ⟨GW2Sdm.driver_scale_of_domains hcs hca hlam hfwd hS hS0 hRk hRk0 hQ hD, ?_⟩
  -- the relative clock at `t`
  have hmem := GW2Sdm.mem_fwdHull_iff_of_chart_dilation hcs hca hlam hfwd (hsame t le_rfl)
  exact GW2Sdm.time_eq_of_mem_iff hS hS0 hRk hRk0 hlam hQ
    (div_nonneg (hcapnn _) (by norm_num)) hmem

end InteractingSLE.Theorem14.GW2Omx
