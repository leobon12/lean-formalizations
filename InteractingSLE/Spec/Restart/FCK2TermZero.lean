/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermChart
import InteractingSLE.Spec.Sec7.Lemma71BStop
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Spec.Supplement.GW1WalkExitCollar

/-! # Zero-side collision at a first real swallow, including a closed horizon -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Restart.FCPlumb
open MartChar.RealFlow FlowStopIdentLL

/-- A nonnegative point alive up to, but not at, T forces the zero right
image to collide at T. No force-word evolution is used. -/
theorem zero_right_collision_of_first_swallow {D : ℝ → ℝ} (hD : Continuous D)
    {X T : ℝ} (hX : 0 ≤ X) (hT : 0 < T)
    (hal : ∀ t, 0 ≤ t → t < T → Alive D X t) (hn : ¬ Alive D X T) :
    rightImg D 0 T = D T := by
  apply le_antisymm ?_ (le_rightImg hD 0 hT.le)
  by_contra hbad
  have hgap : 0 < rightImg D 0 T - D T := sub_pos.2 (lt_of_not_ge hbad)
  let c := (rightImg D 0 T - D T) / 2
  have hc : 0 < c := half_pos hgap
  have hcont : ContinuousAt (fun t => rightImg D 0 t - D t) T :=
    ((continuousOn_rightImg hD 0).continuousAt (Ici_mem_nhds hT)).sub hD.continuousAt
  have hev : ∀ᶠ t in 𝓝 T, c < rightImg D 0 t - D t :=
    hcont.eventually (Ioi_mem_nhds (half_lt_self hgap))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  let r := max (T - δ / 2) 0
  have hr0 : 0 ≤ r := le_max_right _ _
  have hrT : r < T := max_lt (by linarith only [hδ]) hT
  apply hn
  apply Alive.of_forall_le_cflow hD (hal r hr0 hrT) hr0 hc
  intro t ht htAlive
  have ht0 : 0 ≤ t := hr0.trans ht.1
  have hdist : dist t T < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.2)]
    have hr : T - δ / 2 ≤ r := le_max_left _ _
    linarith only [hr, ht.1, hδ]
  have hg := hball hdist
  change c < rightImg D 0 t - D t at hg
  have hdom := rightImg_mono_index hD ht0 hX
  rw [rightImg_eq_gImg hD ht0 htAlive, gImg] at hdom
  linarith only [hg, hdom]

/-- A real terminal visit cannot be alive at the terminal time. The existing
proof for strictly pre-lifetime visits applies with the given global driver;
no extension of the trace past the closed horizon is needed. -/
theorem not_alive_of_closed_real_visit {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hg : IsGeneratingTrace W U γ) (hc : Continuous W) (h0 : W 0 = 0)
    {T : ℝ≥0} (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U) {X : ℝ} (hvis : γ T = X) :
    ¬ Alive (fun r : ℝ => W r.toNNReal) X T := by
  let D : ℝ → ℝ := fun r => W r.toNNReal
  have hD : Continuous D := hc.comp continuous_real_toNNReal
  have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
  intro hal
  obtain ⟨r, hr, hnot⟩ := GB7a.exists_ball_notMem_fwdHull hD T.coe_nonneg
    (WangWu.isForwardSol_of_alive hD hal)
  have hL := GB7a.isLoewnerTraceLT_of_agree hg hTU
    (fun s _ _ => by rfl : ∀ s : ℝ, 0 ≤ s → s < T → D s = W s.toNNReal)
  have hlim := GB7a.tendsto_comp_toNNReal hg hTU hT
  rw [hvis] at hlim
  have hev : ∀ᶠ s in 𝓝[<] (T : ℝ), γ s.toNNReal ∈ ball (X : ℂ) (r / 2) :=
    hlim (ball_mem_nhds _ (half_pos hr))
  obtain ⟨s, hsball, hs⟩ := (hev.and (Ioo_mem_nhdsLT (NNReal.coe_pos.2 hT))).exists
  have hcl := Supp7.G12.trace_mem_closure_fwdHull hD hD0 hL hs.1 hs.2
  have hcl' : γ s.toNNReal ∈ closure (fwdHull D T) :=
    closure_mono (QuantumZipper.fwdHull_mono.1 hs.2.le) hcl
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hcl' (r / 2) (half_pos hr)
  apply hnot z ?_ hzK
  rw [mem_ball] at hsball
  rw [← dist_eq_norm]
  linarith only [hsball, hzd, dist_triangle z (γ s.toNNReal) (X : ℂ),
    dist_comm z (γ s.toNNReal)]

/-- A real point beyond every earlier real contact is alive at each earlier
capacity. This is the existing frozen-driver lemma transported by causality. -/
theorem alive_of_trace_off_global {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hg : IsGeneratingTrace W U γ) (hc : Continuous W) (h0 : W 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < U) {X : ℝ} (hX : 0 < X)
    (hoff : ∀ s ≤ t, ∀ y : ℝ, X ≤ y → γ s ≠ y) :
    Alive (fun r : ℝ => W r.toNNReal) X t := by
  obtain ⟨t₂, htt₂, ht₂U⟩ := Supp7.G11.exists_real_gt_lt ht
  have hal := Sec7.Lemma76E.alive_of_trace_off hg hc.continuousOn h0 ht₂U htt₂ hX hoff
  apply (Sec7.Lemma71B.alive_congr (w := frozenDrive W t₂)
    (w' := fun r : ℝ => W r.toNNReal) (fun r hr => ?_)).1 hal
  exact frozenDrive_eq ⟨hr.1, hr.2.trans htt₂.le⟩

end InteractingSLE.Restart.FCPlumb
