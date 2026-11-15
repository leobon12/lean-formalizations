/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCollision

/-!
# The retained chart path ends on the real line

Packet PROVE-T15-RET. The constructor `stoppedModelTransfer_of_traceInputs` (`RetLeafModelCtor.lean`) needs
three pathwise facts about the source path. For the actual retained continuation of PROVE-RETPLUMB
(`RetAux79.retPath`, `RetAux79.retLife`) at a good disjoint pair:

* interior before the lifetime: the landed `RetAux79.retPath_mem_H_before_life`;
* positive lifetime: `retLife_pos` (the physical lifetime is positive and the clock strictly increasing);
* real at a finite lifetime: `retPath_life_real`.

`retPath_life_real`: at the capacity lifetime the inverse clock is the physical lifetime, where the chart
path has its terminal value `Γ` with `ψ(Γ) = η₂(stop)` (`Supp7.IsRetCont.contPath_endpoint`). If `Γ ∈ ℍ`,
the physical stop point lies in the active domain `D`, which misses both prefixes and `ℝ`. That is
impossible: if the stop is before the end of `η₂`, the first contact with the closed stop set is attained
(`mem_of_contStop_lt`, maximality of the first contact); if the stop is the end of `η₂` itself, the endpoint
of `η₂` is real. The last fact is the single input of this file:
`IntegratedPathEndRealStatement` (deterministic Loewner theory: at a finite lifetime the driving state has a
left limit, which is a threshold state by the frozen `IsIntegratedSLEPath`; a force image colliding with the
driver forces a real tip, `FlowStopIdentLL.real_tip_of_rightImg_eq` with the terminal boundary data
`FlowStopIdentLL.terminal_boundary_data`). Only the existence of the left limit of the driver at the lifetime
is not landed. `ae_flowLine_end_real` transfers it to flow lines.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.Restart.RetLeaf

open Supp7 RetAux79 Sec7

/-! ### Maximality of the first contact -/

/-- **A first contact before the horizon is attained**: if the continuation of a path continuous through
`Z` stops strictly before `Z`, its stop point lies in the closed set `S`. -/
theorem mem_of_contStop_lt {η : ℝ≥0 → ℂ} {Z : ℝ≥0∞} {a : ℝ≥0} {S : Set ℂ} (hS : IsClosed S)
    (hc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ Z}) (ha : (a : ℝ≥0∞) ≤ Z) (h : contStop η Z a S < Z) :
    η (contStop η Z a S).toNNReal ∈ S := by
  have hcs_ne : contStop η Z a S ≠ ⊤ := ne_top_of_lt h
  obtain ⟨c, hc_eq⟩ : ∃ c : ℝ≥0, (c : ℝ≥0∞) = contStop η Z a S := ⟨_, ENNReal.coe_toNNReal hcs_ne⟩
  rw [← hc_eq, ENNReal.toNNReal_coe]
  by_contra hnot
  have hcZ : (c : ℝ≥0∞) < Z := by rw [hc_eq]; exact h
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Z} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt η c := (hc c hcZ.le).continuousAt
    (Filter.mem_of_superset (hopen.mem_nhds hcZ) fun t (ht : (t : ℝ≥0∞) < Z) => ht.le)
  have hev : ∀ᶠ t in 𝓝 c, η t ∉ S ∧ (t : ℝ≥0∞) < Z :=
    (hcont.eventually (hS.isOpen_compl.mem_nhds hnot)).and (hopen.mem_nhds hcZ)
  obtain ⟨u', hcu', hsub⟩ := exists_Ico_subset_of_mem_nhds hev ⟨c + 1, lt_add_one c⟩
  obtain ⟨t, hct, htu⟩ := exists_between hcu'
  have hac : a ≤ c := by
    have h1 : (a : ℝ≥0∞) ≤ (c : ℝ≥0∞) := by
      rw [hc_eq]
      exact le_contStop (self_mem_contSet ha)
    exact_mod_cast h1
  have ht : t ∈ contSet η Z a S := by
    refine ⟨hac.trans hct.le, (hsub ⟨hct.le, htu⟩).2.le, fun t' h1 h2 => ?_⟩
    rcases lt_or_ge t' c with h3 | h3
    · have h5 : (t' : ℝ≥0∞) < contStop η Z a S := by
        rw [← hc_eq]
        exact ENNReal.coe_lt_coe.2 h3
      exact notMem_of_lt_contStop h1 h5
    · exact (hsub ⟨h3, h2.trans htu⟩).1
  have h4 : (t : ℝ≥0∞) ≤ (c : ℝ≥0∞) := by
    rw [hc_eq]
    exact le_contStop ht
  exact absurd (ENNReal.coe_le_coe.1 h4) (not_le.2 hct)

/-! ### The endpoint of a generated integrated path -/

/-- **Named input: a generated integrated SLE path ends on the real line at a finite lifetime.** Deterministic
Loewner theory: the driving state has a left limit at a finite positive lifetime (the trace is continuous
through it), which is a threshold state (`IsIntegratedSLEPath`'s `threshold_of_tendsto`); a force image
colliding with the driver forces a real tip (`FlowStopIdentLL.real_tip_of_rightImg_eq`). Not proved here. -/
def IntegratedPathEndRealStatement : Prop :=
  ∀ (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞)
    (η : ℝ≥0 → ℂ), IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ → IsGeneratingTrace w ζ η → ζ ≠ ⊤ →
      (η ζ.toNNReal).im = 0

/-- A flow line ends on the real line at a finite lifetime, from the named input. -/
theorem ae_flowLine_end_real (hE : IntegratedPathEndRealStatement) {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → (η ω (ζ ω).toNNReal).im = 0 := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  filter_upwards [htr, hcoup.1.2.2.2.2] with ω hωt hωp hζ
  have h1 := hE _ _ _ _ _ _ _ _ _ _ _ hωp hωt hζ
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h1

/-! ### The actual retained continuation -/

section Retained

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₁ x₂ : ℝ} {ω : Ω}

/-- **The retained capacity lifetime is positive.** -/
theorem retLife_pos (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    0 < retLife G η₁' η₂' ζ₂ u r ω := by
  obtain ⟨hR, -, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  obtain ⟨hC, -, -⟩ := retChartPath_clock hd hG hp₂ hpair
  have hU : 0 < retLifeP η₁' η₂' ζ₂ u r ω := hL ▸ hR.pos_contLife
  rw [retLife_eq]
  unfold capLife
  split_ifs with htop
  · exact ENNReal.zero_lt_top
  · have hc0 : 0 < (retLifeP η₁' η₂' ζ₂ u r ω).toNNReal := ENNReal.toNNReal_pos hU.ne' htop
    have hcle : (((retLifeP η₁' η₂' ζ₂ u r ω).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ retLifeP η₁' η₂' ζ₂ u r ω :=
      ENNReal.coe_toNNReal_le_self
    have hlt := hC.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ retLifeP η₁' η₂' ζ₂ u r ω from zero_le) hcle hc0
    rw [hC.zero] at hlt
    exact ENNReal.ofReal_pos.2 hlt

/-- **The retained chart path is real at a finite capacity lifetime**, given that the second flow line ends on
the real line at a finite lifetime. -/
theorem retPath_life_real (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₁ : IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hend : ζ₂ ω ≠ ⊤ → (η₂' ω (ζ₂ ω).toNNReal).im = 0)
    (hV : retLife G η₁' η₂' ζ₂ u r ω ≠ ⊤) :
    (RetAux79.retPath G η₁' η₂' ζ₂ u r ω (retLife G η₁' η₂' ζ₂ u r ω).toNNReal).im = 0 := by
  obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  obtain ⟨hC, -, -⟩ := retChartPath_clock hd hG hp₂ hpair
  have hlife : retLife G η₁' η₂' ζ₂ u r ω = capLife (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
      (retLifeP η₁' η₂' ζ₂ u r ω) := retLife_eq
  have hU₀ : retLifeP η₁' η₂' ζ₂ u r ω ≠ ⊤ := by
    intro h
    apply hV
    rw [hlife]
    unfold capLife
    rw [ite_eq_left h]
  obtain ⟨c, hcU⟩ : ∃ c : ℝ≥0, (c : ℝ≥0∞) = retLifeP η₁' η₂' ζ₂ u r ω := ⟨_, ENNReal.coe_toNNReal hU₀⟩
  obtain ⟨q, hqV⟩ : ∃ q : ℝ≥0, (q : ℝ≥0∞) = retLife G η₁' η₂' ζ₂ u r ω :=
    ⟨_, ENNReal.coe_toNNReal hV⟩
  rw [← hqV, ENNReal.toNNReal_coe]
  have hcap : capLife (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) (retLifeP η₁' η₂' ζ₂ u r ω) =
      ENNReal.ofReal (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) c) := by
    unfold capLife
    rw [ite_eq_right hU₀, ← hcU, ENNReal.toNNReal_coe]
  have hnn : 0 ≤ chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) c := hC.nonneg hcU.le
  have hq : (q : ℝ≥0∞) ≤ capLife (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
      (retLifeP η₁' η₂' ζ₂ u r ω) := by rw [hqV, hlife]
  obtain ⟨hle, hclkq⟩ := hC.invClock_spec hq
  have hqc : (q : ℝ) = chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) c := by
    have h1 : (q : ℝ≥0∞) = ENNReal.ofReal (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) c) := by
      rw [hqV, hlife, hcap]
    have h2 := congrArg ENNReal.toReal h1
    rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal hnn] at h2
  have hinv : invClock (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) (retLifeP η₁' η₂' ζ₂ u r ω) q = c :=
    hC.strictMonoOn.injOn hle hcU.le (hclkq.trans hqc)
  have hpath : RetAux79.retPath G η₁' η₂' ζ₂ u r ω q = retChartPath G η₁' η₂' ζ₂ u r ω c := by
    rw [RetAux79.retPath, canonRetPath_zero]
    show retChartPath G η₁' η₂' ζ₂ u r ω (invClock (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
      (retLifeP η₁' η₂' ζ₂ u r ω) q) = _
    rw [hinv]
  rw [hpath]
  -- the terminal value of the chart path
  have hLK : contLife (η₂' ω) (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r
      (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r) ≠ ⊤ := by rw [← hL]; exact hU₀
  obtain ⟨hHbar, hψ, -⟩ := hR.contPath_endpoint hLK
  have hcL : (contLife (η₂' ω) (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r
      (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r)).toNNReal = c := by
    rw [← hL, ← hcU, ENNReal.toNNReal_coe]
  have hΓ : retChartPath G η₁' η₂' ζ₂ u r ω c = contPath (H \ fillH (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r))
      ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) r (contLife (η₂' ω)
        (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r)) c := by
    unfold retChartPath
    rw [hD, hL]
  rw [hΓ]
  rw [hcL] at hψ hHbar
  by_contra hne
  have hΓH : contPath (H \ fillH (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r))
      ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) r (contLife (η₂' ω)
        (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r)) c ∈ H :=
    lt_of_le_of_ne hHbar (fun h => hne h.symm)
  have hDmem := hR.chart.bijOn_inv.mapsTo hΓH
  rw [hψ] at hDmem
  -- the stop time in physical time
  have hpK : ((r + c : ℝ≥0) : ℝ≥0∞) = contStop (η₂' ω)
      (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r) := by
    rw [ENNReal.coe_add, hcU, hL, contLife, add_tsub_cancel_of_le hR.lt_contStop.le]
  have hpH : η₂' ω (r + c) ∈ H := hDmem.1
  have hnotK : η₂' ω (r + c) ∉ η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r := fun hk =>
    hDmem.2 ⟨hpH, Or.inl (subset_closure hk)⟩
  have hnotR : η₂' ω (r + c) ∉ retStopSet η₁' η₂' u r ω := by
    rintro ((hk | hk) | hk)
    · exact hnotK (Or.inl hk)
    · exact hnotK (Or.inr hk)
    · exact (ne_of_gt hpH) hk
  have hZle : contStop (η₂' ω) (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r
      (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r) ≤ contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω) :=
    contStop_le
  rcases hZle.lt_or_eq with hlt | heq
  · have hm := mem_of_contStop_lt hR.isClosed_K hR.path.continuousOn hR.lt.le hlt
    rw [← hpK, ENNReal.toNNReal_coe] at hm
    exact hnotK hm
  · have hZ2 : contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω) ≤ ζ₂ ω := contStop_le
    rcases hZ2.lt_or_eq with hlt2 | heq2
    · have hRc : IsClosed (retStopSet η₁' η₂' u r ω) := by
        refine (((Supp7.IsPathGood.isCompact_image_Icc_of_le hp₁ hpair.1.le).isClosed).union
          ((Supp7.IsPathGood.isCompact_image_Icc_of_le hp₂ hpair.2.1.le).isClosed)).union ?_
        exact isClosed_eq Complex.continuous_im continuous_const
      have hm := mem_of_contStop_lt hRc hp₂.continuousOn hpair.2.1.le hlt2
      rw [← heq, ← hpK, ENNReal.toNNReal_coe] at hm
      exact hnotR hm
    · have htop : ζ₂ ω ≠ ⊤ := by
        rw [← heq2, ← heq, ← hpK]
        exact ENNReal.coe_ne_top
      have h1 := hend htop
      rw [← heq2, ← heq, ← hpK, ENNReal.toNNReal_coe] at h1
      exact (ne_of_gt hpH) h1

/-- **The three pathwise trace inputs of `stoppedModelTransfer_of_traceInputs` for the actual retained
continuation**, almost surely on an event `F` of good disjoint pairs, with the supported lifetime
`F.indicator retLife` used by PROVE-RETPLUMB's `retAdaptedSafeInputs_of_flowLines`. The second flow line's
endpoint fact comes from the named input through `ae_flowLine_end_real`. -/
theorem retained_traceInputs (hE : IntegratedPathEndRealStatement) {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {θ₂ : ℝ} {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η₂ : Ω → ℝ≥0 → ℂ} (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) {F : Set Ω}
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) :
    (∀ᵐ ω ∂P, ω ∈ F → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω →
      0 < (RetAux79.retPath G η₁' η₂' ζ₂ u r ω t).im) ∧
    (∀ᵐ ω ∂P, ω ∈ F → F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ≠ ⊤ →
      (RetAux79.retPath G η₁' η₂' ζ₂ u r ω (F.indicator (retLife G η₁' η₂' ζ₂ u r) ω).toNNReal).im = 0) ∧
    (∀ᵐ ω ∂P, ω ∈ F → 0 < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω) := by
  have hend : ∀ᵐ ω ∂P, ζ₂ ω ≠ ⊤ → (η₂' ω (ζ₂ ω).toNNReal).im = 0 := by
    filter_upwards [ae_flowLine_end_real hE hη₂, ha₂] with ω h1 h2 htop
    rw [h2 _ ENNReal.coe_toNNReal_le_self]
    exact h1 htop
  refine ⟨Eventually.of_forall fun ω hω t ht0 ht => ?_, ?_, Eventually.of_forall fun ω hω => ?_⟩
  · rw [indicator_of_mem hω] at ht
    exact retPath_mem_H_before_life hd (hF ω hω).2 (hp₂ ω hω) (hF ω hω).1 ht0 ht
  · filter_upwards [hend] with ω hω hωF htop
    rw [indicator_of_mem hωF] at htop ⊢
    exact retPath_life_real hd (hF ω hωF).2 (hp₁ ω hωF) (hp₂ ω hωF) (hF ω hωF).1 hω htop
  · rw [indicator_of_mem hω]
    exact retLife_pos hd (hF ω hω).2 (hp₂ ω hω) (hF ω hω).1

end Retained

end InteractingSLE.Restart.RetLeaf
