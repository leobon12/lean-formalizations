import LQGMetric.Papers.LM.L3_1N2P2

/-!
# LM Lemma 3.1 with `N = 2`: locality at one scale and the past metrics (task P2-LM31N2)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 3.3, l. 631–637.

* `n2_condIndep_scale` (LM l. 632–633): for every open `V`,
  `n2Sig r V ⟂ (σ(h), n2Sig r (ℂ∖V̄)) | (h − h_r(0))|_V`, from LM Def 1.5 (joint locality of
  `e^{−ξh_r(0)} D_n` for `h − h_r(0)`) by weak union (`DFGPS.L219.condIndepEv_transfer`), using
  `σ(h) ⊆ σ((h − h_r(0))|_V) ∨ σ((h − h_r(0))|_{ℂ∖V})` (`LocGermSplit`, LM l. 534).
* `n2_condIndep_past` (LM l. 635–636, "the conditional law of `(h − h_r(0))|_{B_{sr}(0)}` given
  `𝓕_r` depends only on `(h − h_r(0))|_{ℂ∖B_r(0)}`"): the metric data `n2Past i` of the annuli
  `A_0, …, A_{i−1}` is conditionally independent of `h` given `𝓕_{r_k}` (`i ≤ k`), by induction
  on `i` with the contraction property (`condIndepEv_contraction`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- **LM l. 632–633**: locality of the scaled metrics at one scale, in the form with `σ(h)` on the
outside. -/
theorem n2_condIndep_scale (hgerm : LocGermSplit) {ξ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hX : IsXiAdditive2 ξ P h D₁ D₂) {r : ℝ} (hr : 0 < r)
    (V : TopologicalSpace.Opens ℂ) :
    CondIndepEv (fieldSigma (recentre h r) V) (n2Sig ξ h D₁ D₂ r V)
      (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ r (closure (V : Set ℂ))ᶜ) P := by
  obtain ⟨⟨hD₁, hD₂, hlen, -⟩, hloc⟩ := hX
  have J : CondIndepEv (fieldSigma (recentre h r) V)
      (famSigma (normIntFam ξ h D₁ r) V ⊔ famSigma (normIntFam ξ h D₂ r) V)
      (fieldSigmaClosed (recentre h r) (V : Set ℂ)ᶜ ⊔
        famSigma (normIntFam ξ h D₁ r) (closure (V : Set ℂ))ᶜ ⊔
        famSigma (normIntFam ξ h D₂ r) (closure (V : Set ℂ))ᶜ) P := hloc 0 r hr V
  have hXm : Measurable (recentre h r) := measurable_recentre hh.1.measurable r
  have hXg : IsWholePlaneGFF (recentre h r) P :=
    hh.1.addConst ((measurable_circleAvg_left r 0).comp hh.1.measurable).neg
  have hWo : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hlen1 : ∀ᵐ ω ∂P, (D₁ ω).IsLength := hlen.mono fun _ h => h.1
  have hlen2 : ∀ᵐ ω ∂P, (D₂ ω).IsLength := hlen.mono fun _ h => h.2
  have J1 : CondIndepEv (fieldSigma (recentre h r) V) (n2Sig ξ h D₁ D₂ r V)
      (fieldSigmaClosed (recentre h r) (V : Set ℂ)ᶜ ⊔ n2Sig ξ h D₁ D₂ r (closure (V : Set ℂ))ᶜ)
      P := by
    refine GM.Bilip.CondIndepEv.of_le_aeClosure J ?_ ?_
    · exact sup_le_aeClosure (n2Chain_le_famSigma hlen1 V.isOpen)
        (n2Chain_le_famSigma hlen2 V.isOpen)
    · refine sup_le ((le_aeClosure _).trans (aeClosure_mono (le_sup_left.trans le_sup_left))) ?_
      exact (sup_le_aeClosure (n2Chain_le_famSigma hlen1 hWo)
        (n2Chain_le_famSigma hlen2 hWo)).trans
        (aeClosure_mono (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hG : fieldSigma (recentre h r) V ≤ mΩ := ((measurable_restrictTo V).comp hXm).comap_le
  have hS : ∀ W, n2Sig ξ h D₁ D₂ r W ≤ mΩ := n2Sig_le hh.1.measurable hD₁ hD₂ r
  refine condIndepEv_transfer hG (hS _) (sup_le (GM.fieldSigmaClosed_le_gm hXm _) (hS _)) hG J1
    (le_aeClosure _) (le_sup_right.trans (le_aeClosure _)) (le_sup_left.trans (le_aeClosure _))
    (sup_le ?_ ((le_sup_right.trans le_sup_left).trans (le_aeClosure _)))
  refine le_aeClosure_trans (comap_h_le_recentre hh r) ((hgerm P _ hXg V).trans ?_)
  exact aeClosure_mono (sup_le le_sup_right (le_sup_left.trans le_sup_left))

/-- the annulus `A_k = A_{s₁r_k, s₂r_k}(0)` -/
def n2Ann (s₁ s₂ : ℝ) (r : ℕ → ℝ) (k : ℕ) : TopologicalSpace.Opens ℂ :=
  annulus 0 (s₁ * r k) (s₂ * r k)

/-- the metric data of the annuli `A_0, …, A_{i−1}` -/
def n2Past (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | i + 1 => n2Past ξ h D₁ D₂ s₁ s₂ r i ⊔ n2Sig ξ h D₁ D₂ (r i) (n2Ann s₁ s₂ r i)

lemma n2Past_le {ξ : ℝ} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric} (hh : Measurable h)
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    ∀ i, n2Past ξ h D₁ D₂ s₁ s₂ r i ≤ mΩ
  | 0 => bot_le
  | i + 1 => sup_le (n2Past_le hh hD₁ hD₂ s₁ s₂ r i) (n2Sig_le hh hD₁ hD₂ _ _)

lemma n2Past_mono (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ) (r : ℕ → ℝ) :
    Monotone (n2Past ξ h D₁ D₂ s₁ s₂ r) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

/-- LM l. 731–733 (geometry): `A_i ∩ cl A_j = ∅` for `i < j`. -/
lemma n2Ann_subset {s₁ s₂ : ℝ} (hs₂ : s₂ < 1) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k)
    (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁) {i j : ℕ} (hij : i < j) :
    (n2Ann s₁ s₂ r i : Set ℂ) ⊆ (closure (n2Ann s₁ s₂ r j : Set ℂ))ᶜ := by
  have hcl : closure (n2Ann s₁ s₂ r j : Set ℂ) ⊆ closedBall 0 (s₂ * r j) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    have := hx.2; simp only [sub_zero] at this
    simp only [mem_closedBall, dist_zero_right]; exact this.le
  intro x hx hxc
  have h1 := hx.1; simp only [sub_zero] at h1
  have h2 := hcl hxc; simp only [mem_closedBall, dist_zero_right] at h2
  have h3 : r (i + 1) ≤ s₁ * r i := (div_le_iff₀ (hr0 i)).1 (hrs i)
  have h4 : r j ≤ r (i + 1) := hrA hij
  have h5 : s₂ * r j < r j := by nlinarith [hr0 j]
  linarith

/-- the past metric data at scale `j` is outside `cl A_j`, up to null events -/
lemma n2Past_le_out {ξ : ℝ} {P : Measure Ω} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hlen : ∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength) {s₁ s₂ : ℝ} (hs₂ : s₂ < 1)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) (hrs : ∀ k, r (k + 1) / r k ≤ s₁)
    (j : ℕ) : ∀ i, i ≤ j → n2Past ξ h D₁ D₂ s₁ s₂ r i ≤
      aeClosure P (MeasurableSpace.comap h inferInstance ⊔
        n2Sig ξ h D₁ D₂ (r j) (closure (n2Ann s₁ s₂ r j : Set ℂ))ᶜ)
  | 0, _ => bot_le
  | i + 1, hi => sup_le (n2Past_le_out hD₁ hD₂ hlen hs₂ hr0 hrA hrs j i (by omega))
      (n2Sig_le_nest hD₁ hD₂ hlen _ _ (n2Ann s₁ s₂ r i).isOpen isClosed_closure.isOpen_compl
        (n2Ann_subset hs₂ hr0 hrA hrs (by omega)))

lemma lmFiltration_le_aeClosure_h {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r) (k : ℕ) :
    (lmFiltration P hh hr0 hrA k : MeasurableSpace Ω) ≤
      aeClosure P (MeasurableSpace.comap h inferInstance) := by
  rintro s ⟨-, t, ht, hst⟩
  have h1 : lmF h (r k) ≤ MeasurableSpace.comap h inferInstance :=
    (fieldSigmaClosed_le_comapH _ _).trans
      (@measurable_recentre Ω (MeasurableSpace.comap h inferInstance) h
        (comap_measurable h) (r k)).comap_le
  exact ⟨t, h1 t ht, hst⟩

/-- **LM l. 635–636**: the past metric data is conditionally independent of `h` given
`𝓕_{r_k}` (null-augmented field σ-algebra). -/
theorem n2_condIndep_past (hgerm : LocGermSplit) {ξ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hX : IsXiAdditive2 ξ P h D₁ D₂) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ≤ 1) (hs₂ : s₂ < 1) {r : ℕ → ℝ} (hr0 : ∀ k, 0 < r k) (hrA : Antitone r)
    (hrs : ∀ k, r (k + 1) / r k ≤ s₁) (k : ℕ) :
    ∀ i, i ≤ k → CondIndepEv (lmFiltration P hh.1 hr0 hrA k) (MeasurableSpace.comap h inferInstance)
      (n2Past ξ h D₁ D₂ s₁ s₂ r i) P
  | 0, _ => condIndepEv_of_le_cond ((lmFiltration P hh.1 hr0 hrA).le k)
      hh.1.measurable.comap_le bot_le
  | i + 1, hi => by
    obtain ⟨hD₁, hD₂, hlen, -⟩ := hX.1
    have hL := (lmFiltration P hh.1 hr0 hrA).le k
    have hH : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.1.measurable.comap_le
    have hS : ∀ ρ W, n2Sig ξ h D₁ D₂ ρ W ≤ mΩ := n2Sig_le hh.1.measurable hD₁ hD₂
    have hPi := n2Past_le hh.1.measurable hD₁ hD₂ s₁ s₂ r (ξ := ξ) i
    have IH := n2_condIndep_past hgerm hh hX hs₁ hs₂ hr0 hrA hrs k i (by omega)
    have CI := n2_condIndep_scale hgerm hh hX (hr0 i) (n2Ann s₁ s₂ r i)
    have hΦ : fieldSigma (recentre h (r i)) (n2Ann s₁ s₂ r i) ≤ lmFiltration P hh.1 hr0 hrA k :=
      (annSigma_le_lmFiltration hh.1 hr0 hrA hs₁ hrs i).trans
        ((lmFiltration P hh.1 hr0 hrA).mono (by omega))
    have hΦm : fieldSigma (recentre h (r i)) (n2Ann s₁ s₂ r i) ≤ mΩ :=
      ((measurable_restrictTo _).comp (measurable_recentre hh.1.measurable (r i))).comap_le
    have h2 : CondIndepEv (n2Past ξ h D₁ D₂ s₁ s₂ r i ⊔ lmFiltration P hh.1 hr0 hrA k)
        (n2Sig ξ h D₁ D₂ (r i) (n2Ann s₁ s₂ r i)) (MeasurableSpace.comap h inferInstance) P := by
      refine condIndepEv_transfer hΦm (hS _ _) (sup_le hH (hS _ _)) (sup_le hPi hL) CI
        ((hΦ.trans le_sup_right).trans (le_aeClosure _)) ?_ (le_sup_left.trans (le_aeClosure _))
        ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
      refine sup_le ((n2Past_le_out hD₁ hD₂ hlen hs₂ hr0 hrA hrs i i le_rfl).trans
        (aeClosure_mono le_sup_left)) ?_
      exact (lmFiltration_le_aeClosure_h hh.1 hr0 hrA k).trans
        (aeClosure_mono (le_sup_left.trans le_sup_left))
    exact condIndepEv_contraction hL hH hPi (hS _ _) IH h2.symm

end LQGMetric.LM
