/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondWordMeas
import InteractingSLE.Spec.Sec5.Prop59PiecesArc

/-!
# The joint-chart images of the tree paths as a measurable family of killed arcs

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (p. 143): "Fix a deterministic time `r > 0`
for the counterflow […]. Reveal these two disjoint stopped explorations. […] Map that component conformally to `ℍ`
[…]. Denote this map by `ψ`. Rescale it so that the marked points `z₋, z₊` in Figure 5.7 satisfy `z₋ ≤ −3` and
`z₊ ≥ 3`." The flow-line paths of the tree (Proposition 5.13) live in the chart `Q` (seed `0`, target `∞`); the
counterflow prefix up to `r` is read from its history `y` (GLUECOND's `HistorySpace`), and the joint chart is
`Ψ = revChart (cfDrv0 r y) r = R ∘ f′_r ∘ R` (PROVE-GLUECOND5), rescaled by a dilation `λ > 0`. Before its first contact
with `R(K′_r)` the image `λ Ψ ∘ α` of a simple proper arc `α` is a killed arc (WangWu's `isKilledArc_imgCurve`).

* `CfGood`: the counterflow obstacle `R(K′_r)` is closed and equals GLUECOND's hitting-measurable `cfHullQ r y`;
* `tImg`, `tPre`: the dilated image curve and its pre-contact times on a good set `G` (a vertical ray elsewhere);
* `isKilledArc_smul`, **`isKilledArc_tImg`**;
* `measurable_indicator_capClock_of`: the capacity clock of a family of killed arcs with measurable positions and
  pre-contact events is measurable at rational times (PROVE-GLUECOND5's grid-capacity argument, generic);
* **`isKilledFamily_tImg`**: the images form a measurable family of killed arcs (`IsKilledFamily`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord GlueCond CrossCond.Word49 LawUnique
open Sec7.Lemma71C (capClock)

/-! ### Scaled killed arcs -/

theorem isKilledArc_smul {γ : ℝ → ℂ} {P : Set ℝ} (h : IsKilledArc γ P) {c : ℝ} (hc : 0 < c) :
    IsKilledArc (fun u => (c : ℂ) * γ u) P where
  zero_mem := h.zero_mem
  nonneg := h.nonneg
  icc := h.icc
  exists_gt := h.exists_gt
  zero := by simp only [h.zero, mul_zero]
  cont := continuousOn_const.mul h.cont
  inj u hu v hv e := h.inj hu hv (mul_left_cancel₀ (ofReal_ne_zero.2 hc.ne') e)
  mem_H u hu hpos := by
    show (0 : ℝ) < ((c : ℂ) * γ u).im
    rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_pos hc (h.mem_H u hu hpos)

/-! ### The image family -/

section Family

variable {Ω : Type*}

/-- **A good counterflow history at time `r`**: the obstacle `R(K′_r)` read from the stopped history is closed and
equals GLUECOND's hitting-measurable counterflow hull `cfHullQ r y`. -/
def CfGood (r : ℝ≥0) (y : HistorySpace 0 0) : Prop :=
  IsClosed (negInv '' fwdHull (cfDrv0 r y) r) ∧ cfHullQ r y = negInv '' fwdHull (cfDrv0 r y) r

open scoped Classical in
/-- **The dilated joint-chart image of a curve** `α` of the chart `Q`: `λ Ψ ∘ α` on `G`, a vertical ray elsewhere. -/
def tImg (r : ℝ≥0) (y : Ω → HistorySpace 0 0) (lam : Ω → ℝ) (G : Set Ω) (α : Ω → ℝ → ℂ) : Ω → ℝ → ℂ :=
  fun ω u => if ω ∈ G then (lam ω : ℂ) * imgCurve (cfDrv0 r (y ω)) r (α ω) u else vRay u

open scoped Classical in
/-- **The pre-contact times** of `α` with the counterflow obstacle on `G`, `[0, ∞)` elsewhere. -/
def tPre (r : ℝ≥0) (y : Ω → HistorySpace 0 0) (G : Set Ω) (α : Ω → ℝ → ℂ) : Ω → Set ℝ :=
  fun ω => if ω ∈ G then preContact (α ω) (cfHullQ r (y ω)) else Ici 0

variable {r : ℝ≥0} {y : Ω → HistorySpace 0 0} {lam : Ω → ℝ} {G : Set Ω} {α : Ω → ℝ → ℂ}

theorem tImg_of_mem {ω : Ω} (hω : ω ∈ G) :
    tImg r y lam G α ω = fun u => (lam ω : ℂ) * imgCurve (cfDrv0 r (y ω)) r (α ω) u := by
  classical
  funext u
  simp only [tImg, hω, ↓reduceIte]

theorem tImg_of_notMem {ω : Ω} (hω : ω ∉ G) : tImg r y lam G α ω = vRay := by
  classical
  funext u
  simp only [tImg, hω, ↓reduceIte]

theorem tPre_of_mem {ω : Ω} (hω : ω ∈ G) : tPre r y G α ω = preContact (α ω) (cfHullQ r (y ω)) := by
  classical
  simp only [tPre, hω, ↓reduceIte]

/-- **The images are killed arcs** at every sample. -/
theorem isKilledArc_tImg (hG : ∀ ω ∈ G, CfGood r (y ω) ∧ IsProperArc (α ω)) (hlam : ∀ ω, 0 < lam ω) (ω : Ω) :
    IsKilledArc (tImg r y lam G α ω) (tPre r y G α ω) := by
  classical
  by_cases hω : ω ∈ G
  · rw [tImg_of_mem hω, tPre_of_mem hω, (hG ω hω).1.2]
    exact isKilledArc_smul (isKilledArc_imgCurve (continuous_cfDrv0 r (y ω)) (cfDrv0_zero r (y ω)) r.coe_nonneg
      (hG ω hω).1.1 (hG ω hω).2) (hlam ω)
  · rw [tImg_of_notMem hω]
    simp only [tPre, hω, ↓reduceIte]
    exact isKilledArc_vRay

end Family

/-! ### Capacity clocks of measurable families -/

section Cap

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

/-- **The capacity clock at a rational time is measurable on its pre-contact event** for a family of killed arcs
with measurable positions and measurable rational pre-contact events (PROVE-GLUECOND5's argument through the grid
capacity `WholeField.hcapHit` of the frozen path). -/
theorem measurable_indicator_capClock_of (hγ : ∀ ω, IsKilledArc (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω}) (hm : ∀ u : ℝ, Measurable fun ω => γ ω u) (q : ℚ) :
    Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) := by
  classical
  set A := {ω | (q : ℝ) ∈ P ω} with hAdef
  have hA : MeasurableSet A := hP q
  set Γ : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ A then γ ω (min (t : ℝ) q) else 0 with hΓdef
  have hΓc : ∀ ω, Continuous (Γ ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hΓdef, hω, ↓reduceIte]
      have hq0 : (0 : ℝ) ≤ q := (hγ ω).nonneg _ hω
      exact ((hγ ω).cont.mono ((hγ ω).icc _ hω)).comp_continuous
        ((NNReal.continuous_coe.min continuous_const)) fun t => ⟨le_min t.coe_nonneg hq0, min_le_right _ _⟩
    · simp only [hΓdef, hω, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ t, Measurable fun ω => Γ ω t := fun t => Measurable.ite hA (hm _) measurable_const
  have hmeas := Restart.measurable_hcapHit_image hΓc hΓm (q : ℝ).toNNReal
  have heq : A.indicator (fun ω => capClock (γ ω) q) =
      A.indicator fun ω => (WholeField.hcapHit (Γ ω '' Icc 0 (q : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun ω hω => ?_
    have hq0 : (0 : ℝ) ≤ q := (hγ ω).nonneg _ hω
    have himg : γ ω '' Icc 0 q = Γ ω '' Icc 0 (q : ℝ).toNNReal := by
      rw [Sec7.Lemma71E.image_Icc_real_eq hq0]
      refine image_congr fun t ht => ?_
      have htq : (t : ℝ) ≤ q := by
        have := ht.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at this
      simp only [hΓdef, hω, ↓reduceIte, min_eq_left htq]
    have h0 : (Γ ω 0).im ≤ 0 := by
      simp only [hΓdef, hω, ↓reduceIte, NNReal.coe_zero, min_eq_left hq0, (hγ ω).zero, Complex.zero_im,
        le_refl]
    rw [Restart.hcapHit_image_eq (hΓc ω).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (γ ω '' Icc 0 q)) := by
      have := (hγ ω).capClock_nonneg hω
      rw [capClock] at this
      linarith
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

end Cap

/-! ### The image family is measurable -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {r : ℝ≥0} {y : Ω → HistorySpace 0 0} {lam : Ω → ℝ} {G : Set Ω}
  {α : Ω → ℝ → ℂ}

theorem measurable_tImg (hy : Measurable y) (hlam : Measurable lam) (hGm : MeasurableSet G)
    (hαm : ∀ u, Measurable fun ω => α ω u) (u : ℝ) : Measurable fun ω => tImg r y lam G α ω u := by
  classical
  refine Measurable.ite hGm ?_ measurable_const
  refine (Complex.measurable_ofReal.comp hlam).mul ?_
  by_cases hu : u ≤ 0
  · simp only [imgCurve, hu, ↓reduceIte]
    exact measurable_const
  · simp only [imgCurve, hu, ↓reduceIte, revChart]
    have hz : Measurable fun ω => negInv (α ω u) := measurable_negInv.comp (hαm u)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun ω => cfDrv0 r (y ω))
      (fun ω => continuous_cfDrv0 r (y ω)) (fun t => (measurable_cfDrv0_apply' r t).comp hy)
      (fun ω => cfDrv0_zero r (y ω)) (τ := fun _ => (r : ℝ)) measurable_const (fun _ => r.coe_nonneg) hz).1
    exact measurable_negInv.comp h

theorem measurableSet_mem_tPre (hy : Measurable y) (hGm : MeasurableSet G)
    (hG : ∀ ω ∈ G, CfGood r (y ω) ∧ IsProperArc (α ω)) (hαm : ∀ u, Measurable fun ω => α ω u) (q : ℚ) :
    MeasurableSet {ω | (q : ℝ) ∈ tPre r y G α ω} := by
  classical
  by_cases hq : (0 : ℝ) ≤ q
  · set T : Set Ω := ⋃ m : ℕ, ⋂ u : ℚ, ({_ω | (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q}ᶜ ∪
        {ω | Disjoint (ball (α ω u) (1 / ((m : ℝ) + 1))) (cfHullQ r (y ω))}) with hTdef
    have heq : {ω | (q : ℝ) ∈ tPre r y G α ω} = (G ∩ T) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · have hGc : IsClosed (cfHullQ r (y ω)) := by rw [(hG ω hω).1.2]; exact (hG ω hω).1.1
        simp only [mem_ofPred_eq, tPre_of_mem hω, mem_preContact_iff_ball (hG ω hω).2.cont hGc hq, mem_union,
          mem_inter_iff, hω, true_and, mem_compl_iff, not_true_eq_false, or_false, hTdef, mem_iUnion, mem_iInter]
        constructor
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u => ?_⟩
          by_cases hu : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
          · exact Or.inr (hm u hu.1 hu.2)
          · exact Or.inl hu
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u hu0 huq => ?_⟩
          rcases hm u with h | h
          · exact absurd ⟨hu0, huq⟩ h
          · exact h
      · simp only [mem_ofPred_eq, tPre, hω, ↓reduceIte, mem_Ici, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, or_true, iff_true]
        exact hq
    rw [heq]
    refine (hGm.inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u =>
      (MeasurableSet.const _).compl.union ?_)).union hGm.compl
    exact measurableSet_disjoint_ball (hαm u) ((measurable_cfHullQ r).comp hy)
      (fun ω => (cfHullQ_relClosed r (y ω)).1) _
  · have heq : {ω | (q : ℝ) ∈ tPre r y G α ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hmem
      by_cases hω : ω ∈ G
      · rw [tPre_of_mem hω] at hmem; exact hq hmem.1
      · simp only [tPre, hω, ↓reduceIte, mem_Ici] at hmem; exact hq hmem
    rw [heq]
    exact MeasurableSet.empty

/-- **The dilated images of the tree paths form a measurable family of killed arcs.** -/
theorem isKilledFamily_tImg (hy : Measurable y) (hlam : Measurable lam) (hpos : ∀ ω, 0 < lam ω)
    (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, CfGood r (y ω) ∧ IsProperArc (α ω))
    (hαm : ∀ u, Measurable fun ω => α ω u) : IsKilledFamily (tImg r y lam G α) (tPre r y G α) where
  arc := isKilledArc_tImg hG hpos
  pre := measurableSet_mem_tPre hy hGm hG hαm
  cap := measurable_indicator_capClock_of (isKilledArc_tImg hG hpos) (measurableSet_mem_tPre hy hGm hG hαm)
    (measurable_tImg hy hlam hGm hαm)
  pos q := measurable_tImg hy hlam hGm hαm q

end Meas

end InteractingSLE.Sec5.Prop59Pieces
