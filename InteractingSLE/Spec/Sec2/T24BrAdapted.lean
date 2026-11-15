import InteractingSLE.Spec.Sec2.T24BrFiltration
import InteractingSLE.Spec.Sec7.PocketTraversalErase
import InteractingSLE.Spec.Supplement.SB2LkRelMeas

/-!
# Theorem 2.4: recovering the driver in the augmented curve filtration

For `r > t`, reparametrize the curve before time `r` by `u ↦ r u / (1 + u)`.
The landed measurable driver reconstruction then reads `W t` from curve evaluations
strictly before `r`. Right continuity gives adaptedness at `t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

open Sec7.PocketTraversal Sec7.Lemma71C

/-- The hull formula for the curve reparametrized onto a bounded time interval. -/
theorem fwdHull_reparam_eq {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) (clockOf r u) =
      fillH (relCurve (fun s : ℝ => η s.toNNReal) r '' Icc 0 u) := by
  rw [image_relCurve_Icc _ hr hu,
    Sec7.Lemma71E.image_Icc_real_eq (clockOf_nonneg hr hu)]
  simp only [Real.toNNReal_coe]
  have h := Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hη
    (t := (clockOf r u).toNNReal) ENNReal.coe_lt_top
  rwa [Real.coe_toNNReal _ (clockOf_nonneg hr hu)] at h

/-- A generating curve reparametrized onto `[0, r)` has local continuous drivers. -/
theorem isDrivenCurve_reparam {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hw : Continuous w) (hη : IsGeneratingTrace w ⊤ η) {r : ℝ} (hr : 0 < r) :
    IsDrivenCurve (relCurve (fun s : ℝ => η s.toNNReal) r) := by
  have hηc : Continuous η := by
    have hc := hη.2.1
    simp only [le_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  apply isDrivenCurve_relCurve hr (hηc.comp continuous_real_toNNReal).continuousOn
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hη.1)
  intro S hS _
  refine ⟨fun s : ℝ => w s.toNNReal, hw.comp continuous_real_toNNReal,
    by simpa only [Function.comp_apply, Real.toNNReal_zero] using
      Sec7.SideHeight.w_zero_of_isGeneratingTrace hη ENNReal.zero_lt_top,
    id, rfl, strictMonoOn_id, continuousOn_id, ?_⟩
  intro t ht
  rw [Sec7.Lemma71E.image_Icc_real_eq ht.1]
  simp only [Function.comp_apply, Real.toNNReal_coe]
  have h := Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hη
    (t := t.toNNReal) ENNReal.coe_lt_top
  rwa [Real.coe_toNNReal _ ht.1] at h

/-- The capacity of the reparametrized curve is its explicit time change. -/
theorem capClock_reparam_eq {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hw : Continuous w) (hη : IsGeneratingTrace w ⊤ η) {r u : ℝ}
    (hr : 0 < r) (hu : 0 ≤ u) :
    capClock (relCurve (fun s : ℝ => η s.toNNReal) r) u = clockOf r u := by
  have h := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using
      Sec7.SideHeight.w_zero_of_isGeneratingTrace hη ENNReal.zero_lt_top)
    (clockOf_nonneg hr hu) (fwdHull_reparam_eq hη hr hu)
  rw [capClock, h]
  ring

/-- The canonical measurable driver of the reparametrized curve recovers the given driver. -/
theorem drivenDriver_reparam_eq {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hw : Continuous w) (hη : IsGeneratingTrace w ⊤ η) {t : ℝ≥0} {r : ℝ}
    (htr : (t : ℝ) < r) :
    Supp8.GB6.CoordB.drivenDriver
      (fun _ : Unit => relCurve (fun s : ℝ => η s.toNNReal) r) t () = w t := by
  have hr : 0 < r := t.coe_nonneg.trans_lt htr
  let S : ℝ := (r + t) / (r - t)
  have hS : 0 < S := div_pos (by linarith) (sub_pos.2 htr)
  have hcS : clockOf r S = (r + t) / 2 := by
    unfold clockOf S
    field_simp [sub_ne_zero.mpr htr.ne', ne_of_gt hr]
    ring
  have hγ := isDrivenCurve_reparam hw hη hr
  have hcap := capClock_reparam_eq hw hη hr hS.le
  have htcap : (t : ℝ) ≤ capClock (relCurve (fun s : ℝ => η s.toNNReal) r) S := by
    rw [hcap, hcS]
    linarith
  have htle : (t : ℝ≥0∞) ≤ ENNReal.ofReal
      (capClock (relCurve (fun s : ℝ => η s.toNNReal) r) S) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal htcap
  have htlife := htle.trans_lt (hγ.ofReal_capClock_lt hS.le)
  rw [Supp8.GB6.CoordB.drivenDriver_eq
    (γ := fun _ : Unit => relCurve (fun s : ℝ => η s.toNNReal) r) (ω := ()) htlife]
  change segDrv _ (t : ℝ) = w t
  have h := hγ.segDrv_eq hS (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using
      Sec7.SideHeight.w_zero_of_isGeneratingTrace hη ENNReal.zero_lt_top)
    (fun u hu => by
      rw [capClock_reparam_eq hw hη hr hu.1]
      exact fwdHull_reparam_eq hη hr hu.1) t.coe_nonneg htcap
  simpa only [Function.comp_apply, Real.toNNReal_coe] using h

/-- The driver of an a.s. generating curve is adapted to its usual augmented filtration. -/
theorem stronglyAdapted_driver_curveFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω)) :
    StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) W := by
  classical
  let 𝓖 := usualAugmentation (Filtration.natural η hη) P
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgen)
  let G : Set Ω := Nᶜ
  have hgood : ∀ ω ∈ G, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω) := by
    intro ω hω
    by_contra hb
    exact hω (hNsub hb)
  have hG : ∀ r, MeasurableSet[𝓖 r] G := fun r =>
    (Ito.measurableSet_usualAugmentation_of_null hNm hN0 r).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    simpa only [G, mem_compl_iff] using measure_eq_zero_iff_ae_notMem.1 hN0
  have hηa : StronglyAdapted 𝓖 η := fun s =>
    (Filtration.stronglyAdapted_natural hη s).mono
      (Ito.le_usualAugmentation (Filtration.natural η hη) P s)
  have hmeas : ∀ t r : ℝ≥0, t < r → Measurable[𝓖 r] (W t) := by
    intro t r htr
    have hr : 0 < (r : ℝ) := (NNReal.coe_lt_coe.2 (lt_of_le_of_lt zero_le htr))
    let γ : Ω → ℝ → ℂ := fun ω u =>
      if ω ∈ G then relCurve (fun s : ℝ => η s.toNNReal ω) r u
      else (u : ℂ) * Complex.I
    have hγ : ∀ ω, IsDrivenCurve (γ ω) := by
      intro ω
      by_cases hω : ω ∈ G
      · simpa only [γ, hω, ↓reduceIte] using
          isDrivenCurve_reparam (hgood ω hω).1 (hgood ω hω).2 hr
      · simpa only [γ, hω, ↓reduceIte] using Theorem14.SB.Lk.isDrivenCurve_vert
    have hγm : ∀ u, 0 ≤ u → Measurable[𝓖 r] fun ω => γ ω u := by
      intro u hu
      let q : ℝ≥0 := (clockOf r u).toNNReal
      have hqr : q ≤ r := Real.toNNReal_le_iff_le_coe.2 (clockOf_lt hr hu).le
      exact Measurable.ite (hG r)
        ((hηa q).measurable.mono (𝓖.mono hqr) le_rfl) measurable_const
    have hm : Measurable[𝓖 r] (Supp8.GB6.CoordB.drivenDriver γ t) := by
      let : MeasurableSpace Ω := 𝓖 r
      exact Supp8.GB6.CoordB.measurable_drivenDriver hγ hγm t
    have heq : W t =ᵐ[P] Supp8.GB6.CoordB.drivenDriver γ t := by
      filter_upwards [hGae] with ω hω
      have he := drivenDriver_reparam_eq (hgood ω hω).1 (hgood ω hω).2
        (NNReal.coe_lt_coe.2 htr)
      simpa only [Supp8.GB6.CoordB.drivenDriver, γ, hω, ↓reduceIte] using he.symm
    have hc : Measurable[usualAugmentation 𝓖 P r] fun ω => (W t ω : ℂ) :=
      measurable_usualAugmentation_of_ae_eq (Complex.measurable_ofReal.comp (hW t))
        (Complex.measurable_ofReal.comp hm) (heq.mono fun _ h => congrArg Complex.ofReal h)
    have hm' := Complex.measurable_re.comp hc
    change Measurable[usualAugmentation (usualAugmentation (Filtration.natural η hη) P) P r]
      (Complex.re ∘ fun ω => (W t ω : ℂ)) at hm'
    rw [usualAugmentation_idempotent] at hm'
    simpa only [Function.comp_def, Complex.ofReal_re] using hm'
  intro t
  apply Measurable.stronglyMeasurable
  intro A hA
  change MeasurableSet[𝓖 t] (W t ⁻¹' A)
  rw [← Filtration.IsRightContinuous.eq (𝓕 := 𝓖), Filtration.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.2 fun r =>
    MeasurableSpace.measurableSet_iInf.2 fun htr => hmeas t r htr hA

end InteractingSLE.Sec2.T24Bridge
