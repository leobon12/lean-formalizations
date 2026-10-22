import HigherDimLQGMetric.Locality.Normalize
import HigherDimLQGMetric.Local.CopiesMetric
import LQGMetric.Papers.DFGPS.L2_19CI

/-! Conditional-independence transfer between two sphere normalizations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.GM.Bilip
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- One normalized internal family is measurable from the Borel chain version
of another normalization and the new field restricted to `V`, up to null sets. -/
theorem l7a_recenter_intSigma_le_ae_scaledChain {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (D : Ω → ContMetric d) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (ξ : ℝ) (V : TopologicalSpace.Opens (Rd d))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (z₀ : Rd d)
    (hsph : Metric.sphere z₀ r₀ ⊆ V)
    (r : ℝ) (z : Rd d) (W : TopologicalSpace.Opens (Rd d)) :
    famSigmaRd (rescFam ξ h D z r) W ≤
      aeClosure P (famSigmaRd (l7b_chainFam ξ h D r₀ z₀) W ⊔
        fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V) := by
  let g₁ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let a : Ω → ℝ := fun ω => sphereAvg (g₁ ω) r₀ z₀
  let M : MeasurableSpace Ω := famSigmaRd (l7b_chainFam ξ h D r₀ z₀) W ⊔
    fieldSigmaRd g₁ V
  have ham : Measurable[M] a :=
    (l7a_measurable_sphereAvg_fieldSigma g₁ V z₀ r₀
      (by simpa [abs_of_pos hr₀] using hsph)).mono le_sup_right le_rfl
  let Y : Ω → Rd d → Rd d → ℝ≥0∞ := fun ω u v =>
    ENNReal.ofReal (Real.exp (ξ * a ω)) *
      l7b_chainFam ξ h D r₀ z₀ ω W u v
  have hYm : Measurable[M] Y := by
    letI : MeasurableSpace Ω := M
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro v
    have ham' : Measurable a := ham
    have hB : Measurable (fun ω => l7b_chainFam ξ h D r₀ z₀ ω W) := by
      apply measurable_iff_comap_le.mpr
      exact le_sup_left
    have hC : Measurable (fun ω => l7b_chainFam ξ h D r₀ z₀ ω W u v) :=
      (measurable_pi_apply v).comp ((measurable_pi_apply u).comp hB)
    exact (ENNReal.measurable_ofReal.comp (ham'.const_mul ξ).exp).mul hC
  have hscaleAe := @l7a_recenter_fam_scale_ae d hd Ω mΩ P h hh D ξ r₀ hr₀ z₀ r z
  have hae : (fun ω => rescFam ξ h D z r ω W) =ᵐ[P] Y := by
    filter_upwards [hscaleAe, hlen] with ω hscale hω
    funext u v
    rw [hscale W u v]
    change _ * (_ * (D ω).internal W u v) =
      _ * (_ * (D ω).chainInf W u v)
    rw [(D ω).internal_eq_chainInf hω W.isOpen]
    simp only [l7b_scale, a, g₁]
  rintro s ⟨S, hS, rfl⟩
  refine ⟨Y ⁻¹' S, hYm hS, ?_⟩
  filter_upwards [hae] with ω hω
  change (rescFam ξ h D z r ω W ∈ S) = (Y ω ∈ S)
  rw [hω]

/-- Joint locality for a sphere inside `V` transfers to any positive
normalizing radius. The chain metric gives measurable versions of internal
distances on the almost-sure length-metric event. -/
theorem l7a_condIndep_recenter_transfer {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (D : Ω → ContMetric d) (hD : Measurable D)
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (ξ : ℝ) (V : TopologicalSpace.Opens (Rd d))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (z₀ : Rd d)
    (hsph : Metric.sphere z₀ r₀ ⊆ V)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (H : LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀) V)
      (famSigmaRd (rescFam ξ h D z₀ r₀) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀) ⊔
        famSigmaRd (rescFam ξ h D z₀ r₀) (extOpen V)) P) :
    LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
      (famSigmaRd (rescFam ξ h D z r) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
        famSigmaRd (rescFam ξ h D z r) (extOpen V)) P := by
  let g₀ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r₀ z₀
  let g₁ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let G₀ := fieldSigmaRd g₀ V
  let G₁ := fieldSigmaRd g₁ V
  let A₀ := famSigmaRd (l7b_chainFam ξ h D r₀ z₀) V
  let B₀ := fullSigmaRd g₀ ⊔ famSigmaRd (l7b_chainFam ξ h D r₀ z₀) (extOpen V)
  letI : MeasurableSpace Ω := mΩ
  have hg₀ : Measurable g₀ := (l7b_measurable_recenter r₀ z₀).comp hh.measurable
  have hg₁ : Measurable g₁ := (l7b_measurable_recenter r z).comp hh.measurable
  have hG₀ : G₀ ≤ mΩ := ((measurable_restrictTo V).comp hg₀).comap_le
  have hG₁ : G₁ ≤ mΩ := ((measurable_restrictTo V).comp hg₁).comap_le
  have hA₀ : A₀ ≤ mΩ :=
    (l7b_measurable_chainFam ξ hh.measurable hD r₀ z₀ V).comap_le
  have hB₀ : B₀ ≤ mΩ := sup_le hg₀.comap_le
    (l7b_measurable_chainFam ξ hh.measurable hD r₀ z₀ (extOpen V)).comap_le
  have Hchain : LQGMetric.CondIndepEv G₀ A₀ B₀ P := by
    refine LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure H ?_ ?_
    · change A₀ ≤ aeClosure P (famSigmaRd (l7b_intFam ξ h D r₀ z₀) V)
      exact l7b_chainSigma_le_ae_int hlen r₀ z₀ V.isOpen
    · apply sup_le
      · exact (le_sup_left : fullSigmaRd g₀ ≤
          fullSigmaRd g₀ ⊔ famSigmaRd (rescFam ξ h D z₀ r₀) (extOpen V)).trans
          (le_aeClosure _)
      · have hh' := l7b_chainSigma_le_ae_int (P := P) (ξ := ξ) (h := h) (D := D)
          hlen r₀ z₀
          (extOpen V).isOpen
        exact hh'.trans (aeClosure_mono le_sup_right)
  have h1 : G₀ ≤ aeClosure P G₁ :=
    l7a_recenter_fieldSigma_le_aeClosure hd hh V hr₀ z₀ hsph r z
  have h2 : G₁ ≤ aeClosure P (B₀ ⊔ G₀) := by
    have hGF : G₁ ≤ fullSigmaRd g₁ :=
      ((measurable_restrictTo V).comp (comap_measurable g₁)).comap_le
    exact hGF.trans ((l7a_recenter_fullSigma_le_aeClosure hd hh r₀ z₀ hr z).trans
      (aeClosure_mono (le_sup_left.trans le_sup_left)))
  have h3 : famSigmaRd (rescFam ξ h D z r) V ≤ aeClosure P (A₀ ⊔ G₁) :=
    l7a_recenter_intSigma_le_ae_scaledChain hd hh D hlen ξ V hr₀ z₀ hsph r z V
  have h4 : fullSigmaRd g₁ ⊔ famSigmaRd (rescFam ξ h D z r) (extOpen V) ≤
      aeClosure P (B₀ ⊔ G₁) := by
    apply sup_le
    · exact (l7a_recenter_fullSigma_le_aeClosure hd hh r₀ z₀ hr z).trans
        (aeClosure_mono (le_sup_left.trans le_sup_left))
    · exact (l7a_recenter_intSigma_le_ae_scaledChain hd hh D hlen ξ V hr₀ z₀
        hsph r z (extOpen V)).trans (aeClosure_mono
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  exact LQGMetric.DFGPS.L219.condIndepEv_transfer hG₀ hA₀ hB₀ hG₁
    Hchain h1 h2 h3 h4

/-- The internal metric on the empty domain is constant, so its locality
condition holds for every normalization. -/
theorem l7a_condIndep_empty {d : ℕ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (D : Ω → ContMetric d) (hD : Measurable D)
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (ξ : ℝ) (V : TopologicalSpace.Opens (Rd d))
    (hV : (V : Set (Rd d)) = ∅) (r : ℝ) (z : Rd d) :
    LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
      (famSigmaRd (rescFam ξ h D z r) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
        famSigmaRd (rescFam ξ h D z r) (extOpen V)) P := by
  let g : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let G := fieldSigmaRd g V
  letI : MeasurableSpace Ω := mΩ
  have hg : Measurable g := (l7b_measurable_recenter r z).comp hh.measurable
  have hG : G ≤ mΩ := ((measurable_restrictTo V).comp hg).comap_le
  have hA : famSigmaRd (rescFam ξ h D z r) V ≤ aeClosure P G := by
    have hc : (fun ω => rescFam ξ h D z r ω V) =
        fun _ : Ω => (fun _ _ : Rd d => (⊤ : ℝ≥0∞)) := by
      funext ω u v
      dsimp [rescFam]
      rw [hV, ContMetric.internal_empty]
      exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hm : Measurable[G] (fun ω => rescFam ξ h D z r ω V) := by
      letI : MeasurableSpace Ω := G
      rw [hc]
      exact measurable_const
    exact hm.comap_le.trans (le_aeClosure _)
  have hB : fullSigmaRd g ⊔ famSigmaRd (rescFam ξ h D z r) (extOpen V) ≤
      aeClosure P mΩ := by
    apply sup_le
    · exact hg.comap_le.trans (le_aeClosure _)
    · have hchain := l7b_intSigma_le_ae_chain (P := P) (ξ := ξ)
        (h := h) (D := D) hlen r z (extOpen V).isOpen
      have hm := (l7b_measurable_chainFam ξ hh.measurable hD r z
        (extOpen V)).comap_le
      exact hchain.trans (aeClosure_mono hm)
  exact condIndepEv_of_le_aeClosure hG hA hB

end HigherDimLQGMetric
