import HigherDimLQGMetric.Local.CopiesMetric
import LQGMetric.Papers.DFGPS.L2_19CI

/-!
# Conditional independence of separated internal metrics

The radius-one, zero-centred instance of xi-additivity has the original field and
metric on the normalization event.  We transport its conditional independence
statement across that null event, using countable chain representatives of the
internal metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip LQGMetric.DFGPS.L219
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- An almost-sure replacement of a random variable does not change its generated
sigma algebra up to null sets. -/
theorem determ_sigma_le_ae_of_ae_eq {α : Type*} [MeasurableSpace α]
    {f g : Ω → α} (hfg : f =ᵐ[P] g) :
    MeasurableSpace.comap f inferInstance ≤ aeClosure P (MeasurableSpace.comap g inferInstance) := by
  rintro s ⟨t, ht, rfl⟩
  refine ⟨g ⁻¹' t, ⟨t, ht, rfl⟩, ?_⟩
  filter_upwards [hfg] with ω hω
  change (f ω ∈ t) = (g ω ∈ t)
  rw [hω]

private theorem determ_recenter_one_ae {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    (fun ω => l7b_recenter (h ω) 1 0) =ᵐ[P] h := by
  filter_upwards [hh.2] with ω hω
  dsimp [l7b_recenter]
  rw [hω, neg_zero, addConst_zero]

private theorem determ_scale_one_ae {h : Ω → DistRd d} (ξ : ℝ)
    (hh : IsNormalizedLGF h P) :
    (fun ω => l7b_scale ξ h 1 0 ω) =ᵐ[P] fun _ => (1 : ℝ≥0∞) := by
  filter_upwards [hh.2] with ω hω
  simp [l7b_scale, hω]

/-- The inside and outside internal metrics of a xi-additive metric are
conditionally independent given the complete normalized field. -/
theorem determ_local_ci_compl [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {D : Ω → ContMetric d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    (V : TopologicalSpace.Opens (Rd d)) (hV : IsNiceOpen V) :
    LQGMetric.CondIndepEv (fullSigmaRd h)
      (famSigmaRd (internalFamRd D) V)
      (famSigmaRd (internalFamRd D) (closure (V : Set (Rd d)))ᶜ) P := by
  let W : Set (Rd d) := (closure (V : Set (Rd d)))ᶜ
  have hWo : IsOpen W := isClosed_closure.isOpen_compl
  let k : Ω → DistRd d := fun ω => l7b_recenter (h ω) 1 0
  let SA : MeasurableSpace Ω := famSigmaRd (l7b_chainFam ξ h D 1 0) V
  let SB : MeasurableSpace Ω := famSigmaRd (l7b_chainFam ξ h D 1 0) W
  let SA' : MeasurableSpace Ω := famSigmaRd (fun ω S u v => (D ω).chainInf S u v) V
  let SB' : MeasurableSpace Ω := famSigmaRd (fun ω S u v => (D ω).chainInf S u v) W
  letI : MeasurableSpace Ω := mΩ
  have hlen : ∀ᵐ ω ∂P, (D ω).IsLength := hloc.2.2.1.mono fun _ hω => hω.1
  have hk : k =ᵐ[P] h := determ_recenter_one_ae hh
  have hscale := determ_scale_one_ae ξ hh
  have hAV : (fun ω => l7b_chainFam ξ h D 1 0 ω V) =ᵐ[P]
      (fun ω u v => (D ω).chainInf V u v) := by
    filter_upwards [hscale] with ω hω
    funext u v
    simp only [l7b_chainFam, l7b_scale] at hω ⊢
    rw [hω, one_mul]
  have hBW : (fun ω => l7b_chainFam ξ h D 1 0 ω W) =ᵐ[P]
      (fun ω u v => (D ω).chainInf W u v) := by
    filter_upwards [hscale] with ω hω
    funext u v
    simp only [l7b_chainFam, l7b_scale] at hω ⊢
    rw [hω, one_mul]
  have hG : fieldSigmaRd k V ≤ mΩ := by
    exact (((measurable_restrictTo V).comp (comap_measurable k)).comap_le).trans
      ((l7b_measurable_recenter 1 0).comp hh.1.measurable).comap_le
  have hA : SA ≤ mΩ :=
    (l7b_measurable_chainFam ξ hh.1.measurable hloc.1 1 0 V).comap_le
  have hB : SB ≤ mΩ :=
    (l7b_measurable_chainFam ξ hh.1.measurable hloc.1 1 0 W).comap_le
  have hH : fullSigmaRd h ≤ mΩ := hh.1.measurable.comap_le
  have hGm : fieldSigmaRd k V ≤ fullSigmaRd k :=
    ((measurable_restrictTo V).comp (comap_measurable k)).comap_le
  have hci := hloc.2.2.2 0 1 one_pos V hV
  have hci0 : LQGMetric.CondIndepEv (fieldSigmaRd k V)
      (famSigmaRd (l7b_intFam ξ h D 1 0) V)
      (fullSigmaRd k ⊔ famSigmaRd (l7b_intFam ξ h D 1 0) W) P := by
    exact hci.mono le_sup_left le_sup_left
  have hci' : LQGMetric.CondIndepEv (fieldSigmaRd k V) SA (fullSigmaRd k ⊔ SB) P := by
    apply LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hci0
    · exact (l7b_chainSigma_le_ae_int hlen 1 0 V.isOpen)
    · exact sup_le (le_sup_left.trans (le_aeClosure _))
        ((l7b_chainSigma_le_ae_int hlen 1 0 hWo).trans
          (aeClosure_mono le_sup_right))
  have hGtoH : fieldSigmaRd k V ≤ aeClosure P (fullSigmaRd h) :=
    hGm.trans (determ_sigma_le_ae_of_ae_eq hk)
  have hHtoG : fullSigmaRd h ≤ aeClosure P (fullSigmaRd k) :=
    determ_sigma_le_ae_of_ae_eq hk.symm
  have hA' : SA' ≤ aeClosure P SA := determ_sigma_le_ae_of_ae_eq hAV.symm
  have hB' : SB' ≤ aeClosure P SB := determ_sigma_le_ae_of_ae_eq hBW.symm
  have hchain : LQGMetric.CondIndepEv (fullSigmaRd h) SA' SB' P := by
    refine condIndepEv_transfer hG hA
      (sup_le (((l7b_measurable_recenter 1 0).comp hh.1.measurable).comap_le) hB)
      hH hci' hGtoH ?_ ?_ ?_
    · exact hHtoG.trans (aeClosure_mono (le_sup_left.trans le_sup_left))
    · exact hA'.trans (aeClosure_mono le_sup_left)
    · exact hB'.trans (aeClosure_mono (le_sup_right.trans le_sup_left))
  have hIntV : (fun ω => (D ω).internal (V : Set (Rd d))) =ᵐ[P]
      (fun ω => (D ω).chainInf (V : Set (Rd d))) := by
    filter_upwards [hlen] with ω hω
    funext u v
    exact (D ω).internal_eq_chainInf hω V.isOpen u v
  have hIntW : (fun ω => (D ω).internal W) =ᵐ[P]
      (fun ω => (D ω).chainInf W) := by
    filter_upwards [hlen] with ω hω
    funext u v
    exact (D ω).internal_eq_chainInf hω hWo u v
  exact LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hchain
    (determ_sigma_le_ae_of_ae_eq hIntV)
    (determ_sigma_le_ae_of_ae_eq hIntW)

end HigherDimLQGMetric
