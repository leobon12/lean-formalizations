import HigherDimLQGMetric.Main.Probability
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLFPP.Paths.Measurable
import HigherDimLFPP.Exist.Quantile

/-!
# The fixed LFPP normalization is a positive lower median

Packet L10a. A continuous modification on a full-measure event makes the
whole-space LFPP point distance a.e.-measurable. The lower-median API then
identifies the frozen `aEps` with the usual median of its law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- A measurable real process with continuous paths gives an a.e.-measurable
continuous-map-valued random variable. Port of `LQGMetric.DG.aemeasurable_toContMap`. -/
theorem l10a_aemeasurable_toContMap {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (Y : Rd d → Ω → ℝ)
    (hm : ∀ z, AEMeasurable (Y z) P)
    (hc : ∀ ω, Continuous fun z => Y z ω) :
    AEMeasurable (fun ω => (⟨fun z => Y z ω, hc ω⟩ : C(Rd d, ℝ))) P := by
  have key : @Measurable (NullMeasurableSpace Ω P) C(Rd d, ℝ) _ _
      (fun ω => (⟨fun z => Y z ω, hc ω⟩ : C(Rd d, ℝ))) := by
    refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun z => ?_
    exact (hm z).nullMeasurable
  exact (show NullMeasurable (fun ω => (⟨fun z => Y z ω, hc ω⟩ : C(Rd d, ℝ))) P
    from fun s hs => key hs).aemeasurable

/-- Each convolution-field coordinate is measurable, even at junk inputs. -/
theorem l10a_measurable_convMollify_apply {d : ℕ} (κ : Rd d → ℝ)
    (ε : ℝ) (z : Rd d) : Measurable fun g : DistRd d => convMollify κ ε g z := by
  unfold convMollify
  exact (StronglyMeasurable.limUnder (l := atTop) fun n =>
    (measurable_distOn_apply (convTrunc κ ε z n)).stronglyMeasurable).measurable

/-- For a normalized LGF, every positive-cutoff convolution field is continuous a.s. -/
theorem l10a_ae_continuous_convMollify {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Continuous fun z => convMollify κ ε (h ω) z := by
  have hC := l2b_ae_convMollify_continuousOn d hd κ hκ P h hh
  exact hC.mono (fun ω hω => by
    have hc : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
    have hf := hω.comp_continuous hc (fun _ => ⟨hε, mem_univ _⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hf)

/-- The whole-space LFPP point distance is a.e.-measurable for a normalized LGF. -/
theorem l10a_aemeasurable_lfppPoint {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)) P := by
  let H : Rd d → Ω → ℝ := fun z ω => convMollify κ ε (h ω) z
  have hm : ∀ z, Measurable (H z) := fun z =>
    (l10a_measurable_convMollify_apply κ ε z).comp hh.1.measurable
  have hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω :=
    l10a_ae_continuous_convMollify hd κ hκ P h hh hε
  classical
  let Y : Rd d → Ω → ℝ := fun z ω =>
    if hcont : Continuous (fun z => H z ω) then H z ω else 0
  have hYc : ∀ ω, Continuous fun z => Y z ω := by
    intro ω
    by_cases hcont : Continuous (fun z => H z ω)
    · have heq : (fun z => Y z ω) = (fun z => H z ω) := by
        funext z
        exact dite_eq_left hcont
      rw [heq]
      exact hcont
    · have heq : (fun z => Y z ω) = (fun _ => 0) := by
        funext z
        exact dite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYae : ∀ᵐ ω ∂P, ∀ z, Y z ω = H z ω := by
    filter_upwards [hc] with ω hω z
    exact dite_eq_left hω
  have hYm : ∀ z, AEMeasurable (Y z) P := by
    intro z
    have heq : Y z =ᵐ[P] H z := hYae.mono fun _ hω => hω z
    exact (aemeasurable_congr heq.symm).1 (hm z).aemeasurable
  have hCM := l10a_aemeasurable_toContMap Y hYm hYc
  have hF : Measurable (fun φ : C(Rd d, ℝ) =>
      HigherDimLFPP.lfppDistOn ξ φ univ 0 (e₁ d)) :=
    HigherDimLFPP.measurable_lfppDistOn_continuousMap isOpen_univ ξ 0 (e₁ d)
  have hAY : AEMeasurable (fun ω =>
      HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ 0 (e₁ d)) P := by
    simpa only [Function.comp_def, ContinuousMap.coe_mk] using hF.comp_aemeasurable hCM
  have heq : (fun ω => HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ 0 (e₁ d)) =ᵐ[P]
      (fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)) := by
    filter_upwards [hYae] with ω hω
    simp only [lfppDist]
    congr 1
    funext z
    exact hω z
  exact (aemeasurable_congr heq).1 hAY

end HigherDimLQGMetric
