import HigherDimLQGMetric.Determ.LocalCI
import HigherDimLQGMetric.Bilip.Observation
import LQGMetric.Papers.LM.T1_7E3

/-!
# Conditional independence of finitely many separated internal observations

The geometric assumptions are given in the form used by a translated cube grid:
finite unions are nice, and an unused open cell misses the closure of the union.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A countable encoding of the internal metric on `W`. -/
def determ_enc (W : Set (Rd d)) (D : ContMetric d) : ℕ → ℝ≥0∞ := fun n =>
  D.chainInf W (TopologicalSpace.denseSeq (Rd d × Rd d) n).1
    (TopologicalSpace.denseSeq (Rd d × Rd d) n).2

theorem determ_measurable_enc (W : Set (Rd d)) : Measurable (determ_enc W) := by
  apply Measurable.of_eval
  intro n
  exact (ContMetric.measurable_chainInf W).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ContMetric d}

private theorem determ_le_aeClosure_trans {X Y Z : MeasurableSpace Ω}
    (hXY : X ≤ aeClosure P Y) (hYZ : Y ≤ aeClosure P Z) :
    X ≤ aeClosure P Z :=
  hXY.trans ((aeClosure_mono hYZ).trans (aeClosure_aeClosure_le Z))

/-- Encoded internal distances are observable from the full internal metric,
up to the length-metric event. -/
theorem determ_enc_sigma_le_internal (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    {W : Set (Rd d)} (hWo : IsOpen W) :
    MeasurableSpace.comap (determ_enc W ∘ D) inferInstance ≤
      aeClosure P (famSigmaRd (internalFamRd D) W) := by
  let F : (Rd d → Rd d → ℝ≥0∞) → ℕ → ℝ≥0∞ := fun ρ n =>
    ρ (TopologicalSpace.denseSeq (Rd d × Rd d) n).1
      (TopologicalSpace.denseSeq (Rd d × Rd d) n).2
  have hFm : Measurable F := Measurable.of_eval fun n =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  let g : Ω → ℕ → ℝ≥0∞ := fun ω => F ((D ω).internal W)
  have heq : (determ_enc W ∘ D) =ᵐ[P] g := by
    filter_upwards [hlen] with ω hω
    funext n
    exact ((D ω).internal_eq_chainInf hω hWo _ _).symm
  have hgm : Measurable[famSigmaRd (internalFamRd D) W] g :=
    hFm.comp (comap_measurable fun ω => (D ω).internal W)
  exact (determ_sigma_le_ae_of_ae_eq heq).trans (aeClosure_mono hgm.comap_le)

/-- The finite-family version of locality used by the conditional product law. -/
theorem determ_seqIndep {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure P] {h : Ω → DistRd d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    (W : ι → Set (Rd d)) (hWo : ∀ i, IsOpen (W i))
    (hNice : ∀ T : Finset ι,
      IsNiceOpen (⟨⋃ i ∈ T, W i, isOpen_biUnion fun i _ => hWo i⟩ : TopologicalSpace.Opens (Rd d)))
    (hSep : ∀ (T : Finset ι) (j : ι), j ∉ T →
      W j ⊆ (closure (⋃ i ∈ T, W i))ᶜ) :
    LQGMetric.LM.T17eSeqIndep h D (fun i => determ_enc (W i)) P := by
  intro T j hj
  let V : TopologicalSpace.Opens (Rd d) :=
    ⟨⋃ i ∈ T, W i, isOpen_biUnion fun i _ => hWo i⟩
  have hsub (i : ι) (hi : i ∈ T) : W i ⊆ (V : Set (Rd d)) :=
    subset_biUnion_of_mem (u := W) hi
  have hWout : IsOpen (closure (V : Set (Rd d)))ᶜ := isClosed_closure.isOpen_compl
  have hout : W j ⊆ (closure (V : Set (Rd d)))ᶜ := hSep T j hj
  have hlen : ∀ᵐ ω ∂P, (D ω).IsLength := hloc.2.2.1.mono fun _ hω => hω.1
  have hci := determ_local_ci_compl hh hloc V (hNice T)
  have hA : (⨆ i ∈ T, MeasurableSpace.comap (determ_enc (W i) ∘ D) inferInstance) ≤
      aeClosure P (famSigmaRd (internalFamRd D) V) := by
    refine iSup₂_le fun i hi => ?_
    exact determ_le_aeClosure_trans (determ_enc_sigma_le_internal hlen (hWo i))
      (BilipNest.famSigma_le_aeClosure hlen (hWo i) V.isOpen (hsub i hi))
  have hB : MeasurableSpace.comap (determ_enc (W j) ∘ D) inferInstance ≤
      aeClosure P (famSigmaRd (internalFamRd D) (closure (V : Set (Rd d)))ᶜ) :=
    determ_le_aeClosure_trans (determ_enc_sigma_le_internal hlen (hWo j))
      (BilipNest.famSigma_le_aeClosure hlen (hWo j) hWout hout)
  exact LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hci hA hB

/-- For almost every field, the encoded observations in separated cells have
product law under the conditional metric kernel. -/
theorem determ_condDistrib_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty (ContMetric d)]
    [IsProbabilityMeasure P] {h : Ω → DistRd d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    (W : ι → Set (Rd d)) (hWo : ∀ i, IsOpen (W i))
    (hNice : ∀ T : Finset ι,
      IsNiceOpen (⟨⋃ i ∈ T, W i, isOpen_biUnion fun i _ => hWo i⟩ : TopologicalSpace.Opens (Rd d)))
    (hSep : ∀ (T : Finset ι) (j : ι), j ∉ T →
      W j ⊆ (closure (⋃ i ∈ T, W i))ᶜ) :
    ∀ᵐ g ∂P.map h,
      (condDistrib D h P g).map (fun D i => determ_enc (W i) D) =
      Measure.pi fun i => (condDistrib D h P g).map (determ_enc (W i)) :=
  LQGMetric.LM.t17e_condDistrib_pi hh.1.measurable hloc.1
    (fun i => determ_measurable_enc (W i))
    (determ_seqIndep hh hloc W hWo hNice hSep)

end HigherDimLQGMetric
