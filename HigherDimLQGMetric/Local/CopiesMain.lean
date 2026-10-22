import HigherDimLQGMetric.Local.CopiesMetric

/-!
# Joint locality of conditionally independent metric copies

The proof uses Borel chain representatives of open-set internal metrics, followed by
the conditional-independence calculation of MA5 A16.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

/-- At a fixed nice open set, independent metric copies are jointly local after recentering. -/
theorem l7b_joint_local_at {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hlen₁ : ∀ᵐ ω ∂P, (D₁ ω).IsLength) (hlen₂ : ∀ᵐ ω ∂P, (D₂ ω).IsLength)
    (hcopy : CondIndepEv (fullSigmaRd h) (MeasurableSpace.comap D₁ inferInstance)
      (MeasurableSpace.comap D₂ inferInstance) P)
    (z : Rd d) (r : ℝ) (hr : 0 < r) (V : TopologicalSpace.Opens (Rd d))
    (hloc₁ : IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_intFam ξ h D₁ r z) (l7b_intFam ξ h D₁ r z))
    (hloc₂ : IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_intFam ξ h D₂ r z) (l7b_intFam ξ h D₂ r z))
    (hV : IsNiceOpen V) :
    CondIndepEv (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
      (famSigmaRd (l7b_intFam ξ h D₁ r z) V ⊔ famSigmaRd (l7b_intFam ξ h D₂ r z) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
        famSigmaRd (l7b_intFam ξ h D₁ r z) (closure (V : Set (Rd d)))ᶜ ⊔
        famSigmaRd (l7b_intFam ξ h D₂ r z) (closure (V : Set (Rd d)))ᶜ) P := by
  let W : Set (Rd d) := (closure (V : Set (Rd d)))ᶜ
  let k : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let G := fieldSigmaRd k V
  let H' := fullSigmaRd k
  let H := fullSigmaRd h
  let S₁ := MeasurableSpace.comap D₁ inferInstance
  let S₂ := MeasurableSpace.comap D₂ inferInstance
  let R₁ := famSigmaRd (l7b_intFam ξ h D₁ r z) (V : Set (Rd d))
  let R₂ := famSigmaRd (l7b_intFam ξ h D₂ r z) (V : Set (Rd d))
  let T₁ := famSigmaRd (l7b_intFam ξ h D₁ r z) W
  let T₂ := famSigmaRd (l7b_intFam ξ h D₂ r z) W
  let A₁ := famSigmaRd (l7b_chainFam ξ h D₁ r z) (V : Set (Rd d))
  let A₂ := famSigmaRd (l7b_chainFam ξ h D₂ r z) (V : Set (Rd d))
  let B₁ := famSigmaRd (l7b_chainFam ξ h D₁ r z) W
  let B₂ := famSigmaRd (l7b_chainFam ξ h D₂ r z) W
  letI : MeasurableSpace Ω := mΩ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have hHm : H ≤ mΩ := hh.1.measurable.comap_le
  have hH'm : H' ≤ mΩ :=
    ((l7b_measurable_recenter (d := d) r z).comp hh.1.measurable).comap_le
  have hGm : G ≤ H' :=
    ((measurable_restrictTo V).comp (comap_measurable k)).comap_le
  have hGH : G ≤ H := hGm.trans (l7b_recenterSigma_le_fullSigma h r z)
  have hHrec : H ≤ aeClosure P H' := l7b_fullSigma_le_aeClosure_recenter hd hh hr z
  have hSm₁ : S₁ ≤ mΩ := hD₁.comap_le
  have hSm₂ : S₂ ≤ mΩ := hD₂.comap_le
  have hObs₁ : ∀ U : Set (Rd d), Measurable[S₁ ⊔ H]
      (fun ω => l7b_chainFam ξ h D₁ r z ω U) := by
    intro U
    have hDm : Measurable[S₁] D₁ := comap_measurable D₁
    exact l7b_measurable_chainFam ξ
      ((comap_measurable h).mono (le_sup_right : H ≤ S₁ ⊔ H) le_rfl)
      (hDm.mono (le_sup_left : S₁ ≤ S₁ ⊔ H) le_rfl) r z U
  have hObs₂ : ∀ U : Set (Rd d), Measurable[S₂ ⊔ H]
      (fun ω => l7b_chainFam ξ h D₂ r z ω U) := by
    intro U
    have hDm : Measurable[S₂] D₂ := comap_measurable D₂
    exact l7b_measurable_chainFam ξ
      ((comap_measurable h).mono (le_sup_right : H ≤ S₂ ⊔ H) le_rfl)
      (hDm.mono (le_sup_left : S₂ ≤ S₂ ⊔ H) le_rfl) r z U
  have hA₁m : A₁ ≤ mΩ := (hObs₁ V).mono
      (sup_le hSm₁ hHm) le_rfl |>.comap_le
  have hB₁m : B₁ ≤ mΩ := (hObs₁ W).mono
      (sup_le hSm₁ hHm) le_rfl |>.comap_le
  have hA₂m : A₂ ≤ mΩ := (hObs₂ V).mono
      (sup_le hSm₂ hHm) le_rfl |>.comap_le
  have hB₂m : B₂ ≤ mΩ := (hObs₂ W).mono
      (sup_le hSm₂ hHm) le_rfl |>.comap_le
  have hlocR₁ : CondIndepEv G R₁ (H' ⊔ T₁) P := by
    have h := hloc₁ V hV
    change CondIndepEv G (R₁ ⊔ R₁) (H' ⊔ T₁ ⊔ T₁) P at h
    simpa only [sup_idem, sup_assoc] using h
  have hlocR₂ : CondIndepEv G R₂ (H' ⊔ T₂) P := by
    have h := hloc₂ V hV
    change CondIndepEv G (R₂ ⊔ R₂) (H' ⊔ T₂ ⊔ T₂) P at h
    simpa only [sup_idem, sup_assoc] using h
  have hchainA₁ : A₁ ≤ aeClosure P R₁ :=
    l7b_chainSigma_le_ae_int hlen₁ r z V.isOpen
  have hchainA₂ : A₂ ≤ aeClosure P R₂ :=
    l7b_chainSigma_le_ae_int hlen₂ r z V.isOpen
  have hchainB₁ : B₁ ≤ aeClosure P T₁ :=
    l7b_chainSigma_le_ae_int hlen₁ r z hW
  have hchainB₂ : B₂ ≤ aeClosure P T₂ :=
    l7b_chainSigma_le_ae_int hlen₂ r z hW
  have hlocA₁ : CondIndepEv G A₁ (H' ⊔ B₁) P :=
    CondIndepEv.of_le_aeClosure hlocR₁ hchainA₁
      (sup_le (le_sup_left.trans (le_aeClosure _))
        (hchainB₁.trans (aeClosure_mono le_sup_right)))
  have hlocA₂ : CondIndepEv G A₂ (H' ⊔ B₂) P :=
    CondIndepEv.of_le_aeClosure hlocR₂ hchainA₂
      (sup_le (le_sup_left.trans (le_aeClosure _))
        (hchainB₂.trans (aeClosure_mono le_sup_right)))
  have hlocH₁ : CondIndepEv G A₁ (H ⊔ B₁) P :=
    CondIndepEv.of_le_aeClosure hlocA₁ (le_aeClosure _)
      (sup_le (hHrec.trans (aeClosure_mono le_sup_left))
        (le_sup_right.trans (le_aeClosure _)))
  have hlocH₂ : CondIndepEv G A₂ (H ⊔ B₂) P :=
    CondIndepEv.of_le_aeClosure hlocA₂ (le_aeClosure _)
      (sup_le (hHrec.trans (aeClosure_mono le_sup_left))
        (le_sup_right.trans (le_aeClosure _)))
  have hjoin : CondIndepEv G (A₁ ⊔ A₂) (H ⊔ B₁ ⊔ B₂) P :=
    l7b_joint_ci hGH hHm hSm₁ hSm₂ hA₁m hA₂m hB₁m hB₂m
      (sup_le (hObs₁ V).comap_le (hObs₁ W).comap_le)
      (sup_le (hObs₂ V).comap_le (hObs₂ W).comap_le)
      hlocH₁ hlocH₂ hcopy
  have hrawA₁ : R₁ ≤ aeClosure P A₁ := l7b_intSigma_le_ae_chain hlen₁ r z V.isOpen
  have hrawA₂ : R₂ ≤ aeClosure P A₂ := l7b_intSigma_le_ae_chain hlen₂ r z V.isOpen
  have hrawB₁ : T₁ ≤ aeClosure P B₁ := l7b_intSigma_le_ae_chain hlen₁ r z hW
  have hrawB₂ : T₂ ≤ aeClosure P B₂ := l7b_intSigma_le_ae_chain hlen₂ r z hW
  change CondIndepEv G (R₁ ⊔ R₂) (H' ⊔ T₁ ⊔ T₂) P
  exact CondIndepEv.of_le_aeClosure hjoin
    (sup_le (hrawA₁.trans (aeClosure_mono le_sup_left))
      (hrawA₂.trans (aeClosure_mono le_sup_right)))
    (sup_le (sup_le ((l7b_recenterSigma_le_fullSigma h r z).trans
        (le_sup_left.trans le_sup_left) |>.trans (le_aeClosure _))
      (hrawB₁.trans (aeClosure_mono (le_sup_right.trans le_sup_left))))
      (hrawB₂.trans (aeClosure_mono le_sup_right)))

/-- The A16 conclusion in dimensions where sphere averages converge. -/
theorem l7b_copies_of_dim {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (h₁ : IsXiAdditiveRd ξ P h D₁ D₁)
    (h₂ : IsXiAdditiveRd ξ P h D₂ D₂)
    (hcopy : CondIndepEv (fullSigmaRd h) (MeasurableSpace.comap D₁ inferInstance)
      (MeasurableSpace.comap D₂ inferInstance) P) :
    IsXiAdditiveRd ξ P h D₁ D₂ := by
  rcases h₁ with ⟨hD₁, _, hlen₁, hloc₁⟩
  rcases h₂ with ⟨hD₂, _, hlen₂, hloc₂⟩
  refine ⟨hD₁, hD₂, ?_, ?_⟩
  · filter_upwards [hlen₁, hlen₂] with ω hω₁ hω₂
    exact ⟨hω₁.1, hω₂.1⟩
  · intro z r hr V hV
    exact l7b_joint_local_at hd ξ P h D₁ D₂ hh hD₁ hD₂
      (hlen₁.mono fun ω hω => hω.1) (hlen₂.mono fun ω hω => hω.1)
      hcopy z r hr V (hloc₁ z r hr) (hloc₂ z r hr) hV

end HigherDimLQGMetric
