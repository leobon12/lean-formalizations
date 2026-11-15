/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC13Gaussian
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# The filled-pocket mean equals the marked wall mean in the pocket

PROVE-SIDE-COLLAR2. The pocket may be selected using the wall labels.
It need not be measurable from the unmarked wall union. Reuse marked
Proposition 3.9 and compare its enlarged kernel with the filled set's
germ kernel, whose variance is the same on the pocket. The conclusion
holds for arbitrary versions of both local means.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.SideC13

open LocalSets WholeField MarkedProp39 Aux119Heights

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A C : Ω → Set ℂ} {h gA gB : Ω → DistOn upperHalfPlaneOpens}

/-- The centered marked kernel on a selected union of components. -/
theorem ae_condExp_exp_sub_marked_component
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ)
    (hloc : IsLocalSet A h P) (hmark : IsHistoryAvoidanceLocal ℋ A h P)
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma]
      (fun ω => H \ C ω))
    (hCs : ∀ ω, C ω ⊆ H \ A ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    (hgA : IsLocalSetMean A h P gA) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport ψ ⊆ C ω →
      P[fun ω => Complex.exp (Complex.I * ((h ω ψ - gA ω ψ : ℝ) : ℂ)) |
        markedOffCoverSigma A C ℋ h] ω =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω) ψ ψ) : ℝ) : ℂ) := by
  have h𝒦le := markedOffCoverSigma_le hh.measurable hAm hℋ hCm
  have hA𝒦 : germSigma A h ≤ markedOffCoverSigma A C ℋ h :=
    le_sup_left.trans (le_markedOffCoverSigma_germ C)
  have hFull := ae_condExp_exp_eq_of_le_markedOffCover hh hAm hℋ hloc hmark hCm
    (hCc.mono fun ω hω => ⟨hCs ω, hω⟩) hgA (le_markedOffCoverSigma_germ C) le_rfl ψ
  have hPull := condExp_exp_mul_of_measurable (P := P) (m := markedOffCoverSigma A C ℋ h)
      (W := fun ω => -gA ω ψ) (F := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)))
    (((LQGMetric.measurable_distOn_apply ψ).comp hgA.1).mono hA𝒦 le_rfl).neg
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hh.measurable) (P := P)) h𝒦le
  have he : (fun ω => Complex.exp (Complex.I * ((h ω ψ - gA ω ψ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((-gA ω ψ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h ω ψ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  filter_upwards [hFull, hPull] with ω hFullω hPullω hs
  rw [hPullω, hFullω hs, ← mul_assoc, ← Complex.exp_add]
  have hz : Complex.I * ((-gA ω ψ : ℝ) : ℂ) + Complex.I * (gA ω ψ : ℂ) = 0 := by
    push_cast
    ring
  rw [hz, Complex.exp_zero, one_mul]

/-- Per-test filled-pocket comparison. The marks may contain the entire
labelled wall histories; no conditional independence of the two sets is
assumed. -/
theorem ae_apply_filled_eq_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H) (hℋ : ℋ ≤ mΩ)
    (hloc : IsLocalSet A h P) (hmark : IsHistoryAvoidanceLocal ℋ A h P)
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma]
      (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ A ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    (hgA : IsLocalSetMean A h P gA)
    (hgB : IsLocalSetMean (fun ω => H \ C ω) h P gB)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω → gB ω φ = gA ω φ := by
  let B : Ω → Set ℂ := fun ω => H \ C ω
  have hBm : Measurable[mΩ, hittingSigma] B := hCm.mono (sup_le hAm.comap_le hℋ) le_rfl
  have hHB : ∀ ω, H \ B ω = C ω := fun ω => sdiff_sdiff_cancel_left ((hCs ω).trans sdiff_subset)
  have hBreg : ∀ ω, relClosureH (B ω) = B ω := fun ω =>
    relClosureH_eq sdiff_subset (by rw [hHB]; exact hCo ω)
  have hSB : (fun ω => (H \ C ω) ∪ A ω) = B := by
    funext ω
    apply union_eq_left.2
    intro z hz
    exact ⟨hAH ω hz, fun hzC => (hCs ω hzC).2 hz⟩
  have h𝒦le : (markedOffCoverSigma A C ℋ h) ≤ mΩ := markedOffCoverSigma_le hh.measurable hAm hℋ hCm
  have hB𝒦 : germSigma B h ≤ (markedOffCoverSigma A C ℋ h) := by
    have hle := germSigma_le_markedOffCoverSigma (A := A) (ℋ := ℋ) (h := h) C
    rw [hSB] at hle
    exact hle
  have hA𝒦 : germSigma A h ≤ (markedOffCoverSigma A C ℋ h) := le_sup_left.trans (le_markedOffCoverSigma_germ C)
  let E : Set Ω := {ω | Disjoint (tsupport φ) (relClosureH (B ω))}
  have hE : MeasurableSet[germSigma B h] E :=
    comap_le_germSigma B h _ ⟨_, measurableSet_disjoint_relClosureH φ.hasCompactSupport
      φ.tsupport_subset, rfl⟩
  have hEs : ∀ ω, ω ∈ E ↔ tsupport φ ⊆ C ω := by
    intro ω
    change Disjoint (tsupport φ) (relClosureH (B ω)) ↔ _
    rw [hBreg ω]
    constructor
    · intro hd z hz
      by_contra hzC
      exact Set.disjoint_left.1 hd hz ⟨φ.tsupport_subset hz, hzC⟩
    · intro hs
      exact Set.disjoint_left.2 fun z hz hzB => hzB.2 (hs hz)
  have hUpper := ae_condExp_exp_sub_marked_component hh hAm hℋ hloc hmark hCm hCs hCc hgA
  have hUpper' : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * ((h ω (c • φ) - gA ω (c • φ) : ℝ) : ℂ)) |
        markedOffCoverSigma A C ℋ h] ω =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) (c • φ) (c • φ)) : ℝ) : ℂ) := by
    intro c
    filter_upwards [hUpper (c • φ)] with ω hω hωE
    rw [hHB]
    exact hω ((tsupport_smul_subset_right (fun _ => c) φ).trans ((hEs ω).1 hωE))
  have heq := ae_apply_eq_on_of_upper_condCharFun hB𝒦 h𝒦le hh.measurable hgB.1
    (hgA.1.mono hA𝒦 le_rfl) hgB.2.2 φ hE hUpper'
  filter_upwards [heq] with ω hω hs
  exact hω ((hEs ω).2 hs)

/-- The filled and marked means agree simultaneously in all pairings
supported in the selected pocket. -/
theorem ae_forall_apply_filled_eq_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H) (hℋ : ℋ ≤ mΩ)
    (hloc : IsLocalSet A h P) (hmark : IsHistoryAvoidanceLocal ℋ A h P)
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma]
      (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ A ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    (hgA : IsLocalSetMean A h P gA)
    (hgB : IsLocalSetMean (fun ω => H \ C ω) h P gB) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → gB ω φ = gA ω φ := by
  have hHB : ∀ ω, H \ (H \ C ω) = C ω :=
    fun ω => sdiff_sdiff_cancel_left ((hCs ω).trans sdiff_subset)
  have hB : ∀ᵐ ω ∂P, IsHarmonicDistOn (gB ω) (C ω) := by
    simpa only [hHB] using hgB.2.1
  have hA : ∀ᵐ ω ∂P, IsHarmonicDistOn (gA ω) (C ω) :=
    hgA.2.1.mono fun ω ⟨v, hv, hrep⟩ =>
      ⟨v, hv.mono (hCs ω), fun φ hφ => hrep φ (hφ.trans (hCs ω))⟩
  apply ae_forall_apply_eq_of_bump (ae_of_all _ fun ω => ⟨hCo ω, (hCs ω).trans sdiff_subset⟩) hB hA
  intro x δ hδ hB
  filter_upwards [ae_apply_filled_eq_marked hh hAm hAH hℋ hloc hmark hCm hCo hCs hCc hgA hgB
    (GFF.bumpTest x hδ hB)] with ω hω hs
  exact hω ((GFF.tsupport_bumpFun_subset hδ).trans hs)

/-- Every harmonic representative of the filled mean equals every
representative of the wall mean inside the selected pocket. -/
theorem ae_representatives_filled_eq_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H) (hℋ : ℋ ≤ mΩ)
    (hloc : IsLocalSet A h P) (hmark : IsHistoryAvoidanceLocal ℋ A h P)
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma]
      (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ A ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    (hgA : IsLocalSetMean A h P gA)
    (hgB : IsLocalSetMean (fun ω => H \ C ω) h P gB) :
    ∀ᵐ ω ∂P, ∀ vB vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vB (C ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω →
        gB ω φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        gA ω φ = ∫ z, vA z * φ z) → EqOn vB vA (C ω) := by
  filter_upwards [ae_forall_apply_filled_eq_marked hh hAm hAH hℋ hloc hmark hCm hCo hCs hCc hgA hgB]
    with ω heq vB vA hvB hrepB hvA hrepA
  apply Sec6.eqOn_of_integral_mul_eq (hCo ω) ((hCs ω).trans sdiff_subset) hvB (hvA.mono (hCs ω))
  intro φ hφ
  rw [← hrepB φ hφ, ← hrepA φ (hφ.trans (hCs ω)), heq φ hφ]

end InteractingSLE.Sec7.SideC13
