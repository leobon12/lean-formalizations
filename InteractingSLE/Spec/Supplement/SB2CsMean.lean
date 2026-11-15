/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CsFam
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofCover
import InteractingSLE.Spec.Supplement.SB2DrvLineSet
import InteractingSLE.GFF.LocalSets.Prop39

/-!
# The mean of a marked local set does not see the pockets outside its complement component

Packet PROVE-SB2-CONDFIN (round 10, D51 item 1: the joint set's mean). The joint line set `U_J = A₁ ∪ fill (A ∪ B)`
contains the pockets that `A` and B's piece enclose; the union `U_B = A₁ ∪ fill B` of LCMEAN's engine does not.
The engine computes the mean of `U_B`; K2 needs the mean of `U_J` on test functions supported in the relative
component `ℍ ∖ U_J`. They agree there:

* **`ae_localSetMean_eq_of_pockets`**: for two history-marked local sets `U_B`, `U_J` with the same marks `ℋ`, both
  `ℋ`-measurable, and versions `g_B`, `g_J` of their means: almost surely, at every sample where `U_B ∩ ℍ ⊆ U_J`, the
  difference `(ℍ ∖ U_B) ∩ U_J` is open (the pockets are components of `ℍ ∖ U_B`) and `supp φ ⊆ ℍ ∖ U_J`, the two
  means agree on `φ`;
* **`ae_localSetMean_eqOn_of_pockets`**: the same for all test functions at once, on the samples of an event where the
  two geometric conditions hold (`LocalSets.ae_forall_apply_eq_of_bump`).

Proof: both sets lie in the union `V = U_B ∪ U_J`, an almost-sure enlargement of `U_J` with `ℋ`-avoidance events, hence
history-marked local (`Lv.isHistoryAvoidanceLocal_of_ae_enlargement`); the nested-means lemma
(`FlatClockProof.IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq`) applies to `U_B ⊆ V` and to `U_J ⊆ V`; at such a
sample `ℍ ∖ V = ℍ ∖ U_J`, and `σ²_{ℍ ∖ U_B}(φ) = σ²_{ℍ ∖ U_J}(φ)` by the component decomposition of the Green
covariance (`zeroGFFTestCov_eq_of_isClopen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

universe u

namespace InteractingSLE.Theorem14.SB.Cs

open LocalSets WholeField

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The means of `U_B` and `U_J` agree off the pockets.** -/
theorem ae_localSetMean_eq_of_pockets (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ)
    {UB UJ : Ω → Set ℂ} (hBm : Measurable[ℋ, hittingSigma] UB) (hJm : Measurable[ℋ, hittingSigma] UJ)
    (hBc : ∀ ω, UB ω ⊆ H ∧ IsOpen (H \ UB ω)) (hJc : ∀ ω, UJ ω ⊆ H ∧ IsOpen (H \ UJ ω))
    (hBloc : IsHistoryAvoidanceLocal ℋ UB h P) (hJloc : IsHistoryAvoidanceLocal ℋ UJ h P)
    {gB gJ : Ω → DistOn upperHalfPlaneOpens} (hgB : IsLocalSetMean UB h P gB) (hgJ : IsLocalSetMean UJ h P gJ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, UB ω ⊆ UJ ω → IsOpen ((H \ UB ω) ∩ UJ ω) → tsupport φ ⊆ H \ UJ ω → gB ω φ = gJ ω φ := by
  set V : Ω → Set ℂ := fun ω => UB ω ∪ UJ ω with hVdef
  have hVm : Measurable[ℋ, hittingSigma] V := by
    let _ : MeasurableSpace Ω := ℋ
    exact measurable_union_hitting hBm hJm
  have hVc : ∀ ω, V ω ⊆ H ∧ IsOpen (H \ V ω) := by
    intro ω
    refine ⟨union_subset (hBc ω).1 (hJc ω).1, ?_⟩
    have e : H \ V ω = (H \ UB ω) ∩ (H \ UJ ω) := by
      ext z
      simp only [hVdef, Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hBc ω).2.inter (hJc ω).2
  have hVloc : IsHistoryAvoidanceLocal ℋ V h P :=
    Lv.isHistoryAvoidanceLocal_of_ae_enlargement hJloc
      (Eventually.of_forall fun ω z hz => Or.inr hz.1) fun U hUH => hVm (measurableSet_avoid U.isOpen hUH)
  have hVmΩ : Measurable[mΩ, hittingSigma] V := hVm.mono hℋ le_rfl
  have hVl : IsLocalSet V h P :=
    ((isLocalSet_tfae hh hVmΩ (Eventually.of_forall hVc)).out 4 1).2 hVloc.isAvoidanceLocal
  obtain ⟨gV, hgV⟩ := IsLocalSet.exists_isLocalSetMean hh hVmΩ hVl
  have hBmΩ : Measurable[mΩ, hittingSigma] UB := hBm.mono hℋ le_rfl
  have hJmΩ : Measurable[mΩ, hittingSigma] UJ := hJm.mono hℋ le_rfl
  have hrecB : MeasurableSpace.comap UB hittingSigma ≤
      aeSigma (MeasurableSpace.comap V hittingSigma ⊔ ℋ) P :=
    (hBm.comap_le.trans le_sup_right).trans (le_aeSigma _ P)
  have hrecJ : MeasurableSpace.comap UJ hittingSigma ≤
      aeSigma (MeasurableSpace.comap V hittingSigma ⊔ ℋ) P :=
    (hJm.comap_le.trans le_sup_right).trans (le_aeSigma _ P)
  have h1 := Sec7.FlatClockProof.IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hh hBmΩ hVmΩ hℋ hℋ le_rfl
    hBloc hVloc (Eventually.of_forall hBc) (Eventually.of_forall hVc)
    (Eventually.of_forall fun ω z hz => Or.inl hz) hrecB hgB hgV φ
  have h2 := Sec7.FlatClockProof.IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hh hJmΩ hVmΩ hℋ hℋ le_rfl
    hJloc hVloc (Eventually.of_forall hJc) (Eventually.of_forall hVc)
    (Eventually.of_forall fun ω z hz => Or.inr hz) hrecJ hgJ hgV φ
  filter_upwards [h1, h2] with ω hB hJ hsub hopen hsupp
  have hVJ : H \ V ω = H \ UJ ω := by
    ext z
    simp only [hVdef, Set.mem_sdiff, mem_union]
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hz, fun h' => hn (Or.inr h')⟩
    · rintro ⟨hz, hn⟩
      exact ⟨hz, fun h' => h'.elim (fun hb => hn (hsub hb)) hn⟩
  have hcovB : zeroGFFTestCov (H \ UB ω) φ φ = zeroGFFTestCov (H \ UJ ω) φ φ := by
    refine zeroGFFTestCov_eq_of_isClopen (hBc ω).2 sdiff_subset (hJc ω).2
      (fun z hz => ⟨hz.1, fun h' => hz.2 (hsub h')⟩) ?_ φ hsupp
    have e : (H \ UB ω) \ (H \ UJ ω) = (H \ UB ω) ∩ UJ ω := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff]
      constructor
      · rintro ⟨⟨hz, hn⟩, h'⟩
        exact ⟨⟨hz, hn⟩, by by_contra hc; exact h' ⟨hz, hc⟩⟩
      · rintro ⟨⟨hz, hn⟩, hj⟩
        exact ⟨⟨hz, hn⟩, fun h' => h'.2 hj⟩
    rw [e]
    exact hopen
  have e1 := hB (by rw [hcovB, hVJ])
  have e2 := hJ (by rw [hVJ])
  rw [e1, e2]

/-- **The means of `U_B` and `U_J` agree off the pockets, for all test functions at once**, on an event of samples
where `U_B ⊆ U_J` and the pockets `(ℍ ∖ U_B) ∩ U_J` are open. -/
theorem ae_localSetMean_eqOn_of_pockets (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ)
    {UB UJ : Ω → Set ℂ} (hBm : Measurable[ℋ, hittingSigma] UB) (hJm : Measurable[ℋ, hittingSigma] UJ)
    (hBc : ∀ ω, UB ω ⊆ H ∧ IsOpen (H \ UB ω)) (hJc : ∀ ω, UJ ω ⊆ H ∧ IsOpen (H \ UJ ω))
    (hBloc : IsHistoryAvoidanceLocal ℋ UB h P) (hJloc : IsHistoryAvoidanceLocal ℋ UJ h P)
    {gB gJ : Ω → DistOn upperHalfPlaneOpens} (hgB : IsLocalSetMean UB h P gB) (hgJ : IsLocalSetMean UJ h P gJ)
    {Good : Set Ω} (hgood : ∀ ω ∈ Good, UB ω ⊆ UJ ω ∧ IsOpen ((H \ UB ω) ∩ UJ ω)) :
    ∀ᵐ ω ∂P, ω ∈ Good → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ UJ ω → gB ω φ = gJ ω φ := by
  classical
  set O : Ω → Set ℂ := fun ω => if ω ∈ Good then H \ UJ ω else ∅ with hOdef
  have hOsub : ∀ ω, O ω ⊆ H \ UJ ω := fun ω => by
    by_cases hg : ω ∈ Good
    · simp only [hOdef, hg, ↓reduceIte, subset_rfl]
    · simp only [hOdef, hg, ↓reduceIte, empty_subset]
  have hOsubB : ∀ ω, O ω ⊆ H \ UB ω := fun ω => by
    by_cases hg : ω ∈ Good
    · simp only [hOdef, hg, ↓reduceIte]
      exact fun z hz => ⟨hz.1, fun h' => hz.2 ((hgood ω hg).1 h')⟩
    · simp only [hOdef, hg, ↓reduceIte, empty_subset]
  have hO : ∀ᵐ ω ∂P, IsOpen (O ω) ∧ O ω ⊆ H := Eventually.of_forall fun ω => by
    by_cases hg : ω ∈ Good
    · simp only [hOdef, hg, ↓reduceIte]
      exact ⟨(hJc ω).2, sdiff_subset⟩
    · simp only [hOdef, hg, ↓reduceIte]
      exact ⟨isOpen_empty, empty_subset _⟩
  have hBH : ∀ᵐ ω ∂P, IsHarmonicDistOn (gB ω) (O ω) := by
    filter_upwards [hgB.2.1] with ω hω using IsHarmonicDistOn.mono hω (hOsubB ω)
  have hJH : ∀ᵐ ω ∂P, IsHarmonicDistOn (gJ ω) (O ω) := by
    filter_upwards [hgJ.2.1] with ω hω using IsHarmonicDistOn.mono hω (hOsub ω)
  have hall := ae_forall_apply_eq_of_bump hO hBH hJH fun x δ hδ hB => by
    filter_upwards [ae_localSetMean_eq_of_pockets hh hℋ hBm hJm hBc hJc hBloc hJloc hgB hgJ
      (GFF.bumpTest x hδ hB)] with ω hω hball
    have hg : ω ∈ Good := by
      by_contra hg
      have hne : (Metric.closedBall x δ).Nonempty := ⟨x, Metric.mem_closedBall_self hδ.le⟩
      obtain ⟨z, hz⟩ := hne
      have := hball hz
      simp only [hOdef, hg, ↓reduceIte, mem_empty_iff_false] at this
    obtain ⟨hsub, hopen⟩ := hgood ω hg
    exact hω hsub hopen ((GFF.tsupport_bumpFun_subset hδ).trans (hball.trans (hOsub ω)))
  filter_upwards [hall] with ω hω hg φ hφ
  refine hω φ ?_
  simp only [hOdef, hg, ↓reduceIte]
  exact hφ

end InteractingSLE.Theorem14.SB.Cs
