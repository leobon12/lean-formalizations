/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField6Pocket
import InteractingSLE.Spec.Coupling.WholeField4Birth
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.WangWu.NonBoundaryPartition
import InteractingSLE.WangWu.NonBoundaryGerm

/-!
# C.4 at `κ = 4`: labels, hull versions, the first positive stop

Packet PROVE-WHOLEFIELD7 (follow-up note C.4, `source/external/AstraIG1/ig1_followup_proofs.txt` L1651–1704; ruling
R38). The induction of C.4 runs over finitely many deterministic test functions ("labels"). At a time `t` a label with
support `C` is

* **active** (`IsActiveLabel`) if `C` avoids the filled hull `K_t`;
* **a pocket** (`IsPocketLabel`) if all points of `C` are swallowed at one time `β ≤ t` (a set swallowed at once:
  C.3, "every point of `P` has the same first swallowing time").

This file collects the deterministic facts about labels, hitting-measurable versions of hulls at driving stops that
are measurable for the stopped history (`exists_hullVersion`), and the device that makes the birth stop of a pocket
positive (`firstPos`, the first positive term of a nondecreasing sequence of stops: the restart law (WF7) behind
quasi-left continuity is landed only at positive stops or for separated words).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### Labels -/

section Labels

/-- A label with support `C` is **active** at time `t` (for the driving path `w`): `C` avoids the hull `K_t`. -/
def IsActiveLabel (w : ℝ≥0 → ℝ) (C : Set ℂ) (t : ℝ≥0) : Prop :=
  Disjoint C (fwdHull (Ito.rpath w) (t : ℝ))

/-- A label with support `C` is **a pocket** at time `t`: every point of `C` is swallowed at one time `β ≤ t`. -/
def IsPocketLabel (w : ℝ≥0 → ℝ) (C : Set ℂ) (t : ℝ≥0) : Prop :=
  ∃ β : ℝ≥0, β ≤ t ∧ ∀ z ∈ C, swallowTime (Ito.rpath w) z = β

/-- A **label** at time `t`: active or a pocket. -/
def IsLabel (w : ℝ≥0 → ℝ) (C : Set ℂ) (t : ℝ≥0) : Prop :=
  IsActiveLabel w C t ∨ IsPocketLabel w C t

variable {w : ℝ≥0 → ℝ} {C C' : Set ℂ} {t t' : ℝ≥0}

theorem IsActiveLabel.mono (h : IsActiveLabel w C t) (hC : C' ⊆ C) : IsActiveLabel w C' t :=
  h.mono_left hC

theorem IsPocketLabel.mono (h : IsPocketLabel w C t) (hC : C' ⊆ C) : IsPocketLabel w C' t := by
  obtain ⟨β, hβ, hs⟩ := h
  exact ⟨β, hβ, fun z hz => hs z (hC hz)⟩

theorem IsLabel.mono (h : IsLabel w C t) (hC : C' ⊆ C) : IsLabel w C' t :=
  h.imp (fun h => h.mono hC) fun h => h.mono hC

theorem IsPocketLabel.mono_time (h : IsPocketLabel w C t) (htt' : t ≤ t') : IsPocketLabel w C t' := by
  obtain ⟨β, hβ, hs⟩ := h
  exact ⟨β, hβ.trans htt', hs⟩

theorem IsActiveLabel.antitone_time (h : IsActiveLabel w C t) (ht't : t' ≤ t) : IsActiveLabel w C t' :=
  h.mono_right ((QuantumZipper.fwdHull_mono).1 (by exact_mod_cast ht't))

/-- A pocket label lies in the hull at its time. -/
theorem IsPocketLabel.subset_fwdHull (h : IsPocketLabel w C t) (hCH : C ⊆ H) :
    C ⊆ fwdHull (Ito.rpath w) (t : ℝ) := by
  obtain ⟨β, hβ, hs⟩ := h
  intro z hz
  refine ⟨hCH hz, ?_⟩
  rw [hs z hz, ENNReal.ofReal_coe_nnreal]
  exact_mod_cast hβ

/-- A nonempty pocket label is not active. -/
theorem IsPocketLabel.not_isActiveLabel (h : IsPocketLabel w C t) (hCH : C ⊆ H) (hne : C.Nonempty) :
    ¬ IsActiveLabel w C t := fun ha => by
  obtain ⟨z, hz⟩ := hne
  exact Set.disjoint_left.1 ha hz (h.subset_fwdHull hCH hz)

/-- A label whose points are all swallowed after `t` is active at `t`. -/
theorem isActiveLabel_of_lt_swallowTime (h : ∀ z ∈ C, (t : ℝ≥0∞) < swallowTime (Ito.rpath w) z) :
    IsActiveLabel w C t := by
  refine Set.disjoint_left.2 fun z hz hzK => ?_
  have h1 := hzK.2
  rw [ENNReal.ofReal_coe_nnreal] at h1
  exact absurd h1 (not_le.2 (h z hz))

/-- The topological support of a finite sum of test functions lies in the union of the supports. -/
theorem tsupport_sum_subset {ι : Type*} (s : Finset ι) (ψ : ι → TestOn upperHalfPlaneOpens) :
    tsupport (⇑(∑ k ∈ s, ψ k)) ⊆ ⋃ k ∈ s, tsupport (ψ k) := by
  classical
  have hcl : IsClosed (⋃ k ∈ s, tsupport (ψ k)) :=
    s.finite_toSet.isClosed_biUnion fun k _ => isClosed_tsupport _
  refine closure_minimal (fun z hz => ?_) hcl
  rw [Function.mem_support, WangWu.testOn_sum_apply] at hz
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact mem_iUnion₂.2 ⟨k, hk, subset_tsupport _ (Function.mem_support.2 hne)⟩

end Labels

/-! ### The first positive term of a sequence of stops -/

section FirstPos

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

open Classical in
/-- The first positive term of a sequence (`0` if there is none). -/
def firstPos (ρ : ℕ → Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if h : ∃ n, 0 < ρ n ω then ρ (Nat.find h) ω else 0

theorem firstPos_of_exists {ρ : ℕ → Ω → ℝ≥0} {ω : Ω} (h : ∃ n, 0 < ρ n ω) :
    firstPos ρ ω = ρ (Nat.find h) ω := by
  classical
  unfold firstPos
  rw [dite_eq_left_of_eq_true (eq_true h)]

theorem firstPos_of_not_exists {ρ : ℕ → Ω → ℝ≥0} {ω : Ω} (h : ¬ ∃ n, 0 < ρ n ω) :
    firstPos ρ ω = 0 := by
  classical
  unfold firstPos
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem firstPos_pos {ρ : ℕ → Ω → ℝ≥0} {ω : Ω} (h : ∃ n, 0 < ρ n ω) : 0 < firstPos ρ ω := by
  rw [firstPos_of_exists h]
  exact Nat.find_spec h

/-- The first positive term of a nondecreasing sequence is below every positive term. -/
theorem firstPos_le {ρ : ℕ → Ω → ℝ≥0} {ω : Ω} (hm : Monotone fun n => ρ n ω) {n : ℕ}
    (hn : 0 < ρ n ω) : firstPos ρ ω ≤ ρ n ω := by
  have h : ∃ n, 0 < ρ n ω := ⟨n, hn⟩
  rw [firstPos_of_exists h]
  exact hm (Nat.find_min' h hn)

/-- The first positive term is `0` or a term of the sequence. -/
theorem firstPos_eq_zero_or {ρ : ℕ → Ω → ℝ≥0} (ω : Ω) : firstPos ρ ω = 0 ∨ ∃ n, firstPos ρ ω = ρ n ω := by
  by_cases h : ∃ n, 0 < ρ n ω
  · exact Or.inr ⟨_, firstPos_of_exists h⟩
  · exact Or.inl (firstPos_of_not_exists h)

/-- **The first positive term of a sequence of stopping times is a stopping time.** -/
theorem isStoppingTime_firstPos {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime 𝓖 fun ω => (ρ n ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => (firstPos ρ ω : WithTop ℝ≥0) := by
  intro t
  have hz : ∀ j, MeasurableSet[𝓖 t] {ω | ρ j ω = 0} := fun j => by
    have h0 := 𝓖.mono (show (0 : ℝ≥0) ≤ t from bot_le) _ (hρ j 0)
    convert h0 using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, nonpos_iff_eq_zero]
  have hle : ∀ j, MeasurableSet[𝓖 t] {ω | ρ j ω ≤ t} := fun j => by
    convert hρ j t using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  have e : {ω | (firstPos ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | ∀ n, ρ n ω = 0} ∪
        ⋃ n, ({ω | ∀ j < n, ρ j ω = 0} ∩ {ω | ρ n ω = 0}ᶜ ∩ {ω | ρ n ω ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff]
    rw [WithTop.coe_le_coe]
    by_cases h : ∃ n, 0 < ρ n ω
    · rw [firstPos_of_exists h]
      constructor
      · intro ht
        refine Or.inr ⟨Nat.find h, ⟨fun j hj => ?_, (Nat.find_spec h).ne'⟩, ht⟩
        exact nonpos_iff_eq_zero.1 (not_lt.1 (Nat.find_min h hj))
      · rintro (h0 | ⟨n, ⟨hj, hn⟩, ht⟩)
        · exact absurd (h0 (Nat.find h)) (Nat.find_spec h).ne'
        · have hfind : Nat.find h = n := by
            rw [Nat.find_eq_iff]
            exact ⟨pos_iff_ne_zero.2 hn, fun j hjn => not_lt.2 (hj j hjn).le⟩
          rw [hfind]; exact ht
    · rw [firstPos_of_not_exists h]
      push Not at h
      exact iff_of_true bot_le (Or.inl fun n => nonpos_iff_eq_zero.1 (h n))
  rw [e]
  have e0 : {ω | ∀ n, ρ n ω = 0} = ⋂ n, {ω | ρ n ω = 0} := by ext ω; simp
  rw [e0]
  refine (MeasurableSet.iInter fun n => hz n).union (MeasurableSet.iUnion fun n => ?_)
  refine (MeasurableSet.inter ?_ (hz n).compl).inter (hle n)
  have : {ω | ∀ j < n, ρ j ω = 0} = ⋂ j ∈ Finset.range n, {ω | ρ j ω = 0} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun j _ => hz j

end FirstPos

/-! ### Hull versions at driving stops -/

section Hull

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- An announcing sequence of the lifetime by real driving stops, for an admissible seed. -/
theorem exists_isAnnouncingSeq_driving (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ σ₀ : ℕ → Ω → ℝ≥0, IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀ := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  exact ⟨σ₀, hσ₀⟩

/-- **A hull version at a driving stop**: a hitting-measurable random set, almost surely the hull `K_τ`, measurable
for the stopped history `𝓕_τ`. -/
theorem exists_hullVersion (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧
      (∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω : ℝ)) ∧
      Measurable[hτ.measurableSpace, hittingSigma] A := by
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτζ
  obtain ⟨A, hAm, hAe, -⟩ := IsLocalSet.exists_measurable_version
    ((hC.2.2.2.choose_spec _ hτ hτζ').1) hC.2.1
  have hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      (((τ ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := hAe
  obtain ⟨σ₀, hσ₀⟩ := exists_isAnnouncingSeq_driving hC.1 hκ hX
    (not_threshold_seed_of_ae_lt hC.1 hτζ)
  refine ⟨A, hAm, hAK.mono fun ω hω => by rw [hω, WithTop.untopD_coe], ?_⟩
  exact measurable_hull_stopping hC.1 hX hσ₀ hτ hτζ' hAm hAK

end Hull

/-! ### The retained kernel value at `κ = 4`: products and left limits -/

section KerFacts

variable {nL nR : ℕ}

/-- **The frozen mean at time `t` is almost everywhere a bounded measurable function on `ℍ`** (the property supplied,
almost surely at each bounded stop, by the jointly measurable version of Lemma 3.5). -/
def IsMeanGood (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  ∃ g : ℂ → ℝ, Measurable g ∧ (∀ z, |g z| ≤ WangWu.meanBound ρL ρR) ∧
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H → WangWu.frozenMean ρL ρR w vL vR t z = g z

variable {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- A test function vanishes off `ℍ`. -/
theorem testOn_eq_zero_of_notMem_H (ψ : TestOn upperHalfPlaneOpens) {z : ℂ} (hz : z ∉ H) : ψ z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (ψ.tsupport_subset h)

theorem IsMeanGood.integrable {t : ℝ≥0} (hm : IsMeanGood ρL ρR w vL vR t) (ψ : TestOn upperHalfPlaneOpens) :
    Integrable fun z => WangWu.frozenMean ρL ρR w vL vR t z * ψ z := by
  obtain ⟨g, hgm, hgb, hg⟩ := hm
  have hi : Integrable fun z => g z * ψ z :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).bdd_mul hgm.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgb z)
  refine hi.congr ?_
  filter_upwards [hg] with z hz
  by_cases hzH : z ∈ H
  · rw [hz hzH]
  · rw [testOn_eq_zero_of_notMem_H ψ hzH, mul_zero, mul_zero]

/-- **The retained kernel vanishes between an active point and a swallowed point.** -/
theorem retainedGreen_eq_zero_of_active {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) {a b : ℂ} (ha : a ∈ H \ fwdHull (Ito.rpath w) (t : ℝ))
    (hb : b ∈ fwdHull (Ito.rpath w) (t : ℝ)) : WangWu.retainedGreen w t a b = 0 := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (t₂ : ℝ)) := Ito.continuousOn_rpath hw ht₂ζ
  have hc : Continuous (Ito.clampDrv (Ito.rpath w) t₂) := Ito.continuous_clampDrv t₂.coe_nonneg hwc
  have heq : EqOn (Ito.rpath w) (Ito.clampDrv (Ito.rpath w) t₂) (Icc 0 (t₂ : ℝ)) := fun r hr =>
    (Ito.clampDrv_eqOn hr).symm
  have hK : fwdHull (Ito.rpath w) (t : ℝ) = fwdHull (Ito.clampDrv (Ito.rpath w) t₂) (t : ℝ) :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr => heq hr
  have hV' := WangWu.VTe_eq_of_eqOn htt₂' hwc hc.continuousOn heq ha.1 hb.1
  have hbK : b ∈ fwdHull (Ito.clampDrv (Ito.rpath w) t₂) (t : ℝ) := hK ▸ hb
  have haK : a ∉ fwdHull (Ito.clampDrv (Ito.rpath w) t₂) (t : ℝ) := hK ▸ ha.2
  unfold WangWu.retainedGreen K3.VT
  rw [hV', K3.VTe_eq_zero_of_swallowTime_ne hc ha.1 hb.1 ?_ (min_le_of_right_le hbK.2),
    ENNReal.toReal_zero]
  intro he
  exact haK ⟨ha.1, he ▸ hbK.2⟩

end KerFacts

section KerOmega

variable {nL nR : ℕ} {Ω : Type*} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω}

theorem testOn_add_apply (ψ φ : TestOn upperHalfPlaneOpens) (z : ℂ) : (ψ + φ) z = ψ z + φ z := by
  have := WangWu.testOn_sum_apply (Finset.univ : Finset (Fin 2)) ![ψ, φ] z
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

/-- **The kernel of an active test and a test inside the hull factorizes** (the cross term of the retained Green
form vanishes; the frozen mean is additive). -/
theorem kerCF_add_of_active
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (B · ω) (ζ ω))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω)
    (hm : IsMeanGood ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t)
    {ψA ψP : TestOn upperHalfPlaneOpens} (hA : IsActiveLabel (W · ω) (tsupport ψA) t)
    (hPK : tsupport ψP ⊆ fwdHull (Ito.rpath (W · ω)) (t : ℝ)) :
    kerCF ρL ρR W VL VR t (ψA + ψP) ω = kerCF ρL ρR W VL VR t ψA ω * kerCF ρL ρR W VL VR t ψP ω := by
  set fm : ℂ → ℝ := WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t with hfm
  have hmean : (∫ z, fm z * (⇑ψA + ⇑ψP) z) = (∫ z, fm z * ψA z) + ∫ z, fm z * ψP z := by
    rw [← integral_add (hm.integrable ψA) (hm.integrable ψP)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hcross : WangWu.retainedGreenForm (W · ω) t ψA ψP = 0 := by
    unfold WangWu.retainedGreenForm
    refine (integral_congr_ae (Eventually.of_forall fun a => ?_)).trans (integral_zero _ _)
    show (∫ b, ψA a * WangWu.retainedGreen (W · ω) t a b * ψP b) = 0
    by_cases ha : ψA a = 0
    · simp [ha]
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans (integral_zero _ _)
    show ψA a * WangWu.retainedGreen (W · ω) t a b * ψP b = 0
    by_cases hb : ψP b = 0
    · simp [hb]
    have haS : a ∈ tsupport ψA := subset_tsupport _ ha
    have hbS : b ∈ tsupport ψP := subset_tsupport _ hb
    rw [retainedGreen_eq_zero_of_active hP.2.2.2.1 ht
      ⟨ψA.tsupport_subset haS, fun hK => Set.disjoint_left.1 hA haS hK⟩ (hPK hbS)]
    ring
  have hgreen : WangWu.retainedGreenEnergy (W · ω) t (⇑ψA + ⇑ψP) =
      WangWu.retainedGreenEnergy (W · ω) t ψA + WangWu.retainedGreenEnergy (W · ω) t ψP := by
    have hl := WangWu.retainedGreenEnergy_lin hP (isTestFn_of_testOn ψA) (isTestFn_of_testOn ψP) ht 1 1
    rw [hcross] at hl
    have e : (⇑ψA + ⇑ψP : ℂ → ℝ) = fun a => 1 * ψA a + 1 * ψP a := by
      funext a; simp only [Pi.add_apply]; ring
    rw [e, hl]; ring
  unfold kerCF
  rw [← Complex.exp_add]
  rw [hmean, hgreen]
  congr 1
  push_cast
  ring

/-- **Left limit of the kernel value at a birth** (dominated convergence for the frozen mean, continuity of the
retained Green form). -/
theorem tendsto_kerCF_of_tendsto
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (B · ω) (ζ ω))
    {β : ℝ≥0} (hβ : (β : ℝ≥0∞) < ζ ω) {t : ℕ → ℝ≥0} (ht : Tendsto t atTop (𝓝 β)) (htβ : ∀ n, t n ≤ β)
    (ψ : TestOn upperHalfPlaneOpens)
    (hm : ∀ n, IsMeanGood ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (t n))
    (hlim : ∀ᵐ z ∂(volume : Measure ℂ), ψ z ≠ 0 →
      Tendsto (fun n => WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (t n) z)
        atTop (𝓝 (WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) β z)))
    (hbd : ∀ᵐ z ∂(volume : Measure ℂ), ψ z ≠ 0 → ∀ n,
      |WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (t n) z| ≤
        WangWu.meanBound ρL ρR) :
    Tendsto (fun n => kerCF ρL ρR W VL VR (t n) ψ ω) atTop (𝓝 (kerCF ρL ρR W VL VR β ψ ω)) := by
  set fm : ℝ≥0 → ℂ → ℝ := fun s => WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
    (fun i => (VR i · ω)) s with hfm
  have hψi : Integrable (fun z => ψ z) := ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hmean : Tendsto (fun n => ∫ z, fm (t n) z * ψ z) atTop (𝓝 (∫ z, fm β z * ψ z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => WangWu.meanBound ρL ρR * |ψ z|)
      (fun n => ((hm n).integrable ψ).aestronglyMeasurable) (hψi.abs.const_mul _) (fun n => ?_) ?_
    · filter_upwards [hbd] with z hz
      by_cases h0 : ψ z = 0
      · simp [h0]
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hz h0 n) (abs_nonneg _)
    · filter_upwards [hlim] with z hz
      by_cases h0 : ψ z = 0
      · simp [h0]
      · exact (hz h0).mul_const _
  have hc := WangWu.continuous_retainedGreenForm_min hP hβ (isTestFn_of_testOn ψ) (isTestFn_of_testOn ψ)
  have hgreen : Tendsto (fun n => WangWu.retainedGreenEnergy (W · ω) (t n) ψ) atTop
      (𝓝 (WangWu.retainedGreenEnergy (W · ω) β ψ)) := by
    have h1 := (hc.tendsto β).comp ht
    rw [min_self] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, min_eq_left (htβ n)]
    rfl
  have hcont : Continuous fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * ((p.1 : ℝ) : ℂ) - (((1 / 2 : ℝ) * p.2 : ℝ) : ℂ)) := by fun_prop
  exact (hcont.tendsto _).comp (hmean.prodMk_nhds hgreen)

end KerOmega

/-! ### The active factor -/

section ActiveFactor

universe v

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
theorem measurable_pairing (hh : Measurable h) (ψ : TestOn upperHalfPlaneOpens) :
    Measurable fun ω => h ω ψ :=
  (measurable_pi_apply ψ).comp ((Measurable.of_comap_le le_rfl).comp hh)

omit mΩ in
theorem norm_exp_I_mul_pairing (ψ : TestOn upperHalfPlaneOpens) (ω : Ω) :
    ‖Complex.exp (Complex.I * (h ω ψ : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp_I_mul_ofReal]

omit [IsProbabilityMeasure P] in
theorem aestronglyMeasurable_exp_pairing (hh : Measurable h) (ψ : TestOn upperHalfPlaneOpens) :
    AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) P :=
  (Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_pairing hh ψ)))).aestronglyMeasurable

/-- **The active kernel given the germ** at `κ = 4`, in `kerCF` form: for a driving stop `σ < ζ`, a hull version
`A` of `K_σ` and a test `ψ`, almost surely on `{supp ψ ∩ A = ∅}`, `E[e^{i(h,ψ)} | Γ(𝓕_σ, A)] = kerCF_σ(ψ)`. -/
theorem ae_condExp_exp_histGerm_eq_kerCF (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω : ℝ)) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) |
        histGerm hσ.measurableSpace A (centredField h u₀)]) ω = kerCF ρL ρR W VL VR (σ ω) ψ ω := by
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hσζ
  have hAK' : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      (((σ ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := hAK.mono fun ω hω => by rw [hω, WithTop.untopD_coe]
  obtain ⟨-, k2⟩ := ae_condExp_histGerm_hull_eq hC (by norm_num) hu₀ hX hσ hσζ' hA hAK'
    (u := fun ω => bheAt 4 ρL ρR (W (σ ω) ω) (fun i => VL i (σ ω) ω) (fun i => VR i (σ ω) ω))
    (fun ω => by simp only [WithTop.untopD_coe]; exact bheAt_spec 4 ρL ρR _ _ _) ψ
  -- `e^{i(h,ψ)} = e^{i(h⁰,ψ)} e^{i(𝔥₀,ψ)}`
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * ψ z : ℝ) : ℂ)) with hc
  have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ))) =
      c • fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' ψ : ℂ)) := by
    funext ω'
    rw [Pi.smul_apply, centredField_apply h hu₀.1 ω' ψ, smul_eq_mul, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hce := condExp_smul (μ := P) c (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' ψ : ℂ)))
    (histGerm hσ.measurableSpace A (centredField h u₀))
  filter_upwards [k2, hce, hC.1.2.2.2.2, hσζ, hAK] with ω h2 h3 hP hlt hAω hdisj
  rw [hsplit, h3, Pi.smul_apply, smul_eq_mul]
  simp only [WithTop.untopD_coe] at h2
  rw [h2 hdisj]
  have hdisj' : Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (σ ω)) := by
    have : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := hAω ▸ hdisj
    exact this
  rw [hAω, kerCF, WangWu.integral_frozenMean_mul_eq (ρL := ρL) (ρR := ρR) hP hlt
    ψ.tsupport_subset hdisj' (bheAt_spec 4 ρL ρR _ _ _),
    WangWu.retainedGreenEnergy_eq_loewnerGreenEnergy (ρL := ρL) (ρR := ρR) hP hlt ψ.tsupport_subset hdisj']
  have e3 : loewnerGreenEnergy (Ito.rpath (W · ω)) (σ ω) ψ =
      zeroGFFTestCov (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) ψ ψ :=
    loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hP.2.2.2.1 hP.1 hlt ψ hdisj'
  have e4 : couplingMean 4 (Ito.rpath (W · ω)) (σ ω) =
      couplingMean 4 (fun s : ℝ => W s.toNNReal ω) (σ ω) := rfl
  rw [e3, e4, hc, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The active factor** (C.4: "A final tower calculation adds the independent active kernel"). For a driving stop
`σ < ζ`, an active test `ψA` and a test `ψP` inside the hull: almost surely,
`E[e^{i(h, ψA + ψP)} | 𝓕_σ] = kerCF_σ(ψA) · E[e^{i(h, ψP)} | 𝓕_σ]`. The pocket observable `e^{i(h,ψP)}` is a germ
observable, and given the germ the active test has the frozen kernel. -/
theorem ae_condExp_exp_add_eq_of_active (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψA ψP : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsActiveLabel (W · ω) (tsupport ψA) (σ ω) →
      tsupport ψP ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (ψA + ψP) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) ψA ω *
          (P[fun ω' => Complex.exp (Complex.I * (h ω' ψP : ℂ)) | hσ.measurableSpace]) ω := by
  have hh := hC.2.1
  obtain ⟨A, hAm, hAK, hA𝓕⟩ := exists_hullVersion hC (by norm_num) hX hσ hσζ
  obtain ⟨σ₀, hσ₀⟩ := exists_isAnnouncingSeq_driving hC.1 (by norm_num) hX
    (not_threshold_seed_of_ae_lt hC.1 hσζ)
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hσζ
  obtain ⟨G, hGm, hGiff⟩ := exists_measurableSet_ae_iff_disjoint hC.1 hX hσ₀ hσ hσζ'
    ψA.hasCompactSupport.isCompact ψA.tsupport_subset
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hA𝓕 ψP.tsupport_subset
  -- the pocket observable is a germ observable
  set c : ℝ := ∫ z, u₀ z * ψP z with hc
  have hY : StronglyMeasurable[histGerm hσ.measurableSpace A (centredField h u₀)]
      (F.indicator fun ω => Complex.exp (Complex.I * (h ω ψP : ℂ))) := by
    have e : (F.indicator fun ω => Complex.exp (Complex.I * (h ω ψP : ℂ))) =
        F.indicator fun ω => (fun x : ℝ => Complex.exp (Complex.I * ((x + c : ℝ) : ℂ)))
          (centredField h u₀ ω ψP) := by
      congr 1; funext ω
      simp only [centredField_apply h hu₀.1 ω ψP, hc, sub_add_cancel]
    rw [e]
    exact stronglyMeasurable_indicator_histGerm hFm hFsub
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_id.add_const c))))
  have hYb : ∀ ω, ‖(F.indicator fun ω => Complex.exp (Complex.I * (h ω ψP : ℂ))) ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ F
    · rw [indicator_of_mem hω]; exact norm_exp_I_mul_pairing ψP ω
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  -- the active kernel given `𝓕_σ`, truncated
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψA : ℂ)) with hXdef
  set g : Ω → ℂ := WangWu.truncOne (P[X | hσ.measurableSpace]) with hgdef
  have hg : StronglyMeasurable[hσ.measurableSpace] g :=
    WangWu.stronglyMeasurable_truncOne stronglyMeasurable_condExp
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := WangWu.norm_truncOne_le _
  have hXb' : ∀ᵐ ω ∂P, ‖(P[X | hσ.measurableSpace]) ω‖ ≤ 1 :=
    ae_bdd_norm_condExp_of_ae_bdd_norm (Eventually.of_forall fun ω => norm_exp_I_mul_pairing ψA ω)
  have hgerm := ae_condExp_exp_histGerm_eq_kerCF hC hu₀ hX hσ hσζ hAm hAK ψA
  have hact := ae_condExp_exp_eq_kerCF_of_active hC hX hσ hσζ ψA
  have hXg : ∀ᵐ ω ∂P, ω ∈ F ∩ G →
      (P[X | histGerm hσ.measurableSpace A (centredField h u₀)]) ω = g ω := by
    filter_upwards [hgerm, hact, hXb', hGiff, hAK] with ω h1 h2 h3 h4 h5 hω
    simp only [WithTop.untopD_coe] at h4
    have hd : Disjoint (tsupport ψA) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := h4.1 hω.2
    have hdA : Disjoint (tsupport ψA) (A ω) := by rw [h5]; exact hd
    rw [h1 hdA, hgdef, WangWu.truncOne, ite_eq_left h3, h2 hd]
  have hmul := ae_condExp_mul_eq_on (P := P) (le_histGerm A (centredField h u₀))
    (histGerm_le hσ.measurableSpace_le hAm (measurable_centredField hh u₀)) (hFm.inter hGm) hY hYb
    (aestronglyMeasurable_exp_pairing hh ψA) (fun ω => norm_exp_I_mul_pairing ψA ω) hg hgb hXg
  -- indicators
  have hZi : ∀ ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) P :=
    fun ψ => Integrable.of_bound (aestronglyMeasurable_exp_pairing hh ψ) 1
      (Eventually.of_forall fun ω => norm_exp_I_mul_pairing ψ ω)
  have hind1 := condExp_indicator (μ := P) (hZi (ψA + ψP)) hFm
  have hind2 := condExp_indicator (μ := P) (hZi ψP) hFm
  have hYX : (F.indicator fun ω => Complex.exp (Complex.I * (h ω ψP : ℂ))) * X =
      F.indicator fun ω => Complex.exp (Complex.I * (h ω (ψA + ψP) : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ F
    · simp only [Pi.mul_apply, indicator_of_mem hω, hXdef, map_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp only [Pi.mul_apply, indicator_of_notMem hω, zero_mul]
  filter_upwards [hmul, hind1, hind2, hXg, hact, hXb', hGiff, hAK] with ω hm1 hi1 hi2 hxg ha hb hgi hak hA hPK
  simp only [WithTop.untopD_coe] at hgi
  have hd : Disjoint (tsupport ψA) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := hA
  have hωG : ω ∈ G := hgi.2 hd
  have hωF : ω ∈ F := hFmem ω (by rw [hak]; exact hPK)
  rw [hYX] at hm1
  have e1 := hm1 ⟨hωF, hωG⟩
  rw [hi1, indicator_of_mem hωF, hi2, indicator_of_mem hωF] at e1
  rw [e1, hgdef, WangWu.truncOne, ite_eq_left hb, ha hd]

end ActiveFactor

end WholeField

end InteractingSLE
