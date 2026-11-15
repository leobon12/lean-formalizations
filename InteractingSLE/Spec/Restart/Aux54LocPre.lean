/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Code
import InteractingSLE.Spec.Restart.FlowStopIdentLift

/-!
# Aux. lemma 54 for general words, part 7: locality on the extension before the stop

Packet PROVE-AUX54. On a record extension `E`, before the reference's rule stop the driving events of the extension
are the stopped coupling's (`exists_pre_transfer`), and the stopped coupling read through `Prod.fst` is again a coupling
through its stop (`FlowStopIdentLift.isStoppedHullCoupling_fst`). The coded-hull identity
(`setIntegral_lapTest_coded`) at `t₁ < t₂` decreasing to `s`, with the right continuity of the hulls, gives the
projection identity of the original field on `D ∩ {s < V₀} ∩ {C ∩ K_s = ∅}` for every event `D` of the extension's
driving filtration at `s`.

* `killedDrivingFiltration_comp`: the killed driving filtration of a process read through a measurable map is the
  pullback of the original one;
* `closure_fwdHull_inter_H_subset_of_lt`, `eventually_disjoint_closure_fwdHull_iff`: the hull before the lifetime is
  relatively closed in `ℍ`, and avoidance of a compact at `s` is avoidance of the closures at the times decreasing to
  `s`;
* **`setIntegral_lapTest_preExt`**: the identity before the stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov LQGMetric.MarkovZB LocalSets

variable {nL nR : ℕ}

/-! ### Pulled-back killed filtrations and hulls before the lifetime -/

section Pull

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {π : Ω' → Ω}

/-- **The killed driving filtration of a process read through `π`** is the pullback of the original one. -/
theorem killedDrivingFiltration_comp (hX : IsMeasurableKilledDriving W VL VR V)
    (hX' : IsMeasurableKilledDriving (fun t p => W t (π p)) (fun i t p => VL i t (π p))
      (fun j t p => VR j t (π p)) fun p => V (π p)) (t : ℝ≥0) :
    killedDrivingFiltration hX' t = (killedDrivingFiltration hX t).comap π := by
  show MeasurableSpace.generateFrom _ = (MeasurableSpace.generateFrom _).comap π
  rw [MeasurableSpace.comap_generateFrom]
  congr 1
  ext S
  constructor
  · rintro ⟨r, hr, B, hB, rfl⟩
    exact ⟨_, ⟨r, hr, B, hB, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨r, hr, B, hB, rfl⟩, rfl⟩
    exact ⟨r, hr, B, hB, rfl⟩

end Pull

section Hull

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The hull before the lifetime is relatively closed in `ℍ`.** -/
theorem closure_fwdHull_inter_H_subset_of_lt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ) : closure (fwdHull (Ito.rpath w) t) ∩ H ⊆ fwdHull (Ito.rpath w) t := by
  obtain ⟨T, htT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htζ
  have htT' : (t : ℝ) < T := by exact_mod_cast htT
  have hwT : ContinuousOn (Ito.rpath w) (Icc 0 (T : ℝ)) := Ito.continuousOn_rpath hw hTζ
  have hA : Continuous (Ito.clampDrv (Ito.rpath w) T) := Ito.continuous_clampDrv T.coe_nonneg hwT
  have e : fwdHull (Ito.rpath w) t = fwdHull (Ito.clampDrv (Ito.rpath w) T) t :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htT' Ito.clampDrv_eqOn.symm
  rw [e]
  exact Aux10.closure_fwdHull_inter_H hA t.coe_nonneg

/-- **Avoidance at `s` is eventual avoidance of the closures at the times decreasing to `s`** (right continuity of the
hulls on compacts, and their relative closedness). -/
theorem eventually_disjoint_closure_fwdHull_iff (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0}
    (hsζ : (s : ℝ≥0∞) < ζ) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {t : ℕ → ℝ≥0}
    (hts : ∀ n, s ≤ t n) (hlim : Tendsto t atTop (𝓝 s)) :
    (Disjoint C (fwdHull (Ito.rpath w) s) →
      ∀ᶠ n in atTop, Disjoint C (closure (fwdHull (Ito.rpath w) (t n)) ∩ H)) ∧
    (¬ Disjoint C (fwdHull (Ito.rpath w) s) →
      ∀ n, ¬ Disjoint C (closure (fwdHull (Ito.rpath w) (t n)) ∩ H)) := by
  constructor
  · intro hd
    obtain ⟨δ, hδ, hsδ, hdis⟩ := exists_pos_disjoint_fwdHull_rpath' hw hsζ hC hCH hd
    have hev : ∀ᶠ n in atTop, t n < s + δ := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right s hδ))
    filter_upwards [hev] with n hn
    have hnζ : (t n : ℝ≥0∞) < ζ := lt_trans (ENNReal.coe_lt_coe.2 hn) hsδ
    exact (hdis (t n) hn.le).mono_right (closure_fwdHull_inter_H_subset_of_lt hw hnζ)
  · intro hnd n hd
    refine hnd (hd.mono_right fun z hz => ?_)
    have hz' : z ∈ fwdHull (Ito.rpath w) (t n) :=
      QuantumZipper.fwdHull_mono.1 (show (s : ℝ) ≤ t n by exact_mod_cast hts n) hz
    exact ⟨subset_closure hz', QuantumZipper.fwdHull_mono.2 _ hz'⟩

end Hull

/-! ### The empty open set -/

/-- **The projection identity at an empty open set is trivial** (`C_c^∞(∅) = 0`). -/
theorem projIdentity_of_empty {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) {U : TopologicalSpace.Opens ℂ} (hU : (U : Set ℂ) = ∅)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂μ =
      Coupling.projFactor U f Ξ * ∫ ω, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂μ := by
  have hU' : U ≤ upperHalfPlaneOpens := by
    intro z hz
    have : z ∈ (U : Set ℂ) := hz
    rw [hU] at this
    exact absurd this (Set.notMem_empty z)
  have hf : f = 0 := by
    ext z
    show f.1 z = 0
    by_contra hz
    have h1 : z ∈ tsupport f.1 := subset_tsupport _ hz
    have h2 := f.2.2.2 h1
    rw [hU] at h2
    exact h2
  subst hf
  rw [LocalExt.lapTest_zero hU', zero_add]
  have h1 : Coupling.projFactor U 0 Ξ = 1 := by
    simp only [Coupling.projFactor, LocalExt.gradFeat_zsSub_zero, norm_zero, inner_zero_left]
    simp
  rw [h1, one_mul]

/-! ### Before the stop, on the stopped coupling -/

/-- Sets that eventually agree with a statement agree with their `liminf` on it. -/
theorem mem_liminf_iff_of_eventually {α : Type*} {M : ℕ → Set α} {x : α} {T : Prop}
    (h : ∀ᶠ n in atTop, (x ∈ M n ↔ T)) : x ∈ ⋃ N : ℕ, ⋂ n ≥ N, M n ↔ T := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  constructor
  · intro hx
    obtain ⟨N', hN'⟩ := mem_iUnion.1 hx
    exact (hN (max N N') (le_max_left _ _)).1 (mem_iInter₂.1 hN' (max N N') (le_max_right _ _))
  · intro hT
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => (hN n hn).2 hT⟩

section PreP

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The projection identity of a coupling through a stop on an event of the driving filtration at `s` before the
stop** (the coded identities at `s < s + 1/(n+1)`, in the limit `n → ∞`): on a measurable version of
`F₀ ∩ {C ∩ K_s = ∅}`, for `F₀ ∈ 𝓕_s` inside `{s < V}`. -/
theorem setIntegral_lapTest_preP [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) {s : ℝ≥0}
    {F₀ : Set Ω} (hF₀m : ∀ hX : IsMeasurableKilledDriving W VL VR V, MeasurableSet[drivingFiltration P hX s] F₀)
    (hF₀V : ∀ ω ∈ F₀, (s : ℝ≥0∞) < V ω)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) {U : TopologicalSpace.Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∃ M : Set Ω, MeasurableSet M ∧
      M =ᵐ[P] F₀ ∩ {ω | Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))} ∧
      ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
        Coupling.projFactor U f Ξ * ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  classical
  have hhm : Measurable h := hSC.2.2.1
  have hEv := hSC.1
  set t₂ : ℕ → ℝ≥0 := fun n => s + 1 / ((n : ℝ≥0) + 1) with ht₂
  have hpos : ∀ n : ℕ, (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) := fun n => by positivity
  have ht : ∀ n, s < t₂ n := fun n => lt_add_of_pos_right s (hpos n)
  choose M hMm hMeq hMid using fun n => setIntegral_lapTest_coded hSC hT₀ (ht n) hF₀m hF₀V hC hCH hCne hUC f Ξ
  set target : Set Ω := F₀ ∩ {ω | Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))} with htarget
  have hlim : Tendsto t₂ atTop (𝓝 s) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine this.congr fun n => ?_
      push_cast
      rfl
    have h2 := (tendsto_const_nhds (x := s)).add h1
    rw [add_zero] at h2
    exact h2
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ M n ↔ ω ∈ target) := by
    filter_upwards [ae_all_iff.2 hMeq, hEv.ae_path] with ω hω hp
    have hω' : ∀ n, (ω ∈ M n ↔ ω ∈ F₀ ∧ Disjoint C (closure (fwdHull (fun r : ℝ => W r.toNNReal ω)
        ((min ((t₂ n : ℝ≥0) : ℝ≥0∞) (V ω)).toNNReal : ℝ)) ∩ (upperHalfPlaneOpens : Set ℂ))) := fun n =>
      Iff.of_eq (hω n)
    by_cases hF : ω ∈ F₀
    · have hsV := hF₀V ω hF
      set tt : ℕ → ℝ≥0 := fun n => (min ((t₂ n : ℝ≥0) : ℝ≥0∞) (V ω)).toNNReal with htt
      have hne : ∀ n, min ((t₂ n : ℝ≥0) : ℝ≥0∞) (V ω) ≠ ⊤ := fun n =>
        ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
      have hts : ∀ n, s ≤ tt n := fun n => by
        rw [htt, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hne n)]
        exact le_min (ENNReal.coe_le_coe.2 (ht n).le) hsV.le
      have htt2 : ∀ n, tt n ≤ t₂ n := fun n => by
        rw [htt, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hne n)]
        exact min_le_left _ _
      have hlim' : Tendsto tt atTop (𝓝 s) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hts htt2
      have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < V ω} := hp.continuousOn_w
      obtain ⟨hA, hB⟩ := eventually_disjoint_closure_fwdHull_iff (w := fun t => W t ω) hw hsV hC hCH hts hlim'
      by_cases hd : Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))
      · filter_upwards [hA hd] with n hn
        exact (hω' n).trans ⟨fun _ => ⟨hF, hd⟩, fun _ => ⟨hF, hn⟩⟩
      · refine Eventually.of_forall fun n => (hω' n).trans ⟨fun h' => absurd h'.2 (hB hd n), fun h' => absurd h'.2 hd⟩
    · exact Eventually.of_forall fun n => (hω' n).trans ⟨fun h' => absurd h'.1 hF, fun h' => absurd h'.1 hF⟩
  set Mlim : Set Ω := ⋃ N : ℕ, ⋂ n ≥ N, M n with hMlim
  have hMlimm : MeasurableSet Mlim :=
    MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hMm n
  have hev' : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ M n ↔ ω ∈ Mlim) := by
    filter_upwards [hev] with ω hω
    have e := mem_liminf_iff_of_eventually hω
    filter_upwards [hω] with n hn
    exact hn.trans e.symm
  have hMlimeq : Mlim =ᵐ[P] target := by
    filter_upwards [hev] with ω hω
    exact propext (mem_liminf_iff_of_eventually hω)
  refine ⟨Mlim, hMlimm, hMlimeq, ?_⟩
  have hbd : ∀ (χ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))‖ ≤ 1 :=
    fun χ ω => (Complex.norm_exp_I_mul_ofReal _).le
  have hmeas : ∀ χ : TestOn upperHalfPlaneOpens,
      AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) P := fun χ =>
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp
      ((WholeField.measurable_sub_dist T₀).comp hhm))).aestronglyMeasurable
  have h1 := LocalExt.tendsto_setIntegral_of_ae_eventually hMm hMlimm hev' (hmeas _) (hbd (lapTest U f + Ξ))
  have h2 := (LocalExt.tendsto_setIntegral_of_ae_eventually hMm hMlimm hev' (hmeas _) (hbd Ξ)).const_mul
    (Coupling.projFactor U f Ξ)
  simp_rw [hMid] at h1
  exact tendsto_nhds_unique h1 h2

end PreP

/-! ### Before the stop, on the extension -/

section PreE

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens} {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}
  {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {ζ₀ V₀ : Ω₀ → ℝ≥0∞}

/-- **The projection identity on the extension before the reference's stop**: for an event `D` of the null-augmented
driving filtration of the extension at `s` and a measurable version `S` of its safe event at `s`, the original field
read through `Prod.fst` satisfies the projection identity at `U ⊆ C` on `D ∩ S ∩ {s < V₀ ∘ snd}` (the events transfer to
the stopped coupling before the stop, `exists_pre_transfer`, where `setIntegral_lapTest_preP` applies). -/
theorem setIntegral_lapTest_preE [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀)
    {E : Measure (Ω × Ω₀)} (hfst : E.map Prod.fst = P)
    (hXE : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) fun p => ζ₀ p.2)
    (hV₀ζ : ∀ ω₀, V₀ ω₀ ≤ ζ₀ ω₀)
    (hag : ∀ᵐ p ∂E, V p.1 = V₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V p.1 →
      dState W VL VR p.1 t = dState W₀ VL₀ VR₀ p.2 t)
    {s : ℝ≥0} {D : Set (Ω × Ω₀)} (hD : MeasurableSet[Ito.nullAugmented (killedDrivingFiltration hXE) E s] D)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) {U : TopologicalSpace.Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C) {S : Set (Ω × Ω₀)}
    (hS : S =ᵐ[E] {p | (s : ℝ≥0∞) < ζ₀ p.2 ∧ Disjoint C (fwdHull (fun r : ℝ => W₀ r.toNNReal p.2) (s : ℝ))})
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ p in D ∩ S ∩ {p | (s : ℝ≥0∞) < V₀ p.2}, Complex.exp (Complex.I * ((h p.1 - T₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      Coupling.projFactor U f Ξ *
        ∫ p in D ∩ S ∩ {p | (s : ℝ≥0∞) < V₀ p.2}, Complex.exp (Complex.I * ((h p.1 - T₀) Ξ : ℂ)) ∂E := by
  classical
  have hhm : Measurable h := hSC.2.2.1
  obtain ⟨-, -, -, -, hX, -⟩ := id hSC
  obtain ⟨A₀, hA₀, hDA₀⟩ := exists_snd_of_nullAugmented hX₀ hXE hD
  obtain ⟨A', hA', hpre⟩ := exists_pre_transfer hX₀ hX hV₀ζ hag s hA₀
  set F₀ : Set Ω := A' ∩ {ω | (s : ℝ≥0∞) < V ω} with hF₀def
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have hF₀m : ∀ hX' : IsMeasurableKilledDriving W VL VR V, MeasurableSet[drivingFiltration P hX' s] F₀ :=
    fun _ => (Ito.le_usualAugmentation (killedDrivingFiltration hX) P s _ hA').inter
      (LocalExt.measurableSet_lt_stop hV s)
  have hF₀V : ∀ ω ∈ F₀, (s : ℝ≥0∞) < V ω := fun ω hω => hω.2
  obtain ⟨M, hMm, hMeq, hMid⟩ := setIntegral_lapTest_preP hSC hT₀ hF₀m hF₀V hC hCH hCne hUC f Ξ
  have hMeqE : ∀ᵐ p ∂E, (p.1 ∈ M) = (p.1 ∈ F₀ ∩ {ω | Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))}) := by
    have h1 : ∀ᵐ ω ∂(E.map Prod.fst), (ω ∈ M) =
        (ω ∈ F₀ ∩ {ω | Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))}) := by
      rw [hfst]; exact hMeq
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  have hset : (D ∩ S ∩ {p | (s : ℝ≥0∞) < V₀ p.2} : Set (Ω × Ω₀)) =ᵐ[E] Prod.fst ⁻¹' M := by
    filter_upwards [hDA₀, hS, hpre, hag, hMeqE] with p hpD hpS hpp ⟨hVV, hst⟩ hpM
    have hpD' : p ∈ D ↔ p.2 ∈ A₀ := Iff.of_eq hpD
    have hpS' : p ∈ S ↔ (s : ℝ≥0∞) < ζ₀ p.2 ∧
        Disjoint C (fwdHull (fun r : ℝ => W₀ r.toNNReal p.2) (s : ℝ)) := Iff.of_eq hpS
    have hpp' : (p.2 ∈ A₀ ∧ (s : ℝ≥0∞) < V₀ p.2) ↔ (p.1 ∈ A' ∧ (s : ℝ≥0∞) < V₀ p.2) := Iff.of_eq hpp
    have hpM' : p.1 ∈ M ↔ (p.1 ∈ A' ∧ (s : ℝ≥0∞) < V p.1) ∧
        Disjoint C (fwdHull (fun r : ℝ => W r.toNNReal p.1) (s : ℝ)) := Iff.of_eq hpM
    have hhull : (s : ℝ≥0∞) < V p.1 → fwdHull (fun r : ℝ => W r.toNNReal p.1) (s : ℝ) =
        fwdHull (fun r : ℝ => W₀ r.toNNReal p.2) (s : ℝ) := fun hs =>
      fwdHull_rpath_congr_of_lt (w := fun t => W t p.1) (w' := fun t => W₀ t p.2) (a := V p.1)
        (fun t ht => congrArg Prod.fst (hst t ht)) hs
    apply propext
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    rw [hpM']
    constructor
    · rintro ⟨⟨hD', hS'⟩, hs⟩
      have hA := (hpp'.1 ⟨hpD'.1 hD', hs⟩).1
      have hsV : (s : ℝ≥0∞) < V p.1 := hVV ▸ hs
      exact ⟨⟨hA, hsV⟩, by rw [hhull hsV]; exact (hpS'.1 hS').2⟩
    · rintro ⟨⟨hA, hsV⟩, hd⟩
      have hs : (s : ℝ≥0∞) < V₀ p.2 := hVV ▸ hsV
      refine ⟨⟨hpD'.2 (hpp'.2 ⟨hA, hs⟩).1, hpS'.2 ⟨lt_of_lt_of_le hs (hV₀ζ p.2), ?_⟩⟩, hs⟩
      rw [← hhull hsV]; exact hd
  have hmeas : ∀ χ : TestOn upperHalfPlaneOpens,
      Measurable (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) := fun χ =>
    GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp ((WholeField.measurable_sub_dist T₀).comp hhm))
  have htr : ∀ χ : TestOn upperHalfPlaneOpens,
      ∫ p in D ∩ S ∩ {p | (s : ℝ≥0∞) < V₀ p.2}, Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ)) ∂E =
        ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂P := by
    intro χ
    rw [setIntegral_congr_set hset, ← hfst, setIntegral_map hMm (hmeas χ).aestronglyMeasurable
      measurable_fst.aemeasurable]
  rw [htr, htr, hMid]

end PreE

end Aux54

end Restart

end InteractingSLE
