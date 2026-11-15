/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Main
import InteractingSLE.Spec.Sec7.LocalExtLLocQ
import InteractingSLE.Spec.Sec7.LocalExtNCode
import InteractingSLE.Spec.Sec7.SideHeightGeom

/-!
# Aux. lemma 54 for general words, part 6: coding history events into a local hull

Packet PROVE-AUX54. The frozen locality clause is unmarked: `K_τ` is a local set of `h` in the joint law of
`(K_τ, h)`. The projection identity on **history** events of the stopped coupling (history-marked locality) follows
by coding the history event into the capacity clock of a hull at a stopping time (PROVE-LOCEXT-L's argument,
`LocalExt.IsStoppedSeedCoupling.exists_codedHull`, for general words): for `t₁ < t₂`, a history event `F` at `t₁`
and `G = Fᶜ ∩ {t₁ < V}`, the stop `τ'' = t₁` on `G`, `t₂ ∧ V` off `G`, has hull clock `> t₁` exactly on
`F ∩ {t₁ < V}`.

* `truncK`, `preMark`: the history truncated at `t`, and the pre-stop marks `{t < V, history truncated at t ∈ Γ}`;
* `exists_solution_beyond`: a point of `ℍ` outside the hull at `T` has a forward solution beyond `T`, so the driver is
  continuous a little beyond `T` (a driver that is not continuous beyond `T` swallows all of `ℍ` by time `T`);
* **`exists_codedHull`**: the coded hull of a coupling through a stop.
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

/-! ### Truncated histories and pre-stop marks -/

section Marks

open Classical in
/-- **The history truncated at `t`**: lifetime `γ.1 ∧ t`, samples before it. -/
def truncK (t : ℝ≥0) (γ : HistorySpace nL nR) : HistorySpace nL nR :=
  (min γ.1 t, fun p => if (dyadicTime p : ℝ≥0∞) < min γ.1 t then γ.2 p else 0)

theorem measurable_truncK (t : ℝ≥0) : Measurable (truncK (nL := nL) (nR := nR) t) := by
  classical
  refine (measurable_fst.min measurable_const).prodMk (Measurable.of_eval fun p => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.min measurable_const))
    ((measurable_pi_apply p).comp measurable_snd) measurable_const

/-- The killed history truncated at `t` is the history killed at `V ∧ t`. -/
theorem truncK_killedHistory {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) :
    truncK t (killedHistory W VL VR V ω) = killedHistory W VL VR (fun ω => min (t : ℝ≥0∞) (V ω)) ω := by
  classical
  refine Prod.ext ?_ (funext fun p => ?_)
  · simp only [truncK, killedHistory, min_comm]
  · simp only [truncK, killedHistory]
    by_cases h1 : (dyadicTime p : ℝ≥0∞) < min (V ω) (t : ℝ≥0∞)
    · have h2 : (dyadicTime p : ℝ≥0∞) < V ω := lt_of_lt_of_le h1 (min_le_left _ _)
      have h3 : (dyadicTime p : ℝ≥0∞) < min (t : ℝ≥0∞) (V ω) := by rw [min_comm]; exact h1
      simp only [h1, h2, h3, ↓reduceIte]
    · have h3 : ¬ (dyadicTime p : ℝ≥0∞) < min (t : ℝ≥0∞) (V ω) := by rw [min_comm]; exact h1
      simp only [h1, h3, ↓reduceIte]

/-- **The pre-stop marks**: the lifetime is after `t` and the history truncated at `t` lies in `Γ`. -/
def preMark (t : ℝ≥0) (Γ : Set (HistorySpace nL nR)) : Set (HistorySpace nL nR) :=
  {γ | (t : ℝ≥0∞) < γ.1 ∧ truncK t γ ∈ Γ}

theorem measurableSet_preMark (t : ℝ≥0) {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ) :
    MeasurableSet (preMark t Γ) :=
  (measurableSet_lt measurable_const measurable_fst).inter ((measurable_truncK t) hΓ)

end Marks

/-! ### Forward solutions beyond a time -/

/-- **A point of `ℍ` outside the hull at `T` has a forward solution beyond `T`**, so the driver is continuous on
`[0, T']` for some `T' > T`. -/
theorem exists_continuousOn_beyond {w : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H)
    (hzK : z ∉ fwdHull w T) : ∃ T' : ℝ, T < T' ∧ ContinuousOn w (Icc 0 T') := by
  rw [InteractingSLE.mem_fwdHull_iff_forall hT] at hzK
  push Not at hzK
  obtain ⟨T', hT'0, ⟨u, hu⟩, hT'⟩ := hzK hz
  exact ⟨T', hT', Sec7.SideHeight.continuousOn_of_isForwardSol hu⟩

/-! ### The coded hull -/

section Code

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The coded hull** (PROVE-LOCEXT-L's coding stop for a coupling through a stop): for `t₁ < t₂` and a history event
`Γ`, some local set `A` of the centred field satisfies, almost surely, for every nonempty `V' ⊆ ℍ`: its hull clock is
beyond `t₁` and it avoids `V'` exactly when the history is in the pre-stop mark `preMark t₁ Γ` and the hull at
`t₂ ∧ V` avoids `V'`. (`A = K_{τ''}`, `τ'' = t₁` on `G = (mark)ᶜ ∩ {t₁ < V}`, `τ'' = t₂ ∧ V` off `G`.) -/
theorem exists_codedHull_of (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℝ≥0} (ht : t₁ < t₂)
    {F₀ : Set Ω} (hF₀m : ∀ hX : IsMeasurableKilledDriving W VL VR V, MeasurableSet[drivingFiltration P hX t₁] F₀)
    (hF₀V : ∀ ω ∈ F₀, (t₁ : ℝ≥0∞) < V ω) :
    ∃ A : Ω → Set ℂ, IsLocalSet A (fun ω => h ω - T₀) P ∧ ∀ᵐ ω ∂P, ∀ V' : Set ℂ, V' ⊆ H → V'.Nonempty →
      (((t₁ : ℝ≥0∞) < WholeField.hullClock (A ω) ∧ Disjoint (A ω) V') ↔
        (ω ∈ F₀ ∧
          Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) V')) := by
  classical
  obtain ⟨hEv, -, -, -, hX, hcl⟩ := hSC
  set 𝒢 := drivingFiltration P hX with h𝒢
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have hmark : ∀ ω, ω ∈ F₀ ↔ ω ∈ F₀ := fun ω => Iff.rfl
  have hF₀ : MeasurableSet[𝒢 t₁] F₀ := hF₀m hX
  have hτ' : IsStoppingTime 𝒢 fun ω => min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0) :=
    (isStoppingTime_const 𝒢 _).min hV
  have hτ₁ : IsStoppingTime 𝒢 fun ω => min ((t₁ : ℝ≥0) : WithTop ℝ≥0)
      (min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0)) := (isStoppingTime_const 𝒢 _).min hτ'
  have ht12 : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < ((t₂ : ℝ≥0) : WithTop ℝ≥0) := by exact_mod_cast ht
  have hlt_iff : ∀ ω, ((t₁ : ℝ≥0) : WithTop ℝ≥0) < min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0) ↔
      ((t₁ : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0) := fun ω =>
    ⟨fun h => lt_of_lt_of_le h (min_le_right _ _), fun h => lt_min ht12 h⟩
  set G : Set Ω := F₀ᶜ ∩ {ω | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0)} with hGdef
  have hGm : MeasurableSet[hτ₁.measurableSpace] G :=
    LocalExt.measurableSet_stopping_min_of_subset_lt (hF₀.compl.inter (LocalExt.measurableSet_lt_stop hV t₁))
      (fun ω hω => (hlt_iff ω).2 hω.2) hτ₁
  set τ'' : Ω → WithTop ℝ≥0 := G.piecewise
    (fun ω => min ((t₁ : ℝ≥0) : WithTop ℝ≥0) (min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0)))
    (fun ω => min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0)) with hτ''def
  have hτ'' : IsStoppingTime 𝒢 τ'' :=
    WholeField.isStoppingTime_piecewise_of_le hτ₁ hτ' (fun ω => min_le_right _ _) hGm
  have hτ''V : ∀ ω, τ'' ω ≤ (V ω : WithTop ℝ≥0) ∧ τ'' ω ≤ ((t₂ : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hτ''def, Set.piecewise, hω, ↓reduceIte]
      exact ⟨(min_le_right _ _).trans (min_le_right _ _), (min_le_right _ _).trans (min_le_left _ _)⟩
    · simp only [hτ''def, Set.piecewise, hω, ↓reduceIte]
      exact ⟨min_le_right _ _, min_le_left _ _⟩
  refine ⟨fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ'' ω).untopD 0 : ℝ≥0),
    WholeField.IsLocalSet.sub_dist (hcl τ'' hτ'' (ae_of_all _ fun ω =>
      ⟨(hτ''V ω).1, ne_top_of_le_ne_top WithTop.coe_ne_top (hτ''V ω).2⟩)).1 hT₀, ?_⟩
  filter_upwards [hEv.ae_path] with ω hp V' hV'H hV'ne
  have hw0 : W 0 ω = 0 := hp.w_zero
  rw [hmark]
  by_cases hG : ω ∈ G
  · -- the code stops at `t₁`
    have hG2 : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0) := hG.2
    have hτω : ((τ'' ω).untopD 0 : ℝ≥0) = t₁ := by
      simp only [hτ''def, Set.piecewise, hG, ↓reduceIte, min_eq_left ((hlt_iff ω).2 hG2).le, WithTop.untopD_coe]
    have hclock : WholeField.hullClock (fwdHull (fun s : ℝ => W s.toNNReal ω) (t₁ : ℝ)) = t₁ :=
      WholeField.hullClock_fwdHull_rpath hp.continuousOn_w hw0 hG2
    constructor
    · rintro ⟨h1, -⟩
      simp only [hτω, hclock, lt_irrefl] at h1
    · rintro ⟨h1, -⟩
      exact absurd h1 hG.1
  · -- the code is `t₂ ∧ V`
    have hτω : ((τ'' ω).untopD 0 : ℝ≥0) = (min (t₂ : ℝ≥0∞) (V ω)).toNNReal := by
      simp only [hτ''def, Set.piecewise, hG, ↓reduceIte]
      rfl
    simp only [hτω]
    set T : ℝ≥0 := (min (t₂ : ℝ≥0∞) (V ω)).toNNReal with hTdef
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hF
      have hVt : (V ω : WithTop ℝ≥0) ≤ ((t₁ : ℝ≥0) : WithTop ℝ≥0) := by
        by_contra hlt
        exact hG ⟨hF, not_le.1 hlt⟩
      -- the hull at `T ≤ t₁` has clock `≤ t₁`: a point of `V'` is outside it
      obtain ⟨z, hz⟩ := hV'ne
      have hzK : z ∉ fwdHull (fun s : ℝ => W s.toNNReal ω) (T : ℝ) := fun hzK => Set.disjoint_left.1 h2 hzK hz
      obtain ⟨T', hTT', hcT'⟩ := exists_continuousOn_beyond T.coe_nonneg (hV'H hz) hzK
      have hT'0 : (0 : ℝ) ≤ T' := T.coe_nonneg.trans hTT'.le
      have hwc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
        intro t ht
        have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T' := ⟨t.coe_nonneg,
          (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt ht))⟩
        have h1 := (hcT' (t : ℝ) ht').comp (continuous_subtype_val.continuousWithinAt (x := t))
          (fun s hs => ⟨s.coe_nonneg, (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt hs))⟩)
        refine h1.congr (fun s _ => ?_) ?_
        · simp only [Function.comp_apply, Real.toNNReal_coe]
        · simp only [Function.comp_apply, Real.toNNReal_coe]
      have hTT'' : (T : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.2 ((Real.lt_toNNReal_iff_coe_lt).2 hTT')
      have hclock := WholeField.hullClock_fwdHull_rpath hwc hw0 hTT''
      rw [hclock] at h1
      have hTV : (T : ℝ≥0∞) ≤ V ω := by
        rw [hTdef, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
        exact min_le_right _ _
      exact absurd (lt_of_lt_of_le h1 (hTV.trans hVt)) (lt_irrefl _)
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hF : ω ∈ F₀ := h1
      have hlt : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0) := hF₀V ω hF
      obtain ⟨z, hz⟩ := hV'ne
      have hzK : z ∉ fwdHull (fun s : ℝ => W s.toNNReal ω) (T : ℝ) := fun hzK => Set.disjoint_left.1 h2 hzK hz
      obtain ⟨T', hTT', hcT'⟩ := exists_continuousOn_beyond T.coe_nonneg (hV'H hz) hzK
      have hT'0 : (0 : ℝ) ≤ T' := T.coe_nonneg.trans hTT'.le
      have hwc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
        intro t ht
        have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T' := ⟨t.coe_nonneg,
          (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt ht))⟩
        have h1 := (hcT' (t : ℝ) ht').comp (continuous_subtype_val.continuousWithinAt (x := t))
          (fun s hs => ⟨s.coe_nonneg, (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt hs))⟩)
        refine h1.congr (fun s _ => ?_) ?_
        · simp only [Function.comp_apply, Real.toNNReal_coe]
        · simp only [Function.comp_apply, Real.toNNReal_coe]
      have hTT'' : (T : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.2 ((Real.lt_toNNReal_iff_coe_lt).2 hTT')
      rw [WholeField.hullClock_fwdHull_rpath hwc hw0 hTT'', hTdef,
        ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
      exact lt_min (by exact_mod_cast ht) hlt

/-- **The coded hull for a pre-stop mark** (`exists_codedHull_of` with `F₀ = {history ∈ preMark t₁ Γ}`). -/
theorem exists_codedHull (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℝ≥0} (ht : t₁ < t₂)
    {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ) :
    ∃ A : Ω → Set ℂ, IsLocalSet A (fun ω => h ω - T₀) P ∧ ∀ᵐ ω ∂P, ∀ V' : Set ℂ, V' ⊆ H → V'.Nonempty →
      (((t₁ : ℝ≥0∞) < WholeField.hullClock (A ω) ∧ Disjoint (A ω) V') ↔
        (killedHistory W VL VR V ω ∈ preMark t₁ Γ ∧
          Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) V')) := by
  refine exists_codedHull_of hSC hT₀ ht (F₀ := {ω | killedHistory W VL VR V ω ∈ preMark t₁ Γ}) (fun hX => ?_)
    (fun ω hω => hω.1)
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have e : {ω | killedHistory W VL VR V ω ∈ preMark t₁ Γ} = {ω | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0)} ∩
      (killedHistory W VL VR (fun ω => min (t₁ : ℝ≥0∞) (V ω))) ⁻¹' Γ := by
    ext ω
    simp only [preMark, mem_ofPred_eq, truncK_killedHistory, mem_inter_iff, mem_preimage]
    rfl
  rw [e]
  exact (LocalExt.measurableSet_lt_stop hV t₁).inter
    (Ito.le_usualAugmentation (killedDrivingFiltration hX) P t₁ _ ((measurable_killedHistory_min hX t₁) hΓ))

/-- **The projection identity of a coupling through a stop on a coded event** (PROVE-LOCEXT-L's
`setIntegral_lapTest_pre` for general words): for `t₁ < t₂`, an event `F₀` of the driving filtration at `t₁` inside
`{t₁ < V}`, a nonempty compact `C ⊆ ℍ` and an open `U ⊆ C`, the centred field satisfies the projection identity at `U`
on a measurable version `M` of `F₀ ∩ {C ∩ cl(K_{t₂ ∧ V}) ∩ ℍ = ∅}` (the coded hull with the thickenings of `C`
shrinking to `C`). -/
theorem setIntegral_lapTest_coded [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℝ≥0} (ht : t₁ < t₂)
    {F₀ : Set Ω} (hF₀m : ∀ hX : IsMeasurableKilledDriving W VL VR V, MeasurableSet[drivingFiltration P hX t₁] F₀)
    (hF₀V : ∀ ω ∈ F₀, (t₁ : ℝ≥0∞) < V ω)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) {U : TopologicalSpace.Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∃ M : Set Ω, MeasurableSet M ∧
      M =ᵐ[P] F₀ ∩ {ω | Disjoint C (closure (fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) ∩ (upperHalfPlaneOpens : Set ℂ))} ∧
      ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
        Coupling.projFactor U f Ξ * ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  classical
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hhm : Measurable h := hSC.2.2.1
  obtain ⟨A, hloc, hcode⟩ := exists_codedHull_of hSC hT₀ ht hF₀m hF₀V
  obtain ⟨δ, hδ, hδH⟩ := hC.exists_thickening_subset_open QuantumZipper.isOpen_H hCH
  set Vm : ℕ → Set ℂ := fun m => Metric.thickening (δ / ((m : ℝ) + 1)) C with hVmdef
  have hpos : ∀ m : ℕ, (0 : ℝ) < δ / ((m : ℝ) + 1) := fun m => by positivity
  have hVmH : ∀ m, Vm m ⊆ H := fun m => by
    have hle : δ / ((m : ℝ) + 1) ≤ δ := div_le_self hδ.le (by have := m.cast_nonneg (α := ℝ); linarith)
    exact (Metric.thickening_mono hle C).trans hδH
  have hCV : ∀ m, C ⊆ Vm m := fun m => Metric.self_subset_thickening (hpos m) C
  set k : Set ℂ → ℂ := {S : Set ℂ | (t₁ : ℝ≥0∞) < WholeField.hullClock S}.indicator fun _ => (1 : ℂ) with hkdef
  have hk : Measurable[hittingSigma] k :=
    measurable_const.indicator (measurableSet_lt measurable_const WholeField.measurable_hullClock)
  have hkb : ∀ S, ‖k S‖ ≤ 1 := fun S => by
    simp only [hkdef]
    by_cases hS : S ∈ {S : Set ℂ | (t₁ : ℝ≥0∞) < WholeField.hullClock S}
    · rw [indicator_of_mem hS, norm_one]
    · rw [indicator_of_notMem hS, norm_zero]; exact zero_le_one
  have hAm : AEMeasurable A P := measurable_fst.comp_aemeasurable hloc.1
  set N : ℕ → Set Ω := fun m => {ω | (t₁ : ℝ≥0∞) < WholeField.hullClock (A ω) ∧ Disjoint (A ω) (Vm m)} with hNdef
  have hNm : ∀ m, NullMeasurableSet (N m) P := fun m =>
    hAm.nullMeasurableSet_preimage ((measurableSet_lt measurable_const WholeField.measurable_hullClock).inter
      (LocalSets.measurableSet_avoid Metric.isOpen_thickening (hVmH m)))
  set N' : ℕ → Set Ω := fun m => toMeasurable P (N m) with hN'def
  have hN'm : ∀ m, MeasurableSet (N' m) := fun m => measurableSet_toMeasurable _ _
  have hN'N : ∀ m, N' m =ᵐ[P] N m := fun m => (hNm m).toMeasurable_ae_eq
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => h ω - T₀ with hXdef
  have hXm : Measurable X := (WholeField.measurable_sub_dist T₀).comp hhm
  have hcm : ∀ χ : TestOn upperHalfPlaneOpens, Measurable fun ω => Complex.exp (Complex.I * (X ω χ : ℂ)) :=
    fun χ => GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hXm)
  have hnorm : ∀ (χ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * (X ω χ : ℂ))‖ ≤ 1 :=
    fun χ ω => (Complex.norm_exp_I_mul_ofReal _).le
  -- the identity on each `N' m`
  have hid : ∀ m, ∫ ω in N' m, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in N' m, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
    intro m
    have key := LocalExt.integral_indicator_lapTest_eq (V := ⟨Vm m, Metric.isOpen_thickening⟩) hloc
      (show (⟨Vm m, Metric.isOpen_thickening⟩ : TopologicalSpace.Opens ℂ) ≤ upperHalfPlaneOpens from hVmH m)
      (show U ≤ (⟨Vm m, Metric.isOpen_thickening⟩ : TopologicalSpace.Opens ℂ) from hUC.trans (hCV m)) hk hkb f Ξ
    have hind : ∀ χ : TestOn upperHalfPlaneOpens,
        ∫ ω, {ω | Disjoint (A ω) (Vm m)}.indicator (fun ω => k (A ω)) ω *
          Complex.exp (Complex.I * (X ω χ : ℂ)) ∂P =
        ∫ ω in N' m, Complex.exp (Complex.I * (X ω χ : ℂ)) ∂P := by
      intro χ
      rw [setIntegral_congr_set (hN'N m), ← integral_indicator₀ (hNm m)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h1 : Disjoint (A ω) (Vm m)
      · by_cases h2 : (t₁ : ℝ≥0∞) < WholeField.hullClock (A ω)
        · have hω : ω ∈ N m := ⟨h2, h1⟩
          simp only [indicator_of_mem (show ω ∈ {ω | Disjoint (A ω) (Vm m)} from h1), indicator_of_mem hω,
            hkdef, indicator_of_mem (show A ω ∈ {S : Set ℂ | (t₁ : ℝ≥0∞) < WholeField.hullClock S} from h2),
            one_mul]
        · have hω : ω ∉ N m := fun h' => h2 h'.1
          simp only [indicator_of_mem (show ω ∈ {ω | Disjoint (A ω) (Vm m)} from h1), indicator_of_notMem hω,
            hkdef, indicator_of_notMem (show A ω ∉ {S : Set ℂ | (t₁ : ℝ≥0∞) < WholeField.hullClock S} from h2),
            zero_mul]
      · have hω : ω ∉ N m := fun h' => h1 h'.2
        simp only [indicator_of_notMem (show ω ∉ {ω | Disjoint (A ω) (Vm m)} from h1), indicator_of_notMem hω,
          zero_mul]
    have k1 := hind (lapTest U f + Ξ)
    have k2 := hind Ξ
    simp only [hXdef] at k1 k2 key ⊢
    rw [← k1, ← k2]
    exact key
  -- the limit event
  set target : Set Ω := F₀ ∩ {ω | Disjoint C (closure (fwdHull (fun s : ℝ => W s.toNNReal ω)
    ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) ∩ (upperHalfPlaneOpens : Set ℂ))} with htarget
  set M : Set Ω := ⋃ n : ℕ, ⋂ m ≥ n, N' m with hMdef
  have hMm : MeasurableSet M := MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m =>
    MeasurableSet.iInter fun _ => hN'm m
  have hev : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, (ω ∈ N' m ↔ ω ∈ target) := by
    filter_upwards [hcode, ae_all_iff.2 fun m => (hN'N m)] with ω hω hN'ω
    obtain ⟨hev1, hev2⟩ := LocalExt.eventually_disjoint_thickening_iff
      (K := fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) hC hCH hδ
    by_cases hd : Disjoint C (closure (fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (t₂ : ℝ≥0∞) (V ω)).toNNReal : ℝ)) ∩ H)
    · filter_upwards [hev1 hd] with m hm
      have e1 : (ω ∈ N' m) ↔ (ω ∈ N m) := Iff.of_eq (hN'ω m)
      rw [e1, show (ω ∈ N m) ↔ _ from hω (Vm m) (hVmH m) ((hCne.mono (hCV m)))]
      exact ⟨fun h => ⟨h.1, hd⟩, fun h => ⟨h.1, hm⟩⟩
    · refine Eventually.of_forall fun m => ?_
      have e1 : (ω ∈ N' m) ↔ (ω ∈ N m) := Iff.of_eq (hN'ω m)
      rw [e1, show (ω ∈ N m) ↔ _ from hω (Vm m) (hVmH m) ((hCne.mono (hCV m)))]
      exact ⟨fun h => absurd h.2 (hev2 hd m), fun h => absurd h.2 hd⟩
  have hMt : M =ᵐ[P] target := by
    filter_upwards [hev] with ω hω
    apply propext
    simp only [hMdef, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm1, hm2⟩ := (hω.and (eventually_ge_atTop n)).exists
      exact hm1.1 (hn m hm2)
    · intro ht'
      obtain ⟨n, hn⟩ := eventually_atTop.1 hω
      exact ⟨n, fun m hm => (hn m hm).2 ht'⟩
  have hev' : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, (ω ∈ N' m ↔ ω ∈ M) := by
    filter_upwards [hev, hMt] with ω hω hMω
    have e : (ω ∈ M) ↔ (ω ∈ target) := Iff.of_eq hMω
    exact hω.mono fun m hm => hm.trans e.symm
  refine ⟨M, hMm, hMt, ?_⟩
  have L1 := LocalExt.tendsto_setIntegral_of_ae_eventually hN'm hMm hev'
    (hcm (lapTest U f + Ξ)).aestronglyMeasurable (hnorm _)
  have L2 := (LocalExt.tendsto_setIntegral_of_ae_eventually hN'm hMm hev'
    (hcm Ξ).aestronglyMeasurable (hnorm _)).const_mul (Coupling.projFactor U f Ξ)
  simp_rw [← hid] at L2
  exact tendsto_nhds_unique L1 L2

end Code

end Aux54

end Restart

end InteractingSLE
