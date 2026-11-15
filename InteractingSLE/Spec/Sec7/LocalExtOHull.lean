/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOChart
import InteractingSLE.Spec.Sec7.LocalExtHRec
import InteractingSLE.Spec.Coupling.WholeField2Germ

/-!
# The restarted hull as a random set measurable for the stopped restarted history

Packet PROVE-LOCEXT-O. The locality of the restarted hull `K'_τ` is proved on the sample space itself, conditionally on a
σ-algebra containing the stopped history; the decomposition needs a version of `K'_τ` measurable (for the hitting
σ-algebra) with respect to the stopped σ-algebra `𝓖'_τ` of the restarted filtration. It is read from the stopped
restarted driver as a two-seed history (`tsOf`, `tsHull` of PROVE-LOCEXT-H, whose compact avoidance events are Borel):

* `fwdHull_relClosed_of_continuousOn`, `closure_inter_eq_of_relClosed`: hulls of drivers continuous before `a > t` are
  relatively closed in `ℍ`;
* `measurable_tsHull_comp`: the hull read from a measurable history is hitting-measurable;
* `restartPV`, `restartHist`: the progressive version of the restarted driver and its history stopped at `τ`;
  **`measurable_restartHist`** (for `𝓖'_τ`) and **`tsHull_restartHist`** (it is `K'_τ` on every path continuous before
  `ζ` with `τ < ζ − T`);
* `measurable_piecewise_stopping`: a `𝓕_σ`-measurable function restricted to an event of `𝓕_π` on which `σ ≤ π`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull)
open scoped ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open LQGMetric LocalSets Sec2.Restart Sec5.Markov

/-! ### Relatively closed hulls -/

/-- The hull at `t` of a driver continuous before `a > t` is a relatively closed subset of `ℍ`. -/
theorem fwdHull_relClosed_of_continuousOn {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < a})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < a) :
    fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ H ∧ IsOpen (H \ fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  refine ⟨fun z hz => hz.1, ?_⟩
  obtain ⟨t₂, htt₂, ht₂a⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hc := Ito.continuousOn_rpath hw ht₂a
  have htt₂' : (t : ℝ) < (t₂ : ℝ) := by exact_mod_cast htt₂
  have heq : fwdHull (Ito.rpath w) t = fwdHull (Ito.clampDrv (Ito.rpath w) t₂) t :=
    InteractingSLE.fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr =>
      (Ito.clampDrv_eqOn (W := Ito.rpath w) hr).symm
  show IsOpen (H \ fwdHull (Ito.rpath w) t)
  rw [heq]
  exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull (Ito.continuous_clampDrv t₂.coe_nonneg hc) t.coe_nonneg

/-- A relatively closed subset of `ℍ` is its closure intersected with `ℍ`. -/
theorem closure_inter_eq_of_relClosed {K : Set ℂ} (hKH : K ⊆ H) (hK : IsOpen (H \ K)) :
    closure K ∩ (upperHalfPlaneOpens : Set ℂ) = K := by
  ext z
  constructor
  · rintro ⟨hzc, hzH⟩
    by_contra hzK
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzc _ hK ⟨hzH, hzK⟩
    exact hy1.2 hy2
  · intro hz
    exact ⟨subset_closure hz, hKH hz⟩

/-! ### Hulls read from histories -/

/-- The hull read from a two-seed history is relatively closed in `ℍ`. -/
theorem tsHull_relClosed (y : TwoSeedHist) : tsHull y ⊆ H ∧ IsOpen (H \ tsHull y) := by
  refine ⟨fun z hz => hz.2, ?_⟩
  have e : H \ tsHull y = H ∩ (closure (fwdHull (Ito.rpath (Sec4.regPath (tsHist y))) (Sec4.histStop (tsHist y))))ᶜ := by
    ext z
    simp only [tsHull, Sec4.regHull, Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hz, fun hc => h ⟨hc, hz⟩⟩
    · rintro ⟨hz, h⟩; exact ⟨hz, fun hc => h hc.1⟩
  rw [e]
  exact QuantumZipper.isOpen_H.inter isClosed_closure.isOpen_compl

/-- **The hull read from a measurable history is hitting-measurable.** -/
theorem measurable_tsHull_comp {Ω : Type*} {m : MeasurableSpace Ω} {Y : Ω → TwoSeedHist} (hY : Measurable[m] Y) :
    Measurable[m, hittingSigma] fun ω => tsHull (Y ω) := by
  refine @measurable_generateFrom _ _ m _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have : (0 : ℝ) < (0 : ℂ).im := hUH h0
    simp at this⟩
  have e : (fun ω => tsHull (Y ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ k : ℕ, (Y ⁻¹' {y | Disjoint (WholeField.openExhaust U k) (tsHull y)})ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_compl_iff]
    constructor
    · rintro ⟨z, hzK, hzU⟩
      rw [← WholeField.iUnion_openExhaust hU hne] at hzU
      obtain ⟨k, hk⟩ := mem_iUnion.1 hzU
      exact ⟨k, fun hd => Set.disjoint_left.1 hd hk hzK⟩
    · rintro ⟨k, hk⟩
      obtain ⟨z, hzC, hzK⟩ := Set.not_disjoint_iff.1 hk
      exact ⟨z, hzK, WholeField.openExhaust_subset k hzC⟩
  rw [e]
  exact MeasurableSet.iUnion fun k =>
    (hY (measurableSet_disjoint_tsHull (WholeField.isCompact_openExhaust U k))).compl

/-! ### The stopped restarted driver -/

section Restart

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0}

/-- The progressive version of the restarted driver `W_{T+·} − W_T`. -/
def restartPV (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  progVersion (restartLife ζ T) fun t ω => progVersion ζ W (T ω + t) ω - progVersion ζ W (T ω) ω

/-- The restarted driver stopped at `τ`, as a two-seed history (the marks are irrelevant and set to `0`). -/
def restartHist (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : TwoSeedHist :=
  tsOf ((τ ω).untopD 0) fun t => (restartPV ζ W T t ω, fun _ => 0, fun _ => 0)

/-- **The stopped restarted history is measurable for `𝓖'_τ`.** -/
theorem measurable_restartHist (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ) (hτfin : ∀ ω, τ ω ≠ ⊤) :
    Measurable[hτ.measurableSpace] (restartHist ζ W T τ) := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  set 𝓖' := restartFiltration 𝓓 T hT with h𝓖'
  have hle : killedDrivingFiltration hX ≤ 𝓓 := Ito.le_usualAugmentation _ P
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX)
  have hζ : IsStoppingTime 𝓓 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hWad
  have hpv := isStronglyProgressive_progVersion hWad
  have hXad := adaptedBefore_restart hT hζ hpv hpv
  have hR : IsStronglyProgressive 𝓖' (restartPV ζ W T) := isStronglyProgressive_progVersion hXad
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hττ' : τ = fun ω => ((τ' ω : ℝ≥0) : WithTop ℝ≥0) := funext fun ω => by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (hτfin ω)
    simp only [hτ'def, ← hs, WithTop.untopD_coe]
  have hq : ∀ q : ℚ≥0, IsStoppingTime 𝓖' fun ω => ((min (q : ℝ≥0) (τ' ω) : ℝ≥0) : WithTop ℝ≥0) := by
    intro q
    have h := hτ.min_const (q : ℝ≥0)
    have e : (fun ω => ((min (q : ℝ≥0) (τ' ω) : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => min (τ ω) ((q : ℝ≥0) : WithTop ℝ≥0) := by
      funext ω
      rw [WithTop.coe_min, min_comm]
      simp only [hττ']
    rw [e]
    exact h
  have hqle : ∀ q : ℚ≥0, (hq q).measurableSpace ≤ hτ.measurableSpace := fun q =>
    IsStoppingTime.measurableSpace_mono _ _ fun ω => by
      rw [hττ']
      exact WithTop.coe_le_coe.2 (min_le_right _ _)
  have hev : ∀ q : ℚ≥0, Measurable[hτ.measurableSpace] fun ω => restartPV ζ W T (min (q : ℝ≥0) (τ' ω)) ω := by
    intro q
    have h := measurable_stoppedValue hR (hq q)
    exact h.mono (hqle q) le_rfl
  have hτm : Measurable[hτ.measurableSpace] fun ω => ((τ' ω : ℝ≥0) : WithTop ℝ≥0) := by
    rw [← hττ']
    exact hτ.measurable
  refine hτm.prodMk (@Measurable.of_eval Ω ℚ≥0 (fun _ => ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ))
    hτ.measurableSpace _ _ fun q => ?_)
  exact (hev q).prodMk measurable_const

/-- **The hull read from the stopped restarted history is the restarted hull** on every path continuous before `ζ`
with `τ < ζ − T`. -/
theorem tsHull_restartHist {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hτζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω) :
    tsHull (restartHist ζ W T τ ω) =
      fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
  set S : ℝ≥0 := (τ ω).untopD 0 with hSdef
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := fun t ht =>
    (coe_lt_sub_iff _ _).1 ht
  have hTζ : (T ω : ℝ≥0∞) < ζ ω := by
    have := hlt S hτζ
    exact lt_of_le_of_lt (by exact_mod_cast le_self_add) this
  -- the restarted driver is continuous before `ζ − T`
  have hw : ContinuousOn (fun t => restartDrv W T t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} := by
    have h1 : ContinuousOn (fun t : ℝ≥0 => W (T ω + t) ω) {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} :=
      hWc.comp (continuous_const.add continuous_id).continuousOn fun t ht => hlt t ht
    exact h1.sub continuousOn_const
  -- the progressive versions agree with the paths
  have hpvT : progVersion ζ W (T ω) ω = W (T ω) ω := Sec2.Restart.progVersion_eq hWc hTζ
  have hX'eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω →
      progVersion ζ W (T ω + t) ω - progVersion ζ W (T ω) ω = restartDrv W T t ω := fun t ht => by
    rw [hpvT, Sec2.Restart.progVersion_eq hWc (hlt t ht)]
    rfl
  have hX'c : ContinuousOn (fun t => progVersion ζ W (T ω + t) ω - progVersion ζ W (T ω) ω)
      {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} := hw.congr fun t ht => hX'eq t ht
  have hRe : ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → restartPV ζ W T t ω = restartDrv W T t ω :=
    fun t ht => by
      rw [restartPV, Sec2.Restart.progVersion_eq hX'c ht, hX'eq t ht]
  have hIic : ∀ t ∈ Iic S, (t : ℝ≥0∞) < restartLife ζ T ω := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hτζ
  have hXc : ContinuousOn (fun t => (restartPV ζ W T t ω, (fun _ => 0 : Fin 1 → ℝ), (fun _ => 0 : Fin 1 → ℝ)))
      (Iic S) := by
    have h1 : ContinuousOn (fun t => (restartDrv W T t ω, (fun _ => 0 : Fin 1 → ℝ), (fun _ => 0 : Fin 1 → ℝ)))
        (Iic S) := (hw.mono fun t ht => hIic t ht).prodMk continuousOn_const
    exact h1.congr fun t ht => by rw [hRe t (hIic t ht)]
  have hrel := fwdHull_relClosed_of_continuousOn hw hτζ
  rw [restartHist, tsHull_tsOf_eq hXc hτζ hw (fun t ht => hRe t (hIic t ht)),
    closure_inter_eq_of_relClosed hrel.1 hrel.2]

end Restart

/-! ### Piecewise measurability for stopped σ-algebras -/

section Piecewise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open Classical in
/-- A function measurable for `𝓕_σ`, restricted to an event `E` of `𝓕_π` on which `σ ≤ π` (and constant off `E`), is
measurable for `𝓕_π`. -/
theorem measurable_piecewise_stopping {𝓕 : Filtration ℝ≥0 mΩ} {σ π : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime 𝓕 σ) (hπ : IsStoppingTime 𝓕 π) {β : Type*} [MeasurableSpace β] {f : Ω → β}
    (hf : Measurable[hσ.measurableSpace] f) {E : Set Ω} (hE : MeasurableSet[hπ.measurableSpace] E)
    (hEle : ∀ ω ∈ E, σ ω ≤ π ω) (b : β) :
    Measurable[hπ.measurableSpace] (E.piecewise f fun _ => b) := by
  intro S hS
  have hmin : (hσ.min hπ).measurableSpace ≤ hπ.measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun ω => min_le_right _ _
  have h1 : MeasurableSet[hπ.measurableSpace] (f ⁻¹' S ∩ {ω | σ ω ≤ π ω}) :=
    hmin _ (IsStoppingTime.measurableSet_inter_le hσ hπ _ (hf hS))
  have e : E.piecewise f (fun _ => b) ⁻¹' S = (E ∩ (f ⁻¹' S ∩ {ω | σ ω ≤ π ω})) ∪ (Eᶜ ∩ {_ω | b ∈ S}) := by
    ext ω
    by_cases hω : ω ∈ E
    · simp [hω, hEle ω hω]
    · simp [hω]
  rw [e]
  exact (hE.inter h1).union (hE.compl.inter (MeasurableSet.const _))

end Piecewise

end LocalExt

end InteractingSLE
