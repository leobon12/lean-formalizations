/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField5Restart
import InteractingSLE.Spec.Sec7.TwoForceFreeze

/-!
# (WF7a): later driving information does not change a germ field law

Packet PROVE-WHOLEFIELD5 (follow-up note C.2, `ig1_followup_proofs.txt` L1541–1550: "(WF7a) `E[Y | entire canonical
driving path] = E[Y | H_τ]` … conditioning (WF7a) again gives `E[Y | 𝓕_τ] = E[Y | H_τ]`").

* `condExp_eq_of_le_sup_generateFrom` (abstract): the freezing step of Aux. lemma 47 ((GB5),
  `Sec7.condExp_eq_of_le_sup_comap`) for a π-system of events instead of a random element: if `𝓕 ≤ 𝒢`, every event `C`
  of a π-system `𝒞 ∋ univ` has `E[1_C | 𝒢] = E[1_C | 𝓕]`, and `𝓕 ≤ 𝓕' ≤ 𝓕 ⊔ σ(𝒞)`, then `E[Y | 𝓕'] = E[Y | 𝓕]` for
  every bounded `𝒢`-measurable `Y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

/-! ### The freezing step for a π-system of events -/

section Abstract

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The sets `A ∩ C` (`A ∈ 𝓕`, `C ∈ 𝒞`, `univ ∈ 𝒞`) generate `𝓕 ⊔ σ(𝒞)`. -/
theorem sup_generateFrom_eq_generateFrom_inter (𝓕 : MeasurableSpace Ω) {𝒞 : Set (Set Ω)}
    (h𝒞 : univ ∈ 𝒞) :
    𝓕 ⊔ MeasurableSpace.generateFrom 𝒞 =
      MeasurableSpace.generateFrom {s | ∃ A C, MeasurableSet[𝓕] A ∧ C ∈ 𝒞 ∧ s = A ∩ C} := by
  apply le_antisymm
  · refine sup_le (fun A hA => ?_) (MeasurableSpace.generateFrom_le fun C hC => ?_)
    · exact MeasurableSpace.measurableSet_generateFrom ⟨A, univ, hA, h𝒞, by simp⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, C, MeasurableSet.univ, hC, by simp⟩
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    obtain ⟨A, C, hA, hC, rfl⟩ := hs
    exact (le_sup_left (a := 𝓕) (b := MeasurableSpace.generateFrom 𝒞) A hA).inter
      (le_sup_right (a := 𝓕) (b := MeasurableSpace.generateFrom 𝒞) _
        (MeasurableSpace.measurableSet_generateFrom hC))

theorem isPiSystem_inter_of_isPiSystem (𝓕 : MeasurableSpace Ω) {𝒞 : Set (Set Ω)} (h𝒞 : IsPiSystem 𝒞) :
    IsPiSystem {s | ∃ A C, MeasurableSet[𝓕] A ∧ C ∈ 𝒞 ∧ s = A ∩ C} := by
  rintro _ ⟨A₁, C₁, hA₁, hC₁, rfl⟩ _ ⟨A₂, C₂, hA₂, hC₂, rfl⟩ hne
  have hne' : (C₁ ∩ C₂).Nonempty := by
    obtain ⟨ω, hω⟩ := hne
    exact ⟨ω, hω.1.2, hω.2.2⟩
  refine ⟨A₁ ∩ A₂, C₁ ∩ C₂, hA₁.inter hA₂, h𝒞 C₁ hC₁ C₂ hC₂ hne', ?_⟩
  ext ω
  simp only [mem_inter_iff]
  tauto

/-- **The freezing step, π-system form** ((GB5) of Aux. lemma 47 with a π-system of events). Let `𝓕 ≤ 𝒢 ≤ m₀`, let
`𝒞 ∋ univ` be a π-system of measurable events with `E[1_C | 𝒢] = E[1_C | 𝓕]` for every `C ∈ 𝒞`, and let `Y` be
bounded and `𝒢`-measurable. Then `E[Y | 𝓕'] = E[Y | 𝓕]` for every `σ`-algebra `𝓕 ≤ 𝓕' ≤ 𝓕 ⊔ σ(𝒞)`. -/
theorem condExp_eq_of_le_sup_generateFrom {𝓕 𝒢 𝓕' : MeasurableSpace Ω} {𝒞 : Set (Set Ω)}
    (h𝓕𝒢 : 𝓕 ≤ 𝒢) (h𝒢 : 𝒢 ≤ m₀) (h𝓕𝓕' : 𝓕 ≤ 𝓕') (h𝓕'𝒞 : 𝓕' ≤ 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞)
    (h𝒞π : IsPiSystem 𝒞) (h𝒞u : univ ∈ 𝒞) (h𝒞m : ∀ C ∈ 𝒞, MeasurableSet[m₀] C)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[𝒢] Y) {c : ℝ} (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ c)
    (hlaw : ∀ C ∈ 𝒞, μ[C.indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[μ] μ[C.indicator (fun _ => (1 : ℝ)) | 𝓕]) :
    μ[Y | 𝓕'] =ᵐ[μ] μ[Y | 𝓕] := by
  have h𝓕 : 𝓕 ≤ m₀ := h𝓕𝒢.trans h𝒢
  have hYm : AEStronglyMeasurable[m₀] Y μ := (hY.mono h𝒢).aestronglyMeasurable
  have hYi : Integrable Y μ := Integrable.of_bound hYm c hYb
  have h𝓗 : 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞 ≤ m₀ :=
    sup_le h𝓕 (MeasurableSpace.generateFrom_le h𝒞m)
  -- the identity on the generators `A ∩ C`
  have hgen : ∀ A C, MeasurableSet[𝓕] A → C ∈ 𝒞 →
      ∫ ω in A ∩ C, Y ω ∂μ = ∫ ω in A ∩ C, (μ[Y | 𝓕]) ω ∂μ := by
    intro A C hA hC
    have hCm : MeasurableSet[m₀] C := h𝒞m C hC
    set I : Ω → ℝ := C.indicator fun _ => (1 : ℝ) with hIdef
    have hI : Integrable I μ := (integrable_const 1).indicator hCm
    have hmulI : ∀ f : Ω → ℝ, f * I = C.indicator f := fun f => by
      funext ω
      by_cases hω : ω ∈ C
      · simp [hIdef, indicator_of_mem hω]
      · simp [hIdef, indicator_of_notMem hω]
    have hGB1 := Sec7.condExp_mul_eq_mul_condExp_of_condExp_eq h𝓕𝒢 h𝒢 hY hYb hI (hlaw C hC)
    have hgI : Integrable (μ[Y | 𝓕] * I) μ := by
      rw [hmulI]; exact integrable_condExp.indicator hCm
    have hYI : Integrable (Y * I) μ := by
      rw [hmulI]; exact hYi.indicator hCm
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_condExp (m := 𝓕) (μ := μ) (f := Y)) hgI hI
    calc ∫ ω in A ∩ C, Y ω ∂μ = ∫ ω in A, (Y * I) ω ∂μ := by
          rw [hmulI, setIntegral_indicator hCm]
      _ = ∫ ω in A, (μ[Y * I | 𝓕]) ω ∂μ := (setIntegral_condExp h𝓕 hYI hA).symm
      _ = ∫ ω in A, (μ[μ[Y | 𝓕] * I | 𝓕]) ω ∂μ :=
          setIntegral_congr_ae (h𝓕 A hA) (by
            filter_upwards [hGB1, hpull] with ω h1 h2 _
            rw [h1, h2])
      _ = ∫ ω in A, (μ[Y | 𝓕] * I) ω ∂μ := setIntegral_condExp h𝓕 hgI hA
      _ = ∫ ω in A ∩ C, (μ[Y | 𝓕]) ω ∂μ := by
          rw [hmulI, setIntegral_indicator hCm]
  -- Dynkin's π-λ theorem on `𝓕 ⊔ σ(𝒞)`
  have hall : ∀ t, MeasurableSet[𝓕 ⊔ MeasurableSpace.generateFrom 𝒞] t →
      ∫ ω in t, Y ω ∂μ = ∫ ω in t, (μ[Y | 𝓕]) ω ∂μ := by
    intro t ht
    refine MeasurableSpace.induction_on_inter (m := 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞)
      (C := fun t _ => ∫ ω in t, Y ω ∂μ = ∫ ω in t, (μ[Y | 𝓕]) ω ∂μ)
      (sup_generateFrom_eq_generateFrom_inter 𝓕 h𝒞u) (isPiSystem_inter_of_isPiSystem 𝓕 h𝒞π) ?_ ?_ ?_ ?_
      t ht
    · simp
    · rintro _ ⟨A, C, hA, hC, rfl⟩
      exact hgen A C hA hC
    · intro t' ht' hC
      have ht'm : MeasurableSet[m₀] t' := h𝓗 _ ht'
      have huniv := hgen univ univ MeasurableSet.univ h𝒞u
      simp only [univ_inter, Measure.restrict_univ] at huniv
      rw [setIntegral_compl ht'm hYi, setIntegral_compl ht'm integrable_condExp, huniv, hC]
    · intro f hdisj hfm hC
      have hfm' : ∀ i, MeasurableSet[m₀] (f i) := fun i => h𝓗 _ (hfm i)
      rw [integral_iUnion hfm' hdisj hYi.integrableOn, integral_iUnion hfm' hdisj integrable_condExp.integrableOn]
      exact tsum_congr hC
  -- `E[Y | 𝓕]` is a version of `E[Y | 𝓕 ⊔ σ(𝒞)]`; the tower property passes to `𝓕'`
  have hsup : μ[Y | 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞] =ᵐ[μ] μ[Y | 𝓕] :=
    (ae_eq_condExp_of_forall_setIntegral_eq h𝓗 hYi (fun _ _ _ => integrable_condExp.integrableOn)
      (fun t ht _ => (hall t ht).symm)
      ((stronglyMeasurable_condExp (m := 𝓕) (μ := μ) (f := Y)).mono
        (le_sup_left : 𝓕 ≤ 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞)).aestronglyMeasurable).symm
  calc μ[Y | 𝓕'] =ᵐ[μ] μ[μ[Y | 𝓕 ⊔ MeasurableSpace.generateFrom 𝒞] | 𝓕'] :=
        (condExp_condExp_of_le h𝓕'𝒞 h𝓗).symm
    _ =ᵐ[μ] μ[μ[Y | 𝓕] | 𝓕'] := condExp_congr_ae hsup
    _ = μ[Y | 𝓕] := condExp_of_stronglyMeasurable (h𝓕'𝒞.trans h𝓗)
        (stronglyMeasurable_condExp.mono h𝓕𝓕') integrable_condExp

end Abstract

/-! ### The restarted cylinders -/

section Cyl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

open Sec2 Sec2.Restart Sec2.Assembly

/-- The state space of a restarted driving process with its noise increment. -/
abbrev RState (nL nR : ℕ) : Type := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

/-- **The restarted state** at time `q` after `T`, from the progressive versions of the coordinates and a version
`Bv` of the noise: `(W_{T+q} − W_T, V_{T+q} − W_T, Bv_{T+q} − Bv_T)`. -/
def restartTuple (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (Bv : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) (q : ℝ≥0) (ω : Ω) : RState nL nR :=
  (progVersion ζ W (T ω + q) ω - progVersion ζ W (T ω) ω,
    fun i => progVersion ζ (VL i) (T ω + q) ω - progVersion ζ W (T ω) ω,
    fun j => progVersion ζ (VR j) (T ω + q) ω - progVersion ζ W (T ω) ω, Bv (T ω + q) ω - Bv (T ω) ω)

/-- **The restarted cylinder** `{t_j < ζ − T, restartTuple(t_j) ∈ K_j ∀ j}`. -/
def restartCyl (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (Bv : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) (n : ℕ) (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (RState nL nR)) : Set Ω :=
  {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧ restartTuple W VL VR Bv ζ T (ts j) ω ∈ K j}

/-- The π-system of the restarted cylinders inside a set `G`, with `univ`. -/
def restartCylSys (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (Bv : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) (G : Set Ω) : Set (Set Ω) :=
  insert univ {S | ∃ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (RState nL nR)),
    (∀ j, MeasurableSet (K j)) ∧ S = G ∩ restartCyl W VL VR Bv ζ T n ts K}

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bv : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω}

omit mΩ in
theorem restartCyl_inter (n m : ℕ) (ts : Fin n → ℝ≥0) (ts' : Fin m → ℝ≥0) (K : Fin n → Set (RState nL nR))
    (K' : Fin m → Set (RState nL nR)) :
    restartCyl W VL VR Bv ζ T n ts K ∩ restartCyl W VL VR Bv ζ T m ts' K' =
      restartCyl W VL VR Bv ζ T (n + m) (Fin.append ts ts') (Fin.append K K') := by
  ext ω
  simp only [restartCyl, mem_inter_iff, mem_ofPred_eq]
  rw [Fin.forall_fin_add]
  simp only [Fin.append_left, Fin.append_right]

omit mΩ in
theorem isPiSystem_restartCylSys : IsPiSystem (restartCylSys W VL VR Bv ζ T G) := by
  rintro S₁ hS₁ S₂ hS₂ -
  rcases hS₁ with rfl | ⟨n, ts, K, hK, rfl⟩
  · rwa [univ_inter]
  rcases hS₂ with rfl | ⟨m, ts', K', hK', rfl⟩
  · rw [inter_univ]; exact Or.inr ⟨n, ts, K, hK, rfl⟩
  refine Or.inr ⟨n + m, Fin.append ts ts', Fin.append K K', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hK i
    · rw [Fin.append_right]; exact hK' i
  · rw [← restartCyl_inter]
    ext ω; simp only [mem_inter_iff]; tauto

omit mΩ in
theorem univ_mem_restartCylSys : univ ∈ restartCylSys W VL VR Bv ζ T G := mem_insert _ _

omit mΩ in
theorem inter_restartCyl_mem (n : ℕ) (ts : Fin n → ℝ≥0) {K : Fin n → Set (RState nL nR)}
    (hK : ∀ j, MeasurableSet (K j)) :
    G ∩ restartCyl W VL VR Bv ζ T n ts K ∈ restartCylSys W VL VR Bv ζ T G :=
  mem_insert_of_mem _ ⟨n, ts, K, hK, rfl⟩

omit mΩ in
/-- The one-time cylinder. -/
theorem restartCyl_one (q : ℝ≥0) (U : Set (RState nL nR)) :
    restartCyl W VL VR Bv ζ T 1 ![q] ![U] =
      {ω | (q : ℝ≥0∞) < ζ ω - T ω ∧ restartTuple W VL VR Bv ζ T q ω ∈ U} := by
  ext ω
  simp only [restartCyl, mem_ofPred_eq, Fin.forall_fin_one, Matrix.cons_val_zero]

end Cyl

/-! ### The driving σ-algebra is generated by the history at `T` and the restarted cylinders -/

section Gen

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {Bv : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

open Sec2 Sec2.Restart Sec2.Assembly

/-- The lifetime of a measurable killed driving process is measurable. -/
theorem measurable_lifetime (hX : IsMeasurableKilledDriving W VL VR ζ) : Measurable ζ := by
  refine measurable_of_Ioi fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe r =>
    convert hX r univ MeasurableSet.univ using 1
    ext ω
    simp

omit mΩ in
/-- On a good path, before the lifetime, the restarted state is the raw one. -/
theorem restartTuple_eq_raw {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω)) (hTζ : (T ω : ℝ≥0∞) < ζ ω) (hBv : ∀ t, Bv t ω = B t ω) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ ω - T ω) :
    restartTuple W VL VR Bv ζ T q ω = (W (T ω + q) ω - W (T ω) ω, (fun i => VL i (T ω + q) ω - W (T ω) ω),
      (fun j => VR j (T ω + q) ω - W (T ω) ω), B (T ω + q) ω - B (T ω) ω) := by
  have hsum : ((T ω + q : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [ENNReal.coe_add, add_comm]; exact lt_tsub_iff_right.1 hq
  obtain ⟨a1, a2, a3⟩ := restart_values hp hsum
  obtain ⟨b1, -, -⟩ := restart_values hp hTζ
  simp only [restartTuple, a1, a2, a3, b1, hBv]

omit mΩ in
/-- On a good path the restarted state is continuous before the lifetime. -/
theorem continuousOn_restartTuple {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω)) (hTζ : (T ω : ℝ≥0∞) < ζ ω) (hBv : ∀ t, Bv t ω = B t ω)
    (hBvc : Continuous fun t => Bv t ω) :
    ContinuousOn (fun q => restartTuple W VL VR Bv ζ T q ω) {q : ℝ≥0 | (q : ℝ≥0∞) < ζ ω - T ω} := by
  have hF := hp.isForcePath
  have hmaps : MapsTo (fun q : ℝ≥0 => T ω + q) {q : ℝ≥0 | (q : ℝ≥0∞) < ζ ω - T ω}
      {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun q hq => by
    show ((T ω + q : ℝ≥0) : ℝ≥0∞) < ζ ω
    rw [ENNReal.coe_add, add_comm]; exact lt_tsub_iff_right.1 hq
  have hsh : Continuous fun q : ℝ≥0 => T ω + q := continuous_const.add continuous_id
  have cw : ContinuousOn (fun q : ℝ≥0 => W (T ω + q) ω - W (T ω) ω)
      {q : ℝ≥0 | (q : ℝ≥0∞) < ζ ω - T ω} :=
    (hF.continuousOn_w.comp hsh.continuousOn hmaps).sub continuousOn_const
  have cL : ∀ i, ContinuousOn (fun q : ℝ≥0 => VL i (T ω + q) ω - W (T ω) ω)
      {q : ℝ≥0 | (q : ℝ≥0∞) < ζ ω - T ω} := fun i =>
    ((hF.continuousOn_vL i).comp hsh.continuousOn hmaps).sub continuousOn_const
  have cR : ∀ j, ContinuousOn (fun q : ℝ≥0 => VR j (T ω + q) ω - W (T ω) ω)
      {q : ℝ≥0 | (q : ℝ≥0∞) < ζ ω - T ω} := fun j =>
    ((hF.continuousOn_vR j).comp hsh.continuousOn hmaps).sub continuousOn_const
  have cB : Continuous fun q => Bv (T ω + q) ω - Bv (T ω) ω := (hBvc.comp hsh).sub continuous_const
  refine ContinuousOn.congr (cw.prodMk ((continuousOn_pi.2 cL).prodMk ((continuousOn_pi.2 cR).prodMk
    cB.continuousOn))) fun q hq => ?_
  rw [restartTuple_eq_raw hp hTζ hBv hq]
  simp only [hBv]

/-- The restarted state is measurable. -/
theorem measurable_restartTuple (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hBvc : ∀ ω, Continuous fun t => Bv t ω) (hBvm : ∀ t, Measurable (Bv t)) (q : ℝ≥0) :
    Measurable (restartTuple W VL VR Bv ζ T q) := by
  have hWd : AdaptedBefore (drivingFiltration P hX) ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLd : ∀ i, AdaptedBefore (drivingFiltration P hX) ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRd : ∀ j, AdaptedBefore (drivingFiltration P hX) ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX j)
  have hTm : Measurable T := by
    have := (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable'
    simpa only [Function.comp_def, WithTop.untopD_coe] using this
  have hq := isStoppingTime_add_const hT q
  have ev : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore (drivingFiltration P hX) ζ X →
      Measurable (fun ω => progVersion ζ X (T ω + q) ω) ∧ Measurable (fun ω => progVersion ζ X (T ω) ω) :=
    fun hX' => ⟨(measurable_eval_stop (isStronglyProgressive_progVersion hX') hq).mono
      hq.measurableSpace_le le_rfl, (measurable_eval_stop (isStronglyProgressive_progVersion hX') hT).mono
      hT.measurableSpace_le le_rfl⟩
  have hBvj : Measurable (Function.uncurry fun s ω => Bv s ω) :=
    measurable_uncurry_of_continuous_of_measurable hBvc hBvm
  have eB : Measurable fun ω => Bv (T ω + q) ω := hBvj.comp ((hTm.add_const q).prodMk measurable_id)
  have eB0 : Measurable fun ω => Bv (T ω) ω := hBvj.comp (hTm.prodMk measurable_id)
  exact ((ev hWd).1.sub (ev hWd).2).prodMk ((measurable_pi_iff.2 fun i => (ev (hVLd i)).1.sub (ev hWd).2).prodMk
    ((measurable_pi_iff.2 fun j => (ev (hVRd j)).1.sub (ev hWd).2).prodMk (eB.sub eB0)))

/-- The restarted cylinders are measurable. -/
theorem measurableSet_restartCyl (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hBvc : ∀ ω, Continuous fun t => Bv t ω) (hBvm : ∀ t, Measurable (Bv t)) (n : ℕ) (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (RState nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    MeasurableSet (restartCyl W VL VR Bv ζ T n ts K) := by
  have hTm : Measurable T := by
    have := (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable'
    simpa only [Function.comp_def, WithTop.untopD_coe] using this
  have : restartCyl W VL VR Bv ζ T n ts K = ⋂ j, ({ω | (ts j : ℝ≥0∞) < ζ ω - T ω} ∩
      restartTuple W VL VR Bv ζ T (ts j) ⁻¹' K j) := by
    ext ω; simp [restartCyl]
  rw [this]
  exact MeasurableSet.iInter fun j => (measurableSet_lt measurable_const
    ((measurable_lifetime hX).sub (measurable_coe_nnreal_ennreal.comp hTm))).inter
    (measurable_restartTuple hX hT hBvc hBvm (ts j) (hK j))

omit mΩ in
/-- `measurable_pi_iff` for an explicit (non-instance) σ-algebra on the domain. -/
theorem measurable_pi_iff' {α ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (m : MeasurableSpace α)
    {g : α → ∀ i, X i} : Measurable[m] g ↔ ∀ i, Measurable[m] fun x => g x i :=
  @measurable_pi_iff α ι X m _ g

open scoped Classical in
/-- **The driving σ-algebra is generated by the stopped history and the restarted cylinders** (up to null sets).
For a driving stop `T`, a continuous version `Bv` of the noise and a measurable co-null set `G` of good paths
(`T < ζ`, `Bv = B`): `⋁_t 𝓕_t ≤ 𝓕_T ⊔ σ(G ∩ restarted cylinders)`. Proof: an event `{r < ζ, X_r ∈ A}` is, before
`T`, an `𝓕_T`-event; after `T`, on `G`, `X_r = W_T + dec(code)(r − T)` with the dyadic codes of the restarted
coordinates (measurable in the cylinders) and the jointly measurable decoder of Theorem 2.2, and `r < ζ` iff some
rational time after `r − T` is alive. -/
theorem iSup_driving_le_sup_restartCylSys (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hBvc : ∀ ω, Continuous fun t => Bv t ω) (hBvm : ∀ t, Measurable (Bv t))
    {G : Set Ω} (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧ (T ω : ℝ≥0∞) < ζ ω ∧ ∀ t, Bv t ω = B t ω) :
    (⨆ t, drivingFiltration P hX t) ≤
      hT.measurableSpace ⊔ MeasurableSpace.generateFrom (restartCylSys W VL VR Bv ζ T G) := by
  set 𝒞 := restartCylSys W VL VR Bv ζ T G with h𝒞
  have hMle : (hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞) ≤ mΩ := sup_le hT.measurableSpace_le (MeasurableSpace.generateFrom_le fun C hC => by
    rcases hC with rfl | ⟨n, ts, K, hK, rfl⟩
    · exact MeasurableSet.univ
    · exact hGm.inter (measurableSet_restartCyl hX hT hBvc hBvm n ts hK))
  have hTM : hT.measurableSpace ≤ (hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞) := le_sup_left
  have h𝒞M : MeasurableSpace.generateFrom 𝒞 ≤ (hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞) := le_sup_right
  have hnullT : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[hT.measurableSpace] N :=
    fun N hN h0 => measurableSet_stopping_driving_of_null hX hT hN h0
  have hnullM : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] N :=
    fun N hN h0 => hTM _ (hnullT N hN h0)
  have hGT : MeasurableSet[hT.measurableSpace] G := by
    have := (hnullT _ hGm.compl hGc).compl; rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hTm : Measurable[hT.measurableSpace] T := by
    have := (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
    simpa only [Function.comp_def, WithTop.untopD_coe] using this
  have hTm' : Measurable T := hTm.mono hT.measurableSpace_le le_rfl
  have hWd : AdaptedBefore (drivingFiltration P hX) ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLd : ∀ i, AdaptedBefore (drivingFiltration P hX) ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRd : ∀ j, AdaptedBefore (drivingFiltration P hX) ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX j)
  -- the one-time cylinders
  have hcyl1 : ∀ (q : ℝ≥0) (U : Set (RState nL nR)), MeasurableSet U →
      MeasurableSet[MeasurableSpace.generateFrom 𝒞]
        (G ∩ {ω | (q : ℝ≥0∞) < ζ ω - T ω ∧ restartTuple W VL VR Bv ζ T q ω ∈ U}) := by
    intro q U hU
    rw [← restartCyl_one]
    exact MeasurableSpace.measurableSet_generateFrom
      (inter_restartCyl_mem 1 ![q] fun j => by fin_cases j; exact hU)
  -- the restarted state at `0` is known at `T`
  have hR0 : Measurable[hT.measurableSpace] (restartTuple W VL VR Bv ζ T 0) := by
    have e : restartTuple W VL VR Bv ζ T 0 = fun ω => ((0 : ℝ),
        fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω,
        fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω, (0 : ℝ)) := by
      funext ω; simp only [restartTuple, add_zero, sub_self]
    rw [e]
    have e0 := measurable_eval_stop (isStronglyProgressive_progVersion hWd) hT
    exact measurable_const.prodMk (((measurable_pi_iff' _).2 fun i =>
      (measurable_eval_stop (isStronglyProgressive_progVersion (hVLd i)) hT).sub e0).prodMk
      (((measurable_pi_iff' _).2 fun j =>
        (measurable_eval_stop (isStronglyProgressive_progVersion (hVRd j)) hT).sub e0).prodMk
        measurable_const))
  -- the dyadic codes of the restarted coordinates
  set code : (RState nL nR → ℝ) → Ω → PCode := fun φ ω =>
    killedCode (fun q ω' => if ω' ∈ G then φ (restartTuple W VL VR Bv ζ T q ω') else 0)
      (φ (restartTuple W VL VR Bv ζ T 0 ω)) (fun ω' => ζ ω' - T ω') ω with hcode
  have hcodeM : ∀ φ : RState nL nR → ℝ, Continuous φ → Measurable[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] (code φ) := by
    intro φ hφ
    rw [measurable_pi_iff' _]; intro n
    rw [measurable_pi_iff' _]; intro k
    by_cases hd : dyad n k = 0
    · have e : (fun ω => code φ ω n k) = fun ω => φ (restartTuple W VL VR Bv ζ T 0 ω) := by
        funext ω; simp only [hcode, killedCode, hd, ↓reduceIte]
      rw [e]
      exact (hφ.measurable.comp hR0).mono hTM le_rfl
    · have e : (fun ω => code φ ω n k) = fun ω => if ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω then
          (if ω ∈ G then φ (restartTuple W VL VR Bv ζ T (dyad n k) ω) else 0) else 0 := by
        funext ω; simp only [hcode, killedCode, hd, ↓reduceIte]
      rw [e]
      intro U hU
      have h1 := hcyl1 (dyad n k) (φ ⁻¹' U) (hφ.measurable hU)
      have h2 := hcyl1 (dyad n k) univ MeasurableSet.univ
      have e2 : (fun ω => if ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω then
          (if ω ∈ G then φ (restartTuple W VL VR Bv ζ T (dyad n k) ω) else 0) else 0) ⁻¹' U =
          (G ∩ {ω | ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω ∧
            restartTuple W VL VR Bv ζ T (dyad n k) ω ∈ φ ⁻¹' U}) ∪
          (if (0 : ℝ) ∈ U then (G ∩ {ω | ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω ∧
            restartTuple W VL VR Bv ζ T (dyad n k) ω ∈ (univ : Set (RState nL nR))})ᶜ else ∅) := by
        ext ω
        by_cases hq : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω <;> by_cases hω : ω ∈ G <;>
          by_cases h0 : (0 : ℝ) ∈ U <;> simp [hq, hω, h0]
      rw [e2]
      refine h𝒞M _ (h1.union ?_)
      split_ifs
      · exact h2.compl
      · exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom 𝒞)
  have hdec : ∀ φ : RState nL nR → ℝ, Continuous φ → ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω - T ω →
      dec (code φ ω) s = φ (restartTuple W VL VR Bv ζ T s ω) := by
    intro φ hφ ω hω s hs
    obtain ⟨hp, hTζ, hBv⟩ := hG ω hω
    have hc : ContinuousOn (fun q => (fun q ω' => if ω' ∈ G then φ (restartTuple W VL VR Bv ζ T q ω')
        else 0) q ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω - T ω} := by
      simp only [hω, ↓reduceIte]
      exact hφ.comp_continuousOn (continuousOn_restartTuple hp hTζ hBv (hBvc ω))
    have := dec_killedCode (X := fun q ω' => if ω' ∈ G then φ (restartTuple W VL VR Bv ζ T q ω') else 0)
      (x₀ := φ (restartTuple W VL VR Bv ζ T 0 ω)) (ζ := fun ω' => ζ ω' - T ω') (ω := ω)
      (by simp only [hω, ↓reduceIte]) hc hs
    simpa only [hω, ↓reduceIte] using this
  -- the decoded driving state at `r`
  refine iSup_le fun t => ?_
  have hD : drivingFiltration P hX t ≤ killedDrivingFiltration hX (t + 1) ⊔ Ito.nullSets P := by
    show usualAugmentation (killedDrivingFiltration hX) P t ≤ _
    rw [Ito.usualAugmentation_apply]
    exact (iInf₂_le (t + 1) (lt_add_one t)).trans (le_of_eq (Ito.nullAugmented_apply _ _ _))
  refine hD.trans (sup_le ?_ (MeasurableSpace.generateFrom_le fun N hN => hnullM N hN.1 hN.2))
  show killedDrivingSigma W VL VR ζ (t + 1) ≤ (hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨r, -, A', hA', rfl⟩
  set E := {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A'} with hE
  have hEd : MeasurableSet[drivingFiltration P hX r] E := Ito.le_usualAugmentation _ _ r _
    (MeasurableSpace.measurableSet_generateFrom ⟨r, le_rfl, A', hA', rfl⟩)
  have hEm : MeasurableSet E := (drivingFiltration P hX).le r _ hEd
  -- before `T`
  have hc := isStoppingTime_const (drivingFiltration P hX) r
  have hE1 : MeasurableSet[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] (E ∩ {ω | ((r : ℝ≥0) : WithTop ℝ≥0) ≤ (T ω : WithTop ℝ≥0)}) := by
    have := IsStoppingTime.measurableSet_inter_le hc hT E
      (by rw [IsStoppingTime.measurableSpace_const]; exact hEd)
    exact hTM _ (IsStoppingTime.measurableSpace_mono (hc.min hT) hT (fun ω => min_le_right _ _) _ this)
  -- after `T`
  set s : Ω → ℝ≥0 := fun ω => r - T ω with hs
  have hsM : Measurable[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] s := (measurable_const.sub hTm).mono hTM le_rfl
  set Wp : Ω → ℝ := fun ω => progVersion ζ W (T ω) ω with hWp
  have hWpM : Measurable[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] Wp :=
    (measurable_eval_stop (isStronglyProgressive_progVersion hWd) hT).mono hTM le_rfl
  have hdecM : ∀ φ : RState nL nR → ℝ, Continuous φ → Measurable[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] fun ω => dec (code φ ω) (s ω) :=
    fun φ hφ => measurable_dec.comp ((hcodeM φ hφ).prodMk hsM)
  have cL : ∀ i, Continuous fun x : RState nL nR => x.2.1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have cR : ∀ j, Continuous fun x : RState nL nR => x.2.2.1 j := fun j =>
    (continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
  set Φ : Ω → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    (Wp ω + dec (code (fun x => x.1) ω) (s ω), fun i => Wp ω + dec (code (fun x => x.2.1 i) ω) (s ω),
      fun j => Wp ω + dec (code (fun x => x.2.2.1 j) ω) (s ω)) with hΦ
  have hΦM : Measurable[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] Φ :=
    (hWpM.add (hdecM _ continuous_fst)).prodMk (((measurable_pi_iff' _).2 fun i => hWpM.add (hdecM _ (cL i))).prodMk
      ((measurable_pi_iff' _).2 fun j => hWpM.add (hdecM _ (cR j))))
  set Aliv : Set Ω := ⋃ q : ℚ, {ω | ((s ω : ℝ≥0) : ℝ≥0∞) < ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)} ∩
    (G ∩ {ω | ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω ∧
      restartTuple W VL VR Bv ζ T (Real.toNNReal q) ω ∈ (univ : Set (RState nL nR))}) with hAliv
  have hAlivM : MeasurableSet[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] Aliv := MeasurableSet.iUnion fun q =>
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp hsM) measurable_const).inter
      (h𝒞M _ (hcyl1 _ univ MeasurableSet.univ))
  set S : Set Ω := G ∩ {ω | T ω < r} ∩ Aliv ∩ Φ ⁻¹' A' with hSdef
  have hSM : MeasurableSet[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] S :=
    (((hTM _ hGT).inter (hTM _ (measurableSet_lt hTm measurable_const))).inter hAlivM).inter (hΦM hA')
  have hES : ∀ ω ∈ G, (ω ∈ E ∧ T ω < r) ↔ ω ∈ S := by
    intro ω hω
    obtain ⟨hp, hTζ, hBv⟩ := hG ω hω
    have hsr : ∀ hTr : T ω < r, ((s ω : ℝ≥0) : ℝ≥0∞) + T ω = r := fun hTr => by
      rw [← ENNReal.coe_add, hs, tsub_add_cancel_of_le hTr.le]
    have halive : T ω < r → ((r : ℝ≥0∞) < ζ ω ↔ ω ∈ Aliv) := by
      intro hTr
      constructor
      · intro hr
        have hlt : ((s ω : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω := lt_tsub_iff_right.2 ((hsr hTr).symm ▸ hr)
        obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
        exact mem_iUnion.2 ⟨q, h1, hω, h2, mem_univ _⟩
      · intro hA
        obtain ⟨q, h1, -, h2, -⟩ := mem_iUnion.1 hA
        have := lt_tsub_iff_right.1 (h1.trans h2)
        rwa [hsr hTr] at this
    have hΦeq : T ω < r → (r : ℝ≥0∞) < ζ ω → Φ ω = (W r ω, fun i => VL i r ω, fun j => VR j r ω) := by
      intro hTr hr
      have hlt : ((s ω : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω := lt_tsub_iff_right.2 ((hsr hTr).symm ▸ hr)
      have hTs : T ω + s ω = r := add_tsub_cancel_of_le hTr.le
      have hraw := restartTuple_eq_raw hp hTζ hBv hlt
      obtain ⟨b1, -, -⟩ := restart_values hp hTζ
      simp only [hΦ, hdec _ continuous_fst ω hω _ hlt, hdec _ (cL _) ω hω _ hlt, hdec _ (cR _) ω hω _ hlt,
        hraw, hWp, b1, hTs, add_sub_cancel]
    constructor
    · rintro ⟨⟨hr, hX'⟩, hTr⟩
      refine ⟨⟨⟨hω, hTr⟩, (halive hTr).1 hr⟩, ?_⟩
      show Φ ω ∈ A'
      rw [hΦeq hTr hr]; exact hX'
    · rintro ⟨⟨⟨-, hTr⟩, hA⟩, hΦA⟩
      have hr := (halive hTr).2 hA
      have hΦA' : Φ ω ∈ A' := hΦA
      rw [hΦeq hTr hr] at hΦA'
      exact ⟨⟨hr, hΦA'⟩, hTr⟩
  have hE2 : MeasurableSet[(hT.measurableSpace ⊔ MeasurableSpace.generateFrom 𝒞)] (E ∩ {ω | T ω < r}) := by
    refine measurableSet_of_ae_eq hMle hnullM (hEm.inter (measurableSet_lt hTm' measurable_const)) hSM ?_
    filter_upwards [hGae] with ω hω
    exact propext (hES ω hω)
  have e : E = (E ∩ {ω | ((r : ℝ≥0) : WithTop ℝ≥0) ≤ (T ω : WithTop ℝ≥0)}) ∪ (E ∩ {ω | T ω < r}) := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
    constructor
    · intro h
      rcases le_or_gt r (T ω) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  rw [e]
  exact hE1.union hE2

end Gen

/-! ### (WF7a) for the frozen coupling -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {m 𝓕' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

open Sec2 Sec2.Restart Sec2.Assembly LQGMetric QuantumZipper

omit [IsProbabilityMeasure P] in
/-- An indicator whose integrals over the sets of `m` are given by an `m`-measurable density has that density as
conditional expectation. -/
theorem condExp_indicator_eq_toReal [IsFiniteMeasure P] (hm : m ≤ mΩ) {E : Set Ω}
    (hE : MeasurableSet E) {g : Ω → ℝ≥0∞} (hg : Measurable[m] g)
    (hEg : ∀ A, MeasurableSet[m] A → P (A ∩ E) = ∫⁻ ω in A, g ω ∂P) :
    P[E.indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P] fun ω => (g ω).toReal := by
  have hgm : Measurable g := hg.mono hm le_rfl
  have htot : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    have := hEg univ MeasurableSet.univ
    rw [Measure.restrict_univ, univ_inter] at this
    rw [← this]; exact measure_ne_top P E
  have hgi : Integrable (fun ω => (g ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hgm.aemeasurable htot
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hE)
    (fun _ _ _ => hgi.integrableOn) (fun A hA _ => ?_)
    (hg.ennreal_toReal.stronglyMeasurable.aestronglyMeasurable)).symm
  rw [integral_toReal hgm.aemeasurable.restrict (ae_restrict_of_ae (ae_lt_top hgm htot)), ← hEg A hA,
    setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

/-- **(WF7a): later driving information does not change a germ field law** (follow-up note C.2, "conditioning
(WF7a) again gives `E[Y | 𝓕_τ] = E[Y | H_τ]`"; Aux. lemma 47). For the frozen coupling, a driving stop `T < ζ`
(positive, or a separated force word), a bounded `Y` measurable for the germ `Γ(𝓕_T, K_T)`, and every σ-algebra
`𝓕'` between `𝓕_T` and the whole driving σ-algebra `⋁_t 𝓕_t` (e.g. `𝓕_τ` for a driving stop `τ ≥ T`):
`E[Y | 𝓕'] = E[Y | 𝓕_T]`. -/
theorem condExp_histGerm_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {AT : Ω → Set ℂ} (hAT : Measurable[mΩ, hittingSigma] AT)
    (hATK : ∀ᵐ ω ∂P, AT ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (T ω : ℝ))
    {Y : Ω → ℝ} (hY : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)] Y) {c : ℝ}
    (hYb : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ c) (h1 : hT.measurableSpace ≤ 𝓕')
    (h2 : 𝓕' ≤ ⨆ t, drivingFiltration P hX t) :
    P[Y | 𝓕'] =ᵐ[P] P[Y | hT.measurableSpace] := by
  have hE := hC.1
  obtain ⟨Bv, hBvm, hBvc, -, -, hBvae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧ (T ω : ℝ≥0∞) < ζ ω ∧ ∀ t, Bv t ω = B t ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hE.2.2.2.2, hTζ, hBvae] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h'; exact hω (subset_toMeasurable _ _ h')
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set 𝒞 := restartCylSys W VL VR Bv ζ T G with h𝒞
  have hle : hT.measurableSpace ≤ histGerm hT.measurableSpace AT (centredField h u₀) := le_histGerm _ _
  have hgle : histGerm hT.measurableSpace AT (centredField h u₀) ≤ mΩ :=
    histGerm_le hT.measurableSpace_le hAT (measurable_centredField hC.2.1 u₀)
  have h𝒞m : ∀ C ∈ 𝒞, MeasurableSet C := by
    rintro C (rfl | ⟨n, ts, K, hK, rfl⟩)
    · exact MeasurableSet.univ
    · exact hGm.inter (measurableSet_restartCyl hX hT hBvc hBvm n ts hK)
  have hlaw : ∀ C ∈ 𝒞, P[C.indicator (fun _ => (1 : ℝ)) | histGerm hT.measurableSpace AT (centredField h u₀)]
      =ᵐ[P] P[C.indicator (fun _ => (1 : ℝ)) | hT.measurableSpace] := by
    rintro C (rfl | ⟨n, ts, K, hK, rfl⟩)
    · simp only [indicator_univ]
      rw [condExp_const hgle, condExp_const hT.measurableSpace_le]
    · obtain ⟨g, hgT, -, hgA⟩ := exists_restart_germ hC hκ hu₀ hX hT hTζ hT0 hAT hATK ts hK
      have hEm : MeasurableSet (G ∩ restartCyl W VL VR Bv ζ T n ts K) :=
        h𝒞m _ (inter_restartCyl_mem n ts hK)
      have hid : ∀ A, MeasurableSet[histGerm hT.measurableSpace AT (centredField h u₀)] A →
          P (A ∩ (G ∩ restartCyl W VL VR Bv ζ T n ts K)) = ∫⁻ ω in A, g ω ∂P := by
        intro A hA
        rw [← hgA A hA]
        refine measure_congr ?_
        filter_upwards [hGae] with ω hω
        obtain ⟨hp, hTζω, hBv⟩ := hGgood ω hω
        apply propext
        simp only [mem_inter_iff, restartCyl, mem_ofPred_eq, hω, true_and]
        refine and_congr_right fun _ => forall_congr' fun j => and_congr_right fun hlt => ?_
        rw [restartTuple_eq_raw hp hTζω hBv hlt]
      exact (condExp_indicator_eq_toReal hgle hEm (hgT.mono hle le_rfl) hid).trans
        (condExp_indicator_eq_toReal hT.measurableSpace_le hEm hgT fun A hA => hid A (hle A hA)).symm
  exact condExp_eq_of_le_sup_generateFrom hle hgle h1
    (h2.trans (iSup_driving_le_sup_restartCylSys hX hT hBvc hBvm hGm hGc hGgood))
    isPiSystem_restartCylSys univ_mem_restartCylSys h𝒞m hY hYb hlaw

/-- **(WF7a), complex form** (the form consumed by the finite-batch pasting `Sec7.condExp_prod_eq_prod_of_batches`):
for a bounded complex `Z` measurable for the germ `Γ(𝓕_T, K_T)` and `𝓕_T ≤ 𝓕' ≤ ⋁_t 𝓕_t`, `E[Z | 𝓕'] = E[Z | 𝓕_T]`
(real and imaginary parts commute with conditional expectation). -/
theorem condExp_histGerm_eq_complex (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {AT : Ω → Set ℂ} (hAT : Measurable[mΩ, hittingSigma] AT)
    (hATK : ∀ᵐ ω ∂P, AT ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (T ω : ℝ))
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)] Z) {c : ℝ}
    (hZb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ c) (h1 : hT.measurableSpace ≤ 𝓕')
    (h2 : 𝓕' ≤ ⨆ t, drivingFiltration P hX t) :
    P[Z | 𝓕'] =ᵐ[P] P[Z | hT.measurableSpace] := by
  have hgle : histGerm hT.measurableSpace AT (centredField h u₀) ≤ mΩ :=
    histGerm_le hT.measurableSpace_le hAT (measurable_centredField hC.2.1 u₀)
  have hZi : Integrable Z P := Integrable.of_bound (hZ.mono hgle).aestronglyMeasurable c hZb
  have hpart : ∀ L : ℂ →L[ℝ] ℝ, P[L ∘ Z | 𝓕'] =ᵐ[P] P[L ∘ Z | hT.measurableSpace] := fun L =>
    condExp_histGerm_eq hC hκ hu₀ hX hT hTζ hT0 hAT hATK (L.continuous.comp_stronglyMeasurable hZ)
      (c := ‖L‖ * c) (hZb.mono fun ω hω => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hω (norm_nonneg _)))
      h1 h2
  filter_upwards [Complex.reCLM.comp_condExp_comm (m := 𝓕') hZi,
    Complex.imCLM.comp_condExp_comm (m := 𝓕') hZi,
    Complex.reCLM.comp_condExp_comm (m := hT.measurableSpace) hZi,
    Complex.imCLM.comp_condExp_comm (m := hT.measurableSpace) hZi, hpart Complex.reCLM,
    hpart Complex.imCLM] with ω e1 e2 e3 e4 e5 e6
  apply Complex.ext
  · have a1 : (P[Z | 𝓕'] ω).re = P[Complex.reCLM ∘ Z | 𝓕'] ω := e1
    have a3 : (P[Z | hT.measurableSpace] ω).re = P[Complex.reCLM ∘ Z | hT.measurableSpace] ω := e3
    rw [a1, a3, e5]
  · have a2 : (P[Z | 𝓕'] ω).im = P[Complex.imCLM ∘ Z | 𝓕'] ω := e2
    have a4 : (P[Z | hT.measurableSpace] ω).im = P[Complex.imCLM ∘ Z | hT.measurableSpace] ω := e4
    rw [a2, a4, e6]

end Coupling

end WholeField

end InteractingSLE
