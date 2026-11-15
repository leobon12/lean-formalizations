/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1DualComap
import InteractingSLE.Spec.Sec7.LocalExtNRef
import InteractingSLE.Spec.Sec2.Assembly3Entr

/-!
# The killed record of an evolution at rational times, and the uniqueness of its law

Packet PROVE-ZHAN-A1DUAL, step (a) of PROVE-ZHAN-GT4-A2X's "What remains" 1 (the glue over a given large curve needs
a record of the large curve whose law is the same for every evolution of the word). The record is the killed driving
state at the nonnegative rational times, `inl (W_q, VL_q, VR_q, B_q)` while `q < ζ` and `inr ()` afterwards
(`killedRec`), in the countable product `ℚ≥0 → KState nL nR ⊕ Unit`.

* `measurable_killedRec`: the record is measurable for every evolution (adaptedness before the lifetime; the values
  after the lifetime, which the evolution does not constrain, are not read);
* **`map_killedRec_eq`**: two integrated evolutions of the same ordered word have records with the same law. The
  cylinders `{f | ∀ j, f (q j) ∈ inl '' A j}` form a π-system generating the product σ-algebra, and on them the two laws
  agree by the frozen uniqueness in law of Theorem 2.2
  (`IsIntegratedSLEEvolution.measure_killedState_eq_assembled`, the provider of the sealed anchor);
* the real decoders `recAlive`, `recW`, `recVL`, `recVR`, `recB` and their values on records;
* `eq_of_forall_nnrat_lt_iff`, `eqOn_of_nnrat`: the lifetime and the paths before it are read off the record at
  rational times (the latter for paths continuous before the lifetime).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Dual

/-! ### The record -/

/-- The driving state at one time: driver, left marks, right marks, Brownian motion. -/
abbrev KState (nL nR : ℕ) : Type := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

/-- The record space: the killed state at every nonnegative rational time. -/
abbrev RecE (nL nR : ℕ) : Type := ℚ≥0 → KState nL nR ⊕ Unit

section Record

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- **The killed record at rational times**: the state while `q < ζ`, `inr ()` afterwards. -/
def killedRec (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : RecE nL nR := fun q =>
  if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then Sum.inl (W q ω, fun i => VL i q ω, fun j => VR j q ω, B q ω) else Sum.inr ()

/-- A process killed at `ζ` (value `0` from `ζ` on). -/
def killAt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := if (t : ℝ≥0∞) < ζ ω then X t ω else 0

variable {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

theorem measurableSet_lt_lifetime {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω} := by
  have h := 𝓕.le t _ (hX t univ MeasurableSet.univ)
  simpa only [mem_univ, and_true] using h

/-- A process adapted before the lifetime, killed at the lifetime, is measurable at each time. -/
theorem measurable_killAt {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable (killAt ζ X t) := by
  intro A hA
  have e : killAt ζ X t ⁻¹' A =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
    ext ω
    simp only [killAt, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h]
  rw [e]
  exact (𝓕.le t _ (hX t A hA)).union ((measurableSet_lt_lifetime hX t).compl.inter (MeasurableSet.const _))

/-- **The killed record of an evolution is measurable.** -/
theorem measurable_killedRec {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hB : ∀ t, Measurable (B t)) :
    Measurable (killedRec W VL VR B ζ) := by
  refine measurable_pi_iff.2 fun q => ?_
  have e : (fun ω => killedRec W VL VR B ζ ω q) = fun ω =>
      if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then Sum.inl (killAt ζ W q ω, fun i => killAt ζ (VL i) q ω,
        fun j => killAt ζ (VR j) q ω, B q ω) else Sum.inr () := by
    funext ω
    by_cases h : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω
    · simp only [killedRec, killAt, h, ite_true]
    · simp only [killedRec, h, ite_false]
  rw [e]
  refine Measurable.ite (measurableSet_lt_lifetime hW q) (measurable_inl.comp ?_) measurable_const
  exact (measurable_killAt hW q).prodMk ((measurable_pi_iff.2 fun i => measurable_killAt (hVL i) q).prodMk
    ((measurable_pi_iff.2 fun j => measurable_killAt (hVR j) q).prodMk (hB q)))

theorem killedRec_mem_inl_iff {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (ω : Ω) (q : ℚ≥0) (A : Set (KState nL nR)) :
    killedRec W VL VR B ζ ω q ∈ Sum.inl '' A ↔
      ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (W q ω, fun i => VL i q ω, fun j => VR j q ω, B q ω) ∈ A := by
  by_cases h : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω
  · simp only [killedRec, h, ite_true, true_and, mem_image, Sum.inl.injEq, exists_eq_right]
  · simp only [killedRec, h, ite_false, false_and, mem_image, reduceCtorEq, and_false, exists_false]

end Record

/-! ### The law of the record -/

section Law

variable {nL nR : ℕ}

/-- The cylinders of the record space. -/
def recCyl (nL nR : ℕ) : Set (Set (RecE nL nR)) :=
  {S | ∃ (n : ℕ) (q : Fin n → ℚ≥0) (A : Fin n → Set (KState nL nR)), (∀ j, MeasurableSet (A j)) ∧
    S = {f | ∀ j, f (q j) ∈ Sum.inl '' A j}}

theorem mem_recCyl {n : ℕ} (q : Fin n → ℚ≥0) {A : Fin n → Set (KState nL nR)} (hA : ∀ j, MeasurableSet (A j)) :
    {f : RecE nL nR | ∀ j, f (q j) ∈ Sum.inl '' A j} ∈ recCyl nL nR :=
  ⟨n, q, A, hA, rfl⟩

theorem isPiSystem_recCyl : IsPiSystem (recCyl nL nR) := by
  rintro _ ⟨n, q, A, hA, rfl⟩ _ ⟨m, q', A', hA', rfl⟩ -
  have hA'' : ∀ l, MeasurableSet (Fin.append A A' l) := fun l => by
    refine Fin.addCases (fun j => ?_) (fun k => ?_) l
    · rw [Fin.append_left]; exact hA j
    · rw [Fin.append_right]; exact hA' k
  convert mem_recCyl (Fin.append q q') hA'' using 1
  ext f
  simp only [mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left, Fin.append_right]

theorem generateFrom_recCyl : (MeasurableSpace.pi : MeasurableSpace (RecE nL nR)) =
    MeasurableSpace.generateFrom (recCyl nL nR) := by
  apply le_antisymm
  · refine iSup_le fun q => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro C hC
    have hl : MeasurableSet (Sum.inl ⁻¹' C : Set (KState nL nR)) := measurable_inl hC
    have e : (fun f : RecE nL nR => f q) ⁻¹' C = {f | ∀ j : Fin 1, f ((fun _ => q) j) ∈
        Sum.inl '' (fun _ => Sum.inl ⁻¹' C) j} ∪ ({_f | Sum.inr () ∈ C} ∩
          {f | ∀ j : Fin 1, f ((fun _ => q) j) ∈ Sum.inl '' (fun _ => (univ : Set (KState nL nR))) j}ᶜ) := by
      ext f
      simp only [mem_preimage, Fin.forall_fin_one, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff,
        mem_image, mem_univ, true_and]
      rcases f q with s | u
      · simp
      · cases u; simp
    show MeasurableSet[MeasurableSpace.generateFrom (recCyl nL nR)] ((fun f : RecE nL nR => f q) ⁻¹' C)
    rw [e]
    refine MeasurableSet.union (MeasurableSpace.measurableSet_generateFrom
      (mem_recCyl (fun _ => q) fun _ => hl)) (MeasurableSet.inter (MeasurableSet.const _) ?_)
    exact (MeasurableSpace.measurableSet_generateFrom
      (mem_recCyl (fun _ => q) fun _ => MeasurableSet.univ)).compl
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, q, A, hA, rfl⟩
    have e : {f : RecE nL nR | ∀ j, f (q j) ∈ Sum.inl '' A j} = ⋂ j, (fun f : RecE nL nR => f (q j)) ⁻¹'
        (Sum.inl '' A j) := by
      ext f; simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [e]
    exact MeasurableSet.iInter fun j => measurable_pi_apply (q j) (measurableSet_inl_image.2 (hA j))

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The law of the killed record is the same for every integrated evolution of an ordered word** (Theorem 2.2's
uniqueness in law, `measure_killedState_eq_assembled`, on the cylinders). -/
theorem map_killedRec_eq (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    P₁.map (killedRec W₁ VL₁ VR₁ B₁ ζ₁) = P₂.map (killedRec W₂ VL₂ VR₂ B₂ ζ₂) := by
  have hR₁ : Measurable (killedRec W₁ VL₁ VR₁ B₁ ζ₁) := measurable_killedRec h₁.2.1 h₁.2.2.1 h₁.2.2.2.1
    fun t => (h₁.1.2.1 t).mono (𝓕₁.le t) le_rfl
  have hR₂ : Measurable (killedRec W₂ VL₂ VR₂ B₂ ζ₂) := measurable_killedRec h₂.2.1 h₂.2.2.1 h₂.2.2.2.1
    fun t => (h₂.1.2.1 t).mono (𝓕₂.le t) le_rfl
  refine ext_of_generate_finite (recCyl nL nR) generateFrom_recCyl isPiSystem_recCyl ?_ ?_
  · rintro _ ⟨n, q, A, hA, rfl⟩
    have hm : MeasurableSet {f : RecE nL nR | ∀ j, f (q j) ∈ Sum.inl '' A j} :=
      generateFrom_recCyl (nL := nL) (nR := nR) ▸ MeasurableSpace.measurableSet_generateFrom (mem_recCyl q hA)
    rw [Measure.map_apply hR₁ hm, Measure.map_apply hR₂ hm]
    have e₁ : killedRec W₁ VL₁ VR₁ B₁ ζ₁ ⁻¹' {f | ∀ j, f (q j) ∈ Sum.inl '' A j} =
        {ω | ∀ j, (((q j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ₁ ω ∧ (W₁ (q j) ω, (fun i => VL₁ i (q j) ω),
          (fun i => VR₁ i (q j) ω), B₁ (q j) ω) ∈ A j} := by
      ext ω; simp only [mem_preimage, mem_ofPred_eq, killedRec_mem_inl_iff]
    have e₂ : killedRec W₂ VL₂ VR₂ B₂ ζ₂ ⁻¹' {f | ∀ j, f (q j) ∈ Sum.inl '' A j} =
        {ω | ∀ j, (((q j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ₂ ω ∧ (W₂ (q j) ω, (fun i => VL₂ i (q j) ω),
          (fun i => VR₂ i (q j) ω), B₂ (q j) ω) ∈ A j} := by
      ext ω; simp only [mem_preimage, mem_ofPred_eq, killedRec_mem_inl_iff]
    rw [e₁, e₂]
    exact IsIntegratedSLEEvolution.measure_killedState_eq_assembled ha hF h₁ h₂ (ts := fun j => (q j : ℝ≥0)) hA
  · rw [Measure.map_apply hR₁ MeasurableSet.univ, Measure.map_apply hR₂ MeasurableSet.univ]
    simp

end Law

/-! ### Reading the record -/

section Decode

variable {nL nR : ℕ}

/-- The alive flag of the record at `q` (`1` before the lifetime). -/
def recAlive (q : ℚ≥0) (f : RecE nL nR) : ℝ := Sum.elim (fun _ => 1) (fun _ => 0) (f q)

/-- The driver read off the record at `q` (`0` after the lifetime). -/
def recW (q : ℚ≥0) (f : RecE nL nR) : ℝ := Sum.elim (fun s => s.1) (fun _ => 0) (f q)

/-- A left mark read off the record at `q`. -/
def recVL (i : Fin nL) (q : ℚ≥0) (f : RecE nL nR) : ℝ := Sum.elim (fun s => s.2.1 i) (fun _ => 0) (f q)

/-- A right mark read off the record at `q`. -/
def recVR (j : Fin nR) (q : ℚ≥0) (f : RecE nL nR) : ℝ := Sum.elim (fun s => s.2.2.1 j) (fun _ => 0) (f q)

/-- The Brownian motion read off the record at `q`. -/
def recB (q : ℚ≥0) (f : RecE nL nR) : ℝ := Sum.elim (fun s => s.2.2.2) (fun _ => 0) (f q)

theorem measurable_recAlive (q : ℚ≥0) : Measurable (recAlive (nL := nL) (nR := nR) q) :=
  (measurable_const.sumElim measurable_const).comp (measurable_pi_apply q)

theorem measurable_recW (q : ℚ≥0) : Measurable (recW (nL := nL) (nR := nR) q) :=
  (measurable_fst.sumElim measurable_const).comp (measurable_pi_apply q)

theorem measurable_recVL (i : Fin nL) (q : ℚ≥0) : Measurable (recVL (nR := nR) i q) :=
  (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).sumElim measurable_const).comp
    (measurable_pi_apply q)

theorem measurable_recVR (j : Fin nR) (q : ℚ≥0) : Measurable (recVR (nL := nL) j q) :=
  (((measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))).sumElim
    measurable_const).comp (measurable_pi_apply q)

theorem measurable_recB (q : ℚ≥0) : Measurable (recB (nL := nL) (nR := nR) q) :=
  ((measurable_snd.comp (measurable_snd.comp measurable_snd)).sumElim measurable_const).comp
    (measurable_pi_apply q)

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem recAlive_killedRec (ω : Ω) (q : ℚ≥0) :
    recAlive q (killedRec W VL VR B ζ ω) = if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then 1 else 0 := by
  by_cases h : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω <;> simp [recAlive, killedRec, h]

/-- Before the lifetime the record reads the state. -/
theorem killedRec_of_lt (ω : Ω) {q : ℚ≥0} (h : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    recW q (killedRec W VL VR B ζ ω) = W q ω ∧ (∀ i, recVL i q (killedRec W VL VR B ζ ω) = VL i q ω) ∧
      (∀ j, recVR j q (killedRec W VL VR B ζ ω) = VR j q ω) ∧ recB q (killedRec W VL VR B ζ ω) = B q ω := by
  simp [recW, recVL, recVR, recB, killedRec, h]

/-- The lifetime is determined by the rational times before it. -/
theorem eq_of_forall_nnrat_lt_iff {c d : ℝ≥0∞} (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < c ↔ ((q : ℝ≥0) : ℝ≥0∞) < d) :
    c = d := by
  have key : ∀ {c d : ℝ≥0∞}, (∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < c ↔ ((q : ℝ≥0) : ℝ≥0∞) < d) → c ≤ d := by
    intro c d h
    by_contra hcd
    rw [not_le] at hcd
    obtain ⟨r, hdr, hrc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcd
    obtain ⟨r', hdr', hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hdr
    obtain ⟨_, ⟨q, rfl⟩, hq1, hq2⟩ := LocalExt.dense_range_coe_nnrat.exists_between (ENNReal.coe_lt_coe.1 hr'r)
    have h1 : ((q : ℝ≥0) : ℝ≥0∞) < c := (ENNReal.coe_lt_coe.2 hq2).trans hrc
    have h2 : d < ((q : ℝ≥0) : ℝ≥0∞) := hdr'.trans (ENNReal.coe_lt_coe.2 hq1)
    exact absurd ((h q).1 h1) (not_lt.2 h2.le)
  exact le_antisymm (key h) (key fun q => (h q).symm)

/-- **Two paths continuous before `c` that agree at the rational times before `c` agree before `c`.** -/
theorem eqOn_of_nnrat {f g : ℝ≥0 → ℝ} {c : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < c})
    (hg : ContinuousOn g {t | (t : ℝ≥0∞) < c}) (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < c → f q = g q) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < c → f t = g t := by
  have hU : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < c} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hsub := LocalExt.dense_range_coe_nnrat.open_subset_closure_inter hU
  have hE : EqOn f g ({t : ℝ≥0 | (t : ℝ≥0∞) < c} ∩ range ((↑) : ℚ≥0 → ℝ≥0)) := by
    rintro _ ⟨ht, q, rfl⟩
    exact h q ht
  exact fun t ht => hE.of_subset_closure hf hg inter_subset_left hsub ht

end Decode

end InteractingSLE.ZhanGT4.A1Dual
