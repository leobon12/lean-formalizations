/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1PatchInput
import InteractingSLE.Spec.ZhanGT4.A1LawStop

/-!
# A.1's records modulo null sets: the finite patches for arbitrary stopped σ-algebras

Packet PROVE-A1-PATCH (R80). Source: Astra, *Follow-up proofs* §A.1.5 (`ig1_followup_proofs.txt` L411–L413): "Enlarge
each path coordinate by the stopped path and countable generators of the actual augmented stopped sigma-algebra for
every enclosure in the enumeration. These are Borel functions of that marginal path, modulo its fixed null sets";
*Follow-up 4* §2.5 item 4 (L801–L806): "A monotone class extends its identities from the countable generators to the
completed stopped sigma-algebras".

The countable patch of PROVE-A1-LAW (`A1Law.exists_coupling_of_finite_patches`) transports (1.7) only on countably
generated record σ-algebras. Here:

* `exists_countablyGenerated_ae`: on a countably generated space with a finite measure `P`, every sub-σ-algebra `𝓖` has
  a countably generated sub-σ-algebra `𝓖₀ ≤ 𝓖` with every `𝓖`-set `P`-a.e. equal to a `𝓖₀`-set (a countable
  `P`-dense family of `𝓖`-sets, chosen near a countable dense family of the whole space; Borel–Cantelli);
* **`RectDens.of_ae`**: (1.7) on `𝓐₀ ⊗ 𝓑₀` gives (1.7) on `𝓐 ⊗ 𝓑` when `𝓐 ⊆ 𝓐₀`, `𝓑 ⊆ 𝓑₀` modulo null sets, for
  any coupling of `P₁` and `P₂` (rectangles differ by null sets, then Dynkin);
* `FieldPatchSigmaInput`, **`patchInput_of_fieldPatchSigmaInput`**: input (I1) of `PatchInput` from the field data
  of `IsRectField` for ANY filtrations (e.g. usual augmentations), with (I2) stated on the stopped σ-algebras
  themselves — no records are needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal symmDiff

namespace InteractingSLE.ZhanGT4.A1Patch

open A1Law

/-! ### Countable generation modulo null sets -/

section CountGen

/-- **A sub-σ-algebra of a countably generated space is countably generated modulo null sets**: for a finite measure
`P`, every sub-σ-algebra `𝓖` contains a countably generated `𝓖₀` such that every `𝓖`-set is `P`-a.e. equal to a
`𝓖₀`-set. -/
theorem exists_countablyGenerated_ae {X : Type*} {𝓖 : MeasurableSpace X} [mX : MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (h𝓖 : 𝓖 ≤ mX) (P : Measure X) [IsFiniteMeasure P] :
    ∃ 𝓖₀ : MeasurableSpace X, 𝓖₀ ≤ 𝓖 ∧ @MeasurableSpace.CountablyGenerated X 𝓖₀ ∧
      ∀ A, MeasurableSet[𝓖] A → ∃ A₀, MeasurableSet[𝓖₀] A₀ ∧ A =ᵐ[P] A₀ := by
  classical
  obtain ⟨𝒜, h𝒜c, h𝒜⟩ := exists_countable_measureDense (μ := P)
  have : Countable 𝒜 := h𝒜c.to_subtype
  -- a `𝓖`-set within `1/(n+1)` of `a`, when one exists
  set G : 𝒜 × ℕ → Set X := fun p => if h : ∃ B, MeasurableSet[𝓖] B ∧
      P ((p.1 : Set X) ∆ B) < ENNReal.ofReal (1 / ((p.2 : ℝ) + 1)) then h.choose else ∅ with hGdef
  have hG𝓖 : ∀ p, MeasurableSet[𝓖] (G p) := fun p => by
    simp only [hGdef]
    split_ifs with h
    · exact h.choose_spec.1
    · exact @MeasurableSet.empty X 𝓖
  have hGP : ∀ p, (∃ B, MeasurableSet[𝓖] B ∧ P ((p.1 : Set X) ∆ B) < ENNReal.ofReal (1 / ((p.2 : ℝ) + 1))) →
      P ((p.1 : Set X) ∆ G p) < ENNReal.ofReal (1 / ((p.2 : ℝ) + 1)) := fun p h => by
    simp only [hGdef, dite_eq_left h]
    exact h.choose_spec.2
  have hG₀ : ∀ p, MeasurableSet[MeasurableSpace.generateFrom (range G)] (G p) := fun p =>
    MeasurableSpace.measurableSet_generateFrom ⟨p, rfl⟩
  refine ⟨MeasurableSpace.generateFrom (range G), MeasurableSpace.generateFrom_le fun _ ⟨p, hp⟩ => hp ▸ hG𝓖 p,
    @MeasurableSpace.CountablyGenerated.mk X (MeasurableSpace.generateFrom (range G))
      ⟨range G, countable_range G, rfl⟩, fun A hA => ?_⟩
  have hAm : MeasurableSet A := h𝓖 A hA
  -- approximation of `A` by the family `G` within `δ`
  have happ : ∀ δ : ℝ, 0 < δ → ∃ B, MeasurableSet[MeasurableSpace.generateFrom (range G)] B ∧
      P (A ∆ B) < ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hδ)
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨a, ha, haA⟩ := h𝒜.approx A hAm (measure_ne_top P A) _ hn0
    have hex : ∃ B, MeasurableSet[𝓖] B ∧ P ((a : Set X) ∆ B) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ⟨A, hA, by rw [symmDiff_comm]; exact haA⟩
    have h2 := hGP (⟨a, ha⟩, n) hex
    refine ⟨G (⟨a, ha⟩, n), hG₀ _, ?_⟩
    calc P (A ∆ G (⟨a, ha⟩, n)) ≤ P (A ∆ a) + P ((a : Set X) ∆ G (⟨a, ha⟩, n)) := measure_symmDiff_le _ _ _
      _ < ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := ENNReal.add_lt_add haA h2
      _ = ENNReal.ofReal (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)) := (ENNReal.ofReal_add hn0.le hn0.le).symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
  choose B hB hBP using fun j : ℕ => happ ((1 / 2) ^ j) (by positivity)
  refine ⟨limsup B atTop, ?_, ?_⟩
  · rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB i
  · -- Borel–Cantelli on the symmetric differences
    have hsum : ∑' j, P (A ∆ B j) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => (hBP j).le)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) summable_geometric_two]
      exact ENNReal.ofReal_ne_top
    have h0 := measure_limsup_atTop_eq_zero hsum
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) h0, measure_mono_null (fun x hx => ?_) h0⟩
    · obtain ⟨hxA, hxB⟩ := hx
      rw [mem_limsup_iff_frequently_mem] at hxB ⊢
      refine (Filter.not_frequently.1 hxB).frequently.mono fun j hj => ?_
      exact Or.inl ⟨hxA, hj⟩
    · obtain ⟨hxB, hxA⟩ := hx
      rw [mem_limsup_iff_frequently_mem] at hxB ⊢
      exact hxB.mono fun j hj => Or.inr ⟨hj, hxA⟩

end CountGen

/-! ### (1.7) modulo null sets -/

section Null

/-- Rectangles whose sides agree almost everywhere under the marginals agree almost everywhere under every measure
whose marginals are absolutely continuous with respect to them. -/
theorem prod_ae_eq_of_ae_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {P₁ : Measure X}
    {P₂ : Measure Y} {ν : Measure (X × Y)} (h₁ : ν.map Prod.fst ≪ P₁) (h₂ : ν.map Prod.snd ≪ P₂) {A A₀ : Set X}
    {B B₀ : Set Y} (hA : A =ᵐ[P₁] A₀) (hB : B =ᵐ[P₂] B₀) : (A ×ˢ B : Set (X × Y)) =ᵐ[ν] (A₀ ×ˢ B₀ : Set (X × Y)) := by
  have q₁ : Measure.QuasiMeasurePreserving Prod.fst ν P₁ := ⟨measurable_fst, h₁⟩
  have q₂ : Measure.QuasiMeasurePreserving Prod.snd ν P₂ := ⟨measurable_snd, h₂⟩
  rw [Set.prod_eq, Set.prod_eq]
  exact (q₁.preimage_ae_eq hA).inter (q₂.preimage_ae_eq hB)

/-- **(1.7) passes from generators modulo null sets to the full σ-algebras** (follow-up 4 §2.5 item 4: "A monotone
class extends its identities from the countable generators to the completed stopped sigma-algebras"): if every
`𝓐`-set is `P₁`-a.e. equal to an `𝓐₀`-set and every `𝓑`-set is `P₂`-a.e. equal to a `𝓑₀`-set, (1.7) on
`𝓐₀ ⊗ 𝓑₀` for a coupling `μ` of `P₁`, `P₂` gives (1.7) on `𝓐 ⊗ 𝓑`. -/
theorem RectDens.of_ae {X Y : Type*} {𝓐 𝓐₀ : MeasurableSpace X} {𝓑 𝓑₀ : MeasurableSpace Y} [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂] {μ : Measure (X × Y)}
    [IsFiniteMeasure μ] {D : X × Y → ℝ≥0∞} (hD : Measurable D) (h : RectDens 𝓐₀ 𝓑₀ P₁ P₂ μ D)
    (h𝓐₀ : 𝓐₀ ≤ mX) (h𝓑₀ : 𝓑₀ ≤ mY) (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (hμ₁ : μ.map Prod.fst = P₁)
    (hμ₂ : μ.map Prod.snd = P₂) (hA : ∀ A, MeasurableSet[𝓐] A → ∃ A₀, MeasurableSet[𝓐₀] A₀ ∧ A =ᵐ[P₁] A₀)
    (hB : ∀ B, MeasurableSet[𝓑] B → ∃ B₀, MeasurableSet[𝓑₀] B₀ ∧ B =ᵐ[P₂] B₀) :
    RectDens 𝓐 𝓑 P₁ P₂ μ D := by
  intro f hf
  refine A1Core.lintegral_eq_of_rect (P₁ := P₁) (P₂ := P₂) h𝓐 h𝓑 hD (fun A B hAm hBm => ?_) hf
  obtain ⟨A₀, hA₀, hAA⟩ := hA A hAm
  obtain ⟨B₀, hB₀, hBB⟩ := hB B hBm
  have e₁ := prod_ae_eq_of_ae_eq (ν := μ) (hμ₁ ▸ Measure.AbsolutelyContinuous.rfl)
    (hμ₂ ▸ Measure.AbsolutelyContinuous.rfl) hAA hBB
  have e₂ := prod_ae_eq_of_ae_eq (ν := P₁.prod P₂) (Measure.quasiMeasurePreserving_fst).absolutelyContinuous
    (Measure.quasiMeasurePreserving_snd).absolutelyContinuous hAA hBB
  rw [measure_congr e₁, rect_of_rectDens h𝓐₀ h𝓑₀ h A₀ B₀ hA₀ hB₀, setLIntegral_congr e₂]

end Null

/-! ### (I1) of `PatchInput` without records -/

section Sigma

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A.1's finite-patch input from a two-time field, on the stopped σ-algebras** (follow-up 4 §2.5 item 4,
§A.1.4–A.1.5): a sequence of protected rectangles `(S₁ m, S₂ m)` of one positive two-time field `N` with axis values
one (`IsRectField`, for any filtrations `𝓕₁`, `𝓕₂` — e.g. the usual augmentations), and the law input (I2) for every
coupling of `P₁`, `P₂` with (1.7) on the stopped σ-algebras `𝓕¹_{S₁ m} ⊗ 𝓕²_{S₂ m}`, density `N(S₁ m, S₂ m)`. No
coupling and no record is assumed: both are constructed (`patchInput_of_fieldPatchSigmaInput`). -/
def FieldPatchSigmaInput (P₁ : Measure X) (P₂ : Measure Y) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (N : X × Y → ℝ → ℝ → ℝ) (h : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) N),
    (∀ ω s t, 0 < N ω s t) ∧ (∀ ω t, N ω 0 t = 1) ∧ (∀ ω s, N ω s 0 = 1) ∧ IsFieldMeas N S₁ S₂ ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h m).stop₁.measurableSpace (h m).stop₂.measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (N ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- **(I1) of `PatchInput` from the field data on the stopped σ-algebras**: records generating the stopped σ-algebras
modulo null sets (`exists_countablyGenerated_ae`, `exists_record_comap_eq`) carry the staircase patches
(`exists_patches_of_rectField`), and (1.7) on them for a coupling of `P₁`, `P₂` extends to the stopped σ-algebras
(`RectDens.of_ae`), where (I2) applies. -/
theorem patchInput_of_fieldPatchSigmaInput [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X}
    {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {Law : Measure (X × Y) → Prop}
    (h : FieldPatchSigmaInput P₁ P₂ Law) : PatchInput P₁ P₂ Law := by
  obtain ⟨𝓕₁, 𝓕₂, S₁, S₂, N, hR, hpos, hax₁, hax₂, hmeas, hLaw⟩ := h
  choose 𝓐₀ h𝓐₀ hc𝓐 hA using fun m => exists_countablyGenerated_ae (hR m).stop₁.measurableSpace_le P₁
  choose 𝓑₀ h𝓑₀ hc𝓑 hB using fun m => exists_countablyGenerated_ae (hR m).stop₂.measurableSpace_le P₂
  choose f hf hfe using fun m => exists_record_comap_eq ((h𝓐₀ m).trans (hR m).stop₁.measurableSpace_le) (hc𝓐 m)
  choose g hg hge using fun m => exists_record_comap_eq ((h𝓑₀ m).trans (hR m).stop₂.measurableSpace_le) (hc𝓑 m)
  refine patchInput_of_fieldPatchInput ⟨fun _ => ℕ → Bool, fun _ => ℕ → Bool, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, f, g, 𝓕₁, 𝓕₂, S₁, S₂, N, hR, hpos,
    hax₁, hax₂, hmeas, hf, hg, fun m => (hfe m).le.trans (h𝓐₀ m), fun m => (hge m).le.trans (h𝓑₀ m),
    fun μ hμ hμ₁ hμ₂ hd => hLaw μ hμ hμ₁ hμ₂ fun m => ?_⟩
  have e₁ : recSigma f m = 𝓐₀ m := hfe m
  have e₂ : recSigma g m = 𝓑₀ m := hge m
  have hdm := hd m
  rw [e₁, e₂] at hdm
  exact RectDens.of_ae (measurable_rectDens hR hmeas m) hdm ((h𝓐₀ m).trans (hR m).stop₁.measurableSpace_le)
    ((h𝓑₀ m).trans (hR m).stop₂.measurableSpace_le) (hR m).stop₁.measurableSpace_le
    (hR m).stop₂.measurableSpace_le hμ₁ hμ₂ (hA m) (hB m)

end Sigma

/-! ### (1.7) at earlier stops of one curve -/

section Stop

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0} {N : X × Y → ℝ → ℝ → ℝ}

/-- **(1.7) at a stop of curve `2` before its exit** (follow-up 5 §1.3, "If `τ` is bounded by the large-curve protection
time, optional sampling gives the density `M(s, τ)`"): (1.7) on a protected rectangle at its exits gives (1.7) on
`𝓕¹_{S₁} ⊗ 𝓕²_σ` with density `N(S₁, σ)` for every stopping time `σ ≤ S₂` of curve `2` (A1-LAW's
`rectDens_stop_of_exit` with the row martingale `t ↦ N(S₁, t ∧ S₂)`). -/
theorem IsRectField.rectDens_stop_snd [IsFiniteMeasure P₁] [IsFiniteMeasure P₂] (h : IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ N)
    (hpos : ∀ ω s t, 0 < N ω s t) (hmeas : IsFieldMeas N (fun _ : Unit => S₁) (fun _ : Unit => S₂))
    {μ : Measure (X × Y)} [IsFiniteMeasure μ]
    (hexit : RectDens h.stop₁.measurableSpace h.stop₂.measurableSpace P₁ P₂ μ
      fun ω => ENNReal.ofReal (N ω (S₁ ω.1) (S₂ ω.2)))
    {σ : Y → ℝ≥0} (hσ : IsStoppingTime 𝓕₂ fun y => (σ y : WithTop ℝ≥0)) (hσS : ∀ y, σ y ≤ S₂ y) :
    RectDens h.stop₁.measurableSpace hσ.measurableSpace P₁ P₂ μ
      fun ω => ENNReal.ofReal (N ω (S₁ ω.1) (σ ω.2)) := by
  obtain ⟨U, -, hU⟩ := h.bdd
  have hD : Measurable fun ω : X × Y => ENNReal.ofReal (N ω (S₁ ω.1) (σ ω.2)) :=
    ENNReal.measurable_ofReal.comp (hmeas _ _ ((measurable_coe_of_isStoppingTime h.stop₁).comp measurable_fst)
      ((measurable_coe_of_isStoppingTime hσ).comp measurable_snd) (fun ω => (S₁ ω.1).coe_nonneg)
      (fun ω => (σ ω.2).coe_nonneg) fun ω => ⟨(), le_rfl, NNReal.coe_le_coe.2 (hσS ω.2)⟩)
  refine A1Law.rectDens_stop_of_exit (M := fun x (t : ℝ≥0) y => N (x, y) (S₁ x) (min (t : ℝ) (S₂ y)))
    h.stop₁.measurableSpace_le h.stop₂.measurableSpace_le (measurable_rectDens (fun _ : Unit => h) hmeas ()) hD
    hexit (ae_of_all _ fun x => h.row x _ (S₁ x).coe_nonneg le_rfl)
    (fun x y t => (h.row_cont x y _ (S₁ x).coe_nonneg le_rfl).continuousWithinAt) (fun x t y => (hpos _ _ _).le)
    hσ h.stop₂ (fun y => WithTop.coe_le_coe.2 (hσS y)) (T := U) (fun y => WithTop.coe_le_coe.2 (hU y))
    (fun x y => ?_) (fun x y => ?_) (hσ.measurableSpace_mono h.stop₂ fun y => WithTop.coe_le_coe.2 (hσS y))
  · simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe, min_self]
  · simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe, min_eq_left (NNReal.coe_le_coe.2 (hσS y))]

/-- **(1.7) at a stop of curve `1` before its exit** (the mirror, with the column martingale `s ↦ N(s ∧ S₁, S₂)`). -/
theorem IsRectField.rectDens_stop_fst [IsFiniteMeasure P₁] [IsFiniteMeasure P₂] (h : IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ N)
    (hpos : ∀ ω s t, 0 < N ω s t) (hmeas : IsFieldMeas N (fun _ : Unit => S₁) (fun _ : Unit => S₂))
    {μ : Measure (X × Y)} [IsFiniteMeasure μ]
    (hexit : RectDens h.stop₁.measurableSpace h.stop₂.measurableSpace P₁ P₂ μ
      fun ω => ENNReal.ofReal (N ω (S₁ ω.1) (S₂ ω.2)))
    {σ : X → ℝ≥0} (hσ : IsStoppingTime 𝓕₁ fun x => (σ x : WithTop ℝ≥0)) (hσS : ∀ x, σ x ≤ S₁ x) :
    RectDens hσ.measurableSpace h.stop₂.measurableSpace P₁ P₂ μ
      fun ω => ENNReal.ofReal (N ω (σ ω.1) (S₂ ω.2)) := by
  obtain ⟨U, hU, -⟩ := h.bdd
  have hD : Measurable fun ω : X × Y => ENNReal.ofReal (N ω (σ ω.1) (S₂ ω.2)) :=
    ENNReal.measurable_ofReal.comp (hmeas _ _ ((measurable_coe_of_isStoppingTime hσ).comp measurable_fst)
      ((measurable_coe_of_isStoppingTime h.stop₂).comp measurable_snd) (fun ω => (σ ω.1).coe_nonneg)
      (fun ω => (S₂ ω.2).coe_nonneg) fun ω => ⟨(), NNReal.coe_le_coe.2 (hσS ω.1), le_rfl⟩)
  refine A1Law.rectDens_stop_of_exit_fst (M := fun y (s : ℝ≥0) x => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y))
    h.stop₁.measurableSpace_le h.stop₂.measurableSpace_le (measurable_rectDens (fun _ : Unit => h) hmeas ()) hD
    hexit (ae_of_all _ fun y => h.col y) (fun y x t => (h.col_cont x y).continuousWithinAt)
    (fun y t x => (hpos _ _ _).le) hσ h.stop₁ (fun x => WithTop.coe_le_coe.2 (hσS x)) (T := U)
    (fun x => WithTop.coe_le_coe.2 (hU x)) (fun x y => ?_) (fun x y => ?_)
    (hσ.measurableSpace_mono h.stop₁ fun x => WithTop.coe_le_coe.2 (hσS x))
  · simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe, min_self]
  · simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe, min_eq_left (NNReal.coe_le_coe.2 (hσS x))]

end Stop

end InteractingSLE.ZhanGT4.A1Patch
