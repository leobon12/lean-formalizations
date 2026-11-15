/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1PatchStair
import InteractingSLE.Spec.ZhanGT4.A1LawAssembly

/-!
# A.1's finite seeded patches for every `N`: input (I1) of `A1Law.PatchInput`

Packet PROVE-A1-PATCH (R80). Source: Astra, *Follow-up 4* §2.5 item 4 (`ig1_followup4_audited.txt` L789–L796): "For
finitely many protected rectangles, the staircase density (D11)–(D12) … uses only coordinate martingales and their axis
values. … Each finite patch therefore has the two prescribed marginals and the prescribed joint stopped law on each
included rectangle"; *Follow-up proofs* §A.1.5 (L409–L411): "For its first `n` pairs use (D11) to obtain a coupling of
the two fixed complete marginal path laws."

For a sequence of protected rectangles `m ↦ (S₁ m, S₂ m)` of one two-time field `N` (`IsRectField`), the staircase
coupling of the first `n + 1` rectangles (`A1PatchStair`) is, for every `n`, a coupling of `P₁` and `P₂` with (1.7) on
the stopped σ-algebras of every rectangle `m ≤ n`, with density `N(S₁ m, S₂ m)`. Records of the rectangles that are
measurable for the stopped σ-algebras inherit (1.7) (`RectDens.mono`), which is input (I1) of PROVE-A1-LAW's
`PatchInput`.

## Main results

* `RectDens.mono`: (1.7) for smaller σ-algebras;
* **`exists_patches_of_rectField`**: the finite patches `π n` for every `n`;
* `FieldPatchInput`, **`patchInput_of_fieldPatchInput`**: (I1) of `PatchInput` from the field data (records measurable
  for the stopped σ-algebras), keeping (I2) unchanged;
* `exists_record_comap_eq`: a countably generated sub-σ-algebra is the σ-algebra of a record with values in the
  standard Borel space `ℕ → Bool` (records generating the stopped σ-algebras exactly, when these are countably
  generated); `FieldPatchStopInput`, `patchInput_of_fieldPatchStopInput`: the same input with (I2) stated on the stopped
  σ-algebras themselves.
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Patch

open A1Law

/-! ### (1.7) for smaller σ-algebras -/

/-- **(1.7) for smaller σ-algebras**: a test measurable for `𝓐' ⊗ 𝓑'` is measurable for `𝓐 ⊗ 𝓑`. -/
theorem RectDens.mono {X Y : Type*} {𝓐 𝓐' : MeasurableSpace X} {𝓑 𝓑' : MeasurableSpace Y} [MeasurableSpace X]
    [MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {D : X × Y → ℝ≥0∞}
    (h : RectDens 𝓐 𝓑 P₁ P₂ μ D) (h𝓐 : 𝓐' ≤ 𝓐) (h𝓑 : 𝓑' ≤ 𝓑) : RectDens 𝓐' 𝓑' P₁ P₂ μ D := fun f hf =>
  h f (hf.mono (sup_le_sup (MeasurableSpace.comap_mono h𝓐) (MeasurableSpace.comap_mono h𝓑)) le_rfl)

/-! ### The finite patches of a sequence of protected rectangles -/

section Seq

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
  {N : X × Y → ℝ → ℝ → ℝ}

/-- **The finite patches** (§A.1.5, "For its first `n` pairs use (D11) to obtain a coupling of the two fixed complete
marginal path laws"; follow-up 4 §2.5 item 4): for a sequence of protected rectangles of one two-time field `N` with
axis values one, there are couplings `π n` of `P₁` and `P₂` with (1.7) on the stopped σ-algebras of every rectangle
`m ≤ n`, with density `N(S₁ m, S₂ m)` (the staircase coupling of the first `n + 1` rectangles). -/
theorem exists_patches_of_rectField [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (hmeas : IsFieldMeas N S₁ S₂) :
    ∃ π : ℕ → Measure (X × Y), (∀ n, IsProbabilityMeasure (π n)) ∧ (∀ n, (π n).map Prod.fst = P₁) ∧
      (∀ n, (π n).map Prod.snd = P₂) ∧ ∀ n m, m ≤ n →
        RectDens (h m).stop₁.measurableSpace (h m).stop₂.measurableSpace P₁ P₂ (π n)
          fun ω => ENNReal.ofReal (N ω (S₁ m ω.1) (S₂ m ω.2)) := by
  have h' : ∀ n, ∀ j : Fin (n + 1), IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ j) (S₂ j) N := fun n j => h j
  have hm' : ∀ n, IsFieldMeas N (fun j : Fin (n + 1) => S₁ j) (fun j => S₂ j) := fun n => hmeas.comp _
  choose U hU using fun n => exists_bdd_of_isRectField (h' n)
  refine ⟨fun n => stairCoupling P₁ P₂ N (fun j : Fin (n + 1) => S₁ j) (fun j => S₂ j) (U n),
    fun n => isProbabilityMeasure_stairCoupling (h' n) hpos hax₁ hax₂ (hm' n) (U n),
    fun n => stairCoupling_map_fst (h' n) hpos hax₁ hax₂ (hm' n) (U n),
    fun n => stairCoupling_map_snd (h' n) hpos (hm' n) (hU n).2, fun n m hmn => ?_⟩
  exact rectDens_stairCoupling (h' n) hpos hax₁ hax₂ (hm' n) (hU n).1 (hU n).2 ⟨m, Nat.lt_succ_of_le hmn⟩

end Seq

/-! ### Records generating a countably generated σ-algebra -/

/-- **A record generating a countably generated sub-σ-algebra** (§A.1.5: "countable generators of the actual augmented
stopped sigma-algebra … Regard the resulting coordinates as elements of a countable product of real standard Borel
spaces"): the indicator coordinates of a generating sequence, with values in `ℕ → Bool`, pull back exactly to `𝓖`. -/
theorem exists_record_comap_eq {X : Type*} {𝓖 : MeasurableSpace X} [mX : MeasurableSpace X] (h𝓖 : 𝓖 ≤ mX)
    (hc : @MeasurableSpace.CountablyGenerated X 𝓖) :
    ∃ r : X → ℕ → Bool, Measurable r ∧ MeasurableSpace.comap r inferInstance = 𝓖 := by
  have hm := @MeasurableSpace.measurable_mapNatBool X 𝓖 hc
  refine ⟨@MeasurableSpace.mapNatBool X 𝓖 hc, hm.mono h𝓖 le_rfl, le_antisymm hm.comap_le ?_⟩
  conv_lhs => rw [← @MeasurableSpace.generateFrom_natGeneratingSequence X 𝓖 hc]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨(fun f : ℕ → Bool => f n) ⁻¹' {true}, measurable_pi_apply n (measurableSet_singleton true), ?_⟩
  ext x
  simp [MeasurableSpace.mapNatBool]

/-! ### (I1) of `PatchInput` from the field data -/

section Field

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A.1's finite-patch input from a two-time field** (follow-up 4 §2.5 item 4, §A.1.4–A.1.5): stopped records
`f m`, `g m` into standard Borel spaces and a sequence of protected rectangles `(S₁ m, S₂ m)` of one positive two-time
field `N` with axis values one (`IsRectField`: bounds and the two coordinate martingale identities), each record
measurable for the stopped σ-algebra of its rectangle; and the law input (I2) unchanged: every coupling of `P₁`, `P₂`
with (1.7) on the records, density `N(S₁ m, S₂ m)`, has the property `Law`. No coupling is assumed: the finite
patches are constructed (`patchInput_of_fieldPatchInput`). -/
def FieldPatchInput (P₁ : Measure X) (P₂ : Measure Y) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (E F : ℕ → Type) (_ : ∀ m, MeasurableSpace (E m)) (_ : ∀ m, StandardBorelSpace (E m))
    (_ : ∀ m, MeasurableSpace (F m)) (_ : ∀ m, StandardBorelSpace (F m)) (f : ∀ m, X → E m) (g : ∀ m, Y → F m)
    (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (N : X × Y → ℝ → ℝ → ℝ) (h : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) N),
    (∀ ω s t, 0 < N ω s t) ∧ (∀ ω t, N ω 0 t = 1) ∧ (∀ ω s, N ω s 0 = 1) ∧ IsFieldMeas N S₁ S₂ ∧
    (∀ m, Measurable (f m)) ∧ (∀ m, Measurable (g m)) ∧
    (∀ m, recSigma f m ≤ (h m).stop₁.measurableSpace) ∧ (∀ m, recSigma g m ≤ (h m).stop₂.measurableSpace) ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (recSigma f m) (recSigma g m) P₁ P₂ μ fun ω => ENNReal.ofReal (N ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- **(I1) is supplied by the field data**: the staircase couplings of the first `n + 1` rectangles are the finite
patches of `PatchInput`, with the densities `D m = N(S₁ m, S₂ m)`. -/
theorem patchInput_of_fieldPatchInput {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {Law : Measure (X × Y) → Prop} (h : FieldPatchInput P₁ P₂ Law) :
    PatchInput P₁ P₂ Law := by
  obtain ⟨E, F, iE, hE, iF, hF, f, g, 𝓕₁, 𝓕₂, S₁, S₂, N, hR, hpos, hax₁, hax₂, hmeas, hf, hg, hfS, hgS, hLaw⟩ := h
  obtain ⟨π, hπ, hπ₁, hπ₂, hd⟩ := exists_patches_of_rectField hR hpos hax₁ hax₂ hmeas
  exact ⟨E, F, iE, hE, iF, hF, f, g, fun m ω => ENNReal.ofReal (N ω (S₁ m ω.1) (S₂ m ω.2)), π, hf, hg,
    fun m => measurable_rectDens hR hmeas m, hπ, hπ₁, hπ₂,
    fun n m hmn => RectDens.mono (hd n m hmn) (hfS m) (hgS m), hLaw⟩

/-- **The field input with (I2) on the stopped σ-algebras** (no records): the stopped σ-algebras of the rectangles are
countably generated, and every coupling with (1.7) on them, density `N(S₁ m, S₂ m)`, has the property `Law`. -/
def FieldPatchStopInput (P₁ : Measure X) (P₂ : Measure Y) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (N : X × Y → ℝ → ℝ → ℝ) (h : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) N),
    (∀ ω s t, 0 < N ω s t) ∧ (∀ ω t, N ω 0 t = 1) ∧ (∀ ω s, N ω s 0 = 1) ∧ IsFieldMeas N S₁ S₂ ∧
    (∀ m, @MeasurableSpace.CountablyGenerated X (h m).stop₁.measurableSpace) ∧
    (∀ m, @MeasurableSpace.CountablyGenerated Y (h m).stop₂.measurableSpace) ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h m).stop₁.measurableSpace (h m).stop₂.measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (N ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- With countably generated stopped σ-algebras, records generating them exactly (`exists_record_comap_eq`) turn the
stopped-σ-algebra form into the record form. -/
theorem fieldPatchInput_of_stop {P₁ : Measure X} {P₂ : Measure Y} {Law : Measure (X × Y) → Prop}
    (h : FieldPatchStopInput P₁ P₂ Law) : FieldPatchInput P₁ P₂ Law := by
  obtain ⟨𝓕₁, 𝓕₂, S₁, S₂, N, hR, hpos, hax₁, hax₂, hmeas, hc₁, hc₂, hLaw⟩ := h
  choose f hf hfe using fun m => exists_record_comap_eq (hR m).stop₁.measurableSpace_le (hc₁ m)
  choose g hg hge using fun m => exists_record_comap_eq (hR m).stop₂.measurableSpace_le (hc₂ m)
  refine ⟨fun _ => ℕ → Bool, fun _ => ℕ → Bool, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, f, g, 𝓕₁, 𝓕₂, S₁, S₂, N, hR, hpos, hax₁, hax₂, hmeas, hf, hg,
    fun m => (hfe m).le, fun m => (hge m).le, fun μ hμ h₁ h₂ hd => hLaw μ hμ h₁ h₂ fun m => ?_⟩
  have e₁ : recSigma f m = (hR m).stop₁.measurableSpace := hfe m
  have e₂ : recSigma g m = (hR m).stop₂.measurableSpace := hge m
  have := hd m
  rwa [e₁, e₂] at this

/-- **(I1) from the field data, stopped-σ-algebra form.** -/
theorem patchInput_of_fieldPatchStopInput {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {Law : Measure (X × Y) → Prop} (h : FieldPatchStopInput P₁ P₂ Law) :
    PatchInput P₁ P₂ Law :=
  patchInput_of_fieldPatchInput (fieldPatchInput_of_stop h)

end Field

end InteractingSLE.ZhanGT4.A1Patch
