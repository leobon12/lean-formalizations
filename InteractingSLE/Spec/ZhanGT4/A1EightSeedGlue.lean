/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldStatement

/-!
# Zhan's A.1 (R80): the seeded field glued from rectangle-wise records

Packet PROVE-A1-EIGHTSEED. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425: "its
restriction to each stopped rectangle has density `M(S₁ᵐ, S₂ᵐ)`") and follow-up 4 §2.5 (L739–L788).

PROVE-A1-SEEDFIELD's `SeedFieldInput` asks for ONE family of seeded records `d t (x, y)` serving every rectangle. Its
records carry a globally continuous growing driver (`OwnData.cont`, and `IsSourceColumn`'s `W = √κ B + D` with `D`
continuous), while the driver of a regular marginal is continuous only before its lifetime; the natural records of
rectangle `m` use the driver stopped at its own exit `S₁ m x`, which depends on `m`. The density `M(s, t)` itself does
not depend on the record (the seeded logarithm at own time `s` reads the driver on `[0, s]` only:
`A1EightSeedCongr`). Here the records may depend on the rectangle:

* `RecCompat d S₁ S₂`: the records of two rectangles have the same seeded logarithm `normEll` on the intersection of
  the rectangles;
* `glueField d S₁ S₂`: the field read, at `(s, t)`, from the first rectangle containing `(s, t)` (and `1` outside every
  rectangle); on each rectangle it is that rectangle's seeded height field (`glueField_eq`), it is positive with axis
  values one, and measurable on the rectangles when each rectangle's field is (`isFieldMeas_glueField`);
* `isRectField_congr`: a protected rectangle depends only on the field's values on the rectangle;
* `isRectField_of_sourceR`: A1-SEEDFIELD's `isRectField_of_source` with the identity chart at frozen height zero
  required on the rectangle only (the records are controlled up to their horizon only);
* **`SeedFieldInputM`** (the rectangle-wise form of `SeedFieldInput`; its height-zero clause is required for
  `0 ≤ s ≤ S₁ m x` only) and **`fieldPatchSigmaInput_of_seedFieldInputM`**;
  `seedFieldInputM_of_seedFieldInput` (the old form is the special case of constant records);
* `A1DualCouplingEightSeedMStatement` (the Eight statement with `SeedFieldInputM`; binders and law property copied from
  `A1DualCouplingEightSeedStatement`), `a1DualCouplingEightSeedMStatement_of_seed`, and the chain
  `a1DualCouplingEight{FieldLaw,Field,Rect,Canon}Statement_of_seedM`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EightSeed

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField

/-! ### A protected rectangle reads the field on the rectangle only -/

section Congr

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}

/-- **`IsRectField` depends only on the values of the field on the rectangle** `[0, S₁ x] × [0, S₂ y]`. -/
theorem isRectField_congr {N N' : X × Y → ℝ → ℝ → ℝ} (h : IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ N)
    (hN : ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y → N (x, y) s t = N' (x, y) s t) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ N' where
  stop₁ := h.stop₁
  stop₂ := h.stop₂
  bdd := h.bdd
  bound := by
    obtain ⟨c, C, hc, hb⟩ := h.bound
    refine ⟨c, C, hc, fun x y s t hs hsS ht htS => ?_⟩
    rw [← hN x y s t hs hsS ht htS]
    exact hb x y s t hs hsS ht htS
  col y := by
    have e : (fun (s : ℝ≥0) x => N' (x, y) (min (s : ℝ) (S₁ x)) (S₂ y)) =
        fun (s : ℝ≥0) x => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y) := by
      funext s x
      exact (hN x y _ _ (le_min s.coe_nonneg (S₁ x).coe_nonneg) (min_le_right _ _) (S₂ y).coe_nonneg le_rfl).symm
    rw [e]
    exact h.col y
  col_cont x y := by
    have e : (fun s : ℝ≥0 => N' (x, y) (min (s : ℝ) (S₁ x)) (S₂ y)) =
        fun s : ℝ≥0 => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y) := by
      funext s
      exact (hN x y _ _ (le_min s.coe_nonneg (S₁ x).coe_nonneg) (min_le_right _ _) (S₂ y).coe_nonneg le_rfl).symm
    rw [e]
    exact h.col_cont x y
  row x a ha haS := by
    have e : (fun (t : ℝ≥0) y => N' (x, y) a (min (t : ℝ) (S₂ y))) =
        fun (t : ℝ≥0) y => N (x, y) a (min (t : ℝ) (S₂ y)) := by
      funext t y
      exact (hN x y _ _ ha haS (le_min t.coe_nonneg (S₂ y).coe_nonneg) (min_le_right _ _)).symm
    rw [e]
    exact h.row x a ha haS
  row_cont x y a ha haS := by
    have e : (fun t : ℝ≥0 => N' (x, y) a (min (t : ℝ) (S₂ y))) =
        fun t : ℝ≥0 => N (x, y) a (min (t : ℝ) (S₂ y)) := by
      funext t
      exact (hN x y _ _ ha haS (le_min t.coe_nonneg (S₂ y).coe_nonneg) (min_le_right _ _)).symm
    rw [e]
    exact h.row_cont x y a ha haS

end Congr

/-! ### The glued field -/

section Glue

variable {X Y : Type*} {n : ℕ}

/-- **Compatibility of rectangle-wise records**: on the intersection of two rectangles the two records have the same
seeded logarithm. -/
def RecCompat (d : ℕ → ℝ → X × Y → SeedData n) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0) : Prop :=
  ∀ m m' (x : X) (y : Y) (s t : ℝ), 0 ≤ s → s ≤ S₁ m x → s ≤ S₁ m' x → 0 ≤ t → t ≤ S₂ m y → t ≤ S₂ m' y →
    (d m t (x, y)).normEll s = (d m' t (x, y)).normEll s

open Classical in
/-- **The glued seeded field**: at `(s, t)` the seeded height field of the first rectangle containing `(s, t)`, and `1`
outside every rectangle. -/
def glueField (d : ℕ → ℝ → X × Y → SeedData n) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0) (ω : X × Y) (s t : ℝ) :
    ℝ :=
  if h : ∃ m, 0 ≤ s ∧ s ≤ S₁ m ω.1 ∧ 0 ≤ t ∧ t ≤ S₂ m ω.2 then seedHeightField (d (Nat.find h)) ω s t else 1

variable {d : ℕ → ℝ → X × Y → SeedData n} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}

/-- **On each rectangle the glued field is that rectangle's seeded height field.** -/
theorem glueField_eq (hc : RecCompat d S₁ S₂) {m : ℕ} {x : X} {y : Y} {s t : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S₁ m x)
    (ht : 0 ≤ t) (htS : t ≤ S₂ m y) : glueField d S₁ S₂ (x, y) s t = seedHeightField (d m) (x, y) s t := by
  classical
  have h : ∃ k, 0 ≤ s ∧ s ≤ S₁ k (x, y).1 ∧ 0 ≤ t ∧ t ≤ S₂ k (x, y).2 := ⟨m, hs, hsS, ht, htS⟩
  have hk := Nat.find_spec h
  unfold glueField
  simp only [h, ↓reduceDIte]
  unfold seedHeightField
  rw [hc _ m x y s t hs hk.2.1 hsS ht hk.2.2.2 htS,
    hc _ m x y 0 t le_rfl (S₁ _ x).coe_nonneg (S₁ m x).coe_nonneg ht hk.2.2.2 htS]

theorem glueField_pos (d : ℕ → ℝ → X × Y → SeedData n) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0) (ω : X × Y)
    (s t : ℝ) : 0 < glueField d S₁ S₂ ω s t := by
  unfold glueField
  split_ifs
  · exact seedHeightField_pos _ _ _ _
  · exact one_pos

theorem glueField_zero_left (d : ℕ → ℝ → X × Y → SeedData n) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (ω : X × Y) (t : ℝ) : glueField d S₁ S₂ ω 0 t = 1 := by
  unfold glueField
  split_ifs
  · exact seedHeightField_zero_left _ _ _
  · rfl

theorem glueField_zero_right
    (h0 : ∀ m (x : X) (y : Y) (s : ℝ), 0 ≤ s → s ≤ S₁ m x → (d m 0 (x, y)).normEll s = (d m 0 (x, y)).normEll 0)
    (ω : X × Y) (s : ℝ) : glueField d S₁ S₂ ω s 0 = 1 := by
  classical
  unfold glueField
  split_ifs with h
  · have hk := Nat.find_spec h
    simp only [seedHeightField, h0 _ ω.1 ω.2 s hk.1 hk.2.1, sub_self, Real.exp_zero]
  · rfl

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- **The glued field is measurable on the rectangles** when each rectangle's seeded height field is measurable on its
own rectangle: at a pair of random times in some rectangle, the glued field is a countable piecewise function
(`Measurable.find`) of the rectangle-wise fields at the same times. -/
theorem isFieldMeas_glueField (hS₁ : ∀ m, Measurable fun x => (S₁ m x : ℝ))
    (hS₂ : ∀ m, Measurable fun y => (S₂ m y : ℝ))
    (hm : ∀ m, IsFieldMeas (seedHeightField (d m)) (fun _ : Unit => S₁ m) (fun _ : Unit => S₂ m)) :
    IsFieldMeas (glueField d S₁ S₂) S₁ S₂ := by
  classical
  intro U V hU hV hU0 hV0 hUV
  have hp : ∀ m, MeasurableSet {ω : X × Y | 0 ≤ U ω ∧ U ω ≤ S₁ m ω.1 ∧ 0 ≤ V ω ∧ V ω ≤ S₂ m ω.2} := fun m =>
    (measurableSet_le measurable_const hU).inter ((measurableSet_le hU ((hS₁ m).comp measurable_fst)).inter
      ((measurableSet_le measurable_const hV).inter (measurableSet_le hV ((hS₂ m).comp measurable_snd))))
  have hUV' : ∀ ω, ∃ m, 0 ≤ U ω ∧ U ω ≤ S₁ m ω.1 ∧ 0 ≤ V ω ∧ V ω ≤ S₂ m ω.2 := fun ω => by
    obtain ⟨m, h1, h2⟩ := hUV ω
    exact ⟨m, hU0 ω, h1, hV0 ω, h2⟩
  have hf : ∀ m, Measurable fun ω : X × Y =>
      seedHeightField (d m) ω (min (U ω) (S₁ m ω.1)) (min (V ω) (S₂ m ω.2)) := fun m =>
    hm m _ _ (hU.min ((hS₁ m).comp measurable_fst)) (hV.min ((hS₂ m).comp measurable_snd))
      (fun ω => le_min (hU0 ω) (S₁ m ω.1).coe_nonneg) (fun ω => le_min (hV0 ω) (S₂ m ω.2).coe_nonneg)
      (fun _ => ⟨(), min_le_right _ _, min_le_right _ _⟩)
  have key := Measurable.find hf hp hUV'
  have e : (fun ω => glueField d S₁ S₂ ω (U ω) (V ω)) = fun ω => seedHeightField (d (Nat.find (hUV' ω))) ω
      (min (U ω) (S₁ (Nat.find (hUV' ω)) ω.1)) (min (V ω) (S₂ (Nat.find (hUV' ω)) ω.2)) := by
    funext ω
    have hk := Nat.find_spec (hUV' ω)
    rw [min_eq_left hk.2.1, min_eq_left hk.2.2.2]
    unfold glueField
    simp only [hUV' ω, ↓reduceDIte]
  rw [e]
  exact key

end Glue

/-! ### A protected rectangle with the identity chart on the rectangle only -/

section Source

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  [IsProbabilityMeasure P₁] {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {n : ℕ}

/-- The column at frozen height zero when the normalized logarithm is constant on `[0, T]` only. -/
theorem martingale_seedDensityProcess_of_identityOn {sdata : X → SeedData n} {T : X → ℝ≥0}
    (h0 : ∀ x (s : ℝ), 0 ≤ s → s ≤ T x → (sdata x).normEll s = (sdata x).normEll 0) :
    Martingale (seedDensityProcess sdata T) 𝓕₁ P₁ ∧ (∀ x, Continuous (seedDensityProcess sdata T · x)) := by
  have e : seedDensityProcess sdata T = fun _ _ => (1 : ℝ) := by
    funext u x
    have hm : (0 : ℝ) ≤ min (u : ℝ) (T x : ℝ) := le_min u.coe_nonneg (T x).coe_nonneg
    simp only [seedDensityProcess, h0 x _ hm (min_le_right _ _), sub_self, Real.exp_zero]
  rw [e]
  exact ⟨martingale_const 𝓕₁ P₁ 1, fun _ => continuous_const⟩

/-- **`isRectField_of_source` with the identity chart required on the rectangle only** (`0 ≤ s ≤ S₁ x` at frozen
height zero). -/
theorem isRectField_of_sourceR {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (h₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)) (h₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0))
    (hU : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U)
    (hcol : ∀ y, 0 < (S₂ y : ℝ) →
      IsSourceColumn H₁ H₂ p Tm κ rr 𝓕₁ P₁ (S₂ y) (fun x => d (S₂ y) (x, y)) S₁)
    (hrec : ∀ x y (t : ℝ), 0 < t → t ≤ S₂ y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ), IsSourceRecord H₁ H₂ p Tm κ rr W₂ t (d t (x, y)) Vlo Vhi (S₁ x))
    (hzero : ∀ x y (s : ℝ), 0 ≤ s → s ≤ S₁ x → (d 0 (x, y)).normEll s = (d 0 (x, y)).normEll 0)
    (hrow : ∀ x (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) 𝓕₂ P₂)
    (hrowc : ∀ x y (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Continuous fun t : ℝ≥0 => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ (seedHeightField d) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_normEll_le_uniform_right hpp.hull₁ hpp.hull₂ hpp.sep_pos hpp.sep hpp.src
    hpp.prot_pos hpp.prot_lt hpp.rad_pos hpp.prot Tm κ rr
  have hcol' : ∀ y, Martingale (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁) 𝓕₁ P₁ ∧
      (∀ x, Continuous (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁ · x)) := by
    intro y
    rcases (S₂ y).coe_nonneg.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact martingale_seedDensityProcess_of_identityOn fun x s hs hsS => hzero x y s hs hsS
    · exact (hcol y hpos).calculus hpp hκ
  refine isRectField_seedHeightField h₁ h₂ hU ?_ (fun y => (hcol' y).1) (fun x y => (hcol' y).2 x) hrow hrowc
  refine seedHeightField_bound_of_pos_zero hK0 (fun x y s t hs hsS ht htS => ?_) hzero
  obtain ⟨W₂, Vlo, Vhi, hr⟩ := hrec x y t ht htS
  exact ⟨hr.abs_normEll_le hK ⟨hs, hsS⟩, hr.abs_normEll_le hK ⟨le_rfl, (S₁ x).coe_nonneg⟩⟩

end Source

/-! ### The rectangle-wise seeded input -/

section Input

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The rectangle-wise seeded-field data of A.1**: as `SeedFieldInput`, but the seeded records `d m t (x, y)` may
depend on the rectangle `m`, provided records of different rectangles have the same seeded logarithm on the
intersection of the rectangles (`RecCompat`); the row martingales, the measurability and the law input (I2) are
stated for each rectangle's own seeded height field. -/
def SeedFieldInputM (P₁ : Measure X) (P₂ : Measure Y) (κ : ℝ) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (n : ℕ) (rr : Fin n → ℝ) (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0)
    (S₂ : ℕ → Y → ℝ≥0) (d : ℕ → ℝ → X × Y → SeedData n) (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ) (p : ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0)),
    (∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m)) ∧
    (∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U) ∧
    (∀ m y, 0 < (S₂ m y : ℝ) →
      IsSourceColumn (H₁ m) (H₂ m) p (Tm m) κ rr 𝓕₁ P₁ (S₂ m y) (fun x => d m (S₂ m y) (x, y)) (S₁ m)) ∧
    (∀ m x y (t : ℝ), 0 < t → t ≤ S₂ m y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ), IsSourceRecord (H₁ m) (H₂ m) p (Tm m) κ rr W₂ t (d m t (x, y)) Vlo Vhi (S₁ m x)) ∧
    (∀ m x y (s : ℝ), 0 ≤ s → s ≤ S₁ m x → (d m 0 (x, y)).normEll s = (d m 0 (x, y)).normEll 0) ∧
    RecCompat d S₁ S₂ ∧
    (∀ m x (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (d m) (x, y) a (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂) ∧
    (∀ m x y (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField (d m) (x, y) a (min (t : ℝ) (S₂ m y))) ∧
    (∀ m, IsFieldMeas (seedHeightField (d m)) (fun _ : Unit => S₁ m) (fun _ : Unit => S₂ m)) ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField (d m) ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- **The rectangle-wise data give A1-PATCH's field input**: rectangle `m` is an `IsRectField` of its own seeded height
field (`isRectField_of_source`), hence of the glued field (`isRectField_congr`, `glueField_eq`), which is positive,
has axis values one and is measurable on the rectangles. -/
theorem fieldPatchSigmaInput_of_seedFieldInputM {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁]
    {κ : ℝ} (hκ : 0 < κ) {Law : Measure (X × Y) → Prop} (h : SeedFieldInputM P₁ P₂ κ Law) :
    FieldPatchSigmaInput P₁ P₂ Law := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, hlaw⟩ := h
  have hR₀ : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) (seedHeightField (d m)) := fun m =>
    isRectField_of_sourceR (hpp m) hκ (h₁ m) (h₂ m) (hU m) (hcol m) (hrec m) (hzero m) (hrow m) (hrowc m)
  have hR : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) (glueField d S₁ S₂) := fun m =>
    isRectField_congr (hR₀ m) fun x y s t hs hsS ht htS => (glueField_eq hc hs hsS ht htS).symm
  refine ⟨𝓕₁, 𝓕₂, S₁, S₂, glueField d S₁ S₂, hR, glueField_pos d S₁ S₂, glueField_zero_left d S₁ S₂,
    glueField_zero_right hzero,
    isFieldMeas_glueField (fun m => measurable_coe_of_isStoppingTime (h₁ m))
      (fun m => measurable_coe_of_isStoppingTime (h₂ m)) hmeas, fun μ hμ hμ₁ hμ₂ hd => hlaw μ hμ hμ₁ hμ₂ ?_⟩
  intro m
  have e : (fun ω : X × Y => ENNReal.ofReal (glueField d S₁ S₂ ω (S₁ m ω.1) (S₂ m ω.2))) =
      fun ω => ENNReal.ofReal (seedHeightField (d m) ω (S₁ m ω.1) (S₂ m ω.2)) := by
    funext ω
    rw [glueField_eq hc (S₁ m ω.1).coe_nonneg le_rfl (S₂ m ω.2).coe_nonneg le_rfl]
  have hdm := hd m
  rw [e] at hdm
  exact hdm

/-- **The single-record form is the special case of constant records.** -/
theorem seedFieldInputM_of_seedFieldInput {P₁ : Measure X} {P₂ : Measure Y} {κ : ℝ}
    {Law : Measure (X × Y) → Prop} (h : SeedFieldInput P₁ P₂ κ Law) : SeedFieldInputM P₁ P₂ κ Law := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hrow, hrowc,
    hmeas, hlaw⟩ := h
  exact ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, fun _ => d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec,
    fun _ x y s _ _ => hzero x y s, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, hrow, hrowc,
    fun m => hmeas.comp fun _ : Unit => m, hlaw⟩

end Input

/-! ### The Eight statement in the rectangle-wise form -/

section Config

/-- **A.1 (Eight), rectangle-wise seeded form for every pair of regular marginals**: `A1DualCouplingEightSeedStatement`
with `SeedFieldInput` replaced by `SeedFieldInputM` (binders and law property copied verbatim). -/
def A1DualCouplingEightSeedMStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      SeedFieldInputM P₁ P₂ (kh κ) fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- The single-record Eight statement gives the rectangle-wise one. -/
theorem a1DualCouplingEightSeedMStatement_of_seed {κ : ℝ} (h : A1DualCouplingEightSeedStatement κ) :
    A1DualCouplingEightSeedMStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact seedFieldInputM_of_seedFieldInput
    (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- The rectangle-wise form gives A1-PATCH's field form for every pair of regular marginals (Eight). -/
theorem a1DualCouplingEightFieldLawStatement_of_seedM {κ : ℝ} (h : A1DualCouplingEightSeedMStatement κ) :
    A1DualCouplingEightFieldLawStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  exact fieldPatchSigmaInput_of_seedFieldInputM hk
    (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- **The rectangle-wise form gives A1-PATCH's field statement (Eight).** -/
theorem a1DualCouplingEightFieldStatement_of_seedM {κ : ℝ} (h : A1DualCouplingEightSeedMStatement κ) :
    A1DualCouplingEightFieldStatement κ :=
  a1DualCouplingEightFieldStatement_of_fieldLaw (a1DualCouplingEightFieldLawStatement_of_seedM h)

/-- **The rectangle-wise form gives R76's Rect statement (Eight).** -/
theorem a1DualCouplingEightRectStatement_of_seedM {κ : ℝ} (h : A1DualCouplingEightSeedMStatement κ) :
    A1DualCouplingEightRectStatement κ :=
  a1DualCouplingEightRectStatement_of_field (a1DualCouplingEightFieldStatement_of_seedM h)

/-- The rectangle-wise form gives R72's Canon statement (Eight). -/
theorem a1DualCouplingEightCanonStatement_of_seedM {κ : ℝ} (h : A1DualCouplingEightSeedMStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_field (a1DualCouplingEightFieldStatement_of_seedM h)

end Config

end InteractingSLE.ZhanGT4.A1EightSeed
