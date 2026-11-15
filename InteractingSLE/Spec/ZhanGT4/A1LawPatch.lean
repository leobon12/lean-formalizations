/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15
import InteractingSLE.Spec.ZhanGT4.A1CoreFibre
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A.1's coupling of the complete marginals from finite rectangle patches

Packet PROVE-A1-LAW (R76). Source: Astra, *Follow-up 4* §2.5 item 4 (`ig1_followup4_audited.txt` L789–L812, R71):
"For finitely many protected rectangles, the staircase density (D11)–(D12) … Each finite patch therefore has the two
prescribed marginals and the prescribed joint stopped law on each included rectangle. … For the countable patch,
augment each canonical path by its stopped record for every enclosure … These are Borel functions of its full
marginal history … Put these countably many coordinates in fixed Polish models. Each augmented marginal law is fixed.
Hence the family of couplings is tight … In a weak limit, the augmented marginal laws are unchanged … For any fixed
rectangle, all sufficiently late finite patches have the same joint law of the two stopped-record coordinates.
Projection onto those coordinates is continuous in the product topology, so that exact law passes to the limit.
A monotone class extends its identities from the countable generators"; *Follow-up 5* §1.3 (L203–L211), the density
identity (1.7) `E_coupled[F G] = E_{P₁ ⊗ P₂}[M F G]` on each rectangle.

Here the records are measurable maps `f m : X → E m`, `g m : Y → F m` into standard Borel spaces (the stopped records
of the two curves on rectangle `m`), the record σ-algebras are their pull-backs, and the identity (1.7) on rectangle
`m` is `RectDens (recSigma f m) (recSigma g m) P₁ P₂ μ (D m)`. The marginal spaces need only be standard Borel (the
regular marginals of PROVE-A1-MARG live on a measurable subset of a code space, which is not Polish): a finer Polish
topology makes the countably many records continuous (Lusin–Souslin).

## Main results

* `exists_polish_continuous`: a Polish topology, Borel for the given σ-algebra, making countably many measurable maps
  into second-countable spaces continuous;
* `RectDens`, `recSigma`; `map_eq_of_rectDens`, `rectDens_of_map_eq`: (1.7) on the record σ-algebras is the
  equality of the joint record laws under `μ` and under `D · (P₁ ⊗ P₂)`;
* **`exists_coupling_of_patches`**: finite patches (couplings of `P₁`, `P₂` with (1.7) on every rectangle from some
  index on) give ONE coupling of the complete marginals with (1.7) on every rectangle;
* `exists_coupling_of_finite_patches`: the same for patches `π N` that satisfy (1.7) on the rectangles `m ≤ N`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace InteractingSLE.ZhanGT4.A1Law

/-! ### A Polish topology making countably many records continuous -/

/-- **Countably many measurable records are continuous for some compatible Polish topology** (Kechris 13.11; Mathlib's
`Measurable.exists_continuous` and `exists_polishSpace_forall_le`). -/
theorem exists_polish_continuous {X : Type*} [mX : MeasurableSpace X] [StandardBorelSpace X]
    {E : ℕ → Type*} [∀ m, TopologicalSpace (E m)] [∀ m, SecondCountableTopology (E m)]
    [∀ m, MeasurableSpace (E m)] [∀ m, OpensMeasurableSpace (E m)]
    (f : ∀ m, X → E m) (hf : ∀ m, Measurable (f m)) :
    ∃ t : TopologicalSpace X, @PolishSpace X t ∧ @BorelSpace X t mX ∧ ∀ m, Continuous[t, _] (f m) := by
  let t₀ : TopologicalSpace X := (upgradeStandardBorel X).toTopologicalSpace
  have hp₀ : PolishSpace X := (upgradeStandardBorel X).toPolishSpace
  have hb₀ : BorelSpace X := (upgradeStandardBorel X).toBorelSpace
  have h : ∀ m, ∃ t' : TopologicalSpace X, t' ≤ t₀ ∧ Continuous[t', _] (f m) ∧ @PolishSpace X t' :=
    fun m => (hf m).exists_continuous
  choose T hT hc hp using h
  obtain ⟨t', ht'T, ht', hp'⟩ := PolishSpace.exists_polishSpace_forall_le T hT hp
  refine ⟨t', hp', ⟨?_⟩, fun m => continuous_le_dom (ht'T m) (hc m)⟩
  rw [borel_eq_borel_of_le hp' hp₀ ht']
  exact hb₀.measurable_eq

/-! ### The density identity (1.7) on record σ-algebras -/

section DensDef

variable {X Y : Type*}

/-- The σ-algebra of the record `f m` (its pull-back). -/
abbrev recSigma {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] (f : ∀ m, X → E m) (m : ℕ) : MeasurableSpace X :=
  MeasurableSpace.comap (f m) inferInstance

theorem recSigma_le [mX : MeasurableSpace X] {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] {f : ∀ m, X → E m}
    {m : ℕ} (hf : Measurable (f m)) : recSigma f m ≤ mX :=
  hf.comap_le

/-- **The density identity (1.7)** for the σ-algebras `𝓐` (on `X`) and `𝓑` (on `Y`): every test measurable for
`𝓐 ⊗ 𝓑` integrates under `μ` as under `D · (P₁ ⊗ P₂)`. -/
def RectDens (𝓐 : MeasurableSpace X) (𝓑 : MeasurableSpace Y) [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (D : X × Y → ℝ≥0∞) : Prop :=
  ∀ h : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] h →
    ∫⁻ z, h z ∂μ = ∫⁻ z, h z * D z ∂(P₁.prod P₂)

end DensDef

section Dens

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {E F : Type*} [mE : MeasurableSpace E] [mF : MeasurableSpace F]

omit mX mY in
theorem measurable_prodMap_comap (f : X → E) (g : Y → F) :
    Measurable[@Prod.instMeasurableSpace X Y (mE.comap f) (mF.comap g)] (Prod.map f g) := by
  let _ : MeasurableSpace X := mE.comap f
  let _ : MeasurableSpace Y := mF.comap g
  exact (comap_measurable f).prodMap (comap_measurable g)

/-- **(1.7) gives the joint record law**: under `μ` the pair of records has the law it has under `D · (P₁ ⊗ P₂)`. -/
theorem map_eq_of_rectDens {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {f : X → E} {g : Y → F}
    (hf : Measurable f) (hg : Measurable g) {D : X × Y → ℝ≥0∞}
    (h : RectDens (mE.comap f) (mF.comap g) P₁ P₂ μ D) :
    μ.map (Prod.map f g) = ((P₁.prod P₂).withDensity D).map (Prod.map f g) := by
  have hΦ : Measurable (Prod.map f g) := hf.prodMap hg
  ext S hS
  rw [Measure.map_apply hΦ hS, Measure.map_apply hΦ hS, withDensity_apply _ (hΦ hS)]
  have hS' : MeasurableSet[@Prod.instMeasurableSpace X Y (mE.comap f) (mF.comap g)] (Prod.map f g ⁻¹' S) :=
    measurable_prodMap_comap f g hS
  have hind := h ((Prod.map f g ⁻¹' S).indicator 1) (by
    let _ : MeasurableSpace (X × Y) := @Prod.instMeasurableSpace X Y (mE.comap f) (mF.comap g)
    exact measurable_const.indicator hS')
  rw [lintegral_indicator_one (hΦ hS)] at hind
  rw [hind, ← lintegral_indicator (hΦ hS)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ Prod.map f g ⁻¹' S
  · simp only [indicator_of_mem hz, Pi.one_apply, one_mul]
  · simp only [indicator_of_notMem hz, zero_mul]

/-- **The joint record law gives (1.7)** (rectangles of the record σ-algebras are preimages of rectangles, then
Dynkin: A1CORE's `lintegral_eq_of_rect`). -/
theorem rectDens_of_map_eq {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂] {μ : Measure (X × Y)}
    [IsFiniteMeasure μ] {f : X → E} {g : Y → F} (hf : Measurable f) (hg : Measurable g) {D : X × Y → ℝ≥0∞}
    (hD : Measurable D) (h : μ.map (Prod.map f g) = ((P₁.prod P₂).withDensity D).map (Prod.map f g)) :
    RectDens (mE.comap f) (mF.comap g) P₁ P₂ μ D := by
  have hΦ : Measurable (Prod.map f g) := hf.prodMap hg
  intro u hu
  refine A1Core.lintegral_eq_of_rect (P₁ := P₁) (P₂ := P₂) (μ := μ) hf.comap_le hg.comap_le hD (fun A B hA hB => ?_) hu
  obtain ⟨A', hA', rfl⟩ := hA
  obtain ⟨B', hB', rfl⟩ := hB
  have e : (f ⁻¹' A') ×ˢ (g ⁻¹' B') = Prod.map f g ⁻¹' (A' ×ˢ B') := rfl
  have hm := congrArg (fun ν : Measure (E × F) => ν (A' ×ˢ B')) h
  simp only [Measure.map_apply hΦ (hA'.prod hB')] at hm
  rw [e, hm, withDensity_apply _ (hΦ (hA'.prod hB'))]

end Dens

/-! ### The countable patch -/

section Patch

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A.1's countable patch** (follow-up 4 §2.5 item 4). Let `P₁`, `P₂` be probability laws on standard Borel
spaces, `f m`, `g m` measurable records (into standard Borel spaces) and `D m` measurable densities. If the
couplings `π N` of `P₁` and `P₂` satisfy, for every rectangle `m`, the density identity (1.7) on the record
σ-algebras of `m` from some index on, then ONE coupling `μ` of `P₁` and `P₂` satisfies (1.7) on every rectangle. -/
theorem exists_coupling_of_patches [StandardBorelSpace X] [StandardBorelSpace Y]
    (P₁ : Measure X) (P₂ : Measure Y) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {E F : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, StandardBorelSpace (E m)]
    [∀ m, MeasurableSpace (F m)] [∀ m, StandardBorelSpace (F m)]
    (f : ∀ m, X → E m) (g : ∀ m, Y → F m) (hf : ∀ m, Measurable (f m)) (hg : ∀ m, Measurable (g m))
    (D : ℕ → X × Y → ℝ≥0∞) (hD : ∀ m, Measurable (D m))
    (π : ℕ → Measure (X × Y)) [∀ N, IsProbabilityMeasure (π N)]
    (hπ₁ : ∀ N, (π N).map Prod.fst = P₁) (hπ₂ : ∀ N, (π N).map Prod.snd = P₂)
    (hπ : ∀ m, ∀ᶠ N in atTop, RectDens (recSigma f m) (recSigma g m) P₁ P₂ (π N) (D m)) :
    ∃ μ : Measure (X × Y), IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      ∀ m, RectDens (recSigma f m) (recSigma g m) P₁ P₂ μ (D m) := by
  let tE : ∀ m, TopologicalSpace (E m) := fun m => (upgradeStandardBorel (E m)).toTopologicalSpace
  have : ∀ m, PolishSpace (E m) := fun m => (upgradeStandardBorel (E m)).toPolishSpace
  have : ∀ m, BorelSpace (E m) := fun m => (upgradeStandardBorel (E m)).toBorelSpace
  let tF : ∀ m, TopologicalSpace (F m) := fun m => (upgradeStandardBorel (F m)).toTopologicalSpace
  have : ∀ m, PolishSpace (F m) := fun m => (upgradeStandardBorel (F m)).toPolishSpace
  have : ∀ m, BorelSpace (F m) := fun m => (upgradeStandardBorel (F m)).toBorelSpace
  obtain ⟨tX, hpX, hbX, hcX⟩ := exists_polish_continuous f hf
  obtain ⟨tY, hpY, hbY, hcY⟩ := exists_polish_continuous g hg
  let _ := tX
  let _ := tY
  have hev : ∀ m, ∀ᶠ N in atTop, ((⟨π N, inferInstance⟩ : ProbabilityMeasure (X × Y)) : Measure (X × Y)).map
      (Prod.map (f m) (g m)) = ((P₁.prod P₂).withDensity (D m)).map (Prod.map (f m) (g m)) :=
    fun m => (hπ m).mono fun N hN => map_eq_of_rectDens (hf m) (hg m) hN
  obtain ⟨μ, -, hμ₁, hμ₂, hμ⟩ := exists_coupling_of_eventually_map_eq P₁ P₂
    (fun N => (⟨π N, inferInstance⟩ : ProbabilityMeasure (X × Y))) hπ₁ hπ₂
    (fun m => Prod.map (f m) (g m)) (fun m => (hcX m).prodMap (hcY m))
    (fun m => ((P₁.prod P₂).withDensity (D m)).map (Prod.map (f m) (g m))) hev
  exact ⟨μ, inferInstance, hμ₁, hμ₂, fun m => rectDens_of_map_eq (hf m) (hg m) (hD m) (hμ m)⟩

/-- **A.1's countable patch, finite form**: patches `π N` with (1.7) on the rectangles `m ≤ N`. -/
theorem exists_coupling_of_finite_patches [StandardBorelSpace X] [StandardBorelSpace Y]
    (P₁ : Measure X) (P₂ : Measure Y) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {E F : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, StandardBorelSpace (E m)]
    [∀ m, MeasurableSpace (F m)] [∀ m, StandardBorelSpace (F m)]
    (f : ∀ m, X → E m) (g : ∀ m, Y → F m) (hf : ∀ m, Measurable (f m)) (hg : ∀ m, Measurable (g m))
    (D : ℕ → X × Y → ℝ≥0∞) (hD : ∀ m, Measurable (D m))
    (π : ℕ → Measure (X × Y)) [∀ N, IsProbabilityMeasure (π N)]
    (hπ₁ : ∀ N, (π N).map Prod.fst = P₁) (hπ₂ : ∀ N, (π N).map Prod.snd = P₂)
    (hπ : ∀ N m, m ≤ N → RectDens (recSigma f m) (recSigma g m) P₁ P₂ (π N) (D m)) :
    ∃ μ : Measure (X × Y), IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      ∀ m, RectDens (recSigma f m) (recSigma g m) P₁ P₂ μ (D m) :=
  exists_coupling_of_patches P₁ P₂ f g hf hg D hD π hπ₁ hπ₂ fun m =>
    (eventually_ge_atTop m).mono fun N hN => hπ N m hN

end Patch

end InteractingSLE.ZhanGT4.A1Law
