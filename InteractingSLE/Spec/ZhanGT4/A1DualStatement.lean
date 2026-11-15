/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1DualGlue
import InteractingSLE.Spec.ZhanGT4.CrosscutA2
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Swallow

/-!
# A.1 over a given large curve, as a version; reduction to one reference coupling; A.2 and A.3 rewired

Packet PROVE-ZHAN-A1DUAL. Source: Astra, *Follow-up proofs*, §A.1 L183–L187 (R38): "There is a coupling of these two
marginal laws such that, conditionally on any stopping-time prefix of curve `k`, curve `j`, mapped by the hydrodynamic
map of that prefix and stopped on first contact with it, has the corresponding force-point law".

**Why a successor of `A2X.A1DualCouplingG3Statement`.** That statement requires the dual pair on `Ω × Ω'` for the
given large processes read literally (`fun t z => W t z.1`, …). Its conditional image law (`A2X.IsCondImageLaw`, through
`Restart.StoppedK2.IsRandomWordEvolutionUpTo`) demands, at every stopping time `τ` — e.g. a constant one — that the
image word `![0, V_x(τ) − V_y(τ), W(τ) − V_y(τ)]` be measurable. An integrated evolution constrains `W`, `V` only
before its lifetime (`AdaptedBefore`, `IsIntegratedSLEPath`), so a given large curve may carry non-measurable values
after it, and then no dual pair over it exists (see the handoff for the explicit configuration). The source speaks of
laws, which do not see such values. `A1DualCouplingG3VerStatement` therefore asks for the dual pair over **a version**
of the given large curve: a large curve on `Ω × Ω'` that almost surely has the same lifetime and agrees with the given
one at every time before it (`IsFstVersion`). This is all A.2 uses (`lifeHullClosure_congr`); the old statement implies
the new one (`a1DualCouplingG3VerStatement_of_old`).

**The reduction.** `A1DualCouplingG3RefStatement` is A.1 on ONE standard Borel probability space (the form the A.1
construction produces). `a1DualCouplingG3VerStatement_of_ref` glues it over every given large curve: the kernel of
`A1DualGlue` (the reference sample given the large record) and the pullback of `A1DualComap` along the second
projection (surjective, measure-preserving).

## Main results

* `IsFstVersion`, `A1DualCouplingG3VerStatement`, `A1DualCouplingEightVerStatement` (successors) and
  `A1DualCouplingG3RefStatement`, `A1DualCouplingEightRefStatement` (one reference coupling);
* **`a1DualCouplingG3VerStatement_of_ref`**, **`a1DualCouplingEightVerStatement_of_ref`** (steps (a)–(b));
* `a1DualCouplingG3VerStatement_of_old`, `a1DualCouplingEightVerStatement_of_old`;
* `lifeHullClosure_congr`; the rewired consumers `fourForceCrosscutG3LifeStatement_of_dualVer`,
  `threeForceCrosscutEightStatement_of_dualVer`, `firstSwallowCrosscutStatement_of_dualVer`, their `∀ κ` forms, and
  the same from the reference statements (`…_of_ref`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A1Dual

open QuantumZipper A2X Coupling

/-! ### Versions of the large curve -/

/-- **A version of a large curve on `Ω × Ω'`**: almost surely under `Q`, the curve `(W₂, VL₂, VR₂, B₂, ζ₂)` has the
lifetime of the given curve `(W, VL, VR, B, ζ)` read on the first coordinate and agrees with it at every time before
that lifetime. -/
def IsFstVersion {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {nL nR : ℕ} (Q : Measure (Ω × Ω'))
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (W₂ : ℝ≥0 → Ω × Ω' → ℝ) (VL₂ : Fin nL → ℝ≥0 → Ω × Ω' → ℝ) (VR₂ : Fin nR → ℝ≥0 → Ω × Ω' → ℝ)
    (B₂ : ℝ≥0 → Ω × Ω' → ℝ) (ζ₂ : Ω × Ω' → ℝ≥0∞) : Prop :=
  ∀ᵐ z ∂Q, ζ₂ z = ζ z.1 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ z.1 →
    W₂ t z = W t z.1 ∧ (∀ i, VL₂ i t z = VL i t z.1) ∧ (∀ j, VR₂ j t z = VR j t z.1) ∧ B₂ t z = B t z.1

theorem isFstVersion_self {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {nL nR : ℕ}
    (Q : Measure (Ω × Ω')) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    IsFstVersion Q W VL VR B ζ (fun t z => W t z.1) (fun i t z => VL i t z.1) (fun j t z => VR j t z.1)
      (fun t z => B t z.1) (fun z => ζ z.1) :=
  Eventually.of_forall fun _ => ⟨rfl, fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩⟩

/-- **The large hull before the first force collision depends only on the curve before its lifetime.** -/
theorem lifeHullClosure_congr {w w' v v' : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞} (hζ : ζ' = ζ)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w' t = w t) (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v' t = v t) :
    lifeHullClosure w' v' ζ' = lifeHullClosure w v ζ := by
  subst hζ
  have hlife : ∀ t, Strip.IsStripLife w' v' ζ' t ↔ Strip.IsStripLife w v ζ' t := fun t => by
    have key : ∀ r ≤ t, (t : ℝ≥0∞) < ζ' → (v' r < w' r ↔ v r < w r) := fun r hr ht => by
      have hr' : (r : ℝ≥0∞) < ζ' := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht
      rw [hw r hr', hv r hr']
    exact ⟨fun h => ⟨h.1, fun r hr => (key r hr h.1).1 (h.2 r hr)⟩,
      fun h => ⟨h.1, fun r hr => (key r hr h.1).2 (h.2 r hr)⟩⟩
  have hhull : ∀ t, Strip.IsStripLife w v ζ' t →
      fwdHull (fun s : ℝ => w' s.toNNReal) t = fwdHull (fun s : ℝ => w s.toNNReal) t := fun t ht => by
    obtain ⟨T, hT1, hT2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht.1
    refine A34.fwdHull_congr_of_lt t.coe_nonneg (T₀ := T) (by exact_mod_cast ENNReal.coe_lt_coe.1 hT1) fun r hr => ?_
    have h1 : r.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe hr.1).2 hr.2
    exact hw _ ((ENNReal.coe_lt_coe.2 h1).trans hT2)
  unfold lifeHullClosure
  congr 1
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, (hlife t).1 ht, (hhull t ((hlife t).1 ht)) ▸ hz⟩
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, (hlife t).2 ht, (hhull t ht).symm ▸ hz⟩

/-! ### The large words are ordered -/

theorem isOrderedForceWord_largeG3 {y x : ℝ} (hyx : y < x) (hx : x < 0) :
    IsOrderedForceWord (![x, y] : Fin 2 → ℝ) (![] : Fin 0 → ℝ) := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · (fin_cases i <;> fin_cases j <;> simp_all); linarith
  · fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> linarith

theorem isOrderedForceWord_largeEight {x : ℝ} (hx : x < 0) :
    IsOrderedForceWord (![x] : Fin 1 → ℝ) (![] : Fin 0 → ℝ) := by
  refine ⟨fun i j _ => ?_, fun i => ?_, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · fin_cases i; fin_cases j; exact le_rfl
  · fin_cases i; simpa using hx.le

/-! ### The statements -/

/-- **A.1 in the (G3) configuration over a version of a given large curve** (successor of
`A2X.A1DualCouplingG3Statement`): for `4 < κ < 8`, `y < x < 0` and every integrated `SLE_κ(κ − 4, −4)` evolution from
`(0; x, y)` on `(Ω, P)`, there are a Markov kernel `K : Ω → Ω'` and, on `(Ω × Ω', P ⊗ₘ K)`, a version of the large
curve (`IsFstVersion`), filtrations and a small curve forming the dual pair `IsA2DualPairG3`. -/
def A1DualCouplingG3VerStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₂ : Fin 2 → ℝ≥0 → Ω × Ω' → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω × Ω' → ℝ) (B₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₂ : Ω × Ω' → ℝ≥0∞) (W₁ : ℝ≥0 → Ω × Ω' → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ)
            (VR₁ : Fin 3 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ) (ζ₁ : Ω × Ω' → ℝ≥0∞),
            IsFstVersion (P ⊗ₘ K) W VL VR B ζ W₂ VL₂ VR₂ B₂ ζ₂ ∧
              IsA2DualPairG3 κ y x (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 in the (Eight) configuration over a version of a given large curve** (successor of
`A2X.A1DualCouplingEightStatement`). -/
def A1DualCouplingEightVerStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₂ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω × Ω' → ℝ) (B₂ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₂ : Ω × Ω' → ℝ≥0∞) (W₁ : ℝ≥0 → Ω × Ω' → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ)
            (VR₁ : Fin 2 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ) (ζ₁ : Ω × Ω' → ℝ≥0∞),
            IsFstVersion (P ⊗ₘ K) W VL VR B ζ W₂ VL₂ VR₂ B₂ ζ₂ ∧
              IsA2DualPairEight κ x (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 in the (G3) configuration on one reference space** (§A.1 L183–L187: "There is a coupling of these two
marginal laws such that …"): a standard Borel probability space carrying the (G3) dual pair. -/
def A1DualCouplingG3RefStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairG3 κ y x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.1 in the (Eight) configuration on one reference space.** -/
def A1DualCouplingEightRefStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairEight κ x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-! ### The old statements imply the new ones -/

theorem a1DualCouplingG3VerStatement_of_old {κ : ℝ} (h : A1DualCouplingG3Statement.{u} κ) :
    A1DualCouplingG3VerStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ := h hκ4 hκ8 y x hyx hx P 𝓕 W VL VR B ζ hE
  exact ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, _, _, _, _, _, W₁, VL₁, VR₁, B₁, ζ₁, isFstVersion_self _ W VL VR B ζ, hpair⟩

theorem a1DualCouplingEightVerStatement_of_old {κ : ℝ} (h : A1DualCouplingEightStatement.{u} κ) :
    A1DualCouplingEightVerStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ := h hκ8 x hx P 𝓕 W VL VR B ζ hE
  exact ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, _, _, _, _, _, W₁, VL₁, VR₁, B₁, ζ₁, isFstVersion_self _ W VL VR B ζ, hpair⟩

/-! ### The reduction to one reference coupling -/

/-- **A.1 (G3) over every given large curve, from one reference coupling** (A2X "What remains" 1(a)–(b)). -/
theorem a1DualCouplingG3VerStatement_of_ref {κ : ℝ} (h : A1DualCouplingG3RefStatement κ) :
    A1DualCouplingG3VerStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ :=
    h hκ4 hκ8 y x hyx hx
  obtain ⟨K, hK, hsnd, hver⟩ :=
    exists_glue_version.{u} (by linarith : (0 : ℝ) < κ) (isOrderedForceWord_largeG3 hyx hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  exact ⟨ULift.{u} Ω₀, inferInstance, K, hK, filtrationComap 𝓕₂ hπ, filtrationComap 𝓕₁ hπ,
    fun t z => W₂ t z.2.down, fun i t z => VL₂ i t z.2.down, fun i t z => VR₂ i t z.2.down,
    fun t z => B₂ t z.2.down, fun z => ζ₂ z.2.down, fun t z => W₁ t z.2.down, fun i t z => VL₁ i t z.2.down,
    fun i t z => VR₁ i t z.2.down, fun t z => B₁ t z.2.down, fun z => ζ₁ z.2.down, hver,
    IsA2DualPairG3.comap hπ hs hsnd hpair⟩

/-- **A.1 (Eight) over every given large curve, from one reference coupling.** -/
theorem a1DualCouplingEightVerStatement_of_ref {κ : ℝ} (h : A1DualCouplingEightRefStatement κ) :
    A1DualCouplingEightVerStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ := h hκ8 x hx
  obtain ⟨K, hK, hsnd, hver⟩ :=
    exists_glue_version.{u} (by linarith : (0 : ℝ) < κ) (isOrderedForceWord_largeEight hx) hE hpair.1
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := P)
  have hπ : Measurable fun z : Ω × ULift.{u} Ω₀ => z.2.down := measurable_down.comp measurable_snd
  have hs : Function.Surjective fun z : Ω × ULift.{u} Ω₀ => z.2.down :=
    fun ω₀ => ⟨(Classical.arbitrary Ω, ⟨ω₀⟩), rfl⟩
  exact ⟨ULift.{u} Ω₀, inferInstance, K, hK, filtrationComap 𝓕₂ hπ, filtrationComap 𝓕₁ hπ,
    fun t z => W₂ t z.2.down, fun i t z => VL₂ i t z.2.down, fun i t z => VR₂ i t z.2.down,
    fun t z => B₂ t z.2.down, fun z => ζ₂ z.2.down, fun t z => W₁ t z.2.down, fun i t z => VL₁ i t z.2.down,
    fun i t z => VR₁ i t z.2.down, fun t z => B₁ t z.2.down, fun z => ζ₁ z.2.down, hver,
    IsA2DualPairEight.comap hπ hs hsnd hpair⟩

/-! ### A.2 and A.3 from the successor statements -/

/-- **A.2 in the (G3) configuration** (`A34.FourForceCrosscutG3LifeStatement κ`) from A.1 over a version and A.2's
three parts (the same three parts as in `A2X.fourForceCrosscutG3LifeStatement_of_dual`). -/
theorem fourForceCrosscutG3LifeStatement_of_dualVer {κ : ℝ} (hA1 : A1DualCouplingG3VerStatement.{u} κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (h2 : A2HullInsideG3Statement.{u} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hver, hpair⟩ :=
    hA1 hκ4 hκ8 y x hyx hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  have hS2 := h2 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z) (VL₂ 0 · z) (ζ₂ z) = lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.2's three-force version in the (Eight) configuration** (`A35.ThreeForceCrosscutEightStatement κ`) from A.1 over
a version and A.2's three parts. -/
theorem threeForceCrosscutEightStatement_of_dualVer {κ : ℝ} (hA1 : A1DualCouplingEightVerStatement.{u} κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (h2 : A2HullInsideEightStatement.{u} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hver, hpair⟩ :=
    hA1 hκ8 x hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ8 x hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  have hS2 := h2 hκ8 x hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ8 x hx (P ⊗ₘ K) 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3, hver] with z hz1 hz2 hz3 hzv
  have e : lifeHullClosure (W₂ · z) (VL₂ 0 · z) (ζ₂ z) = lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1) :=
    lifeHullClosure_congr hzv.1 (fun t ht => (hzv.2 t ht).1) (fun t ht => (hzv.2 t ht).2.1 0)
  show ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧ 0 < (γ 1).re ∧
    outerBoundary (lifeHullClosure (W · z.1) (VL 0 · z.1) (ζ z.1)) = γ '' Ioo 0 1
  rw [← e]
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.3** (`FirstSwallowCrosscutStatement κ`) from A.1 over versions and A.2's three parts in both configurations. -/
theorem firstSwallowCrosscutStatement_of_dualVer {κ : ℝ} (hA1 : A1DualCouplingG3VerStatement.{0} κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightVerStatement.{u} κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A35.firstSwallowCrosscutStatement_of_A2 (fourForceCrosscutG3LifeStatement_of_dualVer hA1 h1 h2 h3)
    (threeForceCrosscutEightStatement_of_dualVer hA1' h1' h2' h3')

/-- `hA2` of `Wire.theorem13Statement_of_open7_partA` from A.1 over versions and A.2's parts, (G3), all `κ`. -/
theorem forall_fourForceCrosscutG3LifeStatement_of_dualVer (hA1 : ∀ κ : ℝ, A1DualCouplingG3VerStatement.{u} κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutG3Statement.{u} κ) (h2 : ∀ κ : ℝ, A2HullInsideG3Statement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullG3Statement.{u} κ) : ∀ κ : ℝ, A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fun κ => fourForceCrosscutG3LifeStatement_of_dualVer (hA1 κ) (h1 κ) (h2 κ) (h3 κ)

/-- `hA2'` of `Wire.theorem13Statement_of_open7_partA` from A.1 over versions and A.2's parts, (Eight), all `κ`. -/
theorem forall_threeForceCrosscutEightStatement_of_dualVer (hA1 : ∀ κ : ℝ, A1DualCouplingEightVerStatement.{u} κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutEightStatement.{u} κ) (h2 : ∀ κ : ℝ, A2HullInsideEightStatement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullEightStatement.{u} κ) : ∀ κ : ℝ, A35.ThreeForceCrosscutEightStatement.{u} κ :=
  fun κ => threeForceCrosscutEightStatement_of_dualVer (hA1 κ) (h1 κ) (h2 κ) (h3 κ)

/-- **A.2 (G3) from one reference coupling and A.2's three parts.** -/
theorem fourForceCrosscutG3LifeStatement_of_ref {κ : ℝ} (hA1 : A1DualCouplingG3RefStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (h2 : A2HullInsideG3Statement.{u} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fourForceCrosscutG3LifeStatement_of_dualVer (a1DualCouplingG3VerStatement_of_ref hA1) h1 h2 h3

/-- **A.2 (Eight) from one reference coupling and A.2's three parts.** -/
theorem threeForceCrosscutEightStatement_of_ref {κ : ℝ} (hA1 : A1DualCouplingEightRefStatement κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (h2 : A2HullInsideEightStatement.{u} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ :=
  threeForceCrosscutEightStatement_of_dualVer (a1DualCouplingEightVerStatement_of_ref hA1) h1 h2 h3

/-- **A.3 from the two reference couplings and A.2's three parts.** -/
theorem firstSwallowCrosscutStatement_of_ref {κ : ℝ} (hA1 : A1DualCouplingG3RefStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightRefStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  firstSwallowCrosscutStatement_of_dualVer (a1DualCouplingG3VerStatement_of_ref hA1) h1 h2 h3
    (a1DualCouplingEightVerStatement_of_ref hA1') h1' h2' h3'

end InteractingSLE.ZhanGT4.A1Dual
