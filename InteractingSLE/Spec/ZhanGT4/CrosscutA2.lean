/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA2Pair

/-!
# A.2 for the two configurations of A.3, from A.1's dual coupling

Packet PROVE-ZHAN-GT4-A2X. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L510–L617; R38, R53). A.2's proof (L524–L602) has three parts and
a final Jordan step:

1. (L524–L536) "The small curve is simple before its first force collision … Thus the small curve `J` is a crosscut with
   its other endpoint strictly in `(x₂, p₂)`" — **`A2SmallCrosscut*Statement`** (a statement about the small marginal);
2. (L537–L561) "Condition on a stopped large-curve prefix … This shows that the entire large hull lies on the bounded
   side of `J`. The following countable argument makes the conditioning legitimate …" — **`A2HullInside*Statement`**;
3. (L563–L598) "Conversely, condition on a small-curve prefix … Countably many capped rational times exhaust the small
   curve; continuity gives `J ⊂ S`" — **`A2SmallInHull*Statement`**;
4. (L599–L602) "`J ⊂ S ⊂ D(J)` … Jordan separation now identifies the outer boundary of `S` with `J ∩ ℍ`" — A18's
   `IsCrosscutDomain.outerBoundary_eq`.

Parts 2 and 3 are stated for every dual pair (`IsA2DualPairG3`, `IsA2DualPairEight`): they use A.1's conditional image
laws. A.1 itself is the named hypothesis **`A1DualCouplingG3Statement`** / **`A1DualCouplingEightStatement`**: over
every given large-curve evolution on `(Ω, P)` there is a Markov kernel `K : Ω → Ω'` and, on `(Ω × Ω', P ⊗ₘ K)`, a
small curve forming a dual pair with the pulled-back large curve. This is A.1's "coupling of these two marginal laws"
realized over the given large curve (gluing the coupling to the given marginal by disintegration); with it the almost
sure conclusion passes back to `P` without any measurability of the crosscut event
(`ae_of_ae_compProd_fst`, from Mathlib's `Measure.ae_ae_of_ae_compProd`).

## Main results

* `outerBoundary_eq_of_inside`: the Jordan step in the form used here;
* `ae_of_ae_compProd_fst`: an almost sure property of the first coordinate under `P ⊗ₘ K` holds `P`-almost surely
  (no measurability needed);
* **`fourForceCrosscutG3LifeStatement_of_dual`**: `A34.FourForceCrosscutG3LifeStatement κ` from A.1 and parts 1–3;
* **`threeForceCrosscutEightStatement_of_dual`**: `A35.ThreeForceCrosscutEightStatement κ` from A.1 and parts 1–3;
* `firstSwallowCrosscutStatement_of_dual`: A.3 (`FirstSwallowCrosscutStatement κ`) from the same inputs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X

open QuantumZipper

/-! ### The small crosscut -/

/-- **The small curve as a crosscut** (A.2 L524–L536): `γ` is a simple crosscut of `ℍ` from the small source `x₁` to a
positive point (a point of `(x₂, p₂) = (0, ∞)`), and its open part is the small curve's trace over its open lifetime
(`η` a continuous generating trace of the centred small driver `w₁` up to `ζ₁`, translated by `x₁`). -/
def IsSmallCrosscut (x₁ : ℝ) (w₁ : ℝ≥0 → ℝ) (ζ₁ : ℝ≥0∞) (γ : ℝ → ℂ) : Prop :=
  IsRealCrosscut γ ∧ (γ 0).re = x₁ ∧ 0 < (γ 1).re ∧
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w₁ ζ₁ η ∧
      γ '' Ioo 0 1 = (fun z : ℂ => z + x₁) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁})

/-! ### The (G3) configuration: A.1 and the three parts of A.2 -/

/-- **A.1 in the (G3) configuration, over a given large curve** (§A.1 L160–L187 with §A.3.2 L697–L705): for
`4 < κ < 8`, `y < x < 0` and every integrated `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)` on `(Ω, P)`, there are a
Markov kernel `K : Ω → Ω'` and, on `(Ω × Ω', P ⊗ₘ K)`, filtrations and a small curve forming with the pulled-back large
curve the dual pair `IsA2DualPairG3` (both marginals, both conditional image laws up to contact). -/
def A1DualCouplingG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₁ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₁ : Ω × Ω' → ℝ≥0∞),
            IsA2DualPairG3 κ y x (P ⊗ₘ K) 𝓕₂ (fun t z => W t z.1) (fun i t z => VL i t z.1)
              (fun i t z => VR i t z.1) (fun t z => B t z.1) (fun z => ζ z.1) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.2, part 1, (G3)** (L524–L536, with §A.3.2 L702–L705: "Its terminal endpoint is positive by the small-parameter
strip theorem"): every integrated `SLE_{κ̂}` evolution of the (G3) small word (`κ̂ = 16/κ`; source `y`, seeds `y∓`,
marks `x`, `0`) is almost surely a simple crosscut from `y` to a positive point. -/
def A2SmallCrosscutG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 3 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ γ : ℝ → ℂ, IsSmallCrosscut y (W · ω) (ζ ω) γ

/-- **A.2, part 2, (G3)** (L537–L561): for every (G3) dual pair, almost surely the large hull before its first force
collision lies in the closed bounded side of the small crosscut (it misses the unbounded side `D`). -/
def A2HullInsideG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 3, (G3)** (L563–L598): for every (G3) dual pair, almost surely the small crosscut lies in the closure
of the large hulls before the first force collision (`J ⊂ S`). -/
def A2SmallInHullG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
          γ '' Ioo 0 1 ⊆ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)

/-! ### The (Eight) configuration: A.1 and the three parts of A.2 -/

/-- **A.1 in the (Eight) configuration, over a given large curve** (§A.1 with §A.3.1 L657–L670): for `κ ≥ 8`,
`x < 0` and every integrated evolution from `(0; x)` with weight `0` on `(Ω, P)`, there are a Markov kernel
`K : Ω → Ω'` and, on `(Ω × Ω', P ⊗ₘ K)`, a small curve forming with the pulled-back large curve the dual pair
`IsA2DualPairEight`. -/
def A1DualCouplingEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕 W VL VR B ζ →
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (K : Kernel Ω Ω'), IsMarkovKernel K ∧
          ∃ (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω'))) (W₁ : ℝ≥0 → Ω × Ω' → ℝ)
            (VL₁ : Fin 1 → ℝ≥0 → Ω × Ω' → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω × Ω' → ℝ) (B₁ : ℝ≥0 → Ω × Ω' → ℝ)
            (ζ₁ : Ω × Ω' → ℝ≥0∞),
            IsA2DualPairEight κ x (P ⊗ₘ K) 𝓕₂ (fun t z => W t z.1) (fun i t z => VL i t z.1)
              (fun i t z => VR i t z.1) (fun t z => B t z.1) (fun z => ζ z.1) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁

/-- **A.2, part 1, (Eight)** (L524–L536 with §A.3.1 L666–L670): every integrated `SLE_{κ̂}` evolution of the (Eight)
small word (source `x`, seeds `x∓`, mark `0`) is almost surely a simple crosscut from `x` to a positive point. -/
def A2SmallCrosscutEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ γ : ℝ → ℂ, IsSmallCrosscut x (W · ω) (ζ ω) γ

/-- **A.2, part 2, (Eight)** (L537–L561). -/
def A2HullInsideEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
          ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint (lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) D

/-- **A.2, part 3, (Eight)** (L563–L598). -/
def A2SmallInHullEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ᵐ ω ∂P, ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
          γ '' Ioo 0 1 ⊆ lifeHullClosure (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)

/-! ### The Jordan step and the transfer -/

/-- **A.2's Jordan step** (L599–L602): `J ⊂ S` and `S` inside the closed bounded side of `J` identify the outer
boundary of `S` with `J`. -/
theorem outerBoundary_eq_of_inside {S : Set ℂ} {γ : ℝ → ℂ} (hJS : γ '' Ioo 0 1 ⊆ S)
    (hD : ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint S D) : outerBoundary S = γ '' Ioo 0 1 := by
  obtain ⟨D, hD, hSD⟩ := hD
  exact hD.outerBoundary_eq hJS hSD

/-- **An almost sure property of the first coordinate passes from `P ⊗ₘ K` to `P`**, for a Markov kernel `K` and with
no measurability of the property (Mathlib's `Measure.ae_ae_of_ae_compProd` uses a measurable null superset). -/
theorem ae_of_ae_compProd_fst {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} [SFinite P]
    {K : Kernel Ω Ω'} [IsMarkovKernel K] {Q : Ω → Prop} (h : ∀ᵐ z ∂(P ⊗ₘ K), Q z.1) : ∀ᵐ ω ∂P, Q ω := by
  filter_upwards [Measure.ae_ae_of_ae_compProd (p := fun z => Q z.1) h] with ω hω
  have : (ae (K ω)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨_, hQ⟩ := hω.exists
  exact hQ

/-- The pointwise assembly of the three parts. -/
theorem exists_outerBoundary_eq_of_parts {x₁ : ℝ} {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {S : Set ℂ}
    (h1 : ∃ γ : ℝ → ℂ, IsSmallCrosscut x₁ w₁ ζ₁ γ)
    (h2 : ∀ γ : ℝ → ℂ, IsSmallCrosscut x₁ w₁ ζ₁ γ → ∃ D : Set ℂ, IsCrosscutDomain D γ ∧ Disjoint S D)
    (h3 : ∀ γ : ℝ → ℂ, IsSmallCrosscut x₁ w₁ ζ₁ γ → γ '' Ioo 0 1 ⊆ S) :
    ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x₁ ∧ 0 < (γ 1).re ∧ outerBoundary S = γ '' Ioo 0 1 := by
  obtain ⟨γ, hγ⟩ := h1
  exact ⟨γ, hγ.1, hγ.2.1, hγ.2.2.1, outerBoundary_eq_of_inside (h3 γ hγ) (h2 γ hγ)⟩

/-! ### The two A.2 statements -/

/-- **A.2 in the (G3) configuration over the strip life** (`A34.FourForceCrosscutG3LifeStatement κ`) from A.1
(`A1DualCouplingG3Statement`) and A.2's three parts. -/
theorem fourForceCrosscutG3LifeStatement_of_dual {κ : ℝ} (hA1 : A1DualCouplingG3Statement.{u} κ)
    (h1 : A2SmallCrosscutG3Statement.{u} κ) (h2 : A2HullInsideG3Statement.{u} κ)
    (h3 : A2SmallInHullG3Statement.{u} κ) : A34.FourForceCrosscutG3LifeStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ := hA1 hκ4 hκ8 y x hyx hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  have hS2 := h2 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ _ _ _ _ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ4 hκ8 y x hyx hx (P ⊗ₘ K) 𝓕₂ _ _ _ _ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3] with z hz1 hz2 hz3
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.2's three-force version in the (Eight) configuration** (`A35.ThreeForceCrosscutEightStatement κ`) from A.1
(`A1DualCouplingEightStatement`) and A.2's three parts. -/
theorem threeForceCrosscutEightStatement_of_dual {κ : ℝ} (hA1 : A1DualCouplingEightStatement.{u} κ)
    (h1 : A2SmallCrosscutEightStatement.{u} κ) (h2 : A2HullInsideEightStatement.{u} κ)
    (h3 : A2SmallInHullEightStatement.{u} κ) : A35.ThreeForceCrosscutEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕 W VL VR B ζ hE
  obtain ⟨Ω', mΩ', K, hK, 𝓕₂, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩ := hA1 hκ8 x hx P 𝓕 W VL VR B ζ hE
  have hS1 := h1 hκ8 x hx (P ⊗ₘ K) 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  have hS2 := h2 hκ8 x hx (P ⊗ₘ K) 𝓕₂ _ _ _ _ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hS3 := h3 hκ8 x hx (P ⊗ₘ K) 𝓕₂ _ _ _ _ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  refine ae_of_ae_compProd_fst (K := K) (Q := fun ω => ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧
    0 < (γ 1).re ∧ outerBoundary (lifeHullClosure (W · ω) (VL 0 · ω) (ζ ω)) = γ '' Ioo 0 1) ?_
  filter_upwards [hS1, hS2, hS3] with z hz1 hz2 hz3
  exact exists_outerBoundary_eq_of_parts hz1 hz2 hz3

/-- **A.3 for every `κ`** (`FirstSwallowCrosscutStatement κ`) from A.1 and A.2's three parts in both configurations
(through `A35.firstSwallowCrosscutStatement_of_A2`). -/
theorem firstSwallowCrosscutStatement_of_dual {κ : ℝ} (hA1 : A1DualCouplingG3Statement.{0} κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightStatement.{u} κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A35.firstSwallowCrosscutStatement_of_A2 (fourForceCrosscutG3LifeStatement_of_dual hA1 h1 h2 h3)
    (threeForceCrosscutEightStatement_of_dual hA1' h1' h2' h3')

/-- `hA2` of `Wire.theorem13Statement_of_open7_partA` from A.1 and A.2's three parts, (G3), for all parameters. -/
theorem forall_fourForceCrosscutG3LifeStatement_of_dual (hA1 : ∀ κ : ℝ, A1DualCouplingG3Statement.{u} κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutG3Statement.{u} κ) (h2 : ∀ κ : ℝ, A2HullInsideG3Statement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullG3Statement.{u} κ) : ∀ κ : ℝ, A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fun κ => fourForceCrosscutG3LifeStatement_of_dual (hA1 κ) (h1 κ) (h2 κ) (h3 κ)

/-- `hA2'` of `Wire.theorem13Statement_of_open7_partA` from A.1 and A.2's three parts, (Eight), for all parameters. -/
theorem forall_threeForceCrosscutEightStatement_of_dual (hA1 : ∀ κ : ℝ, A1DualCouplingEightStatement.{u} κ)
    (h1 : ∀ κ : ℝ, A2SmallCrosscutEightStatement.{u} κ) (h2 : ∀ κ : ℝ, A2HullInsideEightStatement.{u} κ)
    (h3 : ∀ κ : ℝ, A2SmallInHullEightStatement.{u} κ) : ∀ κ : ℝ, A35.ThreeForceCrosscutEightStatement.{u} κ :=
  fun κ => threeForceCrosscutEightStatement_of_dual (hA1 κ) (h1 κ) (h2 κ) (h3 κ)

end InteractingSLE.ZhanGT4.A2X
