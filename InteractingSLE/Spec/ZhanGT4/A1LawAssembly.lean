/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1LawPatch
import InteractingSLE.Spec.ZhanGT4.A1MargStatement
import InteractingSLE.Spec.ZhanGT4.A1FrozenFamily

/-!
# A.1's law parts: the coupling of the regular marginals, the fibre laws and the image paths

Packet PROVE-A1-LAW (R76). `A1Marg.A1DualCoupling{G3,Eight}MargStatement` asks for regular marginals, a coupling `μ`
and the two law parts `RectLawPart` / `RectLawPartFst`: at every stopping time of the usual augmentation, the density
identity (1.7), the frozen-hull fibre law and the local image path. Source: Astra, *Follow-up 5* §1.3 (L203–L211):
"On each protected rectangle, that construction supplies a continuous joint density `M(s, t)` … optional sampling
gives the density `M(s, τ)` … (1.7) … Conditional Girsanov gives the image SDE. Countable protected-rectangle
exhaustion gives the law up to first contact"; *Follow-up 4* §2.5 item 4 (the finite and the countable patch).

The law parts are assembled from two inputs, in the order of the source:

1. **The finite patches** (A22's seeded staircase (D11)–(D12), follow-up 4 §2.5 item 4): stopped records `f m`, `g m`
   of the two curves on the protected rectangles, densities `D m`, and for every `N` a coupling of the two complete
   marginal laws with (1.7) on the rectangles `m ≤ N`. The countable patch (`A1LawPatch`) turns them into one
   coupling `μ` of the complete marginals with (1.7) on every rectangle.
2. **The frozen-curve families** for every such `μ` (PROVE-A1-FAMILY; the form of PROVE-A1-FROZEN):
   `HasFamilyLaw` — a `FrozenFamily` (the frozen-hull image law at every deterministic frozen time) and, at every
   stopping time of the usual augmentation, its `FamilyRect` data ((1.7) at the stop by optional sampling, the
   stopped-record conditions, the cover of the image lifetime by the caps and the per-cap local image paths); and the
   mirror `HasFamilyLawFst`.

## Main results

* **`rectLawPart_strip_of_family`**, **`rectLawPartFst_lt_of_family`**: for regular marginals, the family input gives
  the law part (the measurability clauses (m1)–(m4) of PROVE-A1-MARG feed PROVE-A1-FROZEN's
  `isRectImageCore_of_family`);
* `PatchInput`, **`exists_coupling_of_patchInput`**: the finite patches give a coupling of the regular marginals with
  (1.7) on every rectangle and with the family input;
* **`A1DualCoupling{G3,Eight}PatchStatement`** (some regular marginals carry the two inputs) and
  **`a1DualCoupling{G3,Eight}MargStatement_of_patch`**, chained to the Rect and Canon statements;
  **`A1DualCoupling{G3,Eight}PatchLawStatement`** (every pair of regular marginals carries them), which gives both the
  patch form and MARG's law form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Law

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg

/-! ### The law parts from the frozen-curve families -/

section Family

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **The frozen-curve family input, conditioning curve on `Y`** (PROVE-A1-FAMILY's output for the coupling `μ`): a
`FrozenFamily` and, at every stopping time of the usual augmentation of the conditioning curve's filtration under its
marginal, the per-stop data `FamilyRect`. -/
def HasFamilyLaw (a : ℝ) (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (𝓕k : Filtration ℝ≥0 mY)
    (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR,
    ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FamilyRect F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})

/-- **The frozen-curve family input, conditioning curve on `X`** (mirror of `HasFamilyLaw`). -/
def HasFamilyLawFst (a : ℝ) (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (𝓕k : Filtration ℝ≥0 mX)
    (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR,
    ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FamilyRectFst F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})

/-- **The law part, conditioning curve on `Y` with live event the strip life of its mark `i₀`**: for regular
marginals, the family input gives `RectLawPart` (PROVE-A1-MARG's (m1)–(m4) and PROVE-A1-FROZEN's
`isRectImageCore_of_family`). -/
theorem rectLawPart_strip_of_family {ak aj a : ℝ} {nLk nRk nLj nRj : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mY} {𝓕j : Filtration ℝ≥0 mX}
    {Wk : ℝ≥0 → Y → ℝ} {VLk : Fin nLk → ℝ≥0 → Y → ℝ} {VRk : Fin nRk → ℝ≥0 → Y → ℝ} {Bk : ℝ≥0 → Y → ℝ}
    {ζk : Y → ℝ≥0∞} {Wj : ℝ≥0 → X → ℝ} {VLj : Fin nLj → ℝ≥0 → X → ℝ} {VRj : Fin nRj → ℝ≥0 → X → ℝ}
    {Bj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₂ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₁ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLk) (xj xk : ℝ)
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (h : HasFamilyLaw a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR) :
    RectLawPart a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  have hcW : ∀ y, ContinuousOn (Wk · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLk i₀ · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.2.1 i₀
  have hm1 := isStronglyProgressive_indicator_isStripLife hk.evol.2.1 hk.progW (hk.progVL i₀) hcW hcV
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  obtain ⟨hm3, hm4⟩ := measurable_rDrv_rLife
    (live := fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) hlive (fun _ _ h => h.1)
    (fun x => (hj.path x).2.2.2.1)
    (fun x => (hj.path x).1) hcW (fun y => (hk.path y).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifetime hj.evol.2.1)
    (measurable_lifetime hk.evol.2.1) xj xk
  exact ((isRectImageCore_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
    (isRectImageCore_of_family (isStronglyProgressive_usualAugmentation hm1 P₂)
      (isStronglyProgressive_usualAugmentation hΘL P₂) (isStronglyProgressive_usualAugmentation hΘR P₂) hm3 hm4
      F hR)).2.2.2.2.2

/-- **The law part, conditioning curve on `X` with live event `t < ζ`** and image lifetime the end of the strip life
of the image curve's mark `i₀`: for regular marginals, the family input gives `RectLawPartFst`. -/
theorem rectLawPartFst_lt_of_family {ak aj a : ℝ} {nLk nRk nLj nRj : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mX} {𝓕j : Filtration ℝ≥0 mY}
    {Wk : ℝ≥0 → X → ℝ} {VLk : Fin nLk → ℝ≥0 → X → ℝ} {VRk : Fin nRk → ℝ≥0 → X → ℝ} {Bk : ℝ≥0 → X → ℝ}
    {ζk : X → ℝ≥0∞} {Wj : ℝ≥0 → Y → ℝ} {VLj : Fin nLj → ℝ≥0 → Y → ℝ} {VRj : Fin nRj → ℝ≥0 → Y → ℝ}
    {Bj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₁ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₂ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLj) (xj xk : ℝ)
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (h : HasFamilyLawFst a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR) :
    RectLawPartFst a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  have hm1 := isStronglyProgressive_indicator_lt hk.evol.2.1
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  have hcW : ∀ y, ContinuousOn (Wj · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLj i₀ · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.2.1 i₀
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife hj.evol.2.1 hj.progW (hj.progVL i₀) hcW hcV)
  obtain ⟨hm3, hm4⟩ := measurable_rDrvFst_rLifeFst
    (live := fun t ω => (t : ℝ≥0∞) < ζk ω) hlive (fun _ _ h => h)
    (fun y => (hcW y).mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) (fun y => (hj.path y).1)
    (fun x => (hk.path x).2.2.2.1) (fun x => (hk.path x).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifeEnd hS) (measurable_lifetime hk.evol.2.1) xj xk
  exact ((isRectImageCoreFst_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
    (isRectImageCoreFst_of_family (isStronglyProgressive_usualAugmentation hm1 P₁)
      (isStronglyProgressive_usualAugmentation hΘL P₁) (isStronglyProgressive_usualAugmentation hΘR P₁) hm3 hm4
      F hR)).2.2.2.2.2

end Family

/-! ### The finite patches give the coupling -/

section Input

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A.1's finite-patch input** (follow-up 4 §2.5 item 4) for the marginals `P₁`, `P₂` and a law property `Law` of
couplings: stopped records `f m`, `g m` into standard Borel spaces (the two curves' records on the protected
rectangle `m`), measurable densities `D m`, and for every `N` a coupling `π N` of `P₁` and `P₂` with the density
identity (1.7) on the rectangles `m ≤ N` (the seeded staircase patch); every coupling of `P₁` and `P₂` with (1.7) on
every rectangle has the property `Law`. -/
def PatchInput (P₁ : Measure X) (P₂ : Measure Y) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (E F : ℕ → Type) (_ : ∀ m, MeasurableSpace (E m)) (_ : ∀ m, StandardBorelSpace (E m))
    (_ : ∀ m, MeasurableSpace (F m)) (_ : ∀ m, StandardBorelSpace (F m)) (f : ∀ m, X → E m) (g : ∀ m, Y → F m)
    (D : ℕ → X × Y → ℝ≥0∞) (π : ℕ → Measure (X × Y)),
    (∀ m, Measurable (f m)) ∧ (∀ m, Measurable (g m)) ∧ (∀ m, Measurable (D m)) ∧
    (∀ N, IsProbabilityMeasure (π N)) ∧ (∀ N, (π N).map Prod.fst = P₁) ∧ (∀ N, (π N).map Prod.snd = P₂) ∧
    (∀ N m, m ≤ N → RectDens (recSigma f m) (recSigma g m) P₁ P₂ (π N) (D m)) ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (recSigma f m) (recSigma g m) P₁ P₂ μ (D m)) → Law μ

/-- **The finite patches give the coupling** (the countable patch, `exists_coupling_of_finite_patches`). -/
theorem exists_coupling_of_patchInput [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X}
    {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {Law : Measure (X × Y) → Prop}
    (h : PatchInput P₁ P₂ Law) :
    ∃ μ : Measure (X × Y), IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧ Law μ := by
  obtain ⟨E, F, _, _, _, _, f, g, D, π, hf, hg, hD, hπ, hπ₁, hπ₂, hdens, hLaw⟩ := h
  obtain ⟨μ, hμ, hμ₁, hμ₂, hμd⟩ := exists_coupling_of_finite_patches P₁ P₂ f g hf hg D hD π hπ₁ hπ₂ hdens
  exact ⟨μ, hμ, hμ₁, hμ₂, hLaw μ hμ hμ₁ hμ₂ hμd⟩

end Input

/-! ### The two configurations of A.1 -/

section Config

/-- **A.1 (G3), patch form**: some regular marginals of the two complete laws (the large curve
`SLE_κ(κ − 4, −4)` with marks `x, y`; the small curve's word) carry the finite-patch input, with the two
frozen-curve family inputs for every coupling with (1.7) on every rectangle. -/
def A1DualCouplingG3PatchStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      PatchInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), patch form.** -/
def A1DualCouplingEightPatchStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      PatchInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **A.1 (G3), patch form for every pair of regular marginals.** -/
def A1DualCouplingG3PatchLawStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      PatchInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), patch form for every pair of regular marginals.** -/
def A1DualCouplingEightPatchLawStatement (κ : ℝ) : Prop :=
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
      PatchInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The patch form gives the marginal form (G3)**: the countable patch gives the coupling, the family inputs give
the two law parts. -/
theorem a1DualCouplingG3MargStatement_of_patch {κ : ℝ} (h : A1DualCouplingG3PatchStatement κ) :
    A1DualCouplingG3MargStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hI⟩ :=
    h hκ4 hκ8 y x hyx hx
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput hI
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, ?_, ?_⟩
  · exact rectLawPart_strip_of_family h₂ h₁ 0 y 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₂.progVL 0) (h₂.progVL 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 1))
            isStronglyProgressive_nil))) hl₁
  · exact rectLawPartFst_lt_of_family h₁ h₂ 0 0 y
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 1) (h₁.progVR 2))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 2))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 2))
            (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 2))
              isStronglyProgressive_nil))))
      (isStronglyProgressive_const _ _) hl₂

/-- **The patch form gives the marginal form (Eight).** -/
theorem a1DualCouplingEightMargStatement_of_patch {κ : ℝ} (h : A1DualCouplingEightPatchStatement κ) :
    A1DualCouplingEightMargStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hI⟩ :=
    h hκ8 x hx
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput hI
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, ?_, ?_⟩
  · exact rectLawPart_strip_of_family h₂ h₁ 0 x 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 0))
          isStronglyProgressive_nil)) hl₁
  · exact rectLawPartFst_lt_of_family h₁ h₂ 0 0 x
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 1))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 1))
            isStronglyProgressive_nil)))
      (isStronglyProgressive_const _ _) hl₂

/-- **The patch law form gives MARG's law form (G3).** -/
theorem a1DualCouplingG3LawStatement_of_patchLaw {κ : ℝ} (h : A1DualCouplingG3PatchLawStatement κ) :
    A1DualCouplingG3LawStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput
    (h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)
  refine ⟨μ, hμ, hm₁, hm₂, ?_, ?_⟩
  · exact rectLawPart_strip_of_family h₂ h₁ 0 y 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₂.progVL 0) (h₂.progVL 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 1))
            isStronglyProgressive_nil))) hl₁
  · exact rectLawPartFst_lt_of_family h₁ h₂ 0 0 y
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 1) (h₁.progVR 2))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 2))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 2))
            (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 2))
              isStronglyProgressive_nil))))
      (isStronglyProgressive_const _ _) hl₂

/-- **The patch law form gives MARG's law form (Eight).** -/
theorem a1DualCouplingEightLawStatement_of_patchLaw {κ : ℝ} (h : A1DualCouplingEightPatchLawStatement κ) :
    A1DualCouplingEightLawStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput
    (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)
  refine ⟨μ, hμ, hm₁, hm₂, ?_, ?_⟩
  · exact rectLawPart_strip_of_family h₂ h₁ 0 x 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 0))
          isStronglyProgressive_nil)) hl₁
  · exact rectLawPartFst_lt_of_family h₁ h₂ 0 0 x
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 1))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 1))
            isStronglyProgressive_nil)))
      (isStronglyProgressive_const _ _) hl₂

/-- **The patch law form gives the patch form (G3)** (the regular marginals exist: `exists_regMarginals_G3`). -/
theorem a1DualCouplingG3PatchStatement_of_patchLaw {κ : ℝ} (h : A1DualCouplingG3PatchLawStatement κ) :
    A1DualCouplingG3PatchStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_G3 hκ4 hyx hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    h₂, h₁, h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁
      h₂ h₁⟩

/-- **The patch law form gives the patch form (Eight).** -/
theorem a1DualCouplingEightPatchStatement_of_patchLaw {κ : ℝ} (h : A1DualCouplingEightPatchLawStatement κ) :
    A1DualCouplingEightPatchStatement κ := by
  intro hκ8 x hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_Eight hκ8 hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    h₂, h₁, h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁
      h₂ h₁⟩

/-- **R76's Rect statement (G3) from the patch form.** -/
theorem a1DualCouplingG3RectStatement_of_patch {κ : ℝ} (h : A1DualCouplingG3PatchStatement κ) :
    A1DualCouplingG3RectStatement κ :=
  a1DualCouplingG3RectStatement_of_marg (a1DualCouplingG3MargStatement_of_patch h)

/-- **R76's Rect statement (Eight) from the patch form.** -/
theorem a1DualCouplingEightRectStatement_of_patch {κ : ℝ} (h : A1DualCouplingEightPatchStatement κ) :
    A1DualCouplingEightRectStatement κ :=
  a1DualCouplingEightRectStatement_of_marg (a1DualCouplingEightMargStatement_of_patch h)

/-- **R72's Canon statement (G3) from the patch form.** -/
theorem a1DualCouplingG3CanonStatement_of_patch {κ : ℝ} (h : A1DualCouplingG3PatchStatement κ) :
    A1Ref.A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_marg (a1DualCouplingG3MargStatement_of_patch h)

/-- **R72's Canon statement (Eight) from the patch form.** -/
theorem a1DualCouplingEightCanonStatement_of_patch {κ : ℝ} (h : A1DualCouplingEightPatchStatement κ) :
    A1Ref.A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_marg (a1DualCouplingEightMargStatement_of_patch h)

end Config

end InteractingSLE.ZhanGT4.A1Law
