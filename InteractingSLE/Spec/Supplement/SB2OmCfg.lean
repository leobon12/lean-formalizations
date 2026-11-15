/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2OmCore
import InteractingSLE.Spec.Supplement.SB2BqCfg

/-!
# SB2(2)'s configuration record from the S2 data in B's stage coordinates

Packet PROVE-GW2-GEOM2, round 9 (PROVE-SB2-LCMEAN's handoff R13.8, item 1). The record `Om.IsCfg` of `SB2OmCore` is
produced by the bridge builder (`Bq.isRelConfigJK_of_bridgePath_noTip`, R120's F1) applied to the S2 data of B's
stage, read in SB2(1)'s (reflected) orientation, and reflected back (`Lm.isRelConfigJKL_of_reflect`):

* `markPosL_neg`, `markPos_neg`: the mark positions of the negated driver at negated points;
* **`isBoundedHarmonicExtension_reflect_flowed`**: the bounded harmonic extension of the flowed force data of the
  negated driver at the reflected marks, reflected, extends the flowed force data of the driver;
* **`IsStageS2`**: the S2 data at one sample — the retained path `q` from `x₁ ≥ 0` with
  `fill R = fill q([0, 1])`, the relative chart `cr` (reflected) as a left entry chart at `0` with a continuous
  finite-fibre extension `g` of its inverse and `LiftRealOn`, S1 (`q` on the closed right side of the proper curve
  `β'`, B's reflected continuation), the proper lift `γ` of `β'`, the relative chain of `γ` with the **negated version
  driver** `−W`, no real arc, B's reflected stage piece `(−wB, η)` with its tip in `ℍ` at the stop `sB`, the relative
  clock `capClock γ sB = u`, and the identifications with B's stage chart `c` and the canonical chart `Φ`;
* **`exists_isCfg_of_stageS2`**: the record `IsCfg`, given the three word identities (retained, explored, union).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open InteractingSLE.Supp9B (IsProperCurve closedRightSide)

namespace InteractingSLE.Theorem14.SB.Om

open Sec7.Lemma71C FinRel
open Supp8.Q3Chain (flowedData flowedJumps initJumps coe_initJumps)
open LP (reflectC)
open Exist.StagedLaw (markPos markPosL)

/-! ### Mark positions and flowed data under reflection -/

theorem markPosL_neg (D : ℝ → ℝ) (u x : ℝ) : markPosL (fun s => -D s) u (-x) = -markPos D u x := by
  show -markPos (fun s => -(-D s)) u (-(-x)) = -markPos D u x
  simp only [neg_neg]

theorem markPos_neg (D : ℝ → ℝ) (u x : ℝ) : markPos (fun s => -D s) u (-x) = -markPosL D u x := by
  show markPos (fun s => -D s) u (-x) = -(-markPos (fun s => -D s) u (-x))
  rw [neg_neg]

/-- **Reflected flowed data**: the bounded harmonic extension of the flowed force data of the negated driver at the
reflected marks (weights swapped), reflected, extends the flowed force data of the driver. -/
theorem isBoundedHarmonicExtension_reflect_flowed {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {D : ℝ → ℝ} {u : ℝ} {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (flowedData κ ρR ρL (fun j => -xR j) (fun i => -xL i) (fun s => -D s) u)
      (flowedJumps (fun j => -xR j) (fun i => -xL i) (fun s => -D s) u) G) :
    IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR D u) (flowedJumps xL xR D u)
      (fun z => -G (reflectC z)) := by
  have e1 : flowedData κ ρR ρL (fun j => -xR j) (fun i => -xL i) (fun s => -D s) u =
      forceBoundaryData κ ρR ρL (fun j => -markPos D u (xR j)) (fun i => -markPosL D u (xL i)) := by
    unfold flowedData
    simp only [markPosL_neg, markPos_neg]
  have e2 : (flowedJumps (fun j => -xR j) (fun i => -xL i) (fun s => -D s) u : Set ℝ) =
      forceJumpSet (fun j => -markPos D u (xR j)) (fun i => -markPosL D u (xL i)) := by
    unfold flowedJumps
    rw [coe_initJumps]
    simp only [markPosL_neg, markPos_neg]
  rw [e1, e2] at hG
  have h := Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect_force hG
  unfold flowedData flowedJumps
  rw [coe_initJumps]
  exact h

/-- The force data of the original marks, from the reflected ones (the retained word). -/
theorem isBoundedHarmonicExtension_reflect_init {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (forceBoundaryData κ ρR ρL (fun j => -xR j) (fun i => -xL i))
      (initJumps (fun j => -xR j) (fun i => -xL i)) G) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR)
      (fun z => -G (reflectC z)) := by
  rw [coe_initJumps] at hG
  exact Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect_force hG

/-! ### The S2 data at one sample -/

/-- **SB2(2)'s S2 data at one sample**, in B's stage coordinates read in SB2(1)'s (reflected) orientation: the
inputs of `Bq.isRelConfigJK_of_bridgePath_noTip` with the reflected B-driver `−wB` and the negated version driver
`−W` as the relative chain's driver, the relative clock `capClock γ sB = u`, and the identifications with B's stage
chart `c` (the retained set) and the canonical chart `Φ` (inverse and lift). -/
def IsStageS2 (c Φ : Chart) (A₁ : Set ℂ) (wB : ℝ → ℝ) (sB : ℝ) (W : ℝ → ℝ) (u : ℝ) : Prop :=
  ∃ (q : ℝ → ℂ) (x₁ : ℝ) (R : Set ℂ) (cr : Chart) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (S₀ Sm : ℝ) (ηr η : ℝ → ℂ),
    ContinuousOn q (Icc 0 1) ∧ q 0 = x₁ ∧ 0 ≤ x₁ ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) ∧
    (∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y) ∧ fillH R = fillH (q '' Icc 0 1) ∧
    IsLeftEntryChart R 0 cr ∧ ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g cr.2.1 H ∧
    (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧ LiftRealOn cr ∧
    IsProperCurve β' ∧ β' 0 = 0 ∧ q '' Icc 0 1 ⊆ closedRightSide β' ∧
    IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' s) ∧
    IsSB2RelChain R cr β' γ 0 S₀ (fun r => -W r) ηr ∧ S₀ < Sm ∧
    interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅ ∧
    sB ∈ Ioc 0 S₀ ∧ Continuous wB ∧ wB 0 = 0 ∧ IsLoewnerTrace (fun r => -wB r) η ∧
    fwdHull (fun r => -wB r) sB = fillH (β' '' Icc 0 sB.toNNReal) ∧
    (∀ r ∈ Icc (0 : ℝ) sB, η r = β' r.toNNReal) ∧ η sB ∈ H ∧
    capClock (fun r : ℝ => γ r.toNNReal) sB = u ∧
    (∀ z ∈ H, z ∈ reflectC '' fillH R ↔ c.2.1 z ∈ A₁) ∧
    (∀ y ∈ H, Φ.2.1 y = c.2.1 (reflectC (cr.2.1 (reflectC y)))) ∧
    (∀ y ∈ H, Φ.2.2 (Φ.2.1 y) = -cr.2.2 (cr.2.1 (reflectC y)) + c.2.2 (Φ.2.1 y))

/-- **The configuration record from the S2 data.** Given the S2 data at a sample, the type data `(ρ, x)` of the
retained word (marks on the correct sides) and the explored data `(ρ', x')`, with the three word identities — the
extension of the retained force data is `β₁.mean + ψχ`, that of the explored flowed data is `GE₀ + ψχ`, that of the
union's flowed data is `Gu` — the record `IsCfg` holds. -/
theorem exists_isCfg_of_stageS2 {κ ψ : ℝ} {c Φ : Chart} {A₁ : Set ℂ} {wB : ℝ → ℝ} {sB : ℝ} {W : ℝ → ℝ} {u : ℝ}
    {β₁ : Restart.BoundaryWord} {GE₀ Gu : ℂ → ℝ} (hS : IsStageS2 c Φ A₁ wB sB W u)
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hG₀ : ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) G →
      EqOn G (fun z => β₁.mean z + ψ * chiC κ) H)
    (hGE : ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension (flowedData κ ρL' ρR' xL' xR' wB sB)
      (flowedJumps xL' xR' wB sB) G → EqOn G (fun z => GE₀ z + ψ * chiC κ) H)
    (hGu : ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR W u) (flowedJumps xL xR W u) G →
      EqOn G Gu H) :
    ∃ d, IsCfg κ ψ c Φ A₁ wB sB W u β₁ GE₀ Gu d := by
  obtain ⟨q, x₁, R, cr, g, β', γ, S₀, Sm, ηr, η, hq, hq0, hx₁, hqH, hqR, hR, hc, hgc, hgi, hgf, hL, hβ', hβ'0, hA,
    hγ, hγ0, hlift, hch, hS₀S, hnR, hs, hwc, hw0, hη, hwt, hηβ, hηH, hcap, hAeq, hinv, hlifteq⟩ := hS
  have hwc' : Continuous fun r => -wB r := hwc.neg
  have hw0' : (fun r => -wB r) 0 = 0 := by simp only [hw0, neg_zero]
  obtain ⟨LΨ, G₀, GE, G, hLeq, hcfg⟩ := Bq.isRelConfigJK_of_bridgePath_noTip (κ := κ) (χ := chiC κ)
    (ρL := ρR) (ρR := ρL) (xL := fun j => -xR j) (xR := fun i => -xL i)
    (ρL' := ρR') (ρR' := ρL') (xL' := fun j => -xR' j) (xR' := fun i => -xL' i)
    (fun j => neg_nonpos.2 (hxR j)) (fun i => neg_nonneg.2 (hxL i))
    (fun j => neg_nonpos.2 (hxR' j)) (fun i => neg_nonneg.2 (hxL' i))
    hq hq0 hx₁ hqH hqR hR hc hgc hgi hgf hL hβ' hβ'0 hA hγ hγ0 hlift hch hS₀S hnR hs hwc' hw0' hη hwt hηβ hηH
  rw [hcap] at hcfg
  have hJKL := Lm.isRelConfigJKL_of_reflect hcfg
  have ew : (-(fun r => -wB r)) = wB := by funext r; simp
  have eW : (-(fun r => -W r)) = W := by funext r; simp
  rw [ew, eW] at hJKL
  refine ⟨⟨reflectC '' fillH R, fun z => reflectC (cr.1 (reflectC z)), fun z => reflectC (cr.2.1 (reflectC z)),
    fun z => conj (LΨ (reflectC z)), Sec7.FlowReflect.reflJumps ∅, fun s => reflectC (η s),
    fun s => reflectC (ηr s), _, _, _, _, _, _, fun z => -G₀ (reflectC z), fun z => -GE (reflectC z),
    fun z => -G (reflectC z), _⟩, hAeq, hJKL, hinv, ?_, ?_, ?_, ?_⟩
  · -- the lift relation
    intro y hy
    have hD := hc.1
    have hmem : cr.2.1 (reflectC y) ∈ H \ fillH R := hD.inv_mem (Sec7.FlowReflect.reflectC_mem_H hy)
    have hl := hLeq hmem
    simp only at hl ⊢
    rw [hlifteq y hy, LP.reflectC_reflectC, Complex.conj_im, ← hl]
  · -- the retained extension
    exact hG₀ _ (isBoundedHarmonicExtension_reflect_init (FinRel.IsRelConfigJK.bhe₀ hcfg))
  · -- the explored extension
    exact hGE _ (isBoundedHarmonicExtension_reflect_flowed (FinRel.IsRelConfigJK.bheE hcfg))
  · -- the union extension
    exact hGu _ (isBoundedHarmonicExtension_reflect_flowed (FinRel.IsRelConfigJK.bheu hcfg))

end InteractingSLE.Theorem14.SB.Om
