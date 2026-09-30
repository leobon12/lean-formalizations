import QuantumZipper.Proofs.Zipper.LocLenF1FlowDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6b: the length cocycle of the open-arc lengths along the flow

Open-arc copies (FOLLOW-PAPER-13 §1) of `F1.lenCocycleStmt_of_flow` (F1LenFlow.lean),
`F1.lenCanonStmt_of_reg` and `F1.lenLeftSurjStmt_of_reg_unbdd` (F1LenInCanon.lean).
Sheffield, arXiv:1012.4797, §1.4 and §5.4, pp. 70–72; Berestycki–Powell arXiv:2404.16642,
Thm 8.16 p. 283, Claim 8.17 pp. 284–285 ("L(1) < ∞").

* `LenFiniteArcStmt`: at each fixed capacity time the two open-arc lengths of the `P_*` sample are
  finite (the `P_*` form of X1, `BaseFin.BaseFiniteStmt`, B-P p. 285 "L(1) < ∞"). By additivity
  along the flow (`LenPairCocycleArcStmt`) this gives finiteness at all times
  (`ae_unzipLengthsArc_lt_top_all`). The old proofs got finiteness for free from the global
  locally finite measure; for open arcs it is a genuine input.
* `lenCocycleArc_of_flow`, `lenCanonArc_of_reg`, `lenLeftSurjArc_of_reg`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Finiteness of the open-arc lengths at fixed times** (`P_*` form of X1). -/
def LenFiniteArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ q : ℝ, 0 ≤ q → ∀ᵐ ω ∂P',
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) q).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) q).2 < ⊤

/-- Finiteness at all times, from fixed integer times and additivity along the flow. -/
theorem ae_unzipLengthsArc_lt_top_all (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt)
    (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) (hP : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2 < ⊤ := by
  have hn := ae_all_iff.2 fun n : ℕ => hF κ P' Y B' hP (n : ℝ) (Nat.cast_nonneg n)
  filter_upwards [hn, hC κ P' Y B' hP] with ω hω hc t ht
  exact ⟨lt_top_of_nat_of_cocycle
      (f := fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1)
      (fun u s hu hs => (hc u s hu hs).1) (fun n => (hω n).1) ht,
    lt_top_of_nat_of_cocycle
      (f := fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2)
      (fun u s hu hs => (hc u s hu hs).2) (fun n => (hω n).2) ht⟩

/-- **Open-arc lengths are invariant under the canonical rescaling at the length times** (copy
of `F1.LenCanonStmt`, F1LenFlow.lean:206). -/
def LenCanonArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ ℓ : ℝ, 0 < ℓ →
      0 < scaleParam (Real.sqrt κ) (zipCapDown (Real.sqrt κ)
        (leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ) (F1.pcfg κ Y B' ω)).1 ∧
      ∀ r : ℝ, 0 ≤ r →
        unzipLengthsArc (Real.sqrt κ) (canonConfig (Real.sqrt κ) (zipCapDown (Real.sqrt κ)
          (leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ) (F1.pcfg κ Y B' ω))) r =
        unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ)
          (leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ) (F1.pcfg κ Y B' ω))
          (scaleParam (Real.sqrt κ) (zipCapDown (Real.sqrt κ)
            (leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ) (F1.pcfg κ Y B' ω)).1 ^ 2 * r)

/-- **`LenCocycleArcStmt` from strict monotonicity, surjectivity, the capacity cocycle, the
canonical rescaling and finiteness** (copy of `F1.lenCocycleStmt_of_flow`). -/
theorem lenCocycleArc_of_flow (hM : LenStrictMonoArcStmt) (hS : LenLeftSurjArcStmt)
    (hC : LenPairCocycleArcStmt) (hK : LenCanonArcStmt) (hF : LenFiniteArcStmt) :
    LenCocycleArcStmt := by
  intro κ Ω' _ P' _ Y B' h
  filter_upwards [hM κ P' Y B' h, hS κ P' Y B' h, hC κ P' Y B' h, hK κ P' Y B' h,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' h] with ω hm hs hc hk hf ℓ s hℓ hs0
  exact lenCocycleArc_det hm hs (fun u s hu hs => (hc u s hu hs).1)
    (fun u s hu hs => (hc u s hu hs).2) hk (fun t ht => (hf t ht).2) hℓ hs0

/-- **Regularity of the canonical rescaling along the flow, open arcs** (copy of
`F1.LenCanonRegStmt` with `CanonRegArc`). -/
def LenCanonRegArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r →
      CanonRegArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) τ (F1.pcfg κ Y B' ω)) r

/-- **`LenCanonArcStmt` from `LenCanonRegArcStmt`** (copy of `F1.lenCanonStmt_of_reg`). -/
theorem lenCanonArc_of_reg (hG : LenCanonRegArcStmt) : LenCanonArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hP.1
  filter_upwards [hG κ P' Y B' hP, hP.2.2.2.1.cont] with ω hω hc ℓ _
  have hτ : 0 ≤ leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ :=
    Real.sInf_nonneg fun t ht => ht.1
  obtain ⟨hW, hW0, hWmax⟩ := F1.zipCapDown_snd_props (γ := Real.sqrt κ)
    (τ := leftTimeArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ) (c := F1.pcfg κ Y B' ω)
    (F1.continuous_drive_of κ hc)
  exact ⟨(hω _ 0 hτ le_rfl).1, fun r hr =>
    unzipLengthsArc_canon_of_reg hγ hW hW0 hWmax hr (hω _ r hτ hr)⟩

/-- **Regularity of the left open-arc length** (copy of `F1.LenLeftRegStmt`). -/
def LenLeftRegArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ContinuousOn
        (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1.toReal) (Ici 0) ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) 0).1 = 0

/-- **Unboundedness of the left open-arc length** (copy of `F1.LenLeftUnbddStmt`). -/
def LenLeftUnbddArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧
      ENNReal.ofReal M ≤ (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1

/-- **`LenLeftSurjArcStmt` from continuity, unboundedness and finiteness of `L⁻`** (copy of
`F1.lenLeftSurjStmt_of_reg_unbdd`). -/
theorem lenLeftSurjArc_of_reg (hR : LenLeftRegArcStmt) (hU : LenLeftUnbddArcStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenLeftSurjArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  filter_upwards [hR κ P' Y B' hP, hU κ P' Y B' hP,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' hP] with ω hr hu hf ℓ hℓ
  exact exists_eq_of_cont_unbdd_arc hr.1 hr.2 hu (fun t ht => (hf t ht).1) hℓ

end LocLen
end QuantumZipper
