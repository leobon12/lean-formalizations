import QuantumZipper.Proofs.Thm18.G3ZqG3Joint
import QuantumZipper.Proofs.Thm18.R18G3TCM7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the Cameron–Martin step `A → B` (R-a)

Generalized copy (D92) of the zoom-dependent parts of `R18G3TCM3.lean` (`sEvX`, `sEvR`, their
measurability and folded-circle locality) and of `g3TCMStmt_holds` (`R18G3TCM7.lean`), with the
plain zooms replaced by abstract zooms `Z` (at `x`) and `Z'` (at `R(x)`). The Cameron–Martin core
`bodyB_core` is abstract in the event and reused. The zooms are used through joint measurability
(`hZm`) and invariance under equal regularized averages (`hZa`; the plain zoom has it by
`Factorization.translate_congr`, `zoomLaw_avgReg_congr`), which gives folded-circle locality
`IsLocS` of the zoom events.

Headlines: `g3TCMStmtZ` (body of the free scheme `A` ⇒ body of the cut-off scheme `B`), and
`g3TProfMixTransferStmtZ_of`: the per-region transfer from (R-a) and the open step `B → C`
(`G3TCutToProfStmtZ`, the abstract-zoom form of `G3TCutToProfStmt`).

Sheffield, arXiv:1012.4797, p. 72, Remark 5.7 (Cameron–Martin for a cut-off profile). Own
bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- `sEvX` with the abstract zoom `Z`. -/
def sEvXZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (s : Set LawD) (m : ℝ) :
    Set (FieldSample × ℝ) :=
  {q | Z i.C q.1 (sX γ i q) ∈ s ∧ |sX γ i q - i.t₁| + m < i.r₁}

/-- `sEvR` with the abstract zoom `Z'`. -/
def sEvRZ (Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (t : Set LawD) (m : ℝ) :
    Set (FieldSample × ℝ) :=
  {q | Z' i.C q.1 (sR γ i q) ∈ t ∧ |sR γ i q - i.t₂| + m < i.r₂}

theorem measurableSet_sEvXZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s) (m : ℝ) :
    MeasurableSet (sEvXZ Z γ i s m) :=
  (((hZm i.C).comp (measurable_fst.prodMk (measurable_sX γ i))) hs).inter
    (measurableSet_sMX γ i m)

theorem measurableSet_sEvRZ (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t) (m : ℝ) :
    MeasurableSet (sEvRZ Z' γ i t m) :=
  (((hZm' i.C).comp (measurable_fst.prodMk (measurable_sR γ i))) ht).inter
    (measurableSet_sMR γ i m)

theorem isLocS_sEvXZ
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (γ : ℝ) (i : G3Idx) (s : Set LawD) (m : ℝ) : IsLocS (sEvXZ Z γ i s m) :=
  fun x x' h ℓ => by
    simp only [sEvXZ, mem_setOf_eq, sX_fc h γ i ℓ, hZa i.C x x' _ (avgReg_fc h)]

theorem isLocS_sEvRZ
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    (γ : ℝ) (i : G3Idx) (t : Set LawD) (m : ℝ) : IsLocS (sEvRZ Z' γ i t m) :=
  fun x x' h ℓ => by
    simp only [sEvRZ, mem_setOf_eq, sR_fc h γ i ℓ, hZa' i.C x x' _ (avgReg_fc h)]

/-- The fixed-region mixing body of scheme `B` (profile `g3wCut γ η`) for abstract zooms. -/
abbrev G3BodyBZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (μ ν : Measure LawD) : Prop :=
  G3FixMixBody μ ν (fun i => g3pPalmLaw γ (g3wCut γ i.η) i) (fun i => g3pX γ (g3wCut γ i.η) i)
    (fun i => g3pR γ (g3wCut γ i.η) i) (fun i => g3pUfZ Z γ (g3wCut γ i.η) i)
    (fun i => g3pVfZ Z' γ (g3wCut γ i.η) i)

set_option maxHeartbeats 800000 in
/-- **(R-a) for abstract zooms**: the fixed-region mixing body of the free scheme `A` implies that
of the cut-off scheme `B`, with the same limit laws (copy of `g3TCMStmt_holds`). -/
theorem g3TCMStmtZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ μ ν : Measure LawD, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3UfZ Z γ) (g3VfZ Z' γ) →
    G3BodyBZ Z Z' γ μ ν := by
  intro μ ν hμ hν hA
  unfold G3FixMixBody at hA
  unfold G3BodyBZ G3FixMixBody
  obtain ⟨hAx, hAR⟩ := hA
  refine ⟨?_, ?_⟩
  · intro s hs δ η m hm ε hε
    by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
    · obtain ⟨hη, hηδ, hδ4⟩ := hcon
      set i₀ : G3Idx := ⟨(δ, η, 0), hη, hηδ, hδ4⟩ with hi₀
      obtain ⟨K, e, hK0, he, hKe⟩ := exists_K_e γ hγ hγ2 i₀ hε
      have hsm : MeasurableSet s := measurableSet_lawCyl hs
      have ha0 : 0 ≤ μ.real s := measureReal_nonneg
      have ha1 : μ.real s ≤ 1 := measureReal_le_one
      filter_upwards [hAx s hs δ η m hm e he] with C hC
      intro i hi G hG
      have h₁ : i.1.1 = i₀.1.1 := by rw [hi]
      have h₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi]
      have hb := bodyB_core hγ hγ2 i (measurableSet_sEvXZ hZm γ i hsm m) (measurableSet_sMX γ i m)
        (isLocS_sEvXZ hZa γ i s m) (isLocS_sMX γ i m) ha0 ha1 hK0 (hC i hi) hG
      rw [cmκ_congr h₁ h₂, cmT_congr h₁ h₂] at hb
      exact hb.trans hKe
    · filter_upwards with C
      intro i hi
      have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
        have := i.2
        rwa [hi] at this
      exact absurd h2 hcon
  · intro t ht δ η m hm ε hε
    by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
    · obtain ⟨hη, hηδ, hδ4⟩ := hcon
      set i₀ : G3Idx := ⟨(δ, η, 0), hη, hηδ, hδ4⟩ with hi₀
      obtain ⟨K, e, hK0, he, hKe⟩ := exists_K_e γ hγ hγ2 i₀ hε
      have htm : MeasurableSet t := measurableSet_lawCyl ht
      have ha0 : 0 ≤ ν.real t := measureReal_nonneg
      have ha1 : ν.real t ≤ 1 := measureReal_le_one
      filter_upwards [hAR t ht δ η m hm e he] with C hC
      intro i hi G hG
      have h₁ : i.1.1 = i₀.1.1 := by rw [hi]
      have h₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi]
      have hb := bodyB_core hγ hγ2 i (measurableSet_sEvRZ hZm' γ i htm m) (measurableSet_sMR γ i m)
        (isLocS_sEvRZ hZa' γ i t m) (isLocS_sMR γ i m) ha0 ha1 hK0 (hC i hi) hG
      rw [cmκ_congr h₁ h₂, cmT_congr h₁ h₂] at hb
      exact hb.trans hKe
    · filter_upwards with C
      intro i hi
      have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
        have := i.2
        rwa [hi] at this
      exact absurd h2 hcon

/-- **`B → C` for abstract zooms** (the abstract-zoom form of `G3TCutToProfStmt`; open: its
`x` side is proved for the plain zoom in `R18G3TXSide4.lean` using the area locality of
`zoomLaw`, its `R(x)` side `G3TCutToProfRStmt` is open even for the plain zoom). -/
def G3TCutToProfStmtZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ μ ν : Measure LawD, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    G3BodyBZ Z Z' γ μ ν →
    G3FixMixBody μ ν (g3pPalmLaw γ (g3wProf γ)) (g3pX γ (g3wProf γ)) (g3pR γ (g3wProf γ))
      (g3pUfZ Z γ (g3wProf γ)) (g3pVfZ Z' γ (g3wProf γ))

/-- **The per-region transfer from (R-a) (proved) and `B → C`.** -/
theorem g3TProfMixTransferStmtZ_of
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hBC : G3TCutToProfStmtZ Z Z' γ) :
    G3TProfMixTransferStmtZ Z Z' γ :=
  fun μ ν hμ hν h => hBC μ ν hμ hν (g3TCMStmtZ hZm hZa hZm' hZa' hγ hγ2 μ ν hμ hν h)

end R18
end QuantumZipper
