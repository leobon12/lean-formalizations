import InteractingSLE.WangWu.BridgeTrace
import InteractingSLE.Spec.Dimension.Finite
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Supplement.LPAssembly

/-!
# Wang–Wu at `κ = 4`: every frozen coupling with the whole-field kernel (WF2) is a full level-line coupling

Packet PROVE-WW-BRIDGE (ruling R40). The frozen Theorem 1.1 specifies a coupling `IsOptionalHullCoupling 4` only off
the filled hull. Wang–Wu's determination (document Theorem 4.25, `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`)
is proved for couplings with the full ambient-field kernel of its Definition 1.5 (`IsFullLevelLineCoupling`). The
follow-up note's whole-field identification (Part C, `source/external/AstraIG1/ig1_followup_proofs.txt` L1382–1910,
ruling R38) closes the gap: its conclusion (WF2), at `κ = 4`, is the hypothesis `HasWholeFieldKernel` below, stated in the
note's exact form (L1405–1420, with the `κ = 4` mean of C.5, L1834–1840):

  at every own-filtration stop `τ ≤ S`, `S < T_*` bounded and a continuous trace `η` available through `S`,
  `E[e^{i(h,φ)} | 𝓕_τ] = exp(i ∫ M_τ φ dA − ½ G_{Ω_τ}(φ, φ))`, `Ω_τ = ℍ \ η[0,τ]`,

with `G_{Ω_τ}` the covariance of a zero-boundary GFF on the possibly disconnected open set `Ω_τ` extended by zero
(QuantumZipper's `zeroGFFTestCov`) and `M_τ` the bounded piecewise harmonic mean (`m_τ` on the active component; in each
pocket the limit of `m_s` as `s` increases to its disconnection time, frozen afterwards: the document's `frozenMean`; at
`κ = 4` "its values on the area-zero trace are arbitrary").

**The bridge** (`IsOptionalHullCoupling.isFullLevelLineCoupling`): a frozen `κ = 4` coupling satisfying (WF2), whose
driver almost surely has a continuous generating trace through its lifetime, is a full level-line coupling. Two steps:

* **Covariance.** `G_{Ω_τ}(φ, φ) = Q_{U_τ}(φ, φ)` (`zeroGFFTestCov_compl_image_eq_retainedGreenEnergy`,
  `BridgeTrace.lean`: QuantumZipper's C5), because the trace has zero area (`dim_H < 2`,
  `IsIntegratedSLEEvolution.ae_dimH_image_inter_H_le`, Aux. lemma 15).
* **Unbounded stopping times.** (WF2) is stated at bounded stops; Definition 1.5 asks for every stopping time `τ < T`.
  At `τ ∧ n` the kernels agree with those at `τ` on `{τ ≤ n}` (`condExp_min_stopping_time_ae_eq_restrict_le_const`), and
  `τ < T` is finite.

**Consumers.** Per force word (`hasFieldDeterminedHistories_of_wholeField`): (WF2) for the word's frozen couplings
(`HasWholeFieldKernels`), the continuous trace of its evolutions (`LP.IsCompleteForceWord 4`) and Theorem 4.25 for the
word (`HasDeterminedFullCouplings`) give `LP.HasFieldDeterminedHistories 4` for the word. For all ordered words
(`wwTheorem17Statement_of_wholeField`): with (WF2) for every frozen `κ = 4` coupling (`WholeFieldKernelFourStatement`,
PROVE-WHOLEFIELD3), the trace (`LP.WWTheorem18Statement`, Wang–Wu Theorem 1.8, PROVE-WW-C) and Wang–Wu's Theorem 4.25
(`WWTheorem425Statement`, PROVE-WW-B4), the input `LP.WWTheorem17Statement` of Corollary LP11 holds. The three are named
inputs, not yet in Lean. Order of proof: (WF2) assumes a continuous prefix, and Wang–Wu's continuity induction
(Theorem 7.7) uses field determination; the per-word form lets the two be proved together, word by word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

/-! ### (WF2) at `κ = 4` -/

/-- **(WF2) at `κ = 4`, for one coupling** (follow-up note Part C, Theorem "original-hull to full-range upgrade",
`ig1_followup_proofs.txt` L1405–1420; the `κ = 4` mean, C.5, L1834–1840). For every bounded stopping time `S < T_*` of
the driving filtration, every stopping time `τ ≤ S` and every test function `φ`: almost surely, for every continuous
generating trace `η` through `S`, `E[e^{i(h,φ)} | 𝓕_τ] = exp(i ∫ M_τ φ dA − ½ G_{Ω_τ}(φ, φ))`, where `Ω_τ = ℍ \ η[0,τ]`,
`G_{Ω_τ}(φ, φ) = zeroGFFTestCov Ω_τ φ φ` is the variance of `(h⁰_{Ω_τ}, φ)` for a zero-boundary GFF on `Ω_τ` extended by
zero, and `M_τ = frozenMean` is the mean `m_τ` on the active component and, in each pocket, the limit of `m_s` as `s`
increases to the pocket's disconnection time (the first swallowing time of each of its points). -/
def HasWholeFieldKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∃ hX : IsMeasurableKilledDriving W VL VR ζ,
    ∀ (S τ : Ω → WithTop ℝ≥0), IsStoppingTime (drivingFiltration P hX) S →
      ∀ hτ : IsStoppingTime (drivingFiltration P hX) τ,
        (∃ N : ℝ≥0, ∀ ω, S ω ≤ N) → (∀ᵐ ω ∂P, (S ω : ℝ≥0∞) < ζ ω) → (∀ ω, τ ω ≤ S ω) →
        ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (S ω : ℝ≥0∞) η →
            condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
              Complex.exp (Complex.I * ((∫ z, frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
                  (fun i => (VR i · ω)) ((τ ω).untopD 0) z * φ z : ℝ) : ℂ) -
                (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov (H \ η '' Icc 0 ((τ ω).untopD 0)) φ φ : ℝ) : ℂ))

/-! ### The bridge -/

section Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- A stopping time with values below a lifetime is below some integer. -/
theorem exists_nat_le_of_lt {τ : WithTop ℝ≥0} {T : ℝ≥0∞} (hτ : (τ : ℝ≥0∞) < T) :
    ∃ n : ℕ, τ ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hτ)
  refine ⟨⌈t⌉₊, ?_⟩
  rw [← ht]
  exact WithTop.coe_le_coe.2 (Nat.le_ceil t)

/-- **The bridge (ruling R40).** A frozen `κ = 4` coupling (`IsOptionalHullCoupling 4`) satisfying the whole-field
identification (WF2) (`HasWholeFieldKernel`), whose driver almost surely has a continuous generating trace through its
lifetime, is a full level-line coupling (Wang–Wu Definition 1.5): the conditional characteristic function of the whole
field at every stopping time `τ < T` is `exp(i ∫ η̄_τ φ − ½ Q_{U_τ}(φ, φ))`. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.isFullLevelLineCoupling [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hWF : HasWholeFieldKernel ρL ρR P W VL VR ζ h)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) :
    IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨hE, hhm, -, -⟩ := hC
  obtain ⟨hX, hK⟩ := hWF
  refine ⟨hE, hhm, hX, fun τ hτ hτζ φ => ?_⟩
  have hSn : ∀ n : ℕ, IsStoppingTime (drivingFiltration P hX)
      (fun ω => min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) := fun n => hτ.min_const (n : ℝ≥0)
  have hSζ : ∀ n : ℕ, ∀ᵐ ω ∂P, ((min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    fun n => by
      filter_upwards [hτζ] with ω hω
      exact lt_of_le_of_lt (min_le_left (τ ω) _) hω
  have hKn := fun n : ℕ => hK _ _ (hSn n) (hSn n) ⟨n, fun ω => min_le_right _ _⟩ (hSζ n)
    (fun ω => le_rfl) φ
  have hloc := fun n : ℕ =>
    ae_imp_of_ae_restrict (condExp_min_stopping_time_ae_eq_restrict_le_const (μ := P)
      (f := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) hτ (n : ℝ≥0))
  filter_upwards [ae_all_iff.2 hKn, ae_all_iff.2 hloc, htr, hτζ, hE.2.2.2.2,
    hE.ae_dimH_image_inter_H_le (by norm_num) (by norm_num)] with ω hKω hlocω htrω hlt hp hdim
  obtain ⟨η, hη⟩ := htrω
  obtain ⟨n, hn⟩ := exists_nat_le_of_lt hlt
  have hmin : min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) = τ ω := min_eq_left hn
  -- the time `t = τ(ω) < ζ(ω)`
  set t : ℝ≥0 := (τ ω).untopD 0 with htdef
  have hτt : τ ω = (t : WithTop ℝ≥0) := by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [htdef, ← hs, WithTop.untopD_coe]
  have htζ : (t : ℝ≥0∞) < ζ ω := by
    have : ((t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hτt ▸ hlt
    exact this
  -- zero area of `η[0, t] ∩ ℍ`
  have harea : volume (η '' Icc 0 t ∩ H) = 0 := by
    refine volume_eq_zero_of_dimH_lt_two (lt_of_le_of_lt (hdim η hη (Icc 0 t) fun s hs =>
      le_trans (ENNReal.coe_le_coe.2 hs.2) htζ.le) ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (Dimension.interiorDimBound_lt_two (by norm_num))
  -- (WF2) at `τ ∧ n`
  have hηn : IsGeneratingTrace (fun t => W t ω)
      ((min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) η :=
    hη.mono_horizon (le_trans (min_le_left (τ ω) _) hlt.le)
  have e2 := hKω n η hηn
  have e1 := hlocω n hn
  simp only [hmin] at e1 e2
  rw [← e1, e2, ← htdef, zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hη hp.2.2.2.1 hp.1 htζ harea φ]

end Bridge

/-! ### Named inputs and the input `LP.WWTheorem17Statement` of Corollary LP11 -/

/-- (WF2) at `κ = 4` for one force word: every coupling of the word that satisfies the optional hull specification of
Theorem 1.1 at `κ = 4`, on a probability space, has the whole-field kernel `HasWholeFieldKernel`. -/
def HasWholeFieldKernels (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h → HasWholeFieldKernel ρL ρR P W VL VR ζ h

/-- Wang–Wu Theorem 4.25 for one force word: the killed driving history of every full level-line coupling
(Definition 1.5) of the word, on a probability space, is a Borel function of the field up to a null set. -/
def HasDeterminedFullCouplings (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F → LP.IsFieldDeterminedHistory P F W VL VR ζ

/-- **Named input: (WF2) at `κ = 4` for every frozen coupling** (follow-up note Part C, ruling R38; packet
PROVE-WHOLEFIELD3, which proves (WF2) from the thinness estimate (WF1)), for every ordered force word. -/
def WholeFieldKernelFourStatement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → HasWholeFieldKernels.{u} xL xR ρL ρR

/-- **Named input: Wang–Wu Theorem 4.25** (determination for finitely many force points; document §4.6, p. 32,
`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`; packet PROVE-WW-B4), for every ordered force word: "the hull
coupled with the GFF by the full stopping-time kernel of Definition 1.5 is determined by that GFF up to its continuation
threshold". -/
def WWTheorem425Statement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → HasDeterminedFullCouplings.{u} xL xR ρL ρR

/-- **Determination for every frozen `κ = 4` coupling of one force word**, from (WF2) for the word, the continuous trace
of its evolutions (`LP.IsCompleteForceWord 4`, Wang–Wu Theorem 1.8 for the word) and Wang–Wu Theorem 4.25 for the
word: every frozen coupling is a full level-line coupling (`IsOptionalHullCoupling.isFullLevelLineCoupling`). This
per-word form fits an induction over force words in which continuity and determination are proved together (Wang–Wu
Theorem 7.7 uses field determination; the whole-field identification assumes a continuous prefix). -/
theorem hasFieldDeterminedHistories_of_wholeField {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hWF : HasWholeFieldKernels.{u} xL xR ρL ρR)
    (htr : LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR) (h425 : HasDeterminedFullCouplings.{u} xL xR ρL ρR) :
    LP.HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR := by
  intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC
  refine h425 P 𝓕 W VL VR B ζ h (hC.isFullLevelLineCoupling (hWF P 𝓕 W VL VR B ζ h hC) ?_)
  filter_upwards [htr P 𝓕 W VL VR B ζ hC.1] with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

/-- **The `κ = 4` input `LP.WWTheorem17Statement` of Corollary LP11**, from (WF2) for every frozen coupling
(`WholeFieldKernelFourStatement`), the continuous trace of Wang–Wu Theorem 1.8 (`LP.WWTheorem18Statement`) and Wang–Wu
Theorem 4.25 (`WWTheorem425Statement`). -/
theorem wwTheorem17Statement_of_wholeField (hWF : WholeFieldKernelFourStatement.{u})
    (hWW18 : LP.WWTheorem18Statement.{u}) (h425 : WWTheorem425Statement.{u}) :
    LP.WWTheorem17Statement.{u} := fun xL xR ρL ρR hxo =>
  hasFieldDeterminedHistories_of_wholeField (hWF xL xR ρL ρR hxo) (hWW18 xL xR ρL ρR hxo)
    (h425 xL xR ρL ρR hxo)

/-- The distinct-position form `LP.WWTheorem17DistinctStatement` under the same inputs. -/
theorem wwTheorem17DistinctStatement_of_wholeField (hWF : WholeFieldKernelFourStatement.{u})
    (hWW18 : LP.WWTheorem18Statement.{u}) (h425 : WWTheorem425Statement.{u}) :
    LP.WWTheorem17DistinctStatement.{u} := fun xL xR ρL ρR hd =>
  wwTheorem17Statement_of_wholeField hWF hWW18 h425 xL xR ρL ρR hd.1

end WangWu

end InteractingSLE
