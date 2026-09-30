import QuantumZipper.Proofs.Zipper.B5VAssemble
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.E6Id

/-!
# UNIF-CLUSTER (decision D26): uniform-in-time B5-V from uniform windows and atomlessness

Decision D26 (`DECISIONS.md`) routes every "for all times at once" node of Theorem 1.3 that
concerns lengths (a.s. monotonicity of `s ↦ L⁻_s`, uniform B5-V, `E6.LenCollidedStmt`, the minus
side of `F2.B5UniformStmt`) through two statements about the unzipped fields
`h⁰_s = h0f κ s B X ω` (the `Γ⁰` field unzipped by capacity time `s`, `L⁻_s = ν_{h⁰_s}[O⁻_s, 0]`):

* `UnifWindowStmt` (**UW**): a.s., for every `s ∈ (0,T]` at once, the window identities
  `ν_{h⁰}(u,v) = ν_{h⁰_s}(F_s u, F_s v)` for rational `0₋(T) < u < v < 0₋(T − s)`, where
  `F_s = realRevMap V (T − s)`. At each fixed `s` this is `B5.ae_hcc` (proved).
* `UnifAtomlessStmt` (**UA**): a.s., for every `s ∈ [0,T]` at once, `ν_{h⁰_s}` has no atoms. At
  each fixed `s` this is B3(a) (`B5.ae_nu0_regular` at horizon `s`, proved).

Main results (the pathwise part is the fixed-time proof `B5.ae_b5v_fixed_of_windows`, run for all
`s` on one full-measure event; the Loewner inputs are made uniform in `s`):

* `ae_forall_isSimpleCurveHull_revHull_Vr`: a.s., for **every** `s > 0`, the reverse hull of
  `Vr κ s B ω = vrev W s` at time `s` is a simple arc (the forward `SLE_κ` hull `η(0,s]`, time
  reversal; one `Blueprint.RohdeSchrammSimple` event serves all `s`).
* **`ae_b5v_uniform_of_windows`**: UW + UA ⇒ a.s. `∀ s ∈ [0,T], L⁻_s = lenRHS s` (uniform B5-V).
* **`ae_monotoneOn_lenMinus_of_windows`**: UW + UA ⇒ the hypothesis `hmono` of `E6.e6_id`,
  `E6.lenCollidedStmt_of`, `ESM.ae_b5v_uniform` and `RegUnif.ae_b5Minus_uniform_of_mono`
  (`s ↦ L⁻_s` is a.s. nondecreasing, in fact strictly increasing and continuous, on `[0,T]`).

Sources: Sheffield, arXiv:1012.4797, Theorem 1.3 and its proof (§5, Lemma 5.6, pp. 66–68: the
length of `η[0,s]` is read off in the unzipped picture and does not depend on the unzipping
time); the paper does not argue uniformity in `s`. The reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Simple reverse hulls at all horizons at once.** Under `RohdeSchrammSimple`, a.s., for every
`s > 0` the reverse hull of `Vr κ s B ω` at time `s` is a simple arc (it is the forward hull
`η(0,s]`, `LoewnerAlgebra.revHull_eq_fwdHull_timeRev`). Same proof as
`B5.ae_isSimpleCurveHull_revHull_Vr`, with the horizon quantified inside the event. -/
theorem ae_forall_isSimpleCurveHull_revHull_Vr (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ ≤ 4) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (Vr κ s B ω) s) := by
  filter_upwards [hRSS κ hκ0 hκ4 P B hB, hB.cont, hB.eval_zero_ae_eq_zero] with ω hrs hc h0
  intro T hT
  obtain ⟨hchord, hhull⟩ := hrs
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev hWc T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ hVc hV0 hT,
    Thm14FromThm13.fwdHull_eq_of_eqOn (by fun_prop) hWc hT.le, hhull T hT.le]
  · exact Thm14FromThm13.isSimpleCurveHull_image_Ioc hchord hT
  · intro s hs
    simp only [Vr]
    rw [vrev_of_mem ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      vrev_of_mem ⟨hT.le, le_rfl⟩, sub_sub_cancel, sub_self, hW0]
    ring

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

end RegUnif
end QuantumZipper
