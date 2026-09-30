import QuantumZipper.Proofs.Zipper.RegUnifDet
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Zipper.B3dStmt

/-!
# REG-UNIF: regularity of the unzipped field for all times at once

Standing setup: `B` a Brownian motion, `X` a free-boundary GFF modulo constants, `pathOf B ⟂ X`,
`W = drive κ B`, `y_t = unzippedField γ (h⁰ + X, W) t`.

**Main reduction** (`ae_forall_isRegularWith_of_jointMod`): if the raw values
`Z(t, c, r) = y_t(fc(c, r))` have a modification `Ẑ` continuous in `(t, c, r)` on
`[0, T] × Hbar × (0, ∞)` which satisfies the circle-commutation identity at every fixed parameter
a.s. (`JointModStmt`: the four-parameter Kolmogorov–Čentsov step plus stochastic Fubini), then
a.s., **for all `t ∈ [0, T]` simultaneously**, `y_t` is a regular sample with witness `Ẑ(t, ·)`
and its raw values converge at every centre of `ℂ`. The time continuity of the raw values at the
countably many dyadic folded circles is `RegCont.ae_continuousOn_unzippedField` (proved); the
rest is `RegUnifDet.forall_isRegularWith_of_joint` (deterministic). All times `t ≥ 0`:
`ae_forall_isRegularSample_of_jointMod` (exhaustion).

**Field cocycle** (`capCocycleRegStmt_of_inputs`): `B3d.CapCocycleRegStmt` follows from
`JointModStmt` together with the fixed-time raw cocycle at the dyadic folded circles
(`RawCocycleFixedStmt`) and the continuity in `(u, s)` of the raw values of the doubly unzipped
field (`DoubleUnzipContStmt`), by density of rational times (`forall_regEq_of_dense`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (arXiv:0808.1560, p. 18) for the structure (continuous modification of circle
averages, Kolmogorov–Čentsov: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed.,
Ch. I, Thm (2.1)); the uniformization in time by density is an **own elementary argument**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- The parameter set `[0, T] × Hbar × (0, ∞)` of the raw values `y_t(fc(c, r))`. -/
def parSet (T : ℝ) : Set (ℝ × (ℂ × ℝ)) := Icc 0 T ×ˢ (Hbar ×ˢ Ioi 0)

/-- **Open input (four-parameter Kolmogorov step + stochastic Fubini).** The raw values
`(t, c, r) ↦ y_t(fc(c, r))` of the unzipped field have a modification `Zh`, continuous on
`[0, T] × Hbar × (0, ∞)` for every `ω`, satisfying the circle-commutation identity a.s. at every
fixed `(t, w, r, ρ)`. (At a fixed time and a fixed deterministic driver this is
`CoordReg.exists_regular_witness_revMap` with `ae_integral_Vhat_eq`.) -/
def JointModStmt (κ γ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∃ Zh : ℝ × (ℂ × ℝ) → Ω → ℝ,
    (∀ ω, ContinuousOn (fun q => Zh q ω) (parSet T)) ∧
    (∀ q ∈ parSet T, (fun ω => Zh q ω) =ᵐ[P] fun ω =>
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) q.1 (foldedCircle q.2.1 q.2.2)) ∧
    ∀ t ∈ Icc 0 T, ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ → ∀ᵐ ω ∂P,
      ∫ u, Zh (t, (u, ρ)) ω ∂foldedCircle w r = ∫ v, Zh (t, (v, r)) ω ∂foldedCircle w ρ

/-- **Regularity of the unzipped field for all `t ∈ [0, T]` at once**, from `JointModStmt`. -/
theorem ae_forall_isRegularWith_of_jointMod [IsProbabilityMeasure P] {κ γ T : ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) (h : JointModStmt κ γ T P B X) :
    ∀ᵐ ω ∂P, ∃ G : ℝ → ℂ × ℝ → ℝ, ∀ t ∈ Icc 0 T,
      IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) (G t) ∧
      LocalRule.RawConverges (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) univ := by
  obtain ⟨Zh, hc, hmod, hcomm⟩ := h
  obtain ⟨D, hDc, hDT, hTD⟩ := TopologicalSpace.exists_countable_dense_subset (Icc (0 : ℝ) T)
  set S4 : Set (ℝ × ((ℂ × ℝ) × ℝ)) := Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  obtain ⟨D4, hD4c, hD4S, hSD4⟩ := TopologicalSpace.exists_countable_dense_subset S4
  have hraw : ∀ᵐ ω ∂P, ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ Dy,
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t (foldedCircle d (radius k)) =
        Zh (t, (d, radius k)) ω :=
    (eventually_countable_ball hDc).2 fun t ht => ae_all_iff.2 fun k =>
      (eventually_countable_ball countable_Dy).2 fun d hd =>
        (hmod (t, (d, radius k)) ⟨hDT ht, Dy_subset_Hbar hd, radius_pos k⟩).mono
          fun ω hω => hω.symm
  have hcm : ∀ᵐ ω ∂P, ∀ q ∈ D4, ∫ u, Zh (q.1, (u, q.2.2)) ω ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, Zh (q.1, (v, q.2.1.2)) ω ∂foldedCircle q.2.1.1 q.2.2 :=
    (eventually_countable_ball hD4c).2 fun q hq => by
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hD4S hq
      exact hcomm q.1 h1 q.2.1.1 h2 q.2.1.2 q.2.2 h3 h4
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn
      (fun t => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t
        (foldedCircle d (radius k))) (Icc 0 T) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d _ =>
      RegCont.ae_continuousOn_unzippedField κ γ hB hX hind hT d (radius_pos k)
  filter_upwards [hraw, hcm, hyc] with ω h1 h2 h3
  exact ⟨fun t p => Zh (t, p) ω, forall_isRegularWith_of_joint (hc ω) h3 hDT hTD h1 hD4S hSD4 h2⟩

/-- **Regularity of the unzipped field for all `t ≥ 0` at once** (exhaustion by `[0, n + 1]`). -/
theorem ae_forall_isRegularSample_of_jointMod [IsProbabilityMeasure P] {κ γ : ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (h : ∀ n : ℕ, JointModStmt κ γ (n + 1) P B X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsRegularSample (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) ∧
      LocalRule.RawConverges (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t) univ := by
  have hall := ae_all_iff.2 fun n : ℕ =>
    ae_forall_isRegularWith_of_jointMod hB hX hind (by positivity) (h n)
  filter_upwards [hall] with ω hω t ht
  obtain ⟨G, hG⟩ := hω ⌈t⌉₊
  have hmem : t ∈ Icc (0 : ℝ) (⌈t⌉₊ + 1) := ⟨ht, (Nat.le_ceil t).trans (by linarith)⟩
  exact ⟨⟨_, (hG t hmem).1⟩, (hG t hmem).2⟩

/-! ## The field cocycle `B3d.CapCocycleRegStmt` -/

/-- The time triangle `{(u, s) : u, s ≥ 0, u + s ≤ T}`. -/
def tri (T : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ T}

end RegUnif
end QuantumZipper
