import MatedCRTHarmonic.GMS4b.Localized
import MatedCRTHarmonic.GMS4b.Interfaces
import MatedCRTHarmonic.Frozen.MatedCRTExcursionSegment

/-!
# The local configuration space of [18] Lemma 4.3 and the statements

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]
(cited `[18]:N`), Lemma 4.3: "For each open set `V ⊂ ℂ`,
The random variable `DA^ε(z) 1(B̄^ε_z ⊂ V)` is a.s. determined by `h|_V` and `h^IG|_V` … The same is true with
`DA^ε(z)` replaced by either `deg^ε_in(z)` or `deg^ε_out(z)`." Proof: "`μ_h` is determined by `h|_V` … From this,
Lemma 2.4, and the definitions of `DA^ε(z)`, `deg^ε_in(z)`, and `deg^ε_out(z)`, we obtain the statement."

[18] Lemma 2.4 (`[18]`; the bundle field S7, `MatedCRT.IsMatingOfTreesCoupling.igMap`, third clause)
determines the *excursion segments* of the curve into `V`: for each point `z ∈ V`, the segment
`c(T_z + ·)|_{[0, S_z − T_z]}` (`MatedCRT.excursionSegment`) between the last entrance `T_z` of `c` into `V` before
its first hit of `z` and the first exit `S_z` after it. The bundle states it at the rational points
(`ratPt q`, `q ∈ ℚ × ℚ`), as a measurable function into `ℚ × ℚ → ℝ → ℂ`. `LocConf` below is only the
**excursion-coordinate space** of a curve. The source's full local configuration additionally needs the restricted
LQG area measure and field; it is `LocalConfiguration` in `GMS4c/LocalConfiguration.lean`.

* `ExcursionRegular V c`: an auxiliary regularity predicate, including rational-point coverage of excursions.
  The inherited files do not prove this predicate almost surely for the SLE curve.
* `supLocDA`, `supLocDegIn`, `supLocDegOut`, `supLocUStar`: the localized quantities of [18] §4.2 restricted to
  `{B̄^ε ⊂ V}` and maximized over the times spent in a set `S`. With `S = {z}` they dominate the paper's
  `DA^ε(z) 1(B̄^ε_z ⊂ V)` etc. at `τ_z` (and equal them when `z` is hit once); with `S = B_ρ(0)` they dominate
  `max_{z ∈ B_ρ(0)}` (Lemma 4.6). Unlike the value at the *first* hitting time `τ_z`, they are local: the order in
  which the excursions into `V` are visited is not seen inside `V`.
* `IsLocallyDetermined V Φ`: auxiliary factorization through the excursion coordinate alone. It does not state the
  paper's Lemma 4.3 for a quantum-time curve.
The original draft's transfer proposition between arbitrary unrelated cell models was incorrect.
The local-law comparison used in (4.16) is defined and proved from a Radon–Nikodym input in
`GMS4c/Transfer.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b

/-! ## Local configurations -/

/-- The rational point `q.1 + q.2 i`. -/
def ratPt (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- The excursion-coordinate space of [18] Lemma 2.4: rationally indexed curve segments with the product σ-algebra.
The full local configuration is `LocalConfiguration`. -/
abbrev LocConf : Type := ℚ × ℚ → ℝ → ℂ

/-- The excursion-coordinate map: the excursion segments of `c` into `V` at rational points. -/
def locConf (V : Set ℂ) (c : C(ℝ, ℂ)) : LocConf :=
  fun q => MatedCRT.excursionSegment c V (ratPt q)

/-- **Excursion regularity** of a curve with respect to an open set `V`: `c` is surjective and transient
(`c(t) → ∞` as `|t| → ∞`), parametrized by the mass of some measure (`μ(c([s, t])) = t − s`, as space-filling SLE
parametrized by Lebesgue measure or by `γ`-LQG area; this makes distinct excursions have distinct segments), and
every time `t` spent in `V` lies strictly inside the first-hit excursion into `V` of a rational point of `V`, i.e.
every excursion of `c` into `V` appears in `locConf V c`. -/
structure ExcursionRegular (V : Set ℂ) (c : C(ℝ, ℂ)) : Prop where
  surjective : Function.Surjective c
  transient : Tendsto c (cocompact ℝ) (cocompact ℂ)
  param : ∃ μ : Measure ℂ, ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)
  exists_ratPt : ∀ t, c t ∈ V → ∃ q : ℚ × ℚ, ratPt q ∈ V ∧
    MatedCRT.entryBefore c V (ratPt q) < t ∧ t < MatedCRT.exitAfter c V (ratPt q)

/-! ## Localized quantities maximized over the times spent in a set -/

/-- `sup { DA^ε(c, t) : c(t) ∈ S, B̄^ε(c, t) ⊂ V }` (localized area ratio (4.4), ball (4.6)). -/
def supLocDA (ε : ℝ) (V S : Set ℂ) (c : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : c t ∈ S) (_ : locBall ε c t ⊆ V), locDA ε c t

/-- `sup { deg^ε_in(c, t) : c(t) ∈ S, B̄^ε(c, t) ⊂ V }`. -/
def supLocDegIn (ε : ℝ) (V S : Set ℂ) (c : ℝ → ℂ) : ℕ∞ :=
  ⨆ (t : ℝ) (_ : c t ∈ S) (_ : locBall ε c t ⊆ V), locDegIn ε c t

/-- `sup { deg^ε_out(c, t) : c(t) ∈ S, B̄^ε(c, t) ⊂ V }`. -/
def supLocDegOut (ε : ℝ) (V S : Set ℂ) (c : ℝ → ℂ) : ℕ∞ :=
  ⨆ (t : ℝ) (_ : c t ∈ S) (_ : locBall ε c t ⊆ V), locDegOut ε c t

/-- `sup { u^ε_*(c, t) : c(t) ∈ S, B̄^ε(c, t) ⊂ V }` (`u^ε_*` of (4.19)). -/
def supLocUStar (ε : ℝ) (V S : Set ℂ) (c : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : c t ∈ S) (_ : locBall ε c t ⊆ V), locUStar ε c t

/-- An auxiliary factorization through excursion coordinates on regular curves; this omits the restricted area
measure needed for [18] Lemma 4.3. -/
def IsLocallyDetermined {β : Type*} [MeasurableSpace β] (V : Set ℂ) (Φ : C(ℝ, ℂ) → β) : Prop :=
  ∃ F : LocConf → β, Measurable F ∧ ∀ c : C(ℝ, ℂ), ExcursionRegular V c → Φ c = F (locConf V c)

end MatedCRTHarmonic.GMS4c
