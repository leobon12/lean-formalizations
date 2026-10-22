import HigherDimLQGMetric.Sec8.Events
import HigherDimLQGMetric.Freq.Defs
import HigherDimLQGMetric.Core.MainInputs

/-!
# [S] §§8–9 interface: what S8 consumes from S7b (orchestrator-owned; ruling M35)

Orchestrator-owned interface module (installed from the planning draft P89, `planning/drafts/Sec89Interfaces.lean.txt`),
written on top of S7a's landed definitions (`HigherDimLQGMetric/Sec8/*.lean`, handoff `planning/handoffs/S7a.md`,
ruling M34). Interface pattern (rulings M30–M33): the producer proves the named `Prop`, the consumer takes it
as a hypothesis, the assembly discharges it.

* §1 — the events of [S] Proposition 8.6 as sets of distributions: the covering event (23) exactly as bounded
  by S7a's `lemma72`, the scale-bin event (25) exactly as bounded by S7d's `lemma81` (complement), their
  intersection `𝒜^ε_R`, and the near-extreme event (27), which is S7a's (C1) `sec8C1` at `q = ε^{B+1}`.
* §2 — `Prop86Shape` (MA4 A16, (30)) for one pair, one trap datum `T : Sec8TrapData` (the output of
  `lemma72`) and one bin exponent `B`; `Prop86Stmt`, its closed form with exactly the hypotheses S8 can
  supply (S7b's export: `theorem prop86Stmt : Prop86Stmt`, unconditional); `S8Goal`
  (S8's export: `theorem theorem14Sharp_of : Prop86Stmt → Theorem14SharpStmt`, i.e. `S8Goal`).
* §3 — S8's internal milestones, stated so that S8 can be split into parallel packets:
  the optimal comparison constants (`upperCompSet`, `optUpper`, `OptUpperShape`), the macro-normalizer
  bound (33) (`MacroRatioShape`), and claim (32) (`Claim32Shape`, `Claim32Stmt`).

Probabilities of the §8–§9 events are **outer** measures `P {ω | …}` (no measurability is claimed;
ruling M34: the raw favorable events are only null-measurable, their Borel representative is S7a's
`FavEventBorel`). Every bound exponent has an explicit type (ruling M29): `N : ℝ` and `ε ^ N`,
`ε ^ (B + 1)`, `ε ^ B` are real powers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The events of Proposition 8.6 -/

/-- **(23)**, the common covering event of [S] Lemma 7.2: every point of `B_{5R}` lies within `r/2` of a
lattice site `z ∈ (r/(100d))ℤ^d`, `r = 64^j ∈ [ε²R, εR]`, at which one of the `J` trap configurations
occurs. With `J = T.J`, `N = T.N` for the trap datum `T` returned by `lemma72`, the failure set bounded by
`lemma72` is literally `{ω | h ω ∉ sec8CoverEvent D Dt ξ Q T.J T.N ε R}`. -/
def sec8CoverEvent (D Dt : DistRd d → ContMetric d) (ξ Q : ℝ) (J : ℕ) (N : ℕ → Set (Config d))
    (ε R : ℝ) : Set (DistRd d) :=
  {g | ∀ x ∈ Metric.ball (0 : Rd d) (5 * R), ∃ j ∈ scaleWin ε R, ∃ k : Fin d → ℤ,
      ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
      g ∈ trapSiteEvent D Dt ξ Q J N ((64 : ℝ) ^ j) (latPt ((64 : ℝ) ^ j / (100 * d)) k)}

/-- **(25)**, the scale-bin event of [S] Lemma 8.1: `ε^B ≤ s_r(z)/S ≤ ε^{-B}` for every `r ∈ 𝒮 ∩ [ε²R, εR]`
and every `z ∈ (r/(100d))ℤ^d ∩ B_{5R}`. Its complement is the exceptional set bounded by `lemma81`. -/
def sec8BinEvent (d : ℕ) (ξ Q B ε R : ℝ) : Set (DistRd d) :=
  {g | ∀ r ∈ scaleLattice, ε ^ 2 * R ≤ r → r ≤ ε * R → ∀ z : Rd d, ‖z‖ < 5 * R →
    (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) →
    ε ^ B ≤ sNorm ξ Q g r z / macroS ξ Q g R ∧ sNorm ξ Q g r z / macroS ξ Q g R ≤ ε ^ (-B)}

/-- `𝒜^ε_R` of [S] Proposition 8.6: the intersection of the covering event (23) and the bin event (25). It
depends neither on the endpoints nor on `N`. -/
def sec8AEvent (D Dt : DistRd d → ContMetric d) (ξ Q : ℝ) (J : ℕ) (N : ℕ → Set (Config d))
    (B ε R : ℝ) : Set (DistRd d) :=
  sec8CoverEvent D Dt ξ Q J N ε R ∩ sec8BinEvent d ξ Q B ε R

/-! ## 2. Proposition 8.6 and S8's goal -/

/-- **[S] Proposition 8.6** ((30); MA4 Details (a) A16) for the pair `(D, D̃) = (D, Dt)`, the upper
comparison constant `C_* = Cs`, the trap datum `T` (Proposition 6.2's `m, V, J, f_j, N_j, a, b, c, g, H, M_f,
c'` with (T) on `N_j`; the output of `lemma72`) and the bin exponent `B` of Lemma 8.1. For every
`η ∈ (0, 1]` and every `N > 0` there are `C_N` and `ε(N, η) > 0` such that, for every whole-space LGF on any
probability space, every `R > 0`, all deterministic `x, y ∈ B_{3R}` with `|x − y| ≥ ηR` and every
`0 < ε < ε(N, η)`:
`P[𝒜^ε_R ∩ {D̃_h(x,y) ≥ C_* D_h(x,y) − ε^{B+1} S}] ≤ C_N ε^N`, `S = R^{ξQ} e^{ξ h_{8R}(0)}` (`macroS`).
The near-extreme condition (27) is S7a's (C1) `sec8C1 … Cs q R x y` at `q = ε^{B+1}`, i.e.
`Cs * D_h(x,y) − ε^(B+1) * macroS ξ Q h R ≤ Dt_h(x,y)`. As noted in MA4 A16, (19) is not needed here (it only
makes `P[𝒜^ε_R]` large); the bound holds for every `R > 0`. -/
def Prop86Shape (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d) (cs Cs : ℝ)
    (T : Sec8TrapData d ξ cs Cs D Dt) (B : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ N : ℝ, 0 < N → ∃ C ε₁ : ℝ, 0 < ε₁ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
    ∀ R : ℝ, 0 < R → ∀ x y : Rd d, ‖x‖ < 3 * R → ‖y‖ < 3 * R → η * R ≤ ‖x - y‖ →
    ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      P {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
          sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} ≤ ENNReal.ofReal (C * ε ^ N)

/-- **Proposition 8.6, closed form** (S7b's export `prop86Stmt : Prop86Stmt`): for `d ≥ 3`, `ξ > 0`,
`Q > √(2d)`, two sharp weak assignments, constants `0 < c_* ≤ C_*` with the a.s. comparison
`c_* D ≤ D̃ ≤ C_* D` for every whole-space LGF (the hypothesis `hcomp` of `sec6Package_of_sharp`, verbatim),
**every** trap datum `T` and every `B > 0`. `T` is universally quantified because S8 obtains it from the
existential of `lemma72`. (`0 < c_*`, `c_* ≤ C_*` are not needed mathematically but let S7b apply
`IsWeakExpMetric.ae_apply_compare` directly; S8 has them.) -/
def Prop86Stmt : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ Q : ℝ}, 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ {D Dt : DistRd d → ContMetric d}, IsSharpWeakExpMetric d ξ Q D →
      IsSharpWeakExpMetric d ξ Q Dt →
    ∀ {cs Cs : ℝ}, 0 < cs → cs ≤ Cs →
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
          ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
            (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v)) →
    ∀ (T : Sec8TrapData d ξ cs Cs D Dt) {B : ℝ}, 0 < B → Prop86Shape d ξ Q D Dt cs Cs T B

/-- S8's goal: [S] §9 ((32) and the closing argument) proves the Phase A anchor's statement from
Proposition 8.6. S8 exports `theorem theorem14Sharp_of : Prop86Stmt → Theorem14SharpStmt`; the assembly
`theorem14Sharp_impl := theorem14Sharp_of prop86Stmt`. -/
def S8Goal : Prop := Prop86Stmt → Theorem14SharpStmt

/-! ## 3. S8's internal milestones (S8-owned; allow S8 to be split into parallel packets) -/

/-- the a.s. upper comparison constants of the ordered pair `(A, B)` (`B ≤ U A`), over all whole-space LGFs -/
def upperCompSet (A B : DistRd d → ContMetric d) : Set ℝ :=
  {U | ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ x y : Rd d, (B (h ω)).1 (x, y) ≤ U * (A (h ω)).1 (x, y)}

/-- the optimal essential upper comparison constant of `(A, B)` ([S] l. 158–168). The source's constants are
`C_* = optUpper D D̃` and `c_* = (optUpper D̃ D)⁻¹` (the lower pair `(D̃, D)` has optimal upper constant `1/c_*`). -/
def optUpper (A B : DistRd d → ContMetric d) : ℝ := sInf (upperCompSet A B)

/-- **Optimal constants** ([S] l. 158–168): for two sharp weak assignments the optimal upper constant is
positive and optimal in MA3's sense (`IsOptUpper`: attained a.s. for every LGF, and no smaller constant works
a.s. for any LGF). Proof: (E3) (`e3_sharp` + `lemmaA1`) for nonemptiness, an LGF (`exists_isWholeSpaceLGF`)
for positivity, countable intersection for attainment, and law transfer of `{g | ∀ x y, B_g ≤ U A_g}` between
LGFs (constant invariance + `normalizedLawUnique`) for optimality at every LGF. -/
def OptUpperShape : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ Q : ℝ}, 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ {A B : DistRd d → ContMetric d}, IsSharpWeakExpMetric d ξ Q A → IsSharpWeakExpMetric d ξ Q B →
      0 < optUpper A B ∧ IsOptUpper d A B (optUpper A B)

/-- **(33)**, upper half: `s_R(0)/S = e^{ξ(h_R(0) − h_{8R}(0))}` is bounded by a deterministic `L`, uniformly in `R`
and over all LGFs, outside an event of probability `≤ δ` (only the upper bound is used in §9). -/
def MacroRatioShape (d : ℕ) (ξ Q : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ L : ℝ, 1 ≤ L ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ R : ℝ, 0 < R →
        P {ω | L * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0} ≤ ENNReal.ofReal δ

/-- **Claim (32)** for one LGF: there is a deterministic `t ∈ (0, C_*)` such that `P[H⁺_R(t)] < p_*` at every
scale `R` satisfying (19). `H⁺_R(t)` is the witness event of the upper pair `(D, D̃)` (`U = C_*`, constants
`aU A₀U ℓU β₀U` from `section5Package_cor55`); (19) is the lower pair's `P[H⁻_R(1/c₀)] ≥ p_*` (`U = 1/c_*`,
constants `aL A₀L ℓL β₀L`), exactly the premise of `lemma72` and `Cor63`. `t` may depend on the LGF (the
modulus constants of `lemma26_modulus` do), but not on `R`. -/
def Claim32Shape (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (cs Cs c0 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
  ∃ t : ℝ, 0 < t ∧ t < Cs ∧ ∀ R : ℝ, 0 < R →
    ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0) →
    P (h ⁻¹' WitEvent D Dt ξ Q Cs aU A₀U ℓU β₀U t R 0) < ENNReal.ofReal pstar

/-- **Claim (32), closed form** (S8's `claim32_of : Prop86Stmt → (∀ d ξ Q, 2 ≤ d → MacroRatioShape d ξ Q) →
Claim32Stmt`): the hypotheses are those of `lemma72` (the conclusions of `sec6Package_of_sharp`), the a.s.
comparison with `0 < c_* ≤ C_*` (as in `Prop86Stmt`), and positivity of `p_*` and of the upper pair's `ℓ`, `β₀`
(needed for `s6b_witEvent_subset_gEvent`). -/
def Claim32Stmt : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ Q : ℝ}, 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ {D Dt : DistRd d → ContMetric d}, IsSharpWeakExpMetric d ξ Q D →
      IsSharpWeakExpMetric d ξ Q Dt →
    ∀ {cs Cs c0 c1 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar : ℝ},
      0 < cs → cs ≤ Cs → 0 < pstar → 0 < ℓU → 0 < β₀U →
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
          ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
            (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v)) →
      TrapFamily d ξ Q D Dt cs Cs c1 aL A₀L ℓL β₀L pstar → ConfigLocal d ξ Q D Dt →
      (∀ m : ℕ, Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m) →
      Claim32Shape d ξ Q D Dt cs Cs c0 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar

end HigherDimLQGMetric
