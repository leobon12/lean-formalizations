/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxAe
import InteractingSLE.Spec.Supplement.GW2BwSel

/-!
# The cap and buffer selection at the conditioning sample (decision D75)

Packet PROVE-GW2-BUF (round 21). The near candidate of slot `(l, n, m)` at the conditioning sample `ω₀` is
`Nat.pair i (Nat.pair q b)`: `i` the rightward selection's angle index (`angSelS`), `(q, b)` chosen at `ω₀` so that
D75's bad set `ZsS = aliveVer ∩ ZbS` has conditional measure at most `1/(m+1)` (`kSelS`). The choice needs no
measurability of the presentation: it is made per conditioning sample, and it succeeds at every angle index whose
bad sets are avoided for almost every kernel sample (two-level dominated convergence, NEARIMG2's
`GW2Ni.exists_pair_measure_le`).

* `ZsS`, `measurableSet_ZsS`, **`kSelS`**, **`kSelS_spec`**;
* `angSelS`, **`kSelBS`** (a `NearSelB`), `nearCandidate_kSelBS`;
* **`ae_refPreV_verU_eq`**: the reference record of the re-indexed family is the base family's.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

section Sets

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- D75's bad sets inside the retained alive version. -/
def ZsS (n i q b : ℕ) : Set Ω := aliveVer h13 c r l ∩ ZbS h13 ver₀ ch c r l n i q b

theorem measurableSet_ZsS (hI : InstInputsX h13 (verS h13 ver₀ ch) ch) (hTO : GW2Sdx.HistOrdered c r l)
    (n i q b : ℕ) : MeasurableSet (ZsS h13 ver₀ ch c r l n i q b) :=
  (sigma_le_ambient c r l _ (measurableSet_aliveVer h13 c r l)).inter
    (measurableSet_ZbS h13 ver₀ ch c r l hI hTO n i q b)

open Classical in
/-- **The cap and buffer selection at the conditioning sample**: a pair `Nat.pair q b` whose bad set has
conditional measure at most `1/(m+1)`, when one exists. -/
def kSelS (ω₀ : Ω) (n i m : ℕ) : ℕ :=
  if h : ∃ k : ℕ, condExpKernel c.P (c.sigma r l) ω₀
      (ZsS h13 ver₀ ch c r l n i (Nat.unpair k).1 (Nat.unpair k).2) ≤ ((m : ℝ≥0∞) + 1)⁻¹ then h.choose else 0

/-- **The selection's bound** at every angle index whose bad sets are avoided by almost every kernel sample. -/
theorem kSelS_spec (hI : InstInputsX h13 (verS h13 ver₀ ch) ch) (hTO : GW2Sdx.HistOrdered c r l) (ω₀ : Ω)
    (n i : ℕ) (hav : ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∃ Q : ℝ≥0, ∀ q : ℕ,
      Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) → ∀ᶠ b in atTop, ξ ∉ ZsS h13 ver₀ ch c r l n i q b) (m : ℕ) :
    condExpKernel c.P (c.sigma r l) ω₀ (ZsS h13 ver₀ ch c r l n i (Nat.unpair (kSelS h13 ver₀ ch c r l ω₀ n i m)).1
      (Nat.unpair (kSelS h13 ver₀ ch c r l ω₀ n i m)).2) ≤ ((m : ℝ≥0∞) + 1)⁻¹ := by
  classical
  have hm : (0 : ℝ≥0∞) < ((m : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  obtain ⟨q, b, hqb⟩ := GW2Ni.exists_pair_measure_le (μ := condExpKernel c.P (c.sigma r l) ω₀)
    (measurableSet_ZsS h13 ver₀ ch c r l hI hTO n i) (GW2Ni.exists_capIdx_ge c r) hav hm
  have hE : ∃ k : ℕ, condExpKernel c.P (c.sigma r l) ω₀
      (ZsS h13 ver₀ ch c r l n i (Nat.unpair k).1 (Nat.unpair k).2) ≤ ((m : ℝ≥0∞) + 1)⁻¹ :=
    ⟨Nat.pair q b, by rw [Nat.unpair_pair]; exact hqb⟩
  unfold kSelS
  rw [dite_eq_left hE]
  exact hE.choose_spec

/-- **The reference record of the re-indexed family is the base family's** (almost surely on the alive event, when
some slot passes the clock). -/
theorem ae_refPreV_verU_eq (ψ : PsiFam.{u}) (gap : RootCv.GapFamily.{u}) (hg : GoodRoot c r) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      (∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
          (RootJ31.historyTime c r l) ξ) < (GW2Rl.verU ver₀ ψ Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ξ) →
        GW2Rl.refPreV h13 (GW2Rl.verU ver₀ ψ) Ω c r l ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ := by
  filter_upwards [ae_slotRec_eq_refV h13 c r l ver₀ gap hg] with ξ href halive hex
  unfold GW2Rl.refPreV
  rw [dite_eq_left hex]
  exact href halive _ _ (Nat.find_spec hex)

end Sets

variable (K₀ : PkgFamily.{u})

/-- **The angle index of the package's near candidate** (the rightward selection's; it does not read the cap and
buffer selection). -/
def angSelS (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (m : ℕ) : ℕ :=
  (Nat.unpair ((pkgS h13 ver₀ ch K₀ kZero k Ω c r).nearCandidate l ω 0 m)).1

/-- **BUF's near selection on the stop family**: the selection at the conditioning sample, at the selected angle. -/
def kSelBS : NearSelB.{u} := fun k Ω _ _ c r l ω n m =>
  kSelS h13 ver₀ ch c r l ω n (angSelS h13 ver₀ ch K₀ k Ω c r l ω m) m

/-- The package's near candidate with BUF's selection. -/
theorem nearCandidate_kSelBS (k : ℕ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (n m : ℕ) :
    (pkgS h13 ver₀ ch K₀ (kSelBS h13 ver₀ ch K₀) k Ω c r).nearCandidate l ω n m =
      Nat.pair (angSelS h13 ver₀ ch K₀ k Ω c r l ω m)
        (kSelS h13 ver₀ ch c r l ω n (angSelS h13 ver₀ ch K₀ k Ω c r l ω m) m) := by
  simp only [angSelS, kSelBS, pkgS, withNearSB, Nat.unpair_pair]

end InteractingSLE.Theorem14.GW2Bh
