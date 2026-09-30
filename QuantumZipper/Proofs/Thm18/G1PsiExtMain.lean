import QuantumZipper.Proofs.Thm18.G1RCRep
import QuantumZipper.Proofs.Complex.CaraBdry
import QuantumZipper.Proofs.Thm18.G1PsiExtCara
import QuantumZipper.Proofs.Thm18.G1PsiExtCoord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PSIEXT: `G1RC.G1PsiExtStmt` from the Carathéodory extension and two named inputs

`G1RC.G1PsiExtStmt` (G1RCRep.lean) is the per-path analytic input of the G1 regularity package:
for a.e. path `a` (for the law `P.map (pathOf B)`) and both sides, the selected inverse normalized
uniformizer `ψ = Ψ left a` satisfies `G1RC.PsiExt ψ`: some `ψe` measurable, continuous on `Hbar`,
`ψe(Hbar) ⊆ Hbar`, `ψe = ψ` on `ℍ`, with `PushFamBounds ψe β` for some `β > 0`.

This file proves

* `psiExtContStmt_holds` (**proved, no hypotheses**): for every simple chord, both sides and every
  normalized uniformizer `φ`, `invFunOn φ (sideDom η left)` has a measurable extension, continuous
  on `Hbar`, mapping `Hbar` into `Hbar` (Carathéodory, Pommerenke 1992, Thm 2.6; G1PsiExtCara.lean);
* `g1PsiExtStmt_of_coord` (**the reduction**): `G1PsiExtStmt` follows from
  - `G1PathCoordGoodStmt Good`: for every countable set `S` of times there is a **measurable** set
    `M` of paths of full `P.map (pathOf B)`-measure each of whose members agrees on `S` with some
    continuous path `a'` whose trace `pathTrace (γ²) a'` is a simple chord and which is `Good`;
  - `PsiBoundsGoodStmt γ (Good γ)`: for such good paths `a'`, the inverse uniformizers of both side
    components have the pushed-circle Kolmogorov bounds `PushFamBounds` for some continuous
    extension.

Why this shape. The a.e. statement is over the path law on the product σ-algebra, whose null sets
are only the measurable ones; the naive input "a.e. path is continuous with simple-chord trace"
is **false** for that law (`QuantumZipper.not_ae_continuous_map`, G1PathNoGo.lean). The selection
`Ψ` of `G1PsiSel` is jointly measurable in `(path, z)`, hence `Ψ left a` depends only on the values
of `a` on a countable set `S` of times (`exists_countable_determined_fun`, G1PsiExtCoord.lean);
so it suffices that a.e. path agrees on `S` with a good path, on a measurable set. The
predicate `Good` is left free: the bounds of `PsiBoundsGoodStmt` are **not** true for every simple
chord (a variance modulus with a power `β` needs a Hölder-type boundary behaviour of `ψ`), and for
SLE`_κ`, `κ = γ² < 4`, they are meant to come from the Hölder continuity of the side uniformizers
(Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 5.2) through Frostman
bounds for the pushed circles (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 for the
circle-average analogue).

The reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-- The Carathéodory part of `PsiExt`, per chord: a measurable extension of `ψ` continuous on
`Hbar`, taking values in `Hbar` and agreeing with `ψ` on `ℍ`. -/
def PsiExtContStmt : Prop :=
  ∀ η : ℝ → ℂ, IsSimpleChord η → ∀ left : Bool, ∀ φ : ℂ → ℂ,
    IsNormalizedUniformizer (sideDom η left) φ →
      ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧
        EqOn (invFunOn φ (sideDom η left)) ψe H

/-- **The Carathéodory part holds** (G1PsiExtCara.lean; Pommerenke 1992, Thm 2.6). -/
theorem psiExtContStmt_holds : PsiExtContStmt := by
  intro η hη left φ hφ
  cases left
  · exact exists_measurable_ext_right hη hφ
  · exact exists_measurable_ext_left hη hφ

/-- `Hbar` is the closure of `ℍ` (`CA.Car.closure_H_eq_Hbar`), so a function continuous on
`Hbar` is determined by its values on `ℍ`. -/
theorem eqOn_Hbar_of_continuousOn_of_eqOn_H {f g : ℂ → ℂ} (hf : ContinuousOn f Hbar)
    (hg : ContinuousOn g Hbar) (h : EqOn f g H) : EqOn f g Hbar := by
  have hcl : closure H = Hbar := CA.Car.closure_H_eq_Hbar
  intro z hz
  have hzcl : z ∈ closure H := by rw [hcl]; exact hz
  have hne : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  have hf' : Tendsto f (𝓝[H] z) (𝓝 (f z)) :=
    (hf z hz).mono_left (nhdsWithin_mono z H_subset_Hbar)
  have hg' : Tendsto g (𝓝[H] z) (𝓝 (g z)) :=
    (hg z hz).mono_left (nhdsWithin_mono z H_subset_Hbar)
  have hev : f =ᶠ[𝓝[H] z] g :=
    eventually_of_mem self_mem_nhdsWithin fun w hw => h hw
  exact tendsto_nhds_unique_of_eventuallyEq hf' hg' hev

/-- `PushFamBounds` only sees the values of `ψ` on `Hbar` (the parametrized circles
`pushPhi ψ q` are supported on `ψ '' Hbar`). -/
theorem pushFamBounds_congr_of_eqOn_Hbar {ψ ψ' : ℂ → ℂ} (h : EqOn ψ ψ' Hbar) (β : ℝ) :
    PushFamBounds ψ β ↔ PushFamBounds ψ' β := by
  have hfun : pushPhi ψ = pushPhi ψ' := by
    funext q θ
    simp only [pushPhi]
    rw [h (CircleFubini.foldH_mem_Hbar' _)]
  unfold PushFamBounds
  rw [hfun]

/-- **`PsiExt` from an extension and a (possibly different) continuous extension with the
bounds**: both agree with `ψ` on the dense set `ℍ`, hence on `Hbar`, so the bounds transfer. -/
theorem psiExt_of_ext_of_bounds {ψ : ℂ → ℂ}
    (h1 : ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧ EqOn ψ ψe H)
    (h2 : ∃ ψe : ℂ → ℂ, ∃ β : ℝ, 0 < β ∧ ContinuousOn ψe Hbar ∧ EqOn ψ ψe H ∧
      PushFamBounds ψe β) : PsiExt ψ := by
  obtain ⟨ψe, hψm, hψc, hψH, heq⟩ := h1
  obtain ⟨ψe', β, hβ, hψc', heq', hBd⟩ := h2
  have hsame : EqOn ψe ψe' Hbar :=
    eqOn_Hbar_of_continuousOn_of_eqOn_H hψc hψc' fun z hz => (heq hz).symm.trans (heq' hz)
  exact ⟨ψe, hψm, hψc, hψH, heq, β, hβ, (pushFamBounds_congr_of_eqOn_Hbar hsame β).2 hBd⟩

/-- **Bounds input, for good paths.** For every continuous path `a'` whose trace is a simple
chord and which satisfies `Good`, both side components' inverse normalized uniformizers have a
continuous extension with the pushed-circle Kolmogorov bounds. -/
def PsiBoundsGoodStmt (γ : ℝ) (Good : (ℝ≥0 → ℝ) → Prop) : Prop :=
  ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) → Good a →
    ∀ left : Bool, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left) φ →
      ∃ ψe : ℂ → ℂ, ∃ β : ℝ, 0 < β ∧ ContinuousOn ψe Hbar ∧
        EqOn (invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left)) ψe H ∧ PushFamBounds ψe β

/-- **Path input, countable-coordinate form.** For every countable set `S` of times, a measurable
set `M` of paths of full measure for the path law, each of whose members agrees on `S` with a
continuous `Good` path whose trace is a simple chord. (For a Brownian `B`, `κ = γ² < 4`: take `S`
enlarged by the rationals and `M` = the paths whose restriction to it extends continuously to a
good path; `M` is measurable if the good continuous paths form a Borel set, and has full measure
by Rohde–Schramm 2005, Thm 6.1 (simple trace) and Thm 5.2 (Hölder), with `Good` their conclusion.)
-/
def G1PathCoordGoodStmt (Good : ℝ → (ℝ≥0 → ℝ) → Prop) : Prop :=
  G1RepSetting fun γ _ _ P B _ _ _ _ _ => ∀ S : Set ℝ≥0, S.Countable →
    ∃ M : Set (ℝ≥0 → ℝ), MeasurableSet M ∧ (∀ᵐ a ∂(P.map (pathOf B)), a ∈ M) ∧
      ∀ a ∈ M, ∃ a' : ℝ≥0 → ℝ, (∀ t ∈ S, a' t = a t) ∧ Continuous a' ∧
        IsSimpleChord (pathTrace (γ ^ 2) a') ∧ Good γ a'

/-- **`G1PsiExtStmt` from the countable-coordinate path input and the bounds input.**
Own bookkeeping: `Ψ left a` depends on `a` only through its values on a countable `S`
(joint measurability, `exists_countable_determined_fun`); a.e. `a` agrees on `S` with a good
path `a'`, for which `G1PsiSel` gives `Ψ left a' = invFunOn φ (sideDom … left)`; the extension is
`psiExtContStmt_holds` and the bounds are the input. -/
theorem g1PsiExtStmt_of_coord (Good : ℝ → (ℝ≥0 → ℝ) → Prop) (h1 : G1PathCoordGoodStmt Good)
    (h2 : ∀ γ : ℝ, 0 < γ → γ < 2 → PsiBoundsGoodStmt γ (Good γ)) : G1PsiExtStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  obtain ⟨S1, hS1, hdet1⟩ := exists_countable_determined_fun (hΨ.1 true)
  obtain ⟨S0, hS0, hdet0⟩ := exists_countable_determined_fun (hΨ.1 false)
  obtain ⟨M, -, hae, hgood⟩ :=
    h1 γ hγ hγ2 P B hB P' X A hX hA hXA (S1 ∪ S0) (hS1.union hS0)
  filter_upwards [hae] with a ha
  obtain ⟨a', hagree, hc, hsc, hg⟩ := hgood a ha
  intro left
  have hΨeq : Ψ left a = Ψ left a' := by
    funext z
    cases left
    · exact hdet0 a a' (fun i hi => (hagree i (Or.inr hi)).symm) z
    · exact hdet1 a a' (fun i hi => (hagree i (Or.inl hi)).symm) z
  rw [hΨeq]
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a' hc hsc left
  rw [hΨa]
  exact psiExt_of_ext_of_bounds (psiExtContStmt_holds _ hsc left φ hφ)
    (h2 γ hγ hγ2 a' hc hsc hg left φ hφ)

end G1RC
end Thm18Asm
end QuantumZipper
