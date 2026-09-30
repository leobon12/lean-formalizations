import QuantumZipper.Proofs.Thm18.G1PkgSel
import QuantumZipper.Proofs.Complex.KernelChordKT2
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# G1 package: chord-measurable inverse uniformizers from a countable dense family of chords

Generic construction for one side. Data (`G1Chord.SideData dom Nrm`): side domains `dom η`
(open for simple chords), a normalization `Nrm η φ` of uniformizers that exists for every simple
chord, and a kernel theorem (KT2: sphere-uniform convergence of simple chords gives locally
uniform convergence of the `Nrm`-normalized inverse uniformizers on `ℍ`). Given a countable family
`ηk` of simple chords, dense for the sphere-uniform metric among simple chords (`ChordSepStmt`),
we build `U η`, jointly measurable in `(η, z)` (product σ-algebra on `ℝ → ℂ`), with measurable
`log ‖(U η)'‖`, equal to an inverse normalized uniformizer for every simple chord:

* `sel n η`: the first `k` with `dQ (ηk k) η < 1/(n+1)`, where `dQ` is the chordal distance read
  at rational times (measurable in `η`); for a simple chord, `ηk (sel n η) → η` sphere-uniformly;
* `Good η`: the maps `ψ_{sel n η}` are uniformly Cauchy on each `Kj j` (read on a countable dense
  set; measurable); simple chords are good by KT2;
* `U η w = lim ψ_{sel n η}(w)` for `w ∈ ℍ`, `η` good; `U η w = w` on `ℍ` otherwise; and
  `U η w = c₀` (the junk value of `invFunOn`) off `ℍ`. Derivatives: Weierstrass
  (`TendstoLocallyUniformlyOn.deriv`) on `ℍ`, `0` off `ℍ`.

Own argument (measurable selection by a countable dense family; the analytic input is KT2,
Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 1.8, via `CA.Kernel`).
-/

noncomputable section

open MeasureTheory Filter Set Function Topology Metric
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

open CA.Kernel

/-- The chordal distance of two chords read at nonnegative rational times. -/
def dQ (η₁ η₂ : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (chordalDist (η₁ q) (η₂ q))

theorem continuous_chordalDist : Continuous fun p : ℂ × ℂ => chordalDist p.1 p.2 := by
  unfold chordalDist
  refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
  positivity

theorem measurable_dQ (η₁ : ℝ → ℂ) : Measurable fun η : ℝ → ℂ => dQ η₁ η := by
  unfold dQ
  refine Measurable.iSup fun q => ENNReal.measurable_ofReal.comp ?_
  exact continuous_chordalDist.measurable.comp (measurable_const.prodMk (measurable_pi_apply _))

/-- On continuous chords, `dQ` dominates the chordal distance at every time `t ≥ 0`. -/
theorem ofReal_chordalDist_le_dQ {η₁ η₂ : ℝ → ℂ} (h₁ : ContinuousOn η₁ (Ici 0))
    (h₂ : ContinuousOn η₂ (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (chordalDist (η₁ t) (η₂ t)) ≤ dQ η₁ η₂ := by
  set q : ℕ → ℚ := fun n => (⌈t * ((n : ℝ) + 1)⌉₊ : ℚ) / ((n : ℚ) + 1) with hq
  have hq0 : ∀ n, (0 : ℚ) ≤ q n := fun n => by positivity
  have hqc : ∀ n, ((q n : ℚ) : ℝ) = (⌈t * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) := fun n => by
    simp [hq]
  have hqt : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝[Ici 0] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have hlo : ∀ n : ℕ, t ≤ ((q n : ℚ) : ℝ) := fun n => by
        rw [hqc, le_div_iff₀ (by positivity)]; exact Nat.le_ceil _
      have hhi : ∀ n : ℕ, ((q n : ℚ) : ℝ) ≤ t + 1 / ((n : ℝ) + 1) := fun n => by
        rw [hqc, div_le_iff₀ (by positivity), add_mul, one_div_mul_cancel (by positivity)]
        exact (Nat.ceil_lt_add_one (by positivity)).le
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlo hhi
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := t)).add h0
    · show (0 : ℝ) ≤ ((q n : ℚ) : ℝ); exact_mod_cast hq0 n
  have hc : ContinuousWithinAt (fun s => ENNReal.ofReal (chordalDist (η₁ s) (η₂ s))) (Ici 0) t :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuous_chordalDist.continuousAt.comp_continuousWithinAt ((h₁ t ht).prodMk (h₂ t ht)))
  refine le_of_tendsto (hc.tendsto.comp hqt) (Eventually.of_forall fun n => ?_)
  exact le_iSup (fun q : {q : ℚ // 0 ≤ q} => ENNReal.ofReal (chordalDist (η₁ q) (η₂ q)))
    ⟨q n, hq0 n⟩

/-- **(C1) Separability** of simple chords for the sphere-uniform metric. -/
def ChordSepStmt : Prop :=
  ∃ ηk : ℕ → ℝ → ℂ, (∀ k, IsSimpleChord (ηk k)) ∧
    ∀ η, IsSimpleChord η → ∀ ε > 0, ∃ k, ∀ t ≥ (0 : ℝ), chordalDist (ηk k t) (η t) < ε

/-- The side data of the construction. -/
structure SideData (dom : (ℝ → ℂ) → Set ℂ) (Nrm : (ℝ → ℂ) → (ℂ → ℂ) → Prop) : Prop where
  isOpen : ∀ η, IsSimpleChord η → IsOpen (dom η)
  normalized : ∀ η φ, IsSimpleChord η → Nrm η φ → IsNormalizedUniformizer (dom η) φ
  exists_nrm : ∀ η, IsSimpleChord η → ∃ φ, Nrm η φ
  kernel : ∀ (η : ℕ → ℝ → ℂ) (ηi : ℝ → ℂ) (φ : ℕ → ℂ → ℂ) (φi : ℂ → ℂ),
    (∀ n, IsSimpleChord (η n)) → IsSimpleChord ηi → SphereUniformConv η ηi →
    (∀ n, Nrm (η n) (φ n)) → Nrm ηi φi →
    TendstoLocallyUniformlyOn (fun n => invFunOn (φ n) (dom (η n))) (invFunOn φi (dom ηi))
      atTop H

/-! ## The selection -/

section Sel

variable (ηk : ℕ → ℝ → ℂ)

/-- The admissibility predicate of index `k` at precision `n`. -/
def selAdmits (n : ℕ) (η : ℝ → ℂ) (k : ℕ) : Prop :=
  dQ (ηk k) η < ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∨
    ∀ j, ¬ dQ (ηk j) η < ENNReal.ofReal (1 / ((n : ℝ) + 1))

theorem exists_selAdmits (n : ℕ) (η : ℝ → ℂ) : ∃ k, selAdmits ηk n η k := by
  by_cases h : ∃ j, dQ (ηk j) η < ENNReal.ofReal (1 / ((n : ℝ) + 1))
  · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr fun j hj => h ⟨j, hj⟩⟩

open Classical in
/-- The selected index. -/
def sel (n : ℕ) (η : ℝ → ℂ) : ℕ := Nat.find (exists_selAdmits ηk n η)

theorem measurable_sel (n : ℕ) : Measurable (sel ηk n) := by
  classical
  refine measurable_find (exists_selAdmits ηk n) fun k => ?_
  have e : {η | selAdmits ηk n η k} = {η | dQ (ηk k) η < ENNReal.ofReal (1 / ((n : ℝ) + 1))} ∪
      ⋂ j, {η | dQ (ηk j) η < ENNReal.ofReal (1 / ((n : ℝ) + 1))}ᶜ := by
    ext η; simp [selAdmits]
  rw [e]
  exact (measurableSet_lt (measurable_dQ _) measurable_const).union
    (MeasurableSet.iInter fun j => (measurableSet_lt (measurable_dQ _) measurable_const).compl)

theorem dQ_sel_lt {n : ℕ} {η : ℝ → ℂ}
    (h : ∃ j, dQ (ηk j) η < ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    dQ (ηk (sel ηk n η)) η < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  classical
  have hs := Nat.find_spec (exists_selAdmits ηk n η)
  rcases hs with hs | hs
  · simpa [sel] using hs
  · obtain ⟨j, hj⟩ := h; exact absurd hj (hs j)

/-- For a simple chord, the selected chords converge sphere-uniformly. -/
theorem sphereUniformConv_sel (hk : ∀ k, IsSimpleChord (ηk k))
    (hden : ∀ η, IsSimpleChord η → ∀ ε > 0, ∃ k, ∀ t ≥ (0 : ℝ), chordalDist (ηk k t) (η t) < ε)
    {η : ℝ → ℂ} (hη : IsSimpleChord η) :
    SphereUniformConv (fun n => ηk (sel ηk n η)) η := by
  have hlt : ∀ n : ℕ, dQ (ηk (sel ηk n η)) η < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    refine dQ_sel_lt ηk ?_
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
    obtain ⟨k, hk'⟩ := hden η hη _ hpos
    refine ⟨k, lt_of_le_of_lt (b := ENNReal.ofReal (1 / ((n : ℝ) + 1) / 2))
      (iSup_le fun q => ?_) ?_⟩
    · exact ENNReal.ofReal_le_ofReal (hk' q (by exact_mod_cast q.2)).le
    · exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with n hn t ht
  have h1 := (ofReal_chordalDist_le_dQ (hk _).2.1 hη.2.1 ht).trans_lt (hlt n)
  have h2 : chordalDist (ηk (sel ηk n η) t) (η t) < 1 / ((n : ℝ) + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h1
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  linarith

end Sel

end G1Chord
end Thm18Asm
end QuantumZipper
