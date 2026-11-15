/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateSide

/-!
# Theorem 1.2's late side lattice leaf from an integer phase index

PROVE-SIDE-LATCOL. The native late side wiring (`late_pocketSideInput` and its Beacon tops) takes the
caller-supplied side data `side j : Late.SideData Ω` and two R.7 side leaves about its phase: the lattice
leaf `hSideLattice` (the phase lies in `ℤ · phaseStep κ` before the traversal lifetime) and the collar leaf
`hSideCollar` (R.5's comparison of local-set harmonic means with the force-boundary word shifted by the
phase on the exposed interval).

In the source the lattice property is part of the word itself: R.5 gives the exposed heights
`−Λ + δ_t`, `+Λ + δ_t` with `δ_t ∈ 2πχℤ` (Astra follow-up 5, (3.1)). This file represents the phase by an
integer index, `SideData.intPhase e κ m` (phase `m q ω · phaseStep κ`), for which the lattice leaf holds by
construction (`lateSideLattice_intPhase`, `lateSideLattice_of_isIntPhase`). The representation loses
nothing: from any data satisfying both leaves, the integer-indexed data with the index read off from the
phase (`SideData.latticeIndex`) satisfies the collar leaf again (`lateSideCollar_latticeIndex`), and the
fields used by the other side leaves (`sets`, `info`, `level`, `lift`, `offset`) are unchanged
(`SideData.intPhase_*`, all `rfl`).

No new mathematics of R.5 is claimed here: the collar leaf for the integer phase is exactly the source's
statement (3.1), and it remains the named input. `LateSideLattice` and `LateSideCollar` are verbatim copies
of the per-test binders `hSideLattice` and `hSideCollar` of `late_pocketSideInput` (checked in the handoff's
scratch file by passing them to `late_pocketSideInput` as those named arguments).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel

namespace Late

/-- **Integer-indexed side data**: the phase is `m q ω · phaseStep κ`; all other fields are those of `e`. -/
def SideData.intPhase {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) : SideData Ω :=
  { e with phase := fun q ω => (m q ω : ℝ) * phaseStep κ }

/-- The phase of `e` is an integer multiple of `phaseStep κ` at every time and sample. -/
def SideData.IsIntPhase {Ω : Type} (e : SideData Ω) (κ : ℝ) : Prop :=
  ∀ (q : ℝ≥0) (ω : Ω), ∃ m : ℤ, e.phase q ω = m * phaseStep κ

theorem SideData.intPhase_phase {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) (q : ℝ≥0)
    (ω : Ω) : (e.intPhase κ m).phase q ω = (m q ω : ℝ) * phaseStep κ := rfl

theorem SideData.intPhase_sets {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).sets = e.sets := rfl

theorem SideData.intPhase_info {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).info = e.info := rfl

theorem SideData.intPhase_level {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).level = e.level := rfl

theorem SideData.intPhase_lift {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).lift = e.lift := rfl

theorem SideData.intPhase_offset {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).offset = e.offset := rfl

theorem SideData.isIntPhase_intPhase {Ω : Type} (e : SideData Ω) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    (e.intPhase κ m).IsIntPhase κ :=
  fun q ω => ⟨m q ω, rfl⟩

open Classical in
/-- The integer read off from a lattice phase (`0` where the phase is not a lattice value). -/
def SideData.latticeIndex {Ω : Type} (e : SideData Ω) (κ : ℝ) : ℝ≥0 → Ω → ℤ :=
  fun q ω => if h : ∃ m : ℤ, e.phase q ω = m * phaseStep κ then h.choose else 0

/-- Where the phase is a lattice value, the integer-indexed data have the same phase. -/
theorem SideData.intPhase_latticeIndex_phase {Ω : Type} (e : SideData Ω) (κ : ℝ) {q : ℝ≥0} {ω : Ω}
    (h : ∃ m : ℤ, e.phase q ω = m * phaseStep κ) :
    (e.intPhase κ (e.latticeIndex κ)).phase q ω = e.phase q ω := by
  rw [SideData.intPhase_phase]
  simp only [SideData.latticeIndex, h, ↓reduceDIte]
  exact h.choose_spec.symm

end Late

/-- The parameter of every late side target is `16 / (16 / κ)`, whatever its shape. -/
theorem SideTest.target_kappa {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω) (i : BothLow)
    (d : WordObjects Ω) : (j.target i d).kappa = 16 / (16 / i.kappa) := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;> rfl

/-- **The lattice binder** `hSideLattice` of `late_pocketSideInput`, verbatim, for one family of side data. -/
def LateSideLattice {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ q : ℝ≥0,
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa

/-- **The collar binder** `hSideCollar` of `late_pocketSideInput`, verbatim, for one family of side data. -/
def LateSideCollar {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0,
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
      target.zeroField target.measure (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField
        target.measure g →
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart) q ω) →
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (activeCompl target.event target.curve target.baseChart) q ω →
          g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
            segDriver (target.curve ω) q)
          (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
            segDriver (target.curve ω) q) →
          ∃ (i : ℕ) (b d : ℝ),
            let inv := (relChart target.baseChart target.curve q ω).2.1;
            let vB := harmRep (gB i ω)
              (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level ω);
            Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
            Tendsto (fun y => vB (inv y) + target.harmonic (inv y) +
                chiC target.kappa * refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
            Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) -
                refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
            b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
                segDriver (target.curve ω) q)
              (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
                segDriver (target.curve ω) q)
              ξ + refs.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                  zL q ω - segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                  zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset

/-- **The lattice leaf holds for integer-phase data**: if every `side j` has an integer phase at the late
parameter `16 / (16 / κ)`, the binder `hSideLattice` holds (for every word frame `d`). -/
theorem lateSideLattice_of_isIntPhase {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (hside : ∀ j, (side j).IsIntPhase (16 / (16 / i.kappa))) :
    LateSideLattice i d side := by
  intro j _ _ _ q
  refine Eventually.of_forall fun ω _ _ => ?_
  show ∃ m : ℤ, (side j).phase q ω = m * phaseStep (j.target i d).kappa
  rw [SideTest.target_kappa]
  exact hside j q ω

/-- **The lattice leaf for integer-indexed data** `(sideZ j).intPhase (16 / (16 / κ)) (idx j)`. -/
theorem lateSideLattice_intPhase {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (sideZ : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) :
    LateSideLattice i d (fun j => (sideZ j).intPhase (16 / (16 / i.kappa)) (idx j)) :=
  lateSideLattice_of_isIntPhase i d _ fun j => (sideZ j).isIntPhase_intPhase _ (idx j)

/-- **No loss in the integer representation**: if `side` satisfies the lattice and collar leaves, then the
integer-indexed data with the index read off from the phase satisfy the collar leaf (and, by
`lateSideLattice_intPhase`, the lattice leaf). The two phases agree almost surely on the live event at every
fixed time, which is all the collar leaf sees. -/
theorem lateSideCollar_latticeIndex {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (hL : LateSideLattice i d side) (hC : LateSideCollar i d side) :
    LateSideCollar i d (fun j => (side j).intPhase (16 / (16 / i.kappa))
      ((side j).latticeIndex (16 / (16 / i.kappa)))) := by
  intro j hj _ _ _ _ q gB hgB g hg
  filter_upwards [hL j hj q, hC j hj q gB hgB g hg] with ω hωL hωC hω hq v hv hvr ξ hξ
  obtain ⟨k, b, d', h1, h2, h3, h4⟩ := hωC hω hq v hv hvr ξ hξ
  refine ⟨k, b, d', h1, h2, h3, ?_⟩
  have hlat : ∃ m : ℤ, (side j).phase q ω = m * phaseStep (16 / (16 / i.kappa)) := by
    rw [← SideTest.target_kappa j i d]
    exact hωL hω hq
  have hph := (side j).intPhase_latticeIndex_phase (16 / (16 / i.kappa)) hlat
  rw [hph]
  exact h4

end InteractingSLE.Wire
