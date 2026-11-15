/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GiDrv
import InteractingSLE.Spec.Supplement.SB2NcSeed
import InteractingSLE.Spec.Supplement.SB2NdRoot
import InteractingSLE.Spec.Supplement.SB2CkEntr
import InteractingSLE.Spec.Supplement.SB2NcObj
import InteractingSLE.Spec.Supplement.SB2NcWalk
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The root construction's two facts: the post-entry curve is driven at the entry offset, the head is filled

Packet PROVE-GW2-GEOM2, round 16 (decision D70: `Mz.CanonIdentOn` at `relOff`). CANON's root chain facts
(`Cz.ae_chainFacts_root`, in-flight `SB2CqRTail`) take two facts of the root construction (CANON's R5.5 (A),
`hdrv`, `hhd`): almost surely on the root event, for the offset `x₀` of `Cz.SB2LowerRootVersionStatement9` (the right
entry value at `R = max (A ∩ ℝ)`),

* the canonical curve of the post-entry piece `P(τ + ·)` (`τ = Nd.entrR`, B's entrance time at `R`) is driven;
* the head `P[0, τ]` lies in `fill X ∪ ℝ` (`X = Nc.retX`, the retained union).

They hold at every sample where the walk facts hold (`Nc.WalkGood`), B launches at `ℓ` and enters `R` before its
lifetime, and `x₀` is the right entry value at `R` (**`rootFacts_at`**). The proof splits on whether `R` is explored
before stage `ℓ`:

* **old** (a mark entry): the piece meets `R` only at its seed, at time `0` (`Lk.visitTime_eq_zero_of_old`), so `τ = 0`
  and the piece starts at `R`; NOJUMP's `Nc.isDrivenCurve_walkStage_old_entry` gives the driven curve at the right entry
  value of `X` at `realMax X = stPt = R` (`realMax_retX_eq_of_explored`), and the head is `{R}`;
* **new** (a pure piece entry): `Gi.isDrivenCurve_walkStage_new_entry` gives the head in `K_A` and the driven
  post-entry curve at the right entry value at `R`.

In both cases the offset is `x₀` by uniqueness of the entry value (`Gi.eq_of_isRightEntryChart`).
**`ae_rootFacts`**: the two facts almost surely on any event inside `Ne.rootEv` carrying the entry clause.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Gi

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

/-- **B's point is the largest real point of the retained union once `R` is explored** (NOJUMP's landed
`Nc.realMax_retX_eq`, with the exploration of `R` at `ℓ` as a hypothesis instead of `relOff < ℓ`; the proof is
NOJUMP's, as in its in-flight `Nf.realMax_retX_eq_of_mem`). -/
theorem realMax_retX_eq_of_explored {ω : Ω} (hg : Nc.WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hRin : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) :
    realMax (Nc.retX κ b jumps E u l k ℓ ω) =
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set s := ExplState.run κ b jumps w D ℓ with hs
  set Pn := SB.prefixPhysSet κ b jumps w D ℓ with hPn
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hg.upath
  set A := upperPrefix κ b jumps E u l k ω with hAdef
  set R := realMax A with hRdef
  have hP := hg.reg
  have hlm := hg.noLeftMove
  have hlh := hg.noLeftHit
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := not_dead_of_launch w D hl'
  -- the records
  have hM : ∀ i, i < ℓ + 1 → stStatus (ExplState.run κ b jumps w D i) ≠ GW1Conn.stDone := fun i hi hd =>
    hnd (by rw [hs, Lx.run_eq_of_done w D hd ℓ (by omega)]; exact hd)
  have hfin := fin_before_first_done hM
  have hri := recInv_ptRec_run_le hP (N := ℓ) (fun j hj hlj => hfin j (by omega) hlj) hlm hlh
  have hrec : ∀ k, k ≤ ℓ → RecInv κ b jumps θ D k := fun k hk => (hri k hk).1
  have hpt : stPt s = stRecR s := by
    rcases (hri ℓ le_rfl).2 with h | h | h
    · exact absurd h hnd
    · exact absurd h hndd
    · exact h
  have hbeyond : ∀ y : ℝ, (y : ℂ) ∈ Pn → y ≤ stPt s := fun y hy => by
    by_contra hlt
    exact notMem_prefix_of_beyond hP hrec hlm hnd (hpt ▸ not_le.1 hlt) hy
  -- the largest real point
  have hAc : IsCompact A := hpA ▸ isCompact_Icc.image_of_continuousOn hpc
  refine realMax_eq_of_le (Nc.isCompact_retX hg hl) (Or.inr (hg.pinv ℓ hnd).2) fun y hy => ?_
  rcases hy with hy | hy
  · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond R hRin)
  · exact hbeyond y hy

/-- **The root construction's two facts at one sample.** See the module docstring. -/
theorem rootFacts_at {ω : Ω} (hg : Nc.WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hent : Nd.entrR κ b jumps E u l k ℓ ω < Nc.bLife b jumps E ℓ ω) {x₀ : ℝ}
    (hx : IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter x₀)) :
    IsDrivenCurve (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) x₀
      (fun s => Nc.bPc κ b jumps E ℓ ω ((Nd.entrR κ b jumps E u l k ℓ ω).toNNReal + s))
      (Nc.bLife b jumps E ℓ ω - (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal)) ∧
    Nc.bPc κ b jumps E ℓ ω '' Icc 0 (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal ⊆
      fillH (Nc.retX κ b jumps E u l k ℓ ω) ∪ {z | z.im = 0} := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set s := ExplState.run κ b jumps w D ℓ with hs
  set A := upperPrefix κ b jumps E u l k ω with hAdef
  set R := realMax A with hRdef
  obtain ⟨pA, hpc, hp0, hpH, hpv, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, hS3⟩ := hg.proper
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  have hX : Nc.retX κ b jumps E u l k ℓ ω = A ∪ SB.prefixPhysSet κ b jumps w D ℓ := rfl
  -- the piece visits `R` before its lifetime
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt s (D ℓ) t = (R : ℂ) := by
    by_contra hv
    have he := Ck.entrTime_eq_life hv
    have : Nd.entrR κ b jumps E u l k ℓ ω = (D ℓ).2 := he
    rw [this] at hent
    exact lt_irrefl _ hent
  have hτ : Nd.entrR κ b jumps E u l k ℓ ω = (visitTime s (D ℓ) R : ℝ≥0∞) := Ck.entrTime_eq_visitTime hvis
  have hτnn : (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal = visitTime s (D ℓ) R := by
    rw [hτ, ENNReal.toNNReal_coe]
  have hpos : (D ℓ).2 ≠ 0 := (lt_of_le_of_lt (zero_le (α := ℝ≥0∞)) hent).ne'
  have hlife : (D ℓ).2 - (visitTime s (D ℓ) R : ℝ≥0∞) ≠ 0 := by
    rw [← hτ]; exact (tsub_pos_of_lt hent).ne'
  have hbPc : Nc.bPc κ b jumps E ℓ ω = pcPt s (D ℓ) := rfl
  have hbL : Nc.bLife b jumps E ℓ ω = (D ℓ).2 := rfl
  rw [hτnn, hbPc, hbL]
  by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 s
  · -- a mark entry: `R` is explored, the piece starts at `R`
    have h0 : visitTime s (D ℓ) R = 0 := Lk.visitTime_eq_zero_of_old hg.reg hg.chain hl hpos hold
    have hP0 : pcPt s (D ℓ) 0 = (R : ℂ) := by
      have := (visitTime_spec hg.reg hl hvis).2.1
      rwa [h0] at this
    have hst : ((stPt s : ℝ) : ℂ) = (R : ℂ) := (pcPt_zero_launch hg.reg hg.chain hl hpos).symm.trans hP0
    obtain ⟨e, hrc, hdr⟩ := Nc.isDrivenCurve_walkStage_old_entry hg.reg hg.chain hg.noLeftMove hg.noLeftHit hl hpos
      (hg.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr (by rw [hpA]; exact hS1) (by rw [hpA]; exact hold)
      (by rw [hpA]; exact hS3)
    rw [hpA] at hrc hdr
    have hrm : realMax (A ∪ SB.prefixPhysSet κ b jumps w D ℓ) = R := by
      rw [← hX, realMax_retX_eq_of_explored hg hl hold]
      exact_mod_cast hst
    rw [hrm, ← hX] at hrc
    have hex : e = x₀ := eq_of_isRightEntryChart hrc hx
    subst hex
    rw [h0]
    refine ⟨?_, ?_⟩
    · simp only [zero_add, ENNReal.coe_zero, tsub_zero]
      rw [hX]; exact hdr
    · rintro _ ⟨t, ht, rfl⟩
      have ht0 : t = 0 := le_antisymm ht.2 bot_le
      rw [ht0, hP0]
      exact Or.inr (by simp)
  · -- a pure piece entry: `R` is new at `ℓ`
    obtain ⟨hhead, e, hrc, hdr⟩ := isDrivenCurve_walkStage_new_entry hg.reg hg.chain hl hpos (hg.pinv ℓ hnd).1 hpc
      hp0 hpH hpv hβ hβ0 hβr (by rw [hpA]; exact hS1) (by rw [hpA]; exact hold) (by rw [hpA]; exact hvis)
      (by rw [hpA]; exact hlife) (by rw [hpA]; exact hS3)
    rw [hpA] at hhead hrc hdr
    rw [← hX] at hrc
    have hex : e = x₀ := eq_of_isRightEntryChart hrc hx
    subst hex
    refine ⟨by rw [hX]; exact hdr, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rcases hhead t ht.2 with h | ⟨y, -, hy⟩
    · exact Or.inl (fillH_mono (by rw [hX]; exact subset_union_left) h)
    · exact Or.inr (by rw [← hy]; simp)

/-- **The root construction's two facts, almost surely** (CANON's `hdrv`, `hhd` of `Cz.ae_chainFacts_root`): on an
event `Fr` inside the root event on which `x₀` is the right entry value at `R`. -/
theorem ae_rootFacts (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {Fr : Set Ω} {x₀ : Ω → ℝ} (hFr : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    (hx : ∀ᵐ ω ∂P, ω ∈ Fr → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (upperPrefix κ b jumps E u l k ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω))) :
    (∀ᵐ ω ∂P, ω ∈ Fr → IsDrivenCurve (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) (x₀ ω)
      (fun s => Nc.bPc κ b jumps E ℓ ω ((Nd.entrR κ b jumps E u l k ℓ ω).toNNReal + s))
      (Nc.bLife b jumps E ℓ ω - (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal))) ∧
    (∀ᵐ ω ∂P, ω ∈ Fr → Nc.bPc κ b jumps E ℓ ω '' Icc 0 (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal ⊆
      fillH (Nc.retX κ b jumps E u l k ℓ ω) ∪ {z | z.im = 0}) := by
  have hgood := Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  have hall : ∀ᵐ ω ∂P, ω ∈ Fr → IsDrivenCurve (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) (x₀ ω)
      (fun s => Nc.bPc κ b jumps E ℓ ω ((Nd.entrR κ b jumps E u l k ℓ ω).toNNReal + s))
      (Nc.bLife b jumps E ℓ ω - (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal)) ∧
      Nc.bPc κ b jumps E ℓ ω '' Icc 0 (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal ⊆
        fillH (Nc.retX κ b jumps E u l k ℓ ω) ∪ {z | z.im = 0} := by
    filter_upwards [hFr, hx, hgood] with ω h1 h2 h3 hω
    obtain ⟨hst, -, -, hent⟩ := h1 hω
    exact rootFacts_at (h3 hst.1) hst.2 hent (h2 hω)
  exact ⟨hall.mono fun ω h hω => (h hω).1, hall.mono fun ω h hω => (h hω).2⟩

end InteractingSLE.Theorem14.SB.Gi
