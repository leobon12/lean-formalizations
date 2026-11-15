/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfNew
import InteractingSLE.Spec.Supplement.SB2NeEnd
import InteractingSLE.Spec.Supplement.SB2NdRoot
import InteractingSLE.Spec.Supplement.SB2CkEntr

/-!
# F2b′'s root: the relative piece and its facts at a sample

Packet PROVE-AUX61-NOJUMP (round 22, the root variant, D51/D57). At the root `ℓ = relOff` (not a zero root) with
B's entrance `entrR` at `R = max (A ∩ ℝ)` before B's lifetime, the relative piece is B's piece read from the
entrance: `rPc t = bPc (rSh + t)`, `rSh = entrR` (as `ℝ≥0`), lifetime `rLife = bLife − rSh`; the relative curve is its
canonical curve `rRel` in the chart of the retained union.

**`root_geo`** (deterministic, at a sample with the walk facts): for the right entry value `x` of the retained union at
`R`, the relative curve is driven, of infinite capacity lifetime at an infinite piece; `R` is the largest real point of
the retained union; B's piece up to the entrance lies in `K_A`; B's point is in the retained union. Two cases:

* `R` already explored (a mark entry): the piece starts at `R` (`Dv.visitTime_eq_zero_of_old`), as at a tail
  (`Nc.isDrivenCurve_walkStage_old_entry`, `Lk.canon_old_top`);
* a pure piece entry: `walkStage_new_root`, `canon_new_top`.

`realMax_retX_eq_of_mem`: `Nc.realMax_retX_eq` with the exploration of `R` as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv Nc Ne

section Defs

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)

/-- **The root shift**: B's entrance time at `R`, as `ℝ≥0`. -/
def rSh (ω : Ω) : ℝ≥0 := (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal

/-- **The relative piece at the root**: B's piece read from its entrance. -/
def rPc (ω : Ω) : ℝ≥0 → ℂ := fun t => bPc κ b jumps E ℓ ω (rSh κ b jumps E u l k ℓ ω + t)

/-- Its lifetime. -/
def rLife (ω : Ω) : ℝ≥0∞ := bLife b jumps E ℓ ω - rSh κ b jumps E u l k ℓ ω

/-- **The root's relative curve** through the chart `Mo.hullChart (fillH K) x₀`. -/
def rRel (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (ω : Ω) : ℝ → ℂ :=
  canonCurve (K ω) (x₀ ω) (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω)

/-- Its values in B's time after the entrance. -/
def rLift (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (ω : Ω) : ℝ≥0 → ℂ :=
  canonVal (K ω) (x₀ ω) (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω)

end Defs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}

/-- **B's point is the largest real point of the retained union once `R` is explored** (`Nc.realMax_retX_eq`'s proof
with the exploration of `R` as a hypothesis). -/
theorem realMax_retX_eq_of_mem (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hRin : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) :
    realMax (retX κ b jumps E u l k ℓ ω) =
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
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
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
  refine realMax_eq_of_le (isCompact_retX hg hl) (Or.inr (hg.pinv ℓ hnd).2) fun y hy => ?_
  rcases hy with hy | hy
  · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond R hRin)
  · exact hbeyond y hy

/-- **The root's geometry at a sample** for an offset `x`. -/
structure RootGeo (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ω : Ω) (x : ℝ) : Prop where
  rmax : realMax (retX κ b jumps E u l k ℓ ω) = realMax (upperPrefix κ b jumps E u l k ω)
  stpt : ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) : ℝ) : ℂ) ∈ retX κ b jumps E u l k ℓ ω
  visit : bPc κ b jumps E ℓ ω (rSh κ b jumps E u l k ℓ ω) = ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ)
  shlt : ((rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) < bLife b jumps E ℓ ω
  sh_eq : ((rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) = Nd.entrR κ b jumps E u l k ℓ ω
  head : ∀ t : ℝ≥0, t ≤ rSh κ b jumps E u l k ℓ ω →
    bPc κ b jumps E ℓ ω t ∈ hullK (upperPrefix κ b jumps E u l k ω)
  pos : rLife κ b jumps E u l k ℓ ω ≠ 0
  entry : IsRightEntryChart (retX κ b jumps E u l k ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω))
    ((Mo.hullChart (fillH (retX κ b jumps E u l k ℓ ω)) 0).recenter x)
  driven : IsDrivenCurve (canonCurve (retX κ b jumps E u l k ℓ ω) x (rPc κ b jumps E u l k ℓ ω)
    (rLife κ b jumps E u l k ℓ ω))
  captop : rLife κ b jumps E u l k ℓ ω = ⊤ → capLife (canonCurve (retX κ b jumps E u l k ℓ ω) x
    (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω)) = ⊤

/-- **The root's geometry at a sample** (deterministic): with the walk facts, at a launch of B's stage `ℓ = relOff`
off a zero root with the entrance before B's lifetime, for some offset. -/
theorem exists_rootGeo (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ)
    (hent : Nd.entrR κ b jumps E u l k ℓ ω < bLife b jumps E ℓ ω) :
    ∃ x : ℝ, RootGeo κ b jumps E u l k ℓ ω x := by
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
  have hP := hg.reg
  have hW := hg.chain
  have hAc : IsCompact A := by rw [hAdef, ← hpA]; exact isCompact_Icc.image_of_continuousOn hpc
  have hRA : (R : ℂ) ∈ A := Nc.realMax_mem hAc (x := 0) (by rw [hAdef, ← hpA]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
    rw [hp0]; simp⟩)
  have hRK : (R : ℂ) ∈ hullK A :=
    Or.inr ⟨R, ⟨FinRel.realMin_le_of_mem hAc hRA, le_rfl⟩, rfl⟩
  -- the visit of `R`
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt s (D ℓ) t = (R : ℂ) := by
    by_contra hno
    have h1 : Nd.entrR κ b jumps E u l k ℓ ω = (D ℓ).2 := Ck.entrTime_eq_life hno
    rw [h1] at hent
    exact lt_irrefl _ hent
  have hsheq : Nd.entrR κ b jumps E u l k ℓ ω = visitTime s (D ℓ) R := Ck.entrTime_eq_visitTime hvis
  have hrSh : rSh κ b jumps E u l k ℓ ω = visitTime s (D ℓ) R := by
    unfold rSh; rw [hsheq]; exact ENNReal.toNNReal_coe _
  have hshL : ((visitTime s (D ℓ) R : ℝ≥0) : ℝ≥0∞) < (D ℓ).2 := by rw [← hsheq]; exact hent
  have hpos : (D ℓ).2 ≠ 0 := (lt_of_le_of_lt zero_le hshL).ne'
  obtain ⟨-, hsh, -⟩ := visitTime_spec hP hl hvis
  have hlife : (D ℓ).2 - (visitTime s (D ℓ) R : ℝ≥0∞) ≠ 0 := (tsub_pos_of_lt hshL).ne'
  have hrPc : rPc κ b jumps E u l k ℓ ω = fun t => pcPt s (D ℓ) (visitTime s (D ℓ) R + t) := by
    funext t; simp only [rPc, hrSh]; rfl
  have hrLife : rLife κ b jumps E u l k ℓ ω = (D ℓ).2 - (visitTime s (D ℓ) R : ℝ≥0∞) := by
    simp only [rLife, hrSh]; rfl
  have hvisit : bPc κ b jumps E ℓ ω (rSh κ b jumps E u l k ℓ ω) = (R : ℂ) := by rw [hrSh]; exact hsh
  have hstpt : ((stPt s : ℝ) : ℂ) ∈ retX κ b jumps E u l k ℓ ω := Or.inr (hg.pinv ℓ hnd).2
  have hXc := isCompact_retX hg hl
  obtain ⟨px, hpxc, hpx0, -, -, hpx⟩ := exists_path_retX hg hl
  have hXA : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) := by rw [← hpx]; exact isHPHull_fillH_path hpxc hpx0
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by rw [hpA]; exact hS1
  have hS3' : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H := by rw [hpA]; exact hS3
  have hretX : retX κ b jumps E u l k ℓ ω = pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps w D ℓ := by
    rw [hpA]; rfl
  by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 s
  · -- a mark entry: the piece starts at `R`
    have hsh0 : visitTime s (D ℓ) R = 0 := Dv.visitTime_eq_zero_of_old hP hW hl hpos hold
    have hpt : ((stPt s : ℝ) : ℂ) = (R : ℂ) := by
      rw [← pcPt_zero_launch hP hW hl hpos, ← hsh0]; exact hsh
    have hpt' : stPt s = R := by exact_mod_cast hpt
    have hrmax : realMax (retX κ b jumps E u l k ℓ ω) = R := by
      rw [realMax_retX_eq_of_mem hg hl hold, hpt']
    have hrPc0 : rPc κ b jumps E u l k ℓ ω = pcPt s (D ℓ) := by rw [hrPc, hsh0]; funext t; rw [zero_add]
    have hrLife0 : rLife κ b jumps E u l k ℓ ω = (D ℓ).2 := by
      rw [hrLife, hsh0, ENNReal.coe_zero, tsub_zero]
    have h := isDrivenCurve_walkStage_old_entry hP hW hg.noLeftMove hg.noLeftHit hl hpos (hg.pinv ℓ hnd).1 hpc
      hp0 hpH hpv hβ hβ0 hβr hS1' (by rw [hpA]; exact hold) hS3'
    rw [hpA] at h
    obtain ⟨x, hent', hdr⟩ := h
    have hX : A ∪ SB.prefixPhysSet κ b jumps w D ℓ = retX κ b jumps E u l k ℓ ω := rfl
    rw [hX, hrmax] at hent'
    rw [hX] at hdr
    refine ⟨x, hrmax, hstpt, hvisit, by rw [hrSh]; exact hshL, by rw [hrSh, ← hsheq], ?_, ?_, hent', ?_, ?_⟩
    · intro t ht
      rw [hrSh, hsh0, nonpos_iff_eq_zero] at ht
      rw [ht, show (0 : ℝ≥0) = rSh κ b jumps E u l k ℓ ω by rw [hrSh, hsh0], hvisit]; exact hRK
    · rw [hrLife0]; exact hpos
    · rw [hrPc0, hrLife0]; exact hdr
    · intro htop
      rw [hrLife0] at htop
      rw [hrPc0, hrLife0]
      have hbpc := continuousOn_pcPt_launch hP hl
      have hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | pcPt s (D ℓ) t' ∈ H \ fillH (pA '' Icc 0 1)} := by
        intro t
        have hcl := mem_closure_goodU hXA.2.2.1 hpos hbpc hdr (NNReal.coe_nonneg t)
        have hsub : (fun v : ℝ => Nc.cTime (D ℓ).2 v) ''
            {v' : ℝ | 0 ≤ v' ∧ Nc.cTime (D ℓ).2 v' ∈ canonGood (retX κ b jumps E u l k ℓ ω) (pcPt s (D ℓ)) (D ℓ).2} ⊆
            {t' : ℝ≥0 | pcPt s (D ℓ) t' ∈ H \ fillH (pA '' Icc 0 1)} := by
          rintro _ ⟨v, hv, rfl⟩
          refine ⟨hv.2.2.1, fun hF => hv.2.2.2 ?_⟩
          exact fillH_mono (by rw [hpA]; exact subset_union_left) hF
        have hct : ContinuousWithinAt (fun v : ℝ => Nc.cTime (D ℓ).2 v)
            {v' : ℝ | 0 ≤ v' ∧ Nc.cTime (D ℓ).2 v' ∈ canonGood (retX κ b jumps E u l k ℓ ω) (pcPt s (D ℓ)) (D ℓ).2}
            (t : ℝ) := (Nc.continuousOn_cTime (t : ℝ) (NNReal.coe_nonneg t)).mono fun v hv => hv.1
        have h1 := hct.mem_closure_image hcl
        have heq : Nc.cTime (D ℓ).2 (t : ℝ) = t := by
          unfold Nc.cTime Nc.rTime
          rw [htop]
          simp
        rw [heq] at h1
        exact closure_mono hsub h1
      obtain ⟨x₁, -, hdr₁, -, -, -, hcapT⟩ := canon_old_top hP hW hg.noLeftMove hg.noLeftHit hl hpos htop
        (hg.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr hS1' (by rw [hpA]; exact hold) hS3' hden
      rw [← hretX] at hdr₁ hcapT
      have hdr' := hdr
      rw [htop] at hdr' hbpc
      have hx : x = x₁ := offset_eq hXA ENNReal.top_ne_zero hbpc hdr' hdr₁
      rw [htop, hx]
      exact hcapT
  · -- a pure piece entry
    have h := walkStage_new_root hP hW hl hpos (hg.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr hS1'
      (by rw [hpA]; exact hold) (by rw [hpA]; exact hvis) (by rw [hpA]; exact hlife) hS3'
    rw [hpA] at h
    obtain ⟨hhead, -, hrmax, x, hent', hdr⟩ := h
    have hX : A ∪ SB.prefixPhysSet κ b jumps w D ℓ = retX κ b jumps E u l k ℓ ω := rfl
    rw [hX] at hent' hdr hrmax
    refine ⟨x, hrmax, hstpt, hvisit, by rw [hrSh]; exact hshL, by rw [hrSh, ← hsheq], ?_, ?_, hent', ?_, ?_⟩
    · intro t ht
      rw [hrSh] at ht
      exact hhead t ht
    · rw [hrLife]; exact hlife
    · rw [hrPc, hrLife]; exact hdr
    · intro htop
      have htop' : (D ℓ).2 = ⊤ := by
        rw [hrLife] at htop
        by_contra hne
        exact (ENNReal.sub_ne_top hne) htop
      have h2 := canon_new_top hP hW hl hpos (hg.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr hS1'
        (by rw [hpA]; exact hold) (by rw [hpA]; exact hvis) (by rw [hpA]; exact hlife) hS3' htop'
      rw [hpA] at h2
      obtain ⟨x₁, hdr₁, hcap₁⟩ := h2
      rw [hX] at hdr₁ hcap₁
      rw [hrLife] at htop
      rw [hrPc, hrLife]
      have hdr' := hdr
      rw [htop] at hdr'
      have hpcc : ContinuousOn (fun t => pcPt s (D ℓ) (visitTime s (D ℓ) R + t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} := by
        have hc := continuousOn_pcPt_launch hP hl
        rw [htop'] at hc
        exact hc.comp (continuous_const.add continuous_id).continuousOn fun t _ =>
          (show ((visitTime s (D ℓ) R + t : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top)
      have hx : x = x₁ := offset_eq hXA ENNReal.top_ne_zero hpcc hdr' hdr₁
      rw [htop, hx]
      exact hcap₁

/-- **The root's geometry for the entry read of a hull with the retained union's fill.** -/
theorem rootGeo_of_entryRead (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ)
    (hent : Nd.entrR κ b jumps E u l k ℓ ω < bLife b jumps E ℓ ω) {K : Set ℂ}
    (hK : fillH K = fillH (retX κ b jumps E u l k ℓ ω)) {x₀ : ℝ}
    (hx : x₀ = entryRead (fillH K) (realMax (upperPrefix κ b jumps E u l k ω))) :
    RootGeo κ b jumps E u l k ℓ ω x₀ := by
  obtain ⟨x, G⟩ := exists_rootGeo hg hl hoff hent
  obtain ⟨px, hpxc, hpx0, -, -, hpx⟩ := exists_path_retX hg hl
  have hXA : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) := by rw [← hpx]; exact isHPHull_fillH_path hpxc hpx0
  have hent' := G.entry
  rw [← G.rmax] at hent'
  have hxe : x₀ = x := by
    rw [hx, hK, ← G.rmax]
    exact entryRead_eq (isCompact_retX hg hl) hXA hent'
  rw [hxe]; exact G

end InteractingSLE.Theorem14.SB.Nf
