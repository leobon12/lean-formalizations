/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CaStmt
import InteractingSLE.Spec.Supplement.SB2CrVer
import InteractingSLE.Spec.Supplement.SB2FlMarks

/-!
# (A1): the root event is an event of the stage-`ℓ + 2` line marks (D85)

Packet PROVE-SB2-CONDFIN, round 16 (decision D85 (A1)). The root event is read off NOJUMP's root versions through their
clock: **`clockEv a = {ω | ∃ n : ℕ, 0 < a n ω}`** for the clock `a` of the first version.

* **`ae_mem_clockEv_iff`**: `clockEv (S.ver 0).a = Fr` almost surely, for root versions `S : Cr.RootVersionS` over the
  version event `Fr` (with the word types' cover and seed clauses). `⊆`: the clock is positive only on `Fr`
  (`clock_root`). `⊇`: on `Fr` the first announced stop is positive (`ann`: `ρs … < V 0`), so for a word type of `ω`
  and a rational `q ∈ (0, V 0)` the clock reaches `q` (`reach`, `Λ = V 0`); it is monotone, so it is positive at an
  integer time.
* **`measurableSet_clockEv`**: `clockEv a` is an event of `lineFiltC P 𝓖' 0` (the line marks of stage `ℓ + 2`) and of
  `aeSigma (stageMarks (ℓ + 2))` whenever `a t` is `lineFiltC P 𝓖 t`-measurable (`clock_meas`): the capped pasts of
  stage `ℓ` at every cap lie in B's past through `ℓ + 1`.
* **`exists_rootEvent`** ((A1)): an event `F'` of both σ-algebras with `F' = Fr` almost surely (with 9E/9F's
  `Fr = rootEv` a.s., the root event).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ca

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw Fl

/-- **The clock event**: the clock is positive at some integer time. -/
def clockEv {Ω : Type u} (a : ℝ≥0 → Ω → ℝ≥0∞) : Set Ω := {ω | ∃ n : ℕ, 0 < a (n : ℝ≥0) ω}

/-- **The clock event of the first root version is the version event**, almost surely. -/
theorem ae_mem_clockEv_iff {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Fr : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord}
    {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : Cr.RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ c types pc tL L relLife) (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w) :
    ∀ᵐ ω ∂P, (ω ∈ clockEv (S.ver 0).a ↔ ω ∈ Fr) := by
  have hroot : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < (S.ver 0).a (n : ℝ≥0) ω → ω ∈ Fr :=
    ae_all_iff.2 fun n => (S.ver 0).clock_root n
  have hreach : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ w (hw : w ∈ types), ω ∈ seedCell κ ψ c Fr w →
      (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) < (S.ver 0).Λ w ω →
      ∃ t, (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ (S.ver 0).a t ω :=
    ae_all_iff.2 fun n => (ae_ball_iff htypes).2 fun w hw => (S.ver 0).reach w hw _
  have hseed' : ∀ᵐ ω ∂P, ∀ w (hw : w ∈ types), ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w :=
    (ae_ball_iff htypes).2 hseed
  filter_upwards [hroot, hreach, hseed', hcover, S.ann 0] with ω h1 h2 h3 h4 h5
  constructor
  · rintro ⟨n, hn⟩
    exact h1 n hn
  · intro hω
    have hV : 0 < S.V 0 ω := lt_of_le_of_lt zero_le ((h5 hω).1 0)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hV.ne'
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    have hq : (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.coe_inv (by exact_mod_cast hn0)]
      rfl
    have hw : angleWordType κ ψ (c ω) ∈ types := h4 hω
    have hcell : ω ∈ seedCell κ ψ c Fr (angleWordType κ ψ (c ω)) := h3 _ hw ⟨hω, rfl⟩
    obtain ⟨t, ht⟩ := h2 n _ hw hcell (by rw [hq, S.Λ_eq 0]; exact hn)
    have hpos : 0 < (S.ver 0).a t ω :=
      lt_of_lt_of_le (by rw [hq]; exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)) ht
    exact ⟨⌈t⌉₊, lt_of_lt_of_le hpos ((S.ver 0).clock_mono ω (Nat.le_ceil t))⟩

/-- **The clock event is an event of the line marks of stage `ℓ + 2` and of the completed retained past there.** -/
theorem measurableSet_clockEv {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    {a : ℝ≥0 → Ω → ℝ≥0∞} (ha : ∀ t, Measurable[lineFiltC P 𝓖 t] (a t)) :
    MeasurableSet[lineFiltC P 𝓖' 0] (clockEv a) ∧
      MeasurableSet[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] (clockEv a) := by
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓ₂ : ℓ + 2 ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ₂).1.le
  have hle : ∀ n : ℕ, 𝓖 (n : ℝ≥0) ≤ 𝓖' 0 ∧ 𝓖 (n : ℝ≥0) ≤ stageMarks κ b jumps E u l k (ℓ + 2) := by
    intro n
    have hc := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hℓ.le hwℓ (n : ℚ≥0)
    rw [NNRat.cast_natCast] at hc
    rw [h𝓖, h𝓖']
    exact ⟨sup_le_sup le_rfl (hc.trans (past_le_capPast _ hℓ₂ (by omega))),
      sup_le_sup le_rfl (hc.trans (pastSigma_mono _ _ (by omega)))⟩
  have hev : clockEv a = ⋃ n : ℕ, {ω | 0 < a (n : ℝ≥0) ω} := by
    ext ω
    simp only [clockEv, mem_ofPred_eq, mem_iUnion]
  have hn : ∀ n : ℕ, MeasurableSet[lineFiltC P 𝓖 (n : ℝ≥0)] {ω | 0 < a (n : ℝ≥0) ω} := fun n =>
    measurableSet_lt measurable_const (ha n)
  rw [hev]
  refine ⟨MeasurableSet.iUnion fun n => ?_, MeasurableSet.iUnion fun n => ?_⟩
  · have h1 : lineFiltC P 𝓖 (n : ℝ≥0) ≤ lineFiltC P 𝓖' 0 :=
      inf_le_inf_left _ (WalkLaw.aeSigma_mono (P := P) (hle n).1)
    exact h1 _ (hn n)
  · have h1 : lineFiltC P 𝓖 (n : ℝ≥0) ≤ aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P :=
      inf_le_right.trans (WalkLaw.aeSigma_mono (P := P) (hle n).2)
    exact h1 _ (hn n)

/-- **(A1): the root event is an event of the stage-`ℓ + 2` line marks** (and of the completed retained past there),
read through NOJUMP's root versions: an event `F'` of both σ-algebras, almost surely equal to the version event. -/
theorem exists_rootEvent {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    {ψ : ℝ} {Fr : Set Ω} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord}
    {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : Cr.RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ c types pc tL L relLife) (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w) :
    ∃ F' : Set Ω, MeasurableSet[lineFiltC P 𝓖' 0] F' ∧
      MeasurableSet[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] F' ∧ ∀ᵐ ω ∂P, (ω ∈ F' ↔ ω ∈ Fr) := by
  obtain ⟨h1, h2⟩ := measurableSet_clockEv (P := P) (E := E) (u := u) (l := l) (k := k) hwℓ hwℓ₂ h𝓖 h𝓖'
    (S.ver 0).clock_meas
  exact ⟨_, h1, h2, ae_mem_clockEv_iff S htypes hcover hseed⟩

end InteractingSLE.Theorem14.SB.Ca
