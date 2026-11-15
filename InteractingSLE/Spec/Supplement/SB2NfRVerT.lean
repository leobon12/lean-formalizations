/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfMain

/-!
# F2b′'s root versions with any entrance agreeing almost surely on the root event

Packet PROVE-AUX61-NOJUMP (round 22, D79). The root versions `RootStop.ver`/`versionS` with the entrance argument
`tL = entrR.toNNReal` replaced by any `tL'` equal to it almost surely on the root's good event (D79's
`tL = Na.rootEntry`, `Nf.tL_eq_rootEntry`): only the `trace` field reads the entrance, almost surely on the root
event (**`RootStop.verT`**, **`RootStop.versionST`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr Nd

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace RootStop

variable (T : RootStop P κ b jumps E u l k ℓ)
  (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
  (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
  (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
  (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
  (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
  {𝓖 : Filtration ℝ≥0 mΩ} (h𝓖 : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t)
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
    A₂ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) ω)
  {β : Ω → BoundaryWord} (hβ : ∀ᵐ ω ∂P, T.cw ω = β ω) (types : Set WordType)
  {tL' : Ω → ℝ≥0} (htL : ∀ᵐ ω ∂P, ω ∈ T.S.Eg → tL' ω = (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal)

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ htL in
/-- **The `m`-th root version with the entrance `tL'`.** -/
def verT (m : ℕ) : Cr.RootVersionG κ (-(Real.pi / 2)) P T.S.Eg 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ) tL' (bLife b jumps E ℓ) :=
  { T.ver hE hER hlθ hℓ hwℓ h𝓖 hA hβ types m with
    trace := fun _ _ t => by
      filter_upwards [T.toG.ae_mem_Gs, htL] with ω hG htLω hc hlt
      obtain ⟨ηr, h1, h2⟩ := T.trace_of_mem (hG hc.1.1) hlt
      exact ⟨ηr, h1, fun s hs hts hd => h2 s hs (by rw [htLω hc.1.1] at hts; exact hts) hd⟩ }

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ htL in
/-- **The root's versions at announced stops with the entrance `tL'`.** -/
def versionST : Cr.RootVersionS κ (-(Real.pi / 2)) P T.S.Eg 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ) tL' (bLife b jumps E ℓ)
    (fun ω => capLife (T.S.ρM ω)) :=
  { T.versionS hE hER hlθ hℓ hwℓ h𝓖 hA hβ types with
    ver := T.verT hE hER hlθ hℓ hwℓ h𝓖 hA hβ types htL }

end RootStop

/-- The root's entrance is `Na.rootEntry` almost surely on the root's good event. -/
theorem RootObj.ae_rootEntry_eq (S : RootObj P κ b jumps E u l k ℓ) :
    ∀ᵐ ω ∂P, ω ∈ S.Eg → Na.rootEntry κ b jumps E u l k ℓ ω = (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal :=
  Eventually.of_forall fun ω hω => (tL_eq_rootEntry (S.Eg_subset_rootEv hω)).symm

end InteractingSLE.Theorem14.SB.Nf
