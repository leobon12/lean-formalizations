/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvMain

/-!
# nearImg for any package with the final package's near data (for ROOTX)

Packet PROVE-GW2-BUF (round 19; D58: one re-indexed package shared by `hwords` and `hnearImg`). `VNearImgOn` reads a
package only through its near families, near candidates and near variables.

* `vNearImgOn_congr`: two packages with the same near data at a root have the same near facts;
* **`vNearImgOn_of_nearData`**: nearImg for every package whose near data are the final package's. For example
  ROOTX's `withNearSB (withShell (pkgXk ver cw Kb k) shells) nearLam nb kSel` with `ver = pkgVerF h13 h12`,
  `Kb = fun _ => pkgKbF h13 h12 K₀`, `nb = pkgNb h13 cwSrc`, `cw = cwSrc` (`withShell` changes only the shells).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2TipSystem GW2TipSystem.RootC24 GW2Sdh GW2Sdi GW2Sdx GW2Sde GW2Rv GW2Rd

/-- **Two packages with the same near data have the same near facts.** -/
theorem vNearImgOn_congr {V V' : VPkgFamily.{u}} {lam : NearDil.{u}} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    {ε : ℝ≥0∞} {A : Set Ω} (hF : (V' Ω c r).nearFamily = (V Ω c r).nearFamily)
    (hC : (V' Ω c r).nearCandidate = (V Ω c r).nearCandidate) (hN : (V' Ω c r).nearVar = (V Ω c r).nearVar)
    (h : GW2Sdz.VNearImgOn V lam Ω c r l ε A) : GW2Sdz.VNearImgOn V' lam Ω c r l ε A := by
  unfold GW2Sdz.VNearImgOn at h ⊢
  rw [hF, hC, hN]
  exact h

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

/-- **nearImg for every package with the final package's near data** (the form ROOTX's top package takes). -/
theorem vNearImgOn_of_nearData (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hlaw : StageLawXStatement h13 (schedVerXDeathFamily h13))
    (hdeath : DeathThrXStatement h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc))
    (kSel : NearSelB.{u}) (hsrc : SrcBoundStatement h13 h12 K₀ kSel) (V : ℕ → VPkgXFamily.{u})
    (hV : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q),
      (V k Ω c r).nearFamily = (pkgF h13 h12 K₀ kSel k Ω c r).nearFamily ∧
        (V k Ω c r).nearCandidate = (pkgF h13 h12 K₀ kSel k Ω c r).nearCandidate ∧
        (V k Ω c r).nearVar = (pkgF h13 h12 K₀ kSel k Ω c r).nearVar)
    (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    GW2Sdz.VNearImgOn ((V k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
      (((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l) :=
  vNearImgOn_congr (hV k Ω c r).1 (hV k Ω c r).2.1 (hV k Ω c r).2.2
    (vNearImgOn_pkgF h13 h12 K₀ hI hlaw hdeath kSel hsrc k Ω c r l)

end InteractingSLE.Theorem14.GW2Bh
