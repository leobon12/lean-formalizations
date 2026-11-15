/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxAvoid
import InteractingSLE.Spec.Supplement.GW2BxUnc

/-!
# D75's bad sets are avoided almost surely at the presented angles

Packet PROVE-GW2-BUF (round 21; D75). Almost surely on the alive event of `J32S GW2Sdq.gapFam` (good root,
time-ordered history, admissible root, strictly ordered history), for every level `n` and every angle index `i`
presented at the sample (`PresS`: some near family with the shape and positions decoded from the reference record
presents the reference word raised by `θ_i`, outer labels controlled), all caps past some value and then all buffers
past some index avoid `ZbS n i q b`. This is `avoid_atS` with the uncapped exit before `min (L_u, d_u)`
(`ae_uncExit_lt_min`) and:

* NEARIMG2's uncapped stage law `GW2Ni.StageLawUXStatement` (as stated), uncapped regularity and agreement;
* the base family's cover (`VerCovers`), exhaustion below the stop (`GW2Ni.ExhStopStatement`), caps below the death
  clock, hull identities, and the death threshold `DeathThrXStatementS3`.

* `PresS`, **`ae_avoid_ZbS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh
  GW2Sdx GW2Sdy GW2Sdo GW2TipSystem.RootN4

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **Angle index `i` is presented at the sample**: some near family with the shape and positions decoded from the
reference record presents the reference word raised by `θ_i`, with its outermost labels controlled. -/
def PresS {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ) : Set Ω :=
  {ξ | ∃ (f : NearCrossingFamily.{u} c.κ) (m : ℕ),
    famShapeB f = shapeD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) ∧
    (∀ i' : Fin f.nL, f.xL i' =
      posLD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) i') ∧
    (∀ j : Fin f.nR, f.xR j =
      posRD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) j) ∧
    GW2Sdf.PresentsO c.κ (upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ)
        (wordD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ))) (scL r l)
        (GW2Sdf.flipOf l.length) f.xL (f.ρLs m) f.xR (f.ρRs m) ∧
    f.mL ≤ f.nL - 1 ∧ f.mR ≤ f.nR - 1}

/-- **D75's bad sets are avoided almost surely** at the presented angles, for large caps and then large buffers. -/
theorem ae_avoid_ZbS (hcov : Wire.T14Rk.VerCovers ver₀) (hexhS : GW2Ni.ExhStopStatement ver₀)
    (hlawU : GW2Ni.StageLawUXStatement.{u}) (hdeath : DeathThrXStatementS3 h13 ver₀ ch)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) (hTO : GW2Sdx.HistOrdered c r l)
    (hcaps : ∀ a : ℕ, ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → RootJ31.oldSuccess c r l ω →
      0 < candLife c r l a ω → ∀ n, (ver₀ Ω c r l a).V n ω < deathClockX c r l a ω)
    (hβ : ∀ (a : ℕ) (y : RecData), (ch Ω c r l a).β y = upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ)
      (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y))
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord' : (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ n i : ℕ, ξ ∈ PresS h13 ver₀ c r l i → ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
        ∀ᶠ b in atTop, ξ ∉ ZbS h13 ver₀ ch c r l n i q b := by
  obtain ⟨hx, hs⟩ := hg
  have hverae : ∀ᵐ ξ ∂c.P, ∀ a j, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
        fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
            (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun j =>
      ((ver₀ Ω c r l a).isA hx j).1.1.2.2.2.2.2.2.mono fun ξ h hgx => (h hgx).2.2
  filter_upwards [ae_all_iff.2 fun a => ae_inst_common h13 GW2Sdq.gapFam c r l a ⟨hx, hs⟩ ver₀ c.κ
      (GW2Sds.cfWordSrc c),
    ae_slotRec_eq_refV h13 c r l ver₀ GW2Sdq.gapFam ⟨hx, hs⟩,
    ae_all_iff.2 fun i => hlawU Ω c r l i ⟨hx, hs⟩ hTO,
    ae_all_iff.2 fun i => GW2Ni.uncRegStatement h13 Ω c r l i hTO,
    ae_all_iff.2 fun i => GW2Ni.uncAgreeStatement h13 Ω c r l i,
    ae_all_iff.2 fun i => ae_uncExit_lt_min h13 ver₀ ch hcov c r l ⟨hx, hs⟩ hTO hcaps hβ hdeath hroot hord' i,
    hverae, ae_all_iff.2 fun a => hexhS Ω c r l a ⟨hx, hs⟩ hTO]
    with ξ hcomm href hlawUξ hreg hUA hunc hvξ hexhξ halive n i hpres
  have hGT : ∀ a, ξ ∈ schedGTX h13 c r l a := fun a => (hcomm a halive).1
  have hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := fun a => (hcomm a halive).2.2.2.2.1
  obtain ⟨-, hold, -, hcf, -⟩ := hcomm 0 halive
  obtain ⟨-, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l 0).1 ξ (hGT 0)
  obtain ⟨huc, hu0, huγ, -⟩ := hreg i
  obtain ⟨Wc, hcanU⟩ := hlawUξ i hcf hold
  have hcovE : ξ ∈ RootCv.coverEvent c r := GW2JDetR12.alive_scaledCover_subset c r _ _ l halive
  obtain ⟨f, m, hsh, hL, hR, hP, hmL, hmR⟩ := hpres
  exact avoid_atS h13 ver₀ ch c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hcanU (hUA i) hGT hcovE hold hTc
    (href halive) (fun a j => hvξ a j hcf) (fun a => hexhξ a hcf hold)
    (hunc i halive Wc hcanU n f m hsh hL hR hP hmL hmR)

end InteractingSLE.Theorem14.GW2Bh
