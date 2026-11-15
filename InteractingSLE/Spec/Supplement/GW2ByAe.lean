/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ByAvoid
import InteractingSLE.Spec.Supplement.GW2ByUnc
import InteractingSLE.Spec.Supplement.GW2BxAe

/-!
# D75's bad sets are avoided almost surely at the presented angles, under the stopped uncapped law (D83)

Packet PROVE-GW2-BUF (round 22; D83). Round 21's `ae_avoid_ZbS` with NEARIMG2's stopped uncapped law
`GW2Ni.StageLawUXSStatement` in place of `GW2Ni.StageLawUXStatement`: at each sample `avoid_atS2` splits on
"contact comes first" (round 21's exit bound `ae_uncExit_lt_min` on the unstopped form given by
`IsCanonUXS.isCanonUX_of_le`) and "death before the contact" (`ae_uncExit_lt_death`).

* **`ae_avoid_ZbS2`**.
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

/-- **D75's bad sets are avoided almost surely** at the presented angles (stopped uncapped law). -/
theorem ae_avoid_ZbS2 (hcov : Wire.T14Rk.VerCovers ver₀) (hexhS : GW2Ni.ExhStopStatement ver₀)
    (hlawU : GW2Ni.StageLawUXSStatement.{u}) (hdeath : DeathThrXStatementS3 h13 ver₀ ch)
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
    ae_all_iff.2 fun i => ae_uncExit_lt_death h13 ver₀ ch hcov c r l ⟨hx, hs⟩ hTO hcaps hβ hdeath hroot hord' i,
    hverae, ae_all_iff.2 fun a => hexhS Ω c r l a ⟨hx, hs⟩ hTO]
    with ξ hcomm href hlawUξ hreg hUA hunc huncD hvξ hexhξ halive n i hpres
  have hGT : ∀ a, ξ ∈ schedGTX h13 c r l a := fun a => (hcomm a halive).1
  have hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := fun a => (hcomm a halive).2.2.2.2.1
  obtain ⟨-, hold, -, hcf, -⟩ := hcomm 0 halive
  obtain ⟨-, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l 0).1 ξ (hGT 0)
  obtain ⟨huc, hu0, huγ, -⟩ := hreg i
  obtain ⟨Wc, hcanU⟩ := hlawUξ i hcf hold
  have hcovE : ξ ∈ RootCv.coverEvent c r := GW2JDetR12.alive_scaledCover_subset c r _ _ l halive
  obtain ⟨f, m, hsh, hL, hR, hP, hmL, hmR⟩ := hpres
  exact avoid_atS2 h13 ver₀ ch c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hcanU (hUA i) hGT hcovE hold hTc
    (href halive) (fun a j => hvξ a j hcf) (fun a => hexhξ a hcf hold)
    (fun h => hunc i halive Wc h n f m hsh hL hR hP hmL hmR)
    (fun hd => huncD i halive Wc hcanU hd n f m hsh hL hR hP hmL hmR)

end InteractingSLE.Theorem14.GW2Bh
