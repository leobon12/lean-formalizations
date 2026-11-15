/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwAvoid
import InteractingSLE.Spec.Supplement.GW2NiFin

/-!
# The bad sets are avoided almost surely on the alive event

Packet PROVE-GW2-BUF (round 20; `hsrc`). Almost surely on the alive event of `J32S GW2Sdq.gapFam` (good root,
time-ordered history), for every level `n` and angle index `i`, all caps past some value and then all buffers past
some index avoid the bad set `Zb n i q b`. This is `avoid_at` with:

* NEARIMG2's uncapped stage law `GW2Ni.StageLawUXStatement` (as stated; D71: NEARIMG2 derives it from RELDET's
  stopped stage law with caps → ∞). No stage law of the capped candidates is used;
* the uncapped regularity and agreement (`GW2Ni.uncRegStatement`, `GW2Ni.uncAgreeStatement`);
* the per-candidate facts (`ae_inst_common`, `ae_slotRec_eq_ref`, the death family's hull identities and caps below
  the death clock) and the contact-first bound `ae_uncExit_lt_life`.

* **`ae_avoid_Zb`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh
  GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u})

/-- **The bad sets are avoided almost surely** on the alive event, for large caps and then large buffers. -/
theorem ae_avoid_Zb (hlawU : GW2Ni.StageLawUXStatement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace
    Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) (hTO : GW2Sdx.HistOrdered c r l) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ n i : ℕ, ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
        ∀ᶠ b in atTop, ξ ∉ Zb h13 h12 c r l n i q b := by
  obtain ⟨hx, hs⟩ := hg
  have hverae : ∀ᵐ ξ ∂c.P, ∀ a j, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤
          (schedVerXDeathFamily h13 Ω c r l a).V j ξ →
        fwdHull (fun q : ℝ => (schedVerXDeathFamily h13 Ω c r l a).R j q.toNNReal ξ)
            (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun j =>
      ((schedVerXDeathFamily h13 Ω c r l a).isA hx j).1.1.2.2.2.2.2.2.mono fun ξ h hgx => (h hgx).2.2
  filter_upwards [ae_all_iff.2 fun a => ae_inst_common h13 GW2Sdq.gapFam c r l a ⟨hx, hs⟩
      (schedVerXDeathFamily h13) c.κ (GW2Sds.cfWordSrc c),
    ae_slotRec_eq_ref h13 c r l GW2Sdq.gapFam ⟨hx, hs⟩,
    ae_all_iff.2 fun i => hlawU Ω c r l i ⟨hx, hs⟩ hTO,
    ae_all_iff.2 fun i => GW2Ni.uncRegStatement h13 Ω c r l i hTO,
    ae_all_iff.2 fun i => GW2Ni.uncAgreeStatement h13 Ω c r l i,
    ae_all_iff.2 fun i => ae_uncExit_lt_life h13 c r l ⟨hx, hs⟩ hTO i, hverae,
    ae_all_iff.2 fun a => schedVerXDeath_lt_deathClockX h13 c r l a hx hs hTO,
    ae_all_iff.2 fun a => GW2Sdt.ae_candLife_pos h13 c r l a]
    with ξ hcomm href hlawUξ hreg hUA hexit hvξ hdcξ hlifeξ halive n i
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  have hGT : ∀ a, ξ ∈ schedGTX h13 c r l a := fun a => (hcomm a halive).1
  have hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := fun a => (hcomm a halive).2.2.2.2.1
  obtain ⟨-, hold, -, hcf, -⟩ := hcomm 0 halive
  obtain ⟨-, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l 0).1 ξ (hGT 0)
  obtain ⟨huc, hu0, huγ, -⟩ := hreg i
  obtain ⟨Wc, hcanU⟩ := hlawUξ i hcf hold
  have hcov : ξ ∈ RootCv.coverEvent c r := GW2JDetR12.alive_scaledCover_subset c r _ _ l halive
  exact avoid_at h13 h12 c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hcanU (hUA i) hGT hcov hold hTc
    (href halive) (fun a j => hvξ a j hcf)
    (fun a j => hdcξ a hcf hold (hlifeξ a halive32) j) (fun h => hexit i halive Wc hcanU h n)

end InteractingSLE.Theorem14.GW2Bh
