/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerBW1

/-!
# Proposition BW1's measurable exhausting relative version

Packet PROVE-BW1-INPUTS2. **`bw1RelVersionStatement`**: `BW1Life.BW1RelVersionStatement` from Theorem 1.3 (allowed:
BW1 serves Theorem 1.4, R48). The relative coordinates of BW1's samples (`exists_bw1_data`, `exists_coord`: GB6's
measurable atlas with the retained time read from the record), GB6's separation gauge at the record's own time as an
almost-sure readout (`exists_aeSeparationReadout_tsRead`), GW4-FIX's any-record gauge-stop versions and announcing
rules, the measurable inverse clock (`invClk`) and the sample tip relation (`sample_tip`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Ver

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.RelDrv.Version
  Supp8.GB6.HullId Supp8.Q3Stop Theorem14.GW4Fix

/-- The supremum of the gauge stops is the coordinate life. -/
theorem iSup_coordStop_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData}
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hread : SourceC.AESeparationReadout P rec D L g G) (ω : Ω) :
    ⨆ m, ((coordStop (g := g) m ω : ℝ≥0) : ℝ≥0∞) = L ω := by
  refine le_antisymm (iSup_le fun m => (coordStop_lt_life hread m ω).le) (le_of_forall_lt fun c hc => ?_)
  have hcne : c ≠ ⊤ := (hc.trans_le le_top).ne
  obtain ⟨m, hm⟩ := exists_lt_localStop (hread.continuous ω) (t := c.toNNReal) fun v hv =>
    hread.positive ω v ((ENNReal.coe_le_coe.2 hv).trans_lt (by rw [ENNReal.coe_toNNReal hcne]; exact hc))
  calc c = ((c.toNNReal : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_toNNReal hcne).symm
    _ < _ := ENNReal.coe_lt_coe.2 hm
    _ ≤ _ := le_iSup (fun m => ((coordStop (g := g) m ω : ℝ≥0) : ℝ≥0∞)) m

/-- **`BW1RelVersionStatement`, from Theorem 1.3.** -/
theorem bw1RelVersionStatement (h13 : Exist.Theorem13Statement.{u}) : BW1RelVersionStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h W' ζ' θ t gw2 rest E hset r
  obtain ⟨TS, Wd, Γ, A, M, hrec, hTS, hΓc, hAc, hΓm, hAm, hMm, hFTS, hae, hM⟩ := exists_bw1_data h13 hset r
  set rec := bwRec κ b jumps (bwSpec gw2 θ t rest) E with hrecdef
  have hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω) := fun ω hω => (hM ω hω).2.1
  obtain ⟨D, L, hDm, hLm, -, hDc, hD0, hDa, hoff, hcoord⟩ := exists_coord hrec hΓc hAc hΓm hAm hMm hgood
  obtain ⟨g, hread⟩ := exists_aeSeparationReadout_tsRead (P := P) hrec hTS hMm (fun ω hω => (hM ω hω).1) hae
    hgood hDm hLm hD0 hoff hcoord
  have hv : ∀ m ω, ((coordStop (g := g) m ω : ℝ≥0) : ℝ≥0∞) < L ω := fun m ω => coordStop_lt_life hread m ω
  have hvm : ∀ m, Measurable (coordStop (g := g) m) := fun m => measurable_coordStop_of_readout hread m
  refine ⟨fun m => coordDriver (D := D) (g := g) m, fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    fun ω => invClk rec Γ A M ω, fun m s => measurable_freeze hDa hDc (hvm m) (hv m) s,
    fun m ω => continuous_freeze hDc (hv m) ω, fun m ω => ?_, fun m ω s hs => ?_,
    fun m => measurable_coe_nnreal_ennreal.comp (hvm m),
    fun s => measurable_invClk hrec hΓc hAc hΓm hAm hMm hgood s, fun m => ?_, ?_⟩
  · simpa only [coordDriver, freeze, zero_min] using hD0 ω
  · rw [ENNReal.toNNReal_coe]
    exact freeze_after (ENNReal.coe_le_coe.1 hs)
  · refine ⟨hitRule (tsRead TS) (recLevel (tsRead TS) m) (m + 1), fun n => annRules (tsRead TS) m n,
      measurable_hitRule (measurable_tsRead hTS) (measurable_recLevel (measurable_tsRead hTS) m),
      isPathRule_hitRule (isCausal_tsRead TS), ae_coordStop_eq_hitRule hread m,
      fun n => measurable_annRules (measurable_tsRead hTS) m n, fun n => isPathRule_annRules (isCausal_tsRead TS) m n,
      fun n x => annRules_ne_top _ m n x, fun x => monotone_annRules _ m x, ?_⟩
    filter_upwards [ae_annRules_coord_rec hread m] with ω hω _
    exact hω
  · filter_upwards [hFTS, hae] with ω hF hMω hωF
    have hωM : ω ∈ M := hMω (hF.1 hωF)
    obtain ⟨-, hg, hw, hch, hbd, hct⟩ := hM ω hωM
    have hC := hcoord ω hωM
    obtain ⟨-, ham, -⟩ := hg.clock_regular
    have hsup := iSup_coordStop_eq hread ω
    have hℓ := invClk_spec hgood hωM hC
    obtain ⟨hsm, hcont, himg⟩ := inverse_clock_props ham (fun t ht => ⟨(hC.hulls t ht).1, (hC.hulls t ht).2.1⟩) hℓ
    obtain ⟨f, Cb, hf, hCb⟩ := hbd
    have hW'e : (fun u => W' u ω) = (Wd · ω) := funext hw
    refine ⟨fun m => ENNReal.coe_pos.2 (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m), ?_, ?_, ?_, ?_⟩
    · rw [hsup]; exact hsm
    · rw [hsup]; exact hcont
    · rw [hsup, himg, hct]
    · intro m s hs z
      rw [hW'e]
      exact sample_tip hg hC hch hf hCb (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m) (hv m ω) hℓ
        (ENNReal.coe_lt_coe.1 hs) z

/-- **Proposition BW1 now needs only K2's (S) and (L) for the relative exploration**: `BW1.BW1Statement` from
Theorems 1.2–1.3 (allowed, R48), the canonical driver codes and `BW1In.BW1RelSafeLawStatement`
(`BW1In.bw1Statement_of_version_law` with the version supplied by `bw1RelVersionStatement`). -/
theorem bw1Statement_of_law (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hcode : Restart.CanonicalDriverCodeStatement)
    (hL : BW1In.BW1RelSafeLawStatement.{u}) : BW1.BW1Statement.{u} :=
  BW1In.bw1Statement_of_version_law h12p h13 hT13₀ hcode (bw1RelVersionStatement h13) hL

end InteractingSLE.Theorem14.BW1Ver
