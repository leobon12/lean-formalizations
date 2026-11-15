/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeStmt

/-!
# Proposition BW1's constructed version has the hull identities

Packet PROVE-BW1-SAFELAW. **`bw1RelVersionHStatement`**: the version built by PROVE-BW1-INPUTS2
(`BW1Ver.bw1RelVersionStatement`: GB6's coordinate driver of BW1's samples frozen at the gauge stops, the inverse
clock `invClk`) also has the hull identities `IsBW1VersionHulls` — the coordinates of a good sample generate the mapped
physical hulls at the clock values (`BW1Ver.IsSampleCoord.hulls`), and freezing before the coordinate life keeps the
hulls up to the stop (`RelDrv.Version.fwdHull_freeze_eq`). Hence **`bw1Statement_of_lawH`**: Proposition BW1 from
Theorems 1.2–1.3, the canonical driver codes and `BW1RelSafeLawHStatement` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life BW1Ver Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.RelDrv.Version
  Supp8.GB6.HullId Supp8.Q3Stop Theorem14.GW4Fix

/-- **BW1's measurable exhausting version with hull identities, from Theorem 1.3.** -/
theorem bw1RelVersionHStatement (h13 : Exist.Theorem13Statement.{u}) : BW1RelVersionHStatement.{u} := by
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
    fun ω => invClk rec Γ A M ω, ⟨fun m s => measurable_freeze hDa hDc (hvm m) (hv m) s,
    fun m ω => continuous_freeze hDc (hv m) ω, fun m ω => ?_, fun m ω s hs => ?_,
    fun m => measurable_coe_nnreal_ennreal.comp (hvm m),
    fun s => measurable_invClk hrec hΓc hAc hΓm hAm hMm hgood s, fun m => ?_, ?_⟩, fun m => ?_⟩
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
  · -- the hull identities: the coordinates generate the mapped hulls, freezing keeps them up to the stop
    filter_upwards [hFTS, hae] with ω hF hMω hωF
    have hωM : ω ∈ M := hMω (hF.1 hωF)
    obtain ⟨-, -, hw, -, -, hct⟩ := hM ω hωM
    have hC := hcoord ω hωM
    have hW'e : (fun u => W' u ω) = (Wd · ω) := funext hw
    rw [hct]
    simp only [hW'e]
    refine ⟨fun u hu => hC.range u (hu.trans (hv m ω)), fun t ht hle => ?_⟩
    obtain ⟨h0, -, hK⟩ := hC.hulls t ht
    have hav : rclk (rec ω) (Wd · ω) t ≤ (coordStop (g := g) m ω : ℝ) := by
      have h := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 hle
      simpa only [ENNReal.coe_toReal] using h
    have hfr := fwdHull_freeze_eq (d := (D · ω)) (hDc ω) (hv m ω) h0 hav
    rw [← hK]
    exact hfr

/-- **Proposition BW1 from K2's (S) and (L) for versions with hull identities**: `BW1.BW1Statement` from Theorems
1.2–1.3 (allowed, R48), the canonical driver codes and `BW1RelSafeLawHStatement`. -/
theorem bw1Statement_of_lawH (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hcode : Restart.CanonicalDriverCodeStatement)
    (hL : BW1RelSafeLawHStatement.{u}) : BW1.BW1Statement.{u} :=
  bw1Statement_of_inputsH h12p h13 hT13₀ hcode (bw1RelVersionHStatement h13) hL

end InteractingSLE.Theorem14.BW1Safe
