/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BhSep
import InteractingSLE.Spec.Supplement.GW2SyVer
import InteractingSLE.Spec.Supplement.GW2SyGood
import InteractingSLE.Spec.Supplement.GW2RdGauge
import InteractingSLE.Spec.Supplement.GW2RootJ31Buffer
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2RootG28Trace

/-!
# GB6's separation readout is J31's physical gauge at the schedule instance (S3)

Packet PROVE-GW2-BUF (S3, ruling R115; independent of the cap decision recorded in the handoff). J31's buffer reads
the separation of the recorded physical prefix from the counterflow prefix (`RootJ31.separationRead`). GB6's causal
readout `ReadD.separationRead` reads the same separation from (counterflow record, relative path), at relative time.
Along any relative coordinates of the schedule instance (root `0`), they agree at the relative clock:

* **`separationRead_clock_eq`** (pathwise): if a continuous monotone clock from `0` reads the physical trace back,
  GB6's readout at the clock value is the compact separation of the physical trace;
* **`ae_separationRead_eq_rootJ31`**: almost surely, on the record event and on the history's success, for every
  physical time `t` before the first contact and up to the program end,
  `ReadD.separationRead s (gb6Clock t) (gb6Rec, D) = RootJ31.separationRead 0 s (T + cap) t (futurePair)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD Supp8.GB6.RelDrv GW2TipSystem
  GW2TipSystem.RootC24 GW2Rd

/-- **GB6's readout at a clock value that reads the physical trace back** is the compact separation of the physical
trace. -/
theorem separationRead_clock_eq {s t₀ : ℝ≥0} {p : RecData × (ℝ≥0 → ℝ)} {clk : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (h0 : clk 0 = 0) (hmono : MonotoneOn clk (Icc 0 t₀)) (hcont : ContinuousOn clk (Icc 0 t₀))
    (hread : ∀ t ≤ t₀, physicalTrace s (clk t).toNNReal p = γ t)
    (hX : ContinuousOn (fun u => physicalTrace s u p) (Iic (clk t₀).toNNReal))
    (hA : ContinuousOn (fun v => recordTrace v p.1) (Iic s)) :
    ReadD.separationRead s (clk t₀).toNNReal p = compactSeparation γ (fun v => recordTrace v p.1) t₀ s := by
  rw [separationRead_eq_compactSeparation s _ p hX hA]
  have hτc : ContinuousOn (fun u => (clk u).toNNReal) (Icc 0 t₀) :=
    continuous_real_toNNReal.comp_continuousOn hcont
  have hτm : MonotoneOn (fun u => (clk u).toNNReal) (Icc 0 t₀) :=
    fun x hx y hy hxy => Real.toNNReal_le_toNNReal (hmono hx hy hxy)
  have hτ0 : (fun u => (clk u).toNNReal) 0 = 0 := by
    simp only [h0, Real.toNNReal_zero]
  have hc := compactSeparation_comp (X := fun u => physicalTrace s u p) (A := fun v => recordTrace v p.1)
    (s := s) hτc hτm hτ0
  refine hc.symm.trans ?_
  exact compactSeparation_congr (fun u hu => hread u hu) (fun _ _ => rfl)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GB6's readout along the schedule instance's relative coordinates is J31's physical gauge** (root `0`), at
every physical time before the first contact and up to the program end. -/
theorem ae_separationRead_eq_rootJ31 (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) (hs : 0 < c.s)
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hC : SourceC.RelativeDriverCoordinates c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α D L) :
    ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → RootJ31.oldSuccess c r l ω →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a →
        ReadD.separationRead c.s (gb6Clock c.s (schedW c r l a) c.W ω t).toNNReal
            (gb6Rec c.s c.W c.ζ ω, fun u => D u ω) =
          RootJ31.separationRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) t
            (RootJ31.futurePair c r l a ω) := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hNR := ae_source_noReturn h13 c
  have hW : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  filter_upwards [ae_physicalReadback_nr hfl hα hNR hW c.s hs hC, ae_separationRead_regular_nr hfl hα hNR hW c.s hs hC,
    hC.relative, ae_gb6RecGood hfl hα c.s, ae_driver_zero_continuousOn hfl, hα, c.hζ,
    ae_schedW_regular h13 c r l a] with ω hread hreg hrel hgood hdrv hαω hζ hsched hm hold t ht htv
  obtain ⟨hs', hsH⟩ := (mem_gb6TS_iff hgood).2 hm
  obtain ⟨h0, hsm, hcont, hpt, -⟩ := hread hs' hsH
  obtain ⟨-, -, -, hAc, hXc⟩ := hreg hm
  obtain ⟨-, hhulls⟩ := hrel hs' hsH
  have hL : ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < L ω := (hhulls t ht).2.1
  have hsub : Icc 0 t ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω} :=
    fun u hu => (ENNReal.coe_le_coe.2 hu.2).trans_lt ht
  have hX : ContinuousOn (fun u => physicalTrace c.s u (gb6Rec c.s c.W c.ζ ω, fun v => D v ω))
      (Iic (gb6Clock c.s (schedW c r l a) c.W ω t).toNNReal) :=
    hXc.mono fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt hL
  rw [separationRead_clock_eq h0 ((hsm.mono hsub).monotoneOn) (hcont.mono hsub)
    (fun u hu => hpt u ((ENNReal.coe_le_coe.2 hu).trans_lt ht)) hX hAc,
    RootJ31.separationRead_eq_compact]
  refine compactSeparation_congr (fun u hu => ?_) (fun w hw => ?_)
  · -- the joined future record reads the explored trace back
    obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ω
    have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ω) ⊤ (schedTr c r l a ω) := by
      have h := hsched.2.2.1
      rwa [schedW_of_oldSuccess c r l a hold] at h
    change schedTr c r l a ω u = ((rootPt r.1 : ℝ) : ℂ) +
      RootG28.frozenTraceRead _ (RootJ31.futurePair c r l a ω).2 u
    rw [Gm.futurePair_snd, Gm.lastTime_futureProgram, Gm.frozenTraceRead_recOfDriver hJ hJ0 hγ, hroot]
    simp only [min_eq_left (hu.trans htv), Complex.ofReal_zero, zero_add]
  · -- the counterflow record reads the counterflow trace back
    have hζ' : c.ζ ω = ⊤ := hζ
    have hWc : Continuous fun t => c.W t ω := by
      have h := hdrv.2
      simp only [hζ', ENNReal.coe_lt_top, ofPred_true] at h
      exact continuousOn_univ.1 h
    have hα' : IsGeneratingTrace (fun t => c.W t ω) ⊤ (c.α ω) := by
      rw [← hζ']
      exact hαω
    change recordTrace w (gb6Rec c.s c.W c.ζ ω) = RootG28.frozenTraceRead c.s (cfRec c.s c.W c.ζ ω) w
    rw [RootG28.frozenTraceRead_cfRec_eq c.W c.ζ c.s ω hWc hdrv.1 hζ' hα']
    simp only [min_eq_left hw]
    exact recordTrace_eq c.s hdrv.1 hdrv.2 hαω hs' hw

end InteractingSLE.Theorem14.GW2Bh
