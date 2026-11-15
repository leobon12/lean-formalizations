/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdHull
import InteractingSLE.Spec.Supplement.GW2RootReg
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Supplement.GW2JDetR7Threshold

/-!
# GW2's relative determination, part 3: the flow driver extended through its lifetime

Packet PROVE-GW2-RELDET. GB6's physical machinery (`RelSafe.physClock`, `RelSafe.PhysGood`, the R-form versions
`HullId.IsGB6RelVersionR`, the lines step `RelSafeS.hasRelSafe_of_lines`) reads an explored driver that is continuous
on `[0, ∞)` with a generating trace on `[0, ∞)`. GW2's explored flow line may stop at a finite continuation threshold
`ζα`. Here it is extended: the regularized driver `GW2TipSystem.regW s Wα ζα` (`StagedReg.regularize`: the driver
before `ζα`, frozen at its left limit from `ζα` on) is measurable at every time, and almost surely on `{ζα > 0}`

* it equals `Wα` before `ζα`, is continuous on `[0, ∞)`, starts at `0`, and
* it has a generating trace on `[0, ∞)` equal to `α` on `[0, ζα]` (`extTr`: the trace continued by the slit of the
  frozen driver, `BW1Prop.exists_frozen_trace_close`).

The left limit at a finite positive lifetime is Aux. lemma 3 (`GW2JDetR7.ae_terminal_bad_prefix`). This is the
explored-curve input that lets GB6's physical machinery run for GW2 with the clock capped at the end time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 GW2TipSystem

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}

/-- The regularized driver is measurable at every time. -/
theorem measurable_regW (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (s t : ℝ≥0) :
    Measurable (regW s Wα ζα t) :=
  (measurable_pi_apply t).comp (measurable_fst.comp (measurable_recOf_cfE hfl s).1)

omit [MeasurableSpace Ω] in
/-- Before the lifetime the regularized driver is the driver (on a sample continuous there from `0`). -/
theorem regW_eq_of_lt (s : ℝ≥0) {ω : Ω} (h0 : Wα 0 ω = 0)
    (hc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζα ω) :
    regW s Wα ζα t ω = Wα t ω := by
  have hK : ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζα ω → GW2JointKernel.cfKW Wα ζα r ω = Wα r ω := fun r hr => by
    simp only [GW2JointKernel.cfKW, hr, ↓reduceIte]
  have h0' : GW2JointKernel.cfKW Wα ζα 0 ω = 0 := by
    by_cases hz : ((0 : ℝ≥0) : ℝ≥0∞) < ζα ω
    · rw [hK 0 hz, h0]
    · simp only [GW2JointKernel.cfKW, hz, ↓reduceIte]
  have hc' : ContinuousOn (fun r => GW2JointKernel.cfKW Wα ζα r ω) {r | (r : ℝ≥0∞) < ζα ω} :=
    hc.congr fun r hr => hK r hr
  have := StagedReg.regularize_eq_of_lt (s : ℝ≥0∞) (e := (fun r => GW2JointKernel.cfKW Wα ζα r ω, ζα ω)) h0' hc' ht
  unfold regW GW2JointKernel.cfE
  rw [this]
  exact hK t ht

omit [MeasurableSpace Ω] in
/-- **The regularized flow driver through the lifetime** (one sample): continuous on `[0, ∞)`, from `0`, equal to
`Wα` before `ζα`, with a generating trace on `[0, ∞)` equal to `α` on `[0, ζα]`, given a left limit of `Wα` at a
finite positive lifetime. -/
theorem regW_extension (s : ℝ≥0) {ω : Ω} (h0 : Wα 0 ω = 0)
    (hc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hαω : IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (hpos : 0 < ζα ω)
    (hlim : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζα ω → ∃ w₀ : ℝ, Tendsto (fun t => Wα t ω) (𝓝[<] T) (𝓝 w₀)) :
    Continuous (fun t => regW s Wα ζα t ω) ∧ regW s Wα ζα 0 ω = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω) ∧
      ∃ ᾱ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ ᾱ ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζα ω → ᾱ u = α ω u := by
  have heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω := fun t ht => regW_eq_of_lt s h0 hc ht
  obtain ⟨-, -, hregfrz, hreglim⟩ :=
    StagedReg.isRegularDriver_regularize (s : ℝ≥0∞) (fun r => GW2JointKernel.cfKW Wα ζα r ω, ζα ω)
  have hsnd : (StagedReg.regularize (s : ℝ≥0∞) (fun r => GW2JointKernel.cfKW Wα ζα r ω, ζα ω)).2 = ζα ω :=
    StagedReg.regularize_snd _ _
  rw [hsnd] at hregfrz hreglim
  have hr0 : regW s Wα ζα 0 ω = 0 := (heq 0 (by simpa using hpos)).trans h0
  rcases eq_or_ne (ζα ω) ⊤ with htop | hfin
  · -- infinite lifetime: the regularized driver is the driver
    have hall : ∀ t : ℝ≥0, regW s Wα ζα t ω = Wα t ω := fun t => heq t (by rw [htop]; exact ENNReal.coe_lt_top)
    have he : (fun t => regW s Wα ζα t ω) = fun t => Wα t ω := funext hall
    have hcont : Continuous fun t => Wα t ω := by
      rw [htop] at hc
      exact continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top)
    refine ⟨by rw [he]; exact hcont, hr0, heq, α ω, ?_, fun u _ => rfl⟩
    rw [he, ← htop]
    exact hαω
  · -- finite positive lifetime
    set S : ℝ≥0 := (ζα ω).toNNReal with hS
    have hSζ : (S : ℝ≥0∞) = ζα ω := ENNReal.coe_toNNReal hfin
    have hS0 : 0 < S := by
      rw [← ENNReal.coe_lt_coe, hSζ]
      simpa using hpos
    obtain ⟨w₀, hw₀⟩ := hlim S hSζ
    set w : ℝ≥0 → ℝ := fun t => regW s Wα ζα t ω with hwdef
    have hwlt : ∀ t : ℝ≥0, t < S → w t = Wα t ω := fun t ht => heq t (by rw [← hSζ]; exact_mod_cast ht)
    -- the regularized driver at the lifetime is the left limit, and it is frozen after
    have hfrz : ∀ t : ℝ≥0, S ≤ t → w t = w S := fun t ht =>
      hregfrz t (by rw [← hSζ]; exact_mod_cast ht)
    have hwlim : Tendsto w (𝓝[<] S) (𝓝 w₀) :=
      hw₀.congr' (eventually_nhdsWithin_of_forall fun t ht => (hwlt t ht).symm)
    have hwS : w S = w₀ := hreglim hfin hpos w₀ hwlim
    have hcS : ContinuousOn w {t : ℝ≥0 | t < S} :=
      (hc.mono fun t ht => (by rw [← hSζ]; exact_mod_cast ht)).congr fun t ht => hwlt t ht
    have hcont : Continuous w := by
      rw [continuous_iff_continuousAt]
      intro t
      rcases lt_trichotomy t S with hlt | hts | hgt
      · exact hcS.continuousAt (Iio_mem_nhds hlt)
      · rw [hts]
        have hleft : ContinuousWithinAt w (Iic S) S := by
          rw [← continuousWithinAt_Iio_iff_Iic]
          show Tendsto w (𝓝[<] S) (𝓝 (w S))
          rw [hwS]
          exact hwlim
        have hright : ContinuousWithinAt w (Ici S) S :=
          (continuousWithinAt_const (b := w S)).congr (fun r hr => hfrz r hr) rfl
        exact continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩
      · have hev : w =ᶠ[𝓝 t] fun _ => w S := by
          filter_upwards [Ioi_mem_nhds hgt] with r hr
          exact hfrz r hr.le
        exact (continuousAt_const (y := w S)).congr hev.symm
    -- the generating trace on `[0, S]` of the regularized driver
    have hαS : IsGeneratingTrace w S (α ω) := by
      refine ⟨hαω.1, by rw [hSζ]; exact hαω.2.1, fun t ht => ?_⟩
      have ht' : (t : ℝ≥0∞) < ζα ω := by rw [← hSζ]; exact ht
      have hfill := hαω.2.2 t ht'
      have htS : t < S := by exact_mod_cast ht
      obtain ⟨t₂, htt₂, ht₂S⟩ := exists_between (show (t : ℝ) < S by exact_mod_cast htS)
      have hK : QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t =
          QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t :=
        fwdHull_eq_of_eqOn t.2 htt₂ fun r hr => hwlt r.toNNReal
          (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]; exact lt_of_le_of_lt hr.2 ht₂S)
      rw [hK]
      exact hfill
    have hwS' : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := hcont.continuousOn
    obtain ⟨αr, hαr, hαeq⟩ := BW1Prop.exists_frozen_trace_close hαS hwS' hr0 hS0
    -- the driver stopped at `S` is the regularized driver
    have hstop : (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (S : ℝ≥0∞)).toNNReal) =
        fun r : ℝ => w r.toNNReal := funext fun r => by
      rcases le_total (r.toNNReal) S with hle | hle
      · rw [min_eq_left (ENNReal.coe_le_coe.2 hle), ENNReal.toNNReal_coe]
      · rw [min_eq_right (ENNReal.coe_le_coe.2 hle), ENNReal.toNNReal_coe, hfrz _ hle]
    rw [hstop] at hαr
    have hgen := BW1In.isGeneratingTrace_of_isLoewnerTrace (U := fun r : ℝ => w r.toNNReal)
      (fun x => by simp only [Real.toNNReal_coe]) hαr
    have hwe : (fun s : ℝ≥0 => (fun r : ℝ => w r.toNNReal) (s : ℝ)) = w := funext fun t => by
      simp only [Real.toNNReal_coe]
    rw [hwe] at hgen
    refine ⟨hcont, hr0, heq, fun t => αr t, hgen, fun u hu => ?_⟩
    have hu' : (u : ℝ) ∈ Icc (0 : ℝ) S := ⟨u.2, by
      have : u ≤ S := by rw [← ENNReal.coe_le_coe, hSζ]; exact hu
      exact_mod_cast this⟩
    show αr (u : ℝ) = α ω u
    rw [hαeq _ hu', Real.toNNReal_coe]

/-- The left limit of a flow-line driver at a finite positive lifetime (Aux. lemma 3). -/
theorem ae_tendsto_driver_at_lifetime [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζα ω → 0 < T →
      ∃ w₀ : ℝ, Tendsto (fun t => Wα t ω) (𝓝[<] T) (𝓝 w₀) := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  filter_upwards [GW2JDetR7.ae_terminal_bad_prefix hκ hC.1] with ω hω T hT hT0
  obtain ⟨w₀, vL₀, vR₀, hconv, -⟩ := hω T hT0 hT
  exact ⟨w₀, (continuous_fst.tendsto _).comp hconv⟩

/-- **GW2's extended flow trace**: a generating trace on `[0, ∞)` of the regularized flow driver, equal to `α` on
`[0, ζα]` (chosen; it exists almost surely on `{ζα > 0}`, `ae_extTr_spec`). -/
def extTr (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (α : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0 → ℂ :=
  Classical.epsilon fun ᾱ : ℝ≥0 → ℂ => IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ ᾱ ∧
    ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζα ω → ᾱ u = α ω u

/-- **The extended flow driver and trace, almost surely on `{ζα > 0}`.** -/
theorem ae_extTr_spec [IsProbabilityMeasure P] (hκ : 0 < κ) (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, 0 < ζα ω → Continuous (fun t => regW s Wα ζα t ω) ∧ regW s Wα ζα 0 ω = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω) ∧
      IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ (extTr s Wα ζα α ω) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω u = α ω u := by
  filter_upwards [ae_driver_zero_continuousOn hfl, hα, ae_tendsto_driver_at_lifetime hκ hfl] with ω hd hαω hlim hpos
  obtain ⟨h1, h2, h3, hex⟩ := regW_extension s hd.1 hd.2 hαω hpos fun T hT => hlim T hT (by
    rw [← ENNReal.coe_lt_coe, hT]; simpa using hpos)
  exact ⟨h1, h2, h3, Classical.epsilon_spec hex⟩

end InteractingSLE.Theorem14.GW2Rd
