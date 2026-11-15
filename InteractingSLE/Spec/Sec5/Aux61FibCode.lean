/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibClock
import InteractingSLE.Spec.Restart.FCThresholdDriverAEMeas
import InteractingSLE.Spec.Restart.RetPlumbProofFinalTrace
import InteractingSLE.Spec.Restart.RetLeafTraceBorel
import LQGMetric.Field.StandardBorelRange

/-!
# The fibre code space and the fibre's clock source

Packet PROVE-AUX61-FIB, piece (F1) of `planning/handoffs/PROVE-AUX61-ACT.md` (the fibre's data on a standard-Borel
code space). The fibres of the restart are regular conditional laws (`condDistrib`) of a **code** given the retained
history; the code must live in a standard Borel space. The code of a restart is

* the field read in the restart chart (a distribution on `ℍ`),
* the restarted chart path in capacity time, coded by the dyadic values of its real and imaginary parts (the codes
  `Sec2.Assembly.PCode` of Theorem 2.2's assembly, decoded continuously by `FCDet.decDrv`), and
* its lifetime (the clock of the restart).

The **driver is not part of the code**: it is read from the path by the landed measurable reconstruction
`Restart.FCPlumb.fcTraceDriver` (the left difference quotient of the mapping-out functions, frozen at the lifetime).
So the glued space only needs a measurable path, not a measurable Loewner driver of the restarted path.

* `FibCode`, `FibCode.field`, `FibCode.trace`, `FibCode.life`, `FibCode.driver` (all measurable; the trace and the
  driver are continuous and start at `0` at **every** code);
* `fibRead`: the code of a measurable field and a measurable path continuous on its closed available interval, with
  **`measurable_fibRead`** and the decoding identities;
* **`FibCode.driver_eq_frz`**: at a code whose path is a generating trace of its driver, the driver is frozen at the
  lifetime;
* `GoodTrace` (measurable) and **`fibSource`**: every probability law on `ULift FibCode` that charges only codes in
  `GoodTrace` (almost surely) is the law of a `Aux61R45.ClockSource` with seed `0`, the decoded driver, path and
  lifetime;
* **`fibClock`**: the fibre's reference clock killed at the clock, with clock `life`, driver `driver` and the explicit
  announcing stops `annStop` (definitionally; from `Aux61FibClock`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Fib

open Sec2.Assembly (PCode enc)
open LQGMetric (DistOn)
open Aux61R45 (ClockSource ReferenceClock)

universe u

/-! ### The code space -/

/-- **The fibre code**: the field read in the restart chart, the dyadic codes of the real and imaginary parts of the
restarted chart path, and its lifetime. -/
abbrev FibCode : Type := DistOn upperHalfPlaneOpens × PCode × PCode × ℝ≥0∞

instance : StandardBorelSpace (PCode × PCode × ℝ≥0∞) := StandardBorelSpace.prod

instance : StandardBorelSpace FibCode := StandardBorelSpace.prod

/-- `ULift` of the code space is standard Borel (the fibre spaces live in the universe of the glued space). -/
instance instStandardBorelSpaceULiftFibCode : StandardBorelSpace (ULift.{u} FibCode) :=
  LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift

namespace FibCode

/-- The field in the restart chart. -/
def field (s : FibCode) : DistOn upperHalfPlaneOpens := s.1

/-- The decoded restarted path (continuous, from `0`, at every code). -/
def trace (s : FibCode) (t : ℝ≥0) : ℂ := ⟨Restart.FCDet.decDrv s.2.1 t, Restart.FCDet.decDrv s.2.2.1 t⟩

/-- The lifetime (the clock of the restart). -/
def life (s : FibCode) : ℝ≥0∞ := s.2.2.2

/-- **The driver read from the path** (`Restart.FCPlumb.fcTraceDriver`, frozen at the lifetime). -/
def driver (t : ℝ≥0) (s : FibCode) : ℝ := Restart.FCPlumb.fcTraceDriver trace life t s

theorem measurable_field : Measurable field := measurable_fst

theorem measurable_life : Measurable life := measurable_snd.snd.snd

theorem measurable_trace (t : ℝ≥0) : Measurable fun s => trace s t := by
  have hR : Measurable fun s : FibCode => Restart.FCDet.decDrv s.2.1 t :=
    (Restart.FCDet.measurable_decDrv t).comp measurable_snd.fst
  have hI : Measurable fun s : FibCode => Restart.FCDet.decDrv s.2.2.1 t :=
    (Restart.FCDet.measurable_decDrv t).comp measurable_snd.snd.fst
  convert (Complex.measurable_ofReal.comp hR).add ((Complex.measurable_ofReal.comp hI).mul_const Complex.I) using 1
  funext s
  apply Complex.ext <;> simp [trace]

theorem continuous_trace (s : FibCode) : Continuous (trace s) := by
  convert (Complex.continuous_ofReal.comp (Restart.FCDet.continuous_decDrv s.2.1)).add
    ((Complex.continuous_ofReal.comp (Restart.FCDet.continuous_decDrv s.2.2.1)).mul_const Complex.I) using 1
  funext t
  apply Complex.ext <;> simp [trace]

theorem trace_zero (s : FibCode) : trace s 0 = 0 := by
  simp only [trace, Restart.FCDet.decDrv_zero]
  rfl

theorem measurable_driver (t : ℝ≥0) : Measurable (driver t) :=
  Restart.FCPlumb.measurable_fcTraceDriver continuous_trace measurable_trace trace_zero measurable_life t

theorem continuous_driver (s : FibCode) : Continuous (driver · s) :=
  Restart.FCPlumb.continuous_fcTraceDriver _ _ s

theorem driver_zero (s : FibCode) : driver 0 s = 0 := Restart.FCPlumb.fcTraceDriver_zero _ _ s

/-- **The driver is frozen at the lifetime** at a code whose path is a generating trace of its driver through a
positive lifetime: the reconstruction `fcTraceDriver` is the decoding of the frozen read driver, and the read driver is
the driver before the lifetime (`fcReadDriver_eq`). -/
theorem driver_eq_frz {s : FibCode} (h0 : 0 < life s)
    (hg : IsGeneratingTrace (driver · s) (life s) (trace s)) (t : ℝ≥0) :
    driver t s = Restart.StoppedK2.frz life driver t s := by
  have hWc : Continuous (driver · s) := continuous_driver s
  have hW0 : driver 0 s = 0 := driver_zero s
  have he (r : ℝ≥0) : Restart.StoppedK2.frz life (Restart.FCPlumb.fcReadDriver trace) r s =
      Restart.StoppedK2.frz life driver r s := by
    unfold Restart.StoppedK2.frz
    split_ifs with ht
    · exact Restart.FCPlumb.fcReadDriver_eq hWc hW0 hg ht
    · congr 1
      funext k
      unfold Sec7.Aux122Disint.killAt
      split_ifs with hk
      · exact Restart.FCPlumb.fcReadDriver_eq hWc hW0 hg hk
      · rfl
  have hc : Continuous (Restart.StoppedK2.frz life driver · s) := by
    by_cases htop : life s = ⊤
    · simpa only [Restart.StoppedK2.frz_of_eq_top htop] using hWc
    · exact Restart.StoppedK2.continuous_frz h0 htop hWc.continuousOn
  have hz : Restart.StoppedK2.frz life driver 0 s = 0 := by
    rw [Restart.StoppedK2.frz_of_lt (by simpa using h0)]
    exact hW0
  change Restart.FCPlumb.fcTraceDriver trace life t s = _
  unfold Restart.FCPlumb.fcTraceDriver
  simp_rw [he]
  rw [Restart.FCDet.decDrv_enc hc hz]

end FibCode

/-! ### Reading a code from a random field and path -/

section Read

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The code of a field and a path with a lifetime** (the path frozen after its lifetime,
`RetAux79.retClosedTrace`). -/
def fibRead (h : Ω → DistOn upperHalfPlaneOpens) (γ : Ω → ℝ≥0 → ℂ) (V : Ω → ℝ≥0∞) (ω : Ω) : FibCode :=
  (h ω, enc fun t => (Restart.RetAux79.retClosedTrace V γ ω t).re,
    enc fun t => (Restart.RetAux79.retClosedTrace V γ ω t).im, V ω)

omit [MeasurableSpace Ω] in
theorem fibRead_field (h : Ω → DistOn upperHalfPlaneOpens) (γ : Ω → ℝ≥0 → ℂ) (V : Ω → ℝ≥0∞) (ω : Ω) :
    (fibRead h γ V ω).field = h ω := rfl

omit [MeasurableSpace Ω] in
theorem fibRead_life (h : Ω → DistOn upperHalfPlaneOpens) (γ : Ω → ℝ≥0 → ℂ) (V : Ω → ℝ≥0∞) (ω : Ω) :
    (fibRead h γ V ω).life = V ω := rfl

variable {h : Ω → DistOn upperHalfPlaneOpens} {γ : Ω → ℝ≥0 → ℂ} {V : Ω → ℝ≥0∞}

/-- **The code reader is measurable.** -/
theorem measurable_fibRead (hh : Measurable h) (hV : Measurable V) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω}) (hγ0 : ∀ ω, γ ω 0 = 0) :
    Measurable (fibRead h γ V) := by
  obtain ⟨hTm, -, -⟩ := Restart.RetAux79.retClosedTrace_data hV hγm hγc hγ0
  exact hh.prodMk ((measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    Complex.measurable_re.comp (hTm _)).prodMk ((measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
      Complex.measurable_im.comp (hTm _)).prodMk hV))

/-- **Decoding returns the path on its closed available interval.** -/
theorem fibRead_trace (hV : Measurable V) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω}) (hγ0 : ∀ ω, γ ω 0 = 0) (ω : Ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ V ω) : (fibRead h γ V ω).trace t = γ ω t := by
  obtain ⟨-, hTc, hTe⟩ := Restart.RetAux79.retClosedTrace_data hV hγm hγc hγ0
  have hΓ0 : Restart.RetAux79.retClosedTrace V γ ω 0 = 0 := (hTe ω 0 (by simp)).trans (hγ0 ω)
  have hR := congrFun (Restart.FCDet.decDrv_enc (Complex.continuous_re.comp (hTc ω)) (by simp [hΓ0])) t
  have hI := congrFun (Restart.FCDet.decDrv_enc (Complex.continuous_im.comp (hTc ω)) (by simp [hΓ0])) t
  exact (Complex.ext hR hI).trans (hTe ω t ht)

end Read

/-! ### The fibre's clock source -/

/-- **The good codes**: the decoded path is a generating trace of the decoded driver through the lifetime. -/
def GoodTrace : Set FibCode := {s | IsGeneratingTrace (FibCode.driver · s) s.life (s.trace)}

theorem measurableSet_goodTrace : MeasurableSet GoodTrace :=
  Restart.RetLeaf.measurableSet_isGeneratingTrace FibCode.measurable_driver FibCode.continuous_driver
    FibCode.driver_zero FibCode.measurable_life FibCode.measurable_trace FibCode.continuous_trace

/-- The killed decoded driver is measurable (no auxiliary coordinates). -/
theorem isMeasurableKilledDriving_fib :
    IsMeasurableKilledDriving (fun t (s : ULift.{u} FibCode) => FibCode.driver t s.down)
      (fun (_ : Fin 0) _ _ => (0 : ℝ)) (fun (_ : Fin 0) _ _ => (0 : ℝ)) (fun s => s.down.life) := by
  intro r A hA
  have hU : Measurable fun s : ULift.{u} FibCode => s.down.life := FibCode.measurable_life.comp measurable_down
  have hW : Measurable fun s : ULift.{u} FibCode => FibCode.driver r s.down :=
    (FibCode.measurable_driver r).comp measurable_down
  have hf : Measurable fun s : ULift.{u} FibCode =>
      (FibCode.driver r s.down, fun (_ : Fin 0) => (0 : ℝ), fun (_ : Fin 0) => (0 : ℝ)) :=
    hW.prodMk (measurable_const.prodMk measurable_const)
  exact (measurableSet_lt measurable_const hU).inter (hf hA)

/-- **The fibre's clock source**: a probability law on the codes charging only good codes. Seed `0`, lifetime `life`,
driver `driver`, path `trace`. -/
def fibSource (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
    (hP : ∀ᵐ s ∂P, s.down ∈ GoodTrace) : ClockSource (ULift.{u} FibCode) where
  P := P
  prob := inferInstance
  y := 0
  U := fun s => s.down.life
  W₀ := fun t s => FibCode.driver t s.down
  Γ := fun s => s.down.trace
  killed := isMeasurableKilledDriving_fib
  regular := ae_of_all _ fun s =>
    ⟨(FibCode.continuous_driver s.down).continuousOn, FibCode.driver_zero s.down⟩
  trace := by
    filter_upwards [hP] with s hs
    have hs' : IsGeneratingTrace (FibCode.driver · s.down) s.down.life s.down.trace := hs
    simpa only [Complex.ofReal_zero, sub_zero] using hs'

section Source

variable (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P] (hP : ∀ᵐ s ∂P, s.down ∈ GoodTrace)

theorem fibSource_P : (fibSource P hP).P = P := rfl

theorem fibSource_y : (fibSource P hP).y = 0 := rfl

theorem fibSource_U : (fibSource P hP).U = fun s => s.down.life := rfl

theorem fibSource_Γ : (fibSource P hP).Γ = fun s => s.down.trace := rfl

omit [IsProbabilityMeasure P] in
/-- **The lifetime is positive** almost surely when the clearance is positive at the seed and nonpositive at a finite
lifetime. -/
theorem ae_life_pos {ℓ : ℂ → ℝ} (hℓ0 : 0 < ℓ 0)
    (hend : ∀ᵐ s ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = s.down.life → ℓ (s.down.trace T) ≤ 0) :
    ∀ᵐ s ∂P, 0 < s.down.life := by
  filter_upwards [hend] with s hs
  rcases eq_zero_or_pos s.down.life with h | h
  · have h0 := hs 0 (by rw [h]; rfl)
    rw [FibCode.trace_zero] at h0
    exact absurd h0 (not_le.2 hℓ0)
  · exact h

omit [IsProbabilityMeasure P] in
include hP in
/-- The decoded driver is frozen at the lifetime, almost surely under a law charging good codes with positive
lifetimes. -/
theorem ae_driver_frz (hlife : ∀ᵐ s ∂P, 0 < s.down.life) :
    ∀ᵐ s ∂P, ∀ t, FibCode.driver t s.down =
      Restart.StoppedK2.frz (fun s : ULift.{u} FibCode => s.down.life)
        (fun t (s : ULift.{u} FibCode) => FibCode.driver t s.down) t s := by
  filter_upwards [hP, hlife] with s hs hs0 t
  exact FibCode.driver_eq_frz hs0 hs t

/-- **The fibre's reference clock killed at the clock** (`ClockSource.refClockSelf` on `fibSource`): clock `life`,
driver `driver`, announcing stops `annStop ℓ`. -/
def fibClock (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (V : Set ℂ)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 0)
      (flowLineRhoR κ b J 0 0) 0 (flowLineXL b J 0) (flowLineXR b J 0))
    (ℓ : ℂ → ℝ) (hℓ : Continuous ℓ) (hℓ0 : 0 < ℓ 0)
    (hpos : ∀ᵐ s ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < s.down.life → 0 < ℓ (s.down.trace t))
    (hend : ∀ᵐ s ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = s.down.life → ℓ (s.down.trace T) ≤ 0)
    (hexit : ∀ᵐ s ∂P, s.down.life = RLC.exitTime V s.down.trace s.down.life)
    (hinterior : ∀ᵐ s ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.down.life → s.down.trace t ∈ QuantumZipper.H) :
    ReferenceClock (fibSource P hP) κ b J 0 V :=
  ClockSource.refClockSelf (fibSource P hP) κ b J 0 V hseed
    (fun s => FibCode.continuous_driver s.down) (fun s => FibCode.driver_zero s.down)
    (fun t => (FibCode.measurable_driver t).comp measurable_down) (ae_driver_frz P hP (ae_life_pos P hℓ0 hend))
    (fun t => (FibCode.measurable_trace t).comp measurable_down) (fun s => FibCode.continuous_trace s.down)
    ℓ hℓ (by simpa only [fibSource_y, Complex.ofReal_zero] using hℓ0) hpos hend hexit hinterior

end Source

end InteractingSLE.Sec5.Aux61Fib
