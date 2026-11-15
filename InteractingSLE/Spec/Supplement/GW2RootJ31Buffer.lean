/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Buffer

/-!
# Separation buffers based at a retained switched prefix

Packet PROVE-T14-GW2ROOT2. Translate the entire recorded physical prefix
by its actual real root, and start the existing positive-level stopping
rule at the end of the old prefix. No zero-root or empty-history condition
is imposed. The geometric positivity premises below concern this explicit
gauge; they do not assert an experiment or comparison law.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist.StagedLaw Restart Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD
open Supp8.GB6.RelDrv.Version RootG28

/-- Separation of the full translated flow prefix from the counterflow prefix. -/
def separationRead (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (separationValue ((x : ℂ) + frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)))
      (frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0))))).toReal

theorem measurable_separationRead (x : ℝ) (s v t : ℝ≥0) :
    Measurable (separationRead x s v t) := by
  have hf : ∀ q : RationalUnit × RationalUnit, Measurable fun p : RecData × RecData =>
      ENNReal.ofReal (separationValue
        ((x : ℂ) + frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)))
        (frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0)))) := by
    intro q
    have hX : Measurable fun p : RecData × RecData =>
        (x : ℂ) + frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)) :=
      measurable_const.add ((measurable_frozenTraceRead v
      (t * (q.1.val : ℝ≥0))).comp measurable_snd)
    have hA : Measurable fun p : RecData × RecData =>
        frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0)) :=
      (measurable_frozenTraceRead s
      (s * (q.2.val : ℝ≥0))).comp measurable_fst
    exact (continuous_separationValue.measurable.comp (hX.prodMk hA)).ennreal_ofReal
  exact (Measurable.iInf hf).ennreal_toReal

theorem separationRead_eq_compact (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) :
    separationRead x s v t p = compactSeparation
      (fun u => (x : ℂ) + frozenTraceRead v p.2 u) (frozenTraceRead s p.1) t s := by
  have hc : Continuous (prefixIntegrand
      (fun u => (x : ℂ) + frozenTraceRead v p.2 u) (frozenTraceRead s p.1) t s) :=
    continuous_prefixIntegrand
    ((continuous_const (y := (x : ℂ))).add (continuous_frozenTraceRead v p.2)).continuousOn
    (continuous_frozenTraceRead s p.1).continuousOn (t := t) (s := s)
  have hn := squareMin_nonneg hc (fun _ => separationValue_nonneg _ _)
  unfold separationRead
  change (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (prefixIntegrand (fun u => (x : ℂ) + frozenTraceRead v p.2 u)
      (frozenTraceRead s p.1) t s (Prod.map fractionCast fractionCast q))).toReal = _
  rw [rationalInf_eq_squareMin hc, ENNReal.toReal_ofReal hn]
  rfl

theorem continuous_separationRead (x : ℝ) (s v : ℝ≥0) (p : RecData × RecData) :
    Continuous fun t => separationRead x s v t p := by
  simp_rw [separationRead_eq_compact]
  exact continuous_compactSeparation
    (continuous_const.add (continuous_frozenTraceRead v p.2))
    (continuous_frozenTraceRead s p.1) s

/-- A finite geometric buffer for the future own time after physical time T. -/
def switchedBuffer (x : ℝ) (s v T b : ℝ≥0) (m : ℕ) (p : RecData × RecData) : ℝ≥0 :=
  min b (localStop (fun t => separationRead x s v (T + t) p) m)

theorem measurable_switchedBuffer (x : ℝ) (s v T b : ℝ≥0) (m : ℕ) :
    Measurable (switchedBuffer x s v T b m) := by
  have hm : Measurable fun p => localStop
      (fun t => separationRead x s v (T + t) p) m :=
    measurable_gaugeStop (fun t => measurable_separationRead x s v (T + t))
      (fun p => (continuous_separationRead x s v p).comp
        (continuous_const.add continuous_id))
      (((measurable_separationRead x s v (T + 0)).div_const 2).min measurable_const) (m + 1)
  exact measurable_const.min hm

theorem switchedBuffer_le (x : ℝ) (s v T b : ℝ≥0) (m : ℕ) (p : RecData × RecData) :
    switchedBuffer x s v T b m p ≤ b := min_le_left _ _

/-- A positive compact separation at the retained tip gives positive future time. -/
theorem switchedBuffer_pos (x : ℝ) (s v T b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) (hb : 0 < b) (hsep : 0 < separationRead x s v T p) :
    0 < switchedBuffer x s v T b m p := by
  have hg : Continuous fun t : ℝ≥0 => separationRead x s v (T + t) p :=
    (continuous_separationRead x s v p).comp (continuous_const.add continuous_id)
  exact lt_min hb (localStop_pos hg (by simpa only [add_zero] using hsep) m)

/-- The buffers exhaust each compact future interval of positive separation. -/
theorem exists_lt_switchedBuffer (x : ℝ) (s v T b t : ℝ≥0)
    (p : RecData × RecData) (htb : t < b)
    (hsep : ∀ u ≤ t, 0 < separationRead x s v (T + u) p) :
    ∃ m, t < switchedBuffer x s v T b m p := by
  obtain ⟨m, hm⟩ := exists_lt_localStop
    ((continuous_separationRead x s v p).comp (continuous_const.add continuous_id)) hsep
  exact ⟨m, lt_min htb hm⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
