/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Cover
import InteractingSLE.Spec.Supplement.GW2JDetR6Actual
import InteractingSLE.Spec.Supplement.GW2JDetR2Root

/-!
# Explicit physical record maps from GW2's stopped kernels

This closes the inverse, capacity-stop and forward lifetime-coverage premises
of record determination. The only unproved stochastic input is the existing
physical stopped-kernel statement. No reconstruction identity is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR6

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Supp8.GB6
open GW2TipSystem GW2JointKernel GW2JDetR2 GW2JDetR4

/-- The explicit physical stopped-record map, from a retained record and the
joint-chart field. It uses the complete code, with its continuation lifetime. -/
def physicalRecordMap (s t : ℝ≥0)
    (F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞)
    (word : RecData → BoundaryWord) (x : RecData × DistOn upperHalfPlaneOpens) : RecData :=
  recordRead s t (x.1, ((fun u => drvDec (F (word x.1, x.2)) u),
    (F (word x.1, x.2)).2))

theorem measurable_physicalRecordMap (s t : ℝ≥0)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : Measurable F) {word : RecData → BoundaryWord} (hw : Measurable word) :
    Measurable (physicalRecordMap s t F word) := by
  let code : RecData × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞ :=
    fun x => F (word x.1, x.2)
  have hm : Measurable code := hF.comp ((hw.comp measurable_fst).prodMk measurable_snd)
  have hpath : Measurable fun x : RecData × DistOn upperHalfPlaneOpens =>
      (fun u : ℝ≥0 => drvDec (code x) u) :=
    measurable_pi_iff.mpr fun u => (measurable_drvDec u).comp hm
  exact (measurable_recordRead s t).comp
    (measurable_fst.prodMk (hpath.prodMk (measurable_snd.comp hm)))

/-- The existing physical stopped-kernel input yields simultaneous
determination of every strictly live pre-contact physical stopped record.
The inverse map and its capacity stopping rules are proved constructions. -/
theorem ae_physical_records_of_stoppedKernels
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    (hK : GW2StoppedKernelStatement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hpL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hpR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hreg : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (s : ℝ≥0) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s)
        1 (specOffset κ) (QuantumZipper.chiC κ) (h ω) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∀ᵐ ω ∂P, γ ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω →
      (t : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
        ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
      cfRec t Wα ζα ω = physicalRecordMap s t F
        (jointWordOfRec (specOffset κ) κ c') (cfRec s W ζ ω, Hc ω) := by
  obtain ⟨M, D, hM, hev, hcover⟩ :=
    hK κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P inferInstance h b J W Wα ζ ζα γ α b' J' h'
      hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc hHcm hHc c' hc'J hc'b
  have hr := measurable_cfRec
    (show IsCenteredCounterflowDriver κ P h W ζ from ⟨b', J', h', hb', hT, hcf⟩) s
  have hMm := hr.comap_le _ hM
  let available : Ω → ℝ≥0 → Prop := fun ω t => (t : ℝ≥0∞) < ζα ω ∧
    (t : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
      ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s)
  have hcov : ∀ᵐ ω ∂P, ω ∈ M → ∀ t, available ω t →
      ∃ (n : ℕ) (q : ℝ≥0), (q : ℝ) =
        relClock (Ito.rpath (W · ω)) s (Ito.rpath (Wα · ω)) t ∧
        (q : ℝ≥0∞) < (D n).stop ((D n).sample ω) ∧
        QuantumZipper.fwdHull
          (fun r : ℝ => (D n).driver r.toNNReal ((D n).sample ω)) q =
          relMap (Ito.rpath (W · ω)) s '' QuantumZipper.fwdHull (Ito.rpath (Wα · ω)) t := by
    filter_upwards [hcover] with ω hω hωM t ht
    exact hω hωM t ht.1 ht.2
  have hdet := ae_hull_lifetime_of_buffers h12p h13 hκ hF hr hMm
    (measurable_jointWordOfRec (specOffset κ) κ c') D
    (fun ω t => relClock (Ito.rpath (W · ω)) s (Ito.rpath (Wα · ω)) t)
    (fun ω t => relMap (Ito.rpath (W · ω)) s ''
      QuantumZipper.fwdHull (Ito.rpath (Wα · ω)) t) available hcov
  have hzero := ae_decoded_zero_of_buffer_cover h12p h13 hκ hF hr hMm
    (measurable_jointWordOfRec (specOffset κ) κ c') D
  filter_upwards [hdet, hzero, hcov, hev, hreg, hα,
    ae_driver_zero_continuousOn hcf, ae_driver_zero_continuousOn hfl]
    with ω hd hz hcovω he hregω hαω hWω hWαω hsH t ht hcontact
  have hωM := he.mp hsH
  obtain ⟨n, q, -, hq, -⟩ := hcovω hωM t ⟨ht, hcontact⟩
  have he0 := hz hωM ⟨n, q, hq⟩
  have htrace : IsGeneratingTrace (W · ω) (ζ ω) (γ ω) := by
    rw [hregω.1]
    exact hregω.2.1
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hregω.1]; exact ENNReal.coe_lt_top
  have hS := firstContactTime_sphereInv (α ω) (γ ω) s
  have htS : (t : ℝ≥0∞) < min
      (firstContactTime (fun u => sphereInv (α ω u : OnePoint ℂ))
        ((fun u => (γ ω u : OnePoint ℂ)) '' Icc 0 s)) (ζα ω) := by
    rw [hS]
    exact lt_min hcontact ht
  have hread := recordRead_eq_of_relative_hulls W ζ ω htrace hWω.2 hWω.1 hsζ hsH
    hαω hWαω.2 hWαω.1 (bot_le.trans_lt ht)
    (e := (drvDec (F (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω), Hc ω)),
      (F (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω), Hc ω)).2))
    (continuousOn_drvDec (F (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω), Hc ω)))
    he0 (fun u hu => ?_) (fun u hu => ?_) htS
  · exact hread.symm
  · rw [hS] at hu
    exact ((hd hωM).2 u ⟨(lt_min_iff.mp hu).2, (lt_min_iff.mp hu).1⟩).2.1
  · rw [hS] at hu
    exact ((hd hωM).2 u ⟨(lt_min_iff.mp hu).2, (lt_min_iff.mp hu).1⟩).2.2

end InteractingSLE.Theorem14.GW2JDetR6
