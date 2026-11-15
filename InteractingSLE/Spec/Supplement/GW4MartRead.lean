/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseRead
import InteractingSLE.Spec.Sec7.CounterflowHullBound
import InteractingSLE.Spec.Sec7.LocalExtAFlow
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# GW4's protected martingales, part 4: reading the phase on a physical line

Packet PROVE-GW4-MART. Astra's follow-up 3 (Q3.6) and §3.4 (`ig1_followup3_audited.txt` L857–L912): the actual mean
is `M_u + δ_u ω_u` with `ω_u` the harmonic measure of the exposed interval, and (Q3.7) at deterministic rational times
"Here `m_t` is the physical-coordinate version of (Q3.3), or of (Q3.6) before phase selection" — so the conditional
mean determines the phase where `ω_u > 0`; follow-up 5 §3.2 (R73): "For every positive time, `V^L_t < V^R_t` and
`ω_t(z) > 0` at an interior active point."

`Sec7.PhaseClause.exists_measurableSet_iff_phase` reads the phase at a **deterministic** capacity time. On a physical
line the capacity time is the **random** clock value `a`. Here the tested canonical means of the far bumps
(`PhaseClause.farBump n`, supported at height `≥ (n + 1)/2`) are read at the random time: every driver keeps the far
bump safe at a fixed level up to capacity `farQ n = ((n + 1)/2)²/10` (`isSafeAt_farBump`), so the tested means stopped
at `farQ n` are continuous in time along every path, and `Supp8.GB6LineL.measurable_apply_randTime` applies
(`measurable_meanInt_randTime`). If a line mean `μ`, measurable for a σ-algebra `m`, is the coupling mean of the
phase-`c` word on the far bumps, then `c = (μ(ψ) − 𝔥_A)/J` with `J > 0`, so every event `{c ∈ B}` agrees almost
surely on the live event with an event of `m` (**`exists_measurableSet_iff_phase_line`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling Ito Restart.DomainMarkov Sec7.PhaseSel Sec7.PhaseClause

/-! ### The far bumps are safe along every driver up to a fixed capacity -/

section Far

/-- The capacity up to which the `n`-th far bump is safe along every driver. -/
def farQ (n : ℕ) : ℝ≥0 := ⟨(((n : ℝ) + 1) / 2) ^ 2 / 10, by positivity⟩

theorem coe_farQ (n : ℕ) : ((farQ n : ℝ≥0) : ℝ) = (((n : ℝ) + 1) / 2) ^ 2 / 10 := rfl

/-- The safe level of the `n`-th far bump. -/
def farLevel (n : ℕ) : ℝ := ((n : ℝ) + 1) / 4

theorem farLevel_pos (n : ℕ) : 0 < farLevel n := by unfold farLevel; positivity

theorem exists_le_farQ (x : ℝ≥0) : ∃ n : ℕ, x ≤ farQ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (40 * (x : ℝ))
  refine ⟨n, ?_⟩
  rw [← NNReal.coe_le_coe, coe_farQ]
  have hx : (0 : ℝ) ≤ x := x.coe_nonneg
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

/-- **Every continuous driver keeps the `n`-th far bump safe at level `(n + 1)/4` up to capacity `farQ n`.** -/
theorem isSafeAt_farBump {w : ℝ≥0 → ℝ} (hw : Continuous w) (n : ℕ) {s : ℝ≥0} (hs : s ≤ farQ n) :
    IsSafeAt (tsupport (farBump n)) (farLevel n) s s ⊤ w s := by
  set y : ℝ := ((n : ℝ) + 1) / 2 with hy
  have hy0 : 0 < y := by positivity
  have hs' : (s : ℝ) ≤ y ^ 2 / 10 := by rw [← coe_farQ]; exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have hwc : Continuous (rpath w) := hw.comp continuous_real_toNNReal
  refine ⟨ENNReal.coe_lt_top, le_rfl, le_rfl, fun z hz => ?_⟩
  have hyz : y ≤ z.im := le_im_of_mem_tsupport_farBump hz
  have hz0 : 0 < z.im := hy0.trans_le hyz
  have halive : ∃ u, IsForwardSol (rpath w) z s u :=
    exists_isForwardSol_rpath_of_im_ge (ζ₀ := ⊤) hw.continuousOn ENNReal.coe_lt_top hy0 hyz (by nlinarith)
  refine ⟨halive, ?_⟩
  have hnot : z ∉ fwdHull (rpath w) s :=
    Sec7.notMem_fwdHull_of_four_mul_lt_im_sq hwc hz0 (by nlinarith)
  have hsq := LocalExt.sq_im_le_sq_im_fwdMap hwc hs0 ⟨hz0, hnot⟩ ⟨hs0, le_rfl⟩
  have hpos : 0 < (fwdMap (rpath w) s z).im :=
    QuantumZipper.FwdHolo.mapsTo_fwdMap hwc hs0 ⟨hz0, hnot⟩
  have h2 : (farLevel n) ^ 2 ≤ (fwdMap (rpath w) s z).im ^ 2 := by
    have e : farLevel n = y / 2 := by simp only [farLevel, hy]; ring
    rw [e]
    nlinarith
  exact (pow_le_pow_iff_left₀ (farLevel_pos n).le hpos.le two_ne_zero).1 h2

end Far

/-! ### The tested canonical means at a random capacity time -/

section Rand

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **The tested canonical mean of a far bump, stopped at `farQ n`, read at a random capacity time is measurable**
for a σ-algebra `m` that cuts the capacity-time events by `{d ≤ a}`. -/
theorem measurable_meanInt_randTime {𝓗 : Filtration ℝ≥0 mΩ} {m : MeasurableSpace Ω}
    (hWa : AdaptedBefore 𝓗 (fun _ => ⊤) W) (hWc : ∀ ω, Continuous (W · ω))
    (hVLa : ∀ i, AdaptedBefore 𝓗 (fun _ => ⊤) (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓗 (fun _ => ⊤) (VR i))
    (hVLc : ∀ ω i, Continuous (VL i · ω)) (hVRc : ∀ ω i, Continuous (VR i · ω))
    (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (n : ℕ) {a : Ω → ℝ≥0∞} (ha : Measurable[m] a)
    (hcut : ∀ (d : ℝ≥0) (D : Set Ω), MeasurableSet[𝓗 d] D → MeasurableSet[m] ({ω | (d : ℝ≥0∞) ≤ a ω} ∩ D)) :
    Measurable[m] fun ω => ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (min (a ω).toNNReal (farQ n)) z * farBump n z := by
  set Y : ℝ≥0 → Ω → ℝ := fun s ω => meanK κ ρL ρR W VL VR (fun _ => ⊤) univ (farBump n) (farLevel n)
    (min s (farQ n)) ω with hYdef
  have hsafe : ∀ ω (s : ℝ≥0), ω ∈ safeSet W (fun _ => ⊤) univ (farBump n) (farLevel n) (min s (farQ n)) :=
    fun ω s => ⟨mem_univ ω, isSafeAt_farBump (hWc ω) n (min_le_right _ _)⟩
  have hYe : ∀ s ω, Y s ω = ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (min s (farQ n)) z * farBump n z := fun s ω => by
    simp only [hYdef, meanK, hsafe ω s, ↓reduceIte]
  have hYc : ∀ ω, Continuous fun s => Y s ω := by
    intro ω
    have hS := isSafeAt_farBump (hWc ω) n (le_refl (farQ n))
    have hc := hS.continuousOn_meanInt (κ := κ) (ρL := ρL) (ρR := ρR) (farBump n).continuous
      (farBump n).hasCompactSupport (hWc ω).continuousOn (fun i => (hVLc ω i).continuousOn)
      (fun i => (hVRc ω i).continuousOn) (Coupling.tsupport_subset_H _) (farLevel_pos n)
    have e : (fun s => Y s ω) = (fun s => ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) s z * farBump n z) ∘ fun s => min s (farQ n) := funext fun s => hYe s ω
    rw [e]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun s => mem_Iic.2 (min_le_right _ _)
  have hYm : ∀ s, Measurable[𝓗 s] (Y s) := fun s =>
    (measurable_meanK hWa (fun ω _ => (hWc ω).continuousOn) MeasurableSet.univ (Coupling.tsupport_subset_H _)
      (farLevel_pos n) κ ρL ρR hVLa hVRa (farBump n).continuous.measurable (min s (farQ n))).mono
      (𝓗.mono (min_le_left _ _)) le_rfl
  have hτ : Measurable[m] fun ω => min (a ω).toNNReal (farQ n) :=
    (ENNReal.measurable_toNNReal.comp ha).min measurable_const
  have h := Supp8.GB6LineL.measurable_apply_randTime (m := m) hYc hτ
    (fun ω => (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans ENNReal.coe_toNNReal_le_self)
    (fun d B hB => hcut d _ (hYm d hB))
  have e : (fun ω => ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (min (a ω).toNNReal (farQ n)) z * farBump n z) = fun ω => Y (min (a ω).toNNReal (farQ n)) ω := by
    funext ω
    rw [hYe, min_assoc, min_self]
  rw [e]
  exact h

end Rand

/-! ### Reading the phase from a line mean -/

section Read

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}

/-- **The phase is read from a line mean.** Let the driver and the coordinates be continuous and adapted to a
capacity-time filtration `𝓗`, ordered, with separated seeds at positive times; let `a` be an `m`-measurable random
capacity time with `{d ≤ a} ∩ D ∈ m` for every `D ∈ 𝓗_d`; and let `μ` be an `m`-measurable random distribution which,
on a live event `L` (positive finite `a`), tested against every test function avoiding the hull at `a`, is the
coupling mean of the phase-`c` word. Then every event `{c ∈ B}` agrees almost surely on `L` with an event of `m`. -/
theorem exists_measurableSet_iff_phase_line (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} {m : MeasurableSpace Ω}
    (hWa : AdaptedBefore 𝓗 (fun _ => ⊤) W) (hWc : ∀ ω, Continuous (W · ω))
    (hVLa : ∀ i, AdaptedBefore 𝓗 (fun _ => ⊤) (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓗 (fun _ => ⊤) (VR i))
    (hVLc : ∀ ω i, Continuous (VL i · ω)) (hVRc : ∀ ω i, Continuous (VR i · ω))
    (hord : ∀ ω s, (∀ i, VL i s ω ≤ W s ω) ∧ ∀ j, W s ω ≤ VR j s ω)
    (hsep : ∀ ω (s : ℝ≥0), 0 < s → VL 0 s ω < VR 0 s ω)
    {a : Ω → ℝ≥0∞} (ha : Measurable[m] a)
    (hcut : ∀ (d : ℝ≥0) (D : Set Ω), MeasurableSet[𝓗 d] D → MeasurableSet[m] ({ω | (d : ℝ≥0∞) ≤ a ω} ∩ D))
    {μ : Ω → DistOn upperHalfPlaneOpens} (hμ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable[m] fun ω => μ ω ψ)
    {L : Set Ω} (hL : ∀ ω ∈ L, 0 < a ω ∧ a ω ≠ ⊤) {c : Ω → ℝ}
    (hmean : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ L →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a ω).toNNReal) →
      μ ω ψ = ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (a ω).toNNReal
        (phaseProc κ ρL ρR W VL VR c ω (a ω).toNNReal) z * ψ z)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ∃ S : Set Ω, MeasurableSet[m] S ∧ ∀ᵐ ω ∂P, ω ∈ L → (c ω ∈ B ↔ ω ∈ S) := by
  set E : ℕ → Set Ω := fun n => {ω | 0 < a ω ∧ a ω ≤ farQ n} with hEdef
  have hEm : ∀ n, MeasurableSet[m] (E n) := fun n =>
    (measurableSet_lt measurable_const ha).inter (measurableSet_le ha measurable_const)
  set IA : ℕ → Ω → ℝ := fun n ω => ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
    (min (a ω).toNNReal (farQ n)) z * farBump n z with hIAdef
  set IB : ℕ → Ω → ℝ := fun n ω => ∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (min (a ω).toNNReal (farQ n)) z * farBump n z with hIBdef
  have hIA : ∀ n, Measurable[m] (IA n) := fun n =>
    measurable_meanInt_randTime hWa hWc hVLa hVRa hVLc hVRc κ ρL ρR n ha hcut
  have hIB : ∀ n, Measurable[m] (IB n) := fun n =>
    measurable_meanInt_randTime hWa hWc hVLa hVRa hVLc hVRc κ (shiftL κ ρL 1) (shiftR κ ρR 1) n ha hcut
  -- the explicit form of the tested mean on each event
  have hform : ∀ n, ∀ᵐ ω ∂P, ω ∈ L → ω ∈ E n →
      0 < IB n ω - IA n ω + (∫ z, farBump n z) ∧
        c ω = (μ ω (farBump n) - IA n ω) / (IB n ω - IA n ω + (∫ z, farBump n z)) := by
    intro n
    filter_upwards [hmean (farBump n)] with ω hω hωL hωE
    set s : ℝ≥0 := (a ω).toNNReal with hs
    have hsq : s ≤ farQ n := by
      rw [hs, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hL ω hωL).2]
      exact hωE.2
    have hspos : 0 < s := by
      rw [hs]
      exact ENNReal.toNNReal_pos (ne_of_gt (hL ω hωL).1) (hL ω hωL).2
    have hmin : min s (farQ n) = s := min_eq_left hsq
    have hsafe := isSafeAt_farBump (hWc ω) n hsq
    have hdis : Disjoint (tsupport (farBump n)) (fwdHull (fun r : ℝ => W r.toNNReal ω) s) :=
      disjoint_fwdHull_of_isSafeAt (w := (W · ω)) (ζ := ⊤) (hWc ω).continuousOn
        (Coupling.tsupport_subset_H _) hsafe
    have hA : IA n ω = ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z *
        farBump n z := by simp only [hIAdef, ← hs, hmin]
    have hB' : IB n ω = ∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) s z * farBump n z := by simp only [hIBdef, ← hs, hmin]
    have hgap : IB n ω - IA n ω + (∫ z, farBump n z) =
        phaseGap κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s (farBump n) := by
      rw [hA, hB', phaseGap]
    have hJ : 0 < IB n ω - IA n ω + (∫ z, farBump n z) := by
      rw [hgap]
      exact phaseGap_pos hκ (farBump n).continuous (farBump n).hasCompactSupport (farBump_nonneg n)
        (integral_farBump_pos n) (hWc ω).continuousOn (Coupling.tsupport_subset_H _) hsafe (farLevel_pos n)
        le_rfl (hsep ω s hspos)
    have hint := integral_couplingMean_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ
      (farBump n).continuous (farBump n).hasCompactSupport (hWc ω).continuousOn (Coupling.tsupport_subset_H _)
      hsafe (farLevel_pos n) le_rfl (hord ω s).1 (hord ω s).2
      (isBoundedHarmonicExtension_phaseProc (ρL := ρL) (ρR := ρR) hκ c ((hord ω s).1 0) ((hord ω s).2 0))
    have hval : μ ω (farBump n) = IA n ω + c ω * (IB n ω - IA n ω + (∫ z, farBump n z)) := by
      rw [hω hωL hdis, hgap, hA, ← phaseInt_eq_add_mul]
      exact hint
    refine ⟨hJ, ?_⟩
    rw [hval]
    field_simp
    ring
  set S : Set Ω := ⋃ n, E n ∩
    {ω | (μ ω (farBump n) - IA n ω) / (IB n ω - IA n ω + (∫ z, farBump n z)) ∈ B} with hSdef
  refine ⟨S, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => (hEm n).inter ?_
    exact ((((hμ (farBump n)).sub (hIA n)).div (((hIB n).sub (hIA n)).add_const _))) hB
  · filter_upwards [ae_all_iff.2 hform] with ω hω hωL
    constructor
    · intro hcB
      obtain ⟨n, hn⟩ := exists_le_farQ (a ω).toNNReal
      have hωE : ω ∈ E n := by
        refine ⟨(hL ω hωL).1, ?_⟩
        rw [← ENNReal.coe_toNNReal (hL ω hωL).2]
        exact ENNReal.coe_le_coe.2 hn
      refine mem_iUnion.2 ⟨n, hωE, ?_⟩
      show _ ∈ B
      rw [← (hω n hωL hωE).2]
      exact hcB
    · intro hS
      obtain ⟨n, hωE, hmB⟩ := mem_iUnion.1 hS
      rw [(hω n hωL hωE).2]
      exact hmB

end Read

end InteractingSLE.Theorem14.GW4Fix.Mart
