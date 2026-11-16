/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermLineMeans
import InteractingSLE.Spec.Supplement.SB2OmCfg
import InteractingSLE.Spec.Supplement.SB2OmWord
import InteractingSLE.Spec.Supplement.SB2XfChain
import InteractingSLE.Spec.Supplement.SB2KqDrv
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase

/-!
# The configuration record at a line

Packet PROVE-RC-TERM, second run (ruling R124). The record `Theorem14.SB.Om.IsCfg` of SB2's line-mean theorem
(`Om.ae_chartTransport_eq_of_cfg`), at a sample of the first path against the completed second path and a positive
physical time `t` before the stop:

* `eqOn_mean_of_isFlowType`: every bounded harmonic extension of the force data of a flow type of a sorted word is the
  word's mean plus `ψχ`;
* `IsKSample.fwdHull_clock`: the hull of a generating driver of the chart path at the clock of a time `s` before the
  stop is the filled chart path;
* **`IsKSample.exists_isCfg`** (deterministic): from the builder `Term.exists_relChain_config` in the reflected frame
  (with the explorer's record driver `wB` and its global Loewner trace), `Lm.isRelConfigJKL_of_reflect`, and the
  agreement of the builder's relative driver with any generating driver `Wv` of the chart path on `[0, clock t]`
  (equal hulls, `Sec6.eqOn_of_fwdHull_eq`): a relative driver `W` with `IsCfgDriver` (equal to `Wv` on
  `[0, clock t]`, same hull at `clock t`, and a record `IsCfg … wB t W (clock t) β₁ GE₀ Gu`), given the three chart
  identifications and the three word identities; `cfgDriverOf`: a chosen such driver;
* `IsKSample.rT_image_entryPath`, `IsKSample.physChart_cfg`: the three chart identifications for the translation
  stage chart `Chart.id.recenter x₁` and the physical chart `Term.physChart`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly RLC.AStopProc
open Theorem14 Theorem14.SB Theorem14.SB.FinRel
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-- **The force data of a flow type of a sorted word extend to the word's mean plus `ψχ`.** -/
theorem eqOn_mean_of_isFlowType {κ ψ : ℝ} (hκ : 0 < κ) {β : BoundaryWord} (hs : β.IsSorted) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hft : FCDet.IsFlowType κ ψ β xL xR ρL ρR) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) G) :
    EqOn G (fun z => β.mean z + ψ * chiC κ) H := by
  set S : Set ℝ := insert 0 (β.jumps ∪ forceJumpSet xL xR) with hSdef
  have hSf : S.Finite := by
    refine Finite.insert 0 (Finite.union (Finset.finite_toSet _) ?_)
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have hG' : IsBoundedHarmonicExtension (fun y => β.fn y + ψ * chiC κ) S G := by
    obtain ⟨hh, hb, hl⟩ := hG
    refine ⟨hh, hb, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
    have hxJ : x ∉ β.jumps := fun h => hx (Or.inr (Or.inl h))
    have hxF : x ∉ forceJumpSet xL xR := fun h => hx (Or.inr (Or.inr h))
    show Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (β.fn x + ψ * chiC κ))
    rw [← Om.forceBoundaryData_eq_of_isFlowType hκ hft hx0 hxJ]
    exact hl x hxF
  have hm := Sec5.GlueCond.isBoundedHarmonicExtension_add_const
    (LocalExt.IsBoundedHarmonicExtension.mono_set (BoundaryWord.isBoundedHarmonicExtension_mean β hs)
      (S' := S) fun x hx => Or.inr (Or.inl hx)) (ψ * chiC κ)
  exact Impl.eqOn_of_isBoundedHarmonicExtension hSf hm hG'

/-- **The relative drivers of the configuration records at a sample**: continuous from `0`, equal to the generating
driver `Wv` on `[0, u]` with the same hull at `u`, and carrying a record `Om.IsCfg`. -/
def IsCfgDriver (κ ψ : ℝ) (c Φ : Chart) (A₁ : Set ℂ) (wB : ℝ → ℝ) (t : ℝ) (Wv : ℝ → ℝ) (u : ℝ)
    (β₁ : BoundaryWord) (GE₀ Gu : ℂ → ℝ) (W : ℝ → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ EqOn W Wv (Icc 0 u) ∧ fwdHull W u = fwdHull Wv u ∧
    ∃ dd : Om.CfgData, Om.IsCfg κ ψ c Φ A₁ wB t W u β₁ GE₀ Gu dd

open Classical in
/-- A relative driver of the configuration records, chosen where one exists. -/
def cfgDriverOf (κ ψ : ℝ) (c Φ : Chart) (A₁ : Set ℂ) (wB : ℝ → ℝ) (t : ℝ) (Wv : ℝ → ℝ) (u : ℝ)
    (β₁ : BoundaryWord) (GE₀ Gu : ℂ → ℝ) : ℝ → ℝ :=
  Classical.epsilon (IsCfgDriver κ ψ c Φ A₁ wB t Wv u β₁ GE₀ Gu)

theorem isCfgDriver_cfgDriverOf {κ ψ : ℝ} {c Φ : Chart} {A₁ : Set ℂ} {wB : ℝ → ℝ} {t : ℝ} {Wv : ℝ → ℝ} {u : ℝ}
    {β₁ : BoundaryWord} {GE₀ Gu : ℂ → ℝ} (h : ∃ W, IsCfgDriver κ ψ c Φ A₁ wB t Wv u β₁ GE₀ Gu W) :
    IsCfgDriver κ ψ c Φ A₁ wB t Wv u β₁ GE₀ Gu (cfgDriverOf κ ψ c Φ A₁ wB t Wv u β₁ GE₀ Gu) :=
  Classical.epsilon_spec h

section K

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}

/-- **The hull of a generating driver of the chart path at the clock** of a time before the stop. -/
theorem IsKSample.fwdHull_clock (h : IsKSample U T ρ₂ q d w ζ ρ₁) {Wv : ℝ≥0 → ℝ}
    (hgen : IsGeneratingTrace Wv (kLife U ρ₂ T d ρ₁ ζ) (kTrace U ρ₂ T d ρ₁ ζ)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ) :
    fwdHull (fun r : ℝ => Wv r.toNNReal) (chartClock (kPath U ρ₂ T d ρ₁ ζ) s) =
      fillH (kPath U ρ₂ T d ρ₁ ζ '' Icc 0 s) := by
  have hg := h.isAGood (Ω := Unit) ()
  have h1 := fwdHull_aClock hg (W := Wv) hgen hs
  rw [hg.coe_aClock s] at h1
  exact h1

/-- Every clock value up to the clock of `t` is the clock of an earlier time. -/
theorem IsKSample.exists_time_of_clock (h : IsKSample U T ρ₂ q d w ζ ρ₁) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (chartClock (kPath U ρ₂ T d ρ₁ ζ) t)) :
    ∃ s : ℝ≥0, s ≤ t ∧ chartClock (kPath U ρ₂ T d ρ₁ ζ) s = x := by
  have hclk := h.isClockOn
  have hle : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      capLife (chartClock (kPath U ρ₂ T d ρ₁ ζ)) (kStop ρ₂ T d ρ₁ ζ) :=
    le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hx.2)) (hclk.coe_toNNReal_le_capLife ht.le)
  obtain ⟨hsL, hsq⟩ := hclk.invClock_spec hle
  rw [Real.coe_toNNReal _ hx.1] at hsq
  refine ⟨_, ?_, hsq⟩
  by_contra hlt
  have h1 := hclk.strictMonoOn (show (t : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ from ht.le) hsL (not_le.1 hlt)
  rw [hsq] at h1
  exact absurd hx.2 (not_le.2 h1)

/-- **The configuration record at a line** (see the module docstring). -/
theorem IsKSample.exists_isCfg (h : IsKSample U T ρ₂ q d w ζ ρ₁) {κ ψ : ℝ} {c Φ : Chart} {A₁ : Set ℂ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ)
    {wB : ℝ → ℝ} (hwB : Continuous wB) (hwB0 : wB 0 = 0) {αr : ℝ → ℂ} (hαr : IsLoewnerTrace wB αr)
    (hα : ∀ r ∈ Icc (0 : ℝ) t, αr r = ρ₁ r.toNNReal) (htip : ρ₁ t ∈ H)
    {Wv : ℝ≥0 → ℝ} (hWc : Continuous Wv) (hW0 : Wv 0 = 0)
    (hgen : IsGeneratingTrace Wv (kLife U ρ₂ T d ρ₁ ζ) (kTrace U ρ₂ T d ρ₁ ζ))
    (hA : ∀ z ∈ H, z ∈ reflectC '' fillH (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) ↔
      c.2.1 z ∈ A₁)
    (hinv : ∀ y ∈ H, Φ.2.1 y = c.2.1 (reflectC ((entryChart (-U) (T : ℝ) d).2.1 (reflectC y))))
    (hlift : ∀ y ∈ H, Φ.2.2 (Φ.2.1 y) =
      -(entryChart (-U) (T : ℝ) d).2.2 ((entryChart (-U) (T : ℝ) d).2.1 (reflectC y)) + c.2.2 (Φ.2.1 y))
    {β₁ : BoundaryWord} {GE₀ Gu : ℂ → ℝ}
    (hG₀ : ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) G →
      EqOn G (fun z => β₁.mean z + ψ * chiC κ) H)
    (hGE : ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension (flowedData κ ρL' ρR' xL' xR' wB t)
      (flowedJumps xL' xR' wB t) G → EqOn G (fun z => GE₀ z + ψ * chiC κ) H)
    (hGu : ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
      EqOn W (fun r : ℝ => Wv r.toNNReal) (Icc 0 (chartClock (kPath U ρ₂ T d ρ₁ ζ) t)) →
      ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension
        (flowedData κ ρL ρR xL xR W (chartClock (kPath U ρ₂ T d ρ₁ ζ) t))
        (flowedJumps xL xR W (chartClock (kPath U ρ₂ T d ρ₁ ζ) t)) G → EqOn G Gu H) :
    ∃ W : ℝ → ℝ, IsCfgDriver κ ψ c Φ A₁ wB (t : ℝ) (fun r : ℝ => Wv r.toNNReal)
      (chartClock (kPath U ρ₂ T d ρ₁ ζ) t) β₁ GE₀ Gu W := by
  have hP : IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s)) := h
  obtain ⟨a, hta, haL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hta' : t < a := ENNReal.coe_lt_coe.1 hta
  have haζ : (a : ℝ≥0∞) < ζ := lt_life_of_lt haL
  have hPre := hP.isExpPrefix haL
  obtain ⟨β', γ, Wr, ηr, -, hγ, hγ0, hγeq, hch, -, hcfg⟩ := exists_relChain_config (V := -U)
    (ξ := fun s => reflectC (ρ₂ s)) (p := -q) (d := d) (ρL := ρR) (ρR := ρL) (xL := fun j => -xR j)
    (xR := fun i => -xL i) (ρL' := ρR') (ρR' := ρL') (xL' := fun j => -xR' j) (xR' := fun i => -xL' i) κ
    (chiC κ) (fun j => neg_nonpos.2 (hxR j)) (fun i => neg_nonneg.2 (hxL i)) (fun j => neg_nonpos.2 (hxR' j))
    (fun i => neg_nonneg.2 (hxL' i)) hP.entry hP.tipPos hP.ne hP.gen hP.drvCont hP.drvZero haζ
    (hP.inj.mono fun s hs => show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs.2).trans haζ.le)
    hPre.hbar hPre.off (hP.order a haζ) (S₀ := (t : ℝ)) t.coe_nonneg (NNReal.coe_lt_coe.2 hta')
  obtain ⟨W, rfl⟩ : ∃ W : ℝ → ℝ, Wr = fun r => -W r := ⟨fun r => -Wr r, by funext r; simp⟩
  have hWcont : Continuous W := by
    have h1 : Continuous fun r => -(-W r) := hch.1.neg
    simpa only [neg_neg] using h1
  have hW0' : W 0 = 0 := by
    have h1 : -W 0 = 0 := hch.2.1
    exact neg_eq_zero.1 h1
  -- the chart path is the lift on `[0, a]`
  have heq : ∀ s ≤ a, chartPath (-U) (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ s = γ s := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, hP.chartPath_zero, hγ0]
    · rw [hγeq s hs0 hs, hP.chartPath_eq_fwd hs0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) haL)]
  -- the two clocks
  have hclk : ∀ s : ℝ≥0, s ≤ t → Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (s : ℝ) =
      chartClock (kPath U ρ₂ T d ρ₁ ζ) s := by
    intro s hs
    have e1 : chartClock (kPath U ρ₂ T d ρ₁ ζ) s =
        chartClock (chartPath (-U) (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ) s :=
      FCPlumb.FCKerD.chartClock_reflect _ s
    rw [e1]
    unfold Sec7.Lemma71C.capClock chartClock
    rw [Mn.image_toNNReal_Icc γ s.coe_nonneg, Real.toNNReal_coe,
      image_congr fun r hr => (heq r (hr.2.trans (hs.trans hta'.le))).symm]
  -- the hulls of `W` at the clock
  have hhullW : ∀ s : ℝ≥0, s ≤ t → fwdHull W (chartClock (kPath U ρ₂ T d ρ₁ ζ) s) =
      fillH (kPath U ρ₂ T d ρ₁ ζ '' Icc 0 s) := by
    intro s hs
    have hsI : (s : ℝ) ∈ Icc (0 : ℝ) t := ⟨s.coe_nonneg, NNReal.coe_le_coe.2 hs⟩
    have h2 := (hch.2.2.2.2.2.2 (s : ℝ) hsI).2.2.1
    rw [hclk s hs, Real.toNNReal_coe] at h2
    have h3 : fwdHull (fun r => -W r) (chartClock (kPath U ρ₂ T d ρ₁ ζ) s) =
        reflectC '' fwdHull W (chartClock (kPath U ρ₂ T d ρ₁ ζ) s) := LP.fwdHull_neg W _
    have h4 : kPath U ρ₂ T d ρ₁ ζ '' Icc 0 s = reflectC '' (γ '' Icc 0 s) := by
      rw [image_image]
      refine image_congr fun r hr => ?_
      show reflectC (chartPath (-U) (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ r) =
        reflectC (γ r)
      rw [heq r (hr.2.trans (hs.trans hta'.le))]
    rw [h4, LP.fillH_image_reflectC, ← h2, h3, Sec7.FlowReflect.reflectC_image_image]
  -- the relative driver is the generating driver on `[0, clock t]`
  have hu0 : 0 ≤ chartClock (kPath U ρ₂ T d ρ₁ ζ) t := (h.isAGood (Ω := Unit) ()).chartClock_nonneg t
  have hagree : EqOn W (fun r : ℝ => Wv r.toNNReal) (Icc 0 (chartClock (kPath U ρ₂ T d ρ₁ ζ) t)) := by
    have hWv0 : (fun r : ℝ => Wv r.toNNReal) 0 = 0 := by
      show Wv (0 : ℝ).toNNReal = 0
      rw [Real.toNNReal_zero, hW0]
    refine Sec6.eqOn_of_fwdHull_eq (W' := fun r : ℝ => Wv r.toNNReal) hWcont
      (hWc.comp continuous_real_toNNReal) hW0' hWv0 hu0 fun x hx => ?_
    obtain ⟨s, hs, hsx⟩ := h.exists_time_of_clock ht hx
    rw [← hsx, hhullW s hs]
    exact (h.fwdHull_clock hgen (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht)).symm
  -- the explorer in the reflected frame
  have hwg : Continuous fun r => -wB r := hwB.neg
  have hwg0 : (fun r => -wB r) 0 = 0 := by simp only [hwB0, neg_zero]
  have hηg : IsLoewnerTrace (fun r => -wB r) (fun r => reflectC (αr r)) :=
    Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hαr
  have htI : (t : ℝ) ∈ Ioc (0 : ℝ) t := ⟨NNReal.coe_pos.2 ht0, le_rfl⟩
  have himg : (fun r : ℝ => reflectC (αr r)) '' Icc 0 (t : ℝ) =
      (fun s : ℝ≥0 => reflectC (ρ₁ s)) '' Icc 0 t := by
    have e := Mn.image_toNNReal_Icc (fun s : ℝ≥0 => reflectC (ρ₁ s)) t.coe_nonneg
    rw [Real.toNNReal_coe] at e
    rw [← e]
    refine image_congr fun r hr => ?_
    show reflectC (αr r) = reflectC (ρ₁ r.toNNReal)
    rw [hα r hr]
  have hKg : fwdHull (fun r => -wB r) (t : ℝ) =
      fillH ((fun s : ℝ≥0 => reflectC (ρ₁ s)) '' Icc 0 ((t : ℝ).toNNReal)) := by
    rw [hηg.2.2 (t : ℝ) t.coe_nonneg, himg, Real.toNNReal_coe]
  have hag : ∀ r ∈ Icc (0 : ℝ) (t : ℝ), (fun r => reflectC (αr r)) r =
      (fun s : ℝ≥0 => reflectC (ρ₁ s)) r.toNNReal := fun r hr => by
    show reflectC (αr r) = reflectC (ρ₁ r.toNNReal)
    rw [hα r hr]
  have hηH : (fun r => reflectC (αr r)) (t : ℝ) ∈ H := by
    show reflectC (αr (t : ℝ)) ∈ H
    rw [hα (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩, Real.toNNReal_coe]
    exact Sec7.FlowReflect.reflectC_mem_H htip
  obtain ⟨LΨ, G₀, GE, G, hLeq, hJK⟩ := hcfg (fun r => -wB r) (fun r => reflectC (αr r)) (t : ℝ) htI hwg hwg0
    hηg hKg hag hηH
  rw [hclk t le_rfl] at hJK
  have hJKL := Lm.isRelConfigJKL_of_reflect hJK
  have ew : (-(fun r => -wB r)) = wB := by funext r; simp
  have eW : (-(fun r => -W r)) = W := by funext r; simp
  rw [ew, eW] at hJKL
  have hhull : fwdHull W (chartClock (kPath U ρ₂ T d ρ₁ ζ) t) =
      fwdHull (fun r : ℝ => Wv r.toNNReal) (chartClock (kPath U ρ₂ T d ρ₁ ζ) t) := by
    rw [hhullW t le_rfl]
    exact (h.fwdHull_clock hgen ht).symm
  refine ⟨W, hWcont, hW0', hagree, hhull,
    ⟨reflectC '' fillH (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1),
    fun z => reflectC ((entryChart (-U) (T : ℝ) d).1 (reflectC z)),
    fun z => reflectC ((entryChart (-U) (T : ℝ) d).2.1 (reflectC z)), fun z => conj (LΨ (reflectC z)),
    Sec7.FlowReflect.reflJumps ∅, fun s => reflectC (reflectC (αr s)), fun s => reflectC (ηr s), _, _, _, _, _, _,
    fun z => -G₀ (reflectC z), fun z => -GE (reflectC z), fun z => -G (reflectC z), _⟩, hA,
    hJKL, hinv, ?_, ?_, ?_, ?_⟩
  · -- the lift relation
    intro y hy
    have hmem : (entryChart (-U) (T : ℝ) d).2.1 (reflectC y) ∈
        H \ fillH (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) :=
      hP.entry.isDomainChart'.inv_mem (Sec7.FlowReflect.reflectC_mem_H hy)
    have hl := hLeq hmem
    simp only at hl ⊢
    rw [hlift y hy, LP.reflectC_reflectC, Complex.conj_im, ← hl]
  · exact hG₀ _ (Om.isBoundedHarmonicExtension_reflect_init (IsRelConfigJK.bhe₀ hJK))
  · exact hGE _ (Om.isBoundedHarmonicExtension_reflect_flowed (IsRelConfigJK.bheE hJK))
  · exact hGu W hWcont hW0' hagree _ (Om.isBoundedHarmonicExtension_reflect_flowed (IsRelConfigJK.bheu hJK))

/-- The reflection–translation of the builder's retained path is the retained path. -/
theorem IsKSample.rT_image_entryPath (h : IsKSample U T ρ₂ q d w ζ ρ₁) (x₁ : ℝ) :
    rT x₁ '' (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) =
      (fun s : ℝ≥0 => ρ₂ (s : ℝ) + ((x₁ - d : ℝ) : ℂ)) '' Icc 0 T := by
  have hP : IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s)) := h
  rw [image_entryPath_eq hP.tpos, image_image]
  refine image_congr fun s _ => ?_
  show reflectC (reflectC (ρ₂ (s : ℝ)) + (d : ℂ)) + (x₁ : ℂ) = _
  rw [reflectC_add_ofReal, LP.reflectC_reflectC]
  push_cast
  ring

/-- **The three chart identifications** of the configuration record for the translation stage chart
`Chart.id.recenter x₁` and the physical chart of a record with the driver and time of the sample. -/
theorem IsKSample.physChart_cfg (h : IsKSample U T ρ₂ q d w ζ ρ₁) {r : RecData} (hU : rdrv r = U)
    (hT : rtime r = (T : ℝ)) {x₁ x₂ : ℝ} (hd : d = x₁ - x₂) :
    (∀ z ∈ H, z ∈ reflectC '' fillH (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) ↔
      (Chart.id.recenter x₁).2.1 z ∈ fillH ((fun s : ℝ≥0 => ρ₂ (s : ℝ) + (x₂ : ℂ)) '' Icc 0 T)) ∧
    (∀ y ∈ H, (physChart x₂ r (markPos U (T : ℝ) d)).2.1 y =
      (Chart.id.recenter x₁).2.1 (reflectC ((entryChart (-U) (T : ℝ) d).2.1 (reflectC y)))) ∧
    ∀ y ∈ H, (physChart x₂ r (markPos U (T : ℝ) d)).2.2 ((physChart x₂ r (markPos U (T : ℝ) d)).2.1 y) =
      -(entryChart (-U) (T : ℝ) d).2.2 ((entryChart (-U) (T : ℝ) d).2.1 (reflectC y)) +
        (Chart.id.recenter x₁).2.2 ((physChart x₂ r (markPos U (T : ℝ) d)).2.1 y) := by
  have hP : IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s)) := h
  have hV := hP.entry.tip.cont
  have hV0 := hP.entry.tip.zero
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hUc : Continuous U := by
    have h1 : Continuous fun s => -(-U s) := hV.neg
    simpa only [neg_neg] using h1
  have hU0 : U 0 = 0 := by
    have h1 : -U 0 = 0 := hV0
    exact neg_eq_zero.1 h1
  have hx₂ : ((x₁ - d : ℝ) : ℂ) = (x₂ : ℂ) := by rw [hd]; push_cast; ring
  -- the inverse on `ℍ`
  have hinv : ∀ y ∈ H, (physChart x₂ r (markPos U (T : ℝ) d)).2.1 y =
      reflectC ((entryChart (-U) (T : ℝ) d).2.1 (reflectC y)) + (x₁ : ℂ) := by
    intro y hy
    rw [physChart_inv, hU, hT, h.fwdMapInv_eq_kInv hy]
    show reflectC (entryInv (-U) (T : ℝ) d (reflectC y)) + (d : ℂ) + (x₂ : ℂ) = _
    rw [entryInv_eqOn hV hV0 hT0 d (Sec7.FlowReflect.reflectC_mem_H hy), hd]
    push_cast
    ring
  refine ⟨fun z _ => ?_, hinv, fun y hy => ?_⟩
  · have e : fillH ((fun s : ℝ≥0 => ρ₂ (s : ℝ) + (x₂ : ℂ)) '' Icc 0 T) =
        rT x₁ '' fillH (entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1) := by
      rw [rT_image_fillH, h.rT_image_entryPath x₁, hx₂]
    rw [e]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, hpz⟩
      refine ⟨p, hp, ?_⟩
      have h1 : reflectC p + (x₁ : ℂ) = z + (x₁ : ℂ) := hpz
      exact add_right_cancel h1
  · have hyτ : y + (markPos U (T : ℝ) d : ℂ) ∈ H := by
      show 0 < (y + (markPos U (T : ℝ) d : ℂ)).im
      have : 0 < y.im := hy
      simpa using this
    have hmL : markPosL (-U) (T : ℝ) (-d) = -markPos U (T : ℝ) d := Om.markPosL_neg U (T : ℝ) d
    have hw : (entryChart (-U) (T : ℝ) d).2.1 (reflectC y) - (d : ℂ) =
        reflectC (fwdMapInv U (T : ℝ) (y + (markPos U (T : ℝ) d : ℂ))) := by
      rw [entryChart_inv, hmL, add_sub_cancel_right, ← CfNoReturn.fwdMapInv_neg hUc hU0 hT0 hyτ,
        reflectC_add_ofReal]
      push_cast
      ring_nf
    have hL : (physChart x₂ r (markPos U (T : ℝ) d)).2.2 ((physChart x₂ r (markPos U (T : ℝ) d)).2.1 y) =
        (logDerivFwd U (T : ℝ) (fwdMapInv U (T : ℝ) (y + (markPos U (T : ℝ) d : ℂ)))).im := by
      rw [physChart_lift, physChart_inv, hU, hT, add_sub_cancel_right]
    rw [hL, entryChart_lift, hw, LP.im_logDerivFwd_neg U hT0]
    show _ = -(-(logDerivFwd U (T : ℝ) (fwdMapInv U (T : ℝ) (y + (markPos U (T : ℝ) d : ℂ)))).im + 0) + 0
    ring

end K

end Term

end InteractingSLE.RealContact
