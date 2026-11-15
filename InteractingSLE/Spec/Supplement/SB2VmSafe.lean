/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VmAd

/-!
# SB2(1)'s version half: the safe events of the frozen driver, and `Vk.SB2DriverAdaptStatement` proved

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half). The safe events ask, at the clock time `a t`, that
the threshold of the driver with the cell's force points is after `a t` and that the driver's hull at `a t` avoids a
closed set. Both see the driver only on `[0, a t]`. There it equals the **stopped driver**, which is measurable for
`D.lineFiltC t` (`Vm.exists_goodReading`).

* `measurable_stopped`: a driver stopped at a measurable time, read from readings below that time;
* `measurable_thr_of_le`: the threshold is measurable for any σ-algebra the driver and word are measurable for;
* `thr_le_iff_of_eqOn`: whether the threshold is at most `τ` depends on the driver on `[0, τ]` only (attained
  threshold, `RLC.OrdModel.threshold_congr`);
* **`measurableSet_safe`**: the safe event for a closed set is in `D.lineFiltC t` (it is a.s. the stopped driver's
  event; completeness `Vf.lineFiltC_closed`);
* **`sb2DriverAdaptStatement`**: `Vk.SB2DriverAdaptStatement` from Theorem 1.3 and S3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vm

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal Sec7.Lemma71C

/-- A family indexed by a measurable `ℕ`-valued function is measurable. -/
theorem measurable_comp_nat {Ω β : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace β] {g : Ω → ℕ}
    (hg : Measurable[𝒢] g) {F : ℕ → Ω → β} (hF : ∀ k, Measurable[𝒢] (F k)) :
    Measurable[𝒢] fun ω => F (g ω) ω := by
  intro B hB
  have e : (fun ω => F (g ω) ω) ⁻¹' B = ⋃ k, g ⁻¹' {k} ∩ F k ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨g ω, rfl, h⟩, fun ⟨k, hk, h⟩ => hk ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun k => (hg (measurableSet_singleton k)).inter (hF k hB)

open scoped Classical in
/-- **The driver stopped at a measurable time is measurable**, given readings below that time. -/
theorem measurable_stopped {Ω : Type*} {𝒢 : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun q => W q ω) {Eg : Set Ω} {τ : Ω → ℝ≥0} (hτ : Measurable[𝒢] τ)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ v, Measurable[𝒢] (Y v)) (hYon : ∀ v ω, ω ∈ Eg → v ≤ τ ω → Y v ω = W v ω)
    (hYoff : ∀ v ω, ω ∉ Eg → Y v ω = 0) (s : ℝ≥0) :
    Measurable[𝒢] fun ω => if ω ∈ Eg then W (min s (τ ω)) ω else 0 := by
  set f : ℕ → Ω → ℝ := fun n ω => Y (min s (Vj.dfl n (τ ω))) ω with hfdef
  have hfm : ∀ n, Measurable[𝒢] (f n) := fun n =>
    measurable_comp_nat (g := fun ω => ⌊τ ω * 2 ^ n⌋₊) ((hτ.mul_const _).nat_floor)
      (F := fun k => Y (min s ((k : ℝ≥0) / 2 ^ n))) fun k => hY _
  refine measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ Eg
  · simp only [hω, ↓reduceIte]
    have hval : ∀ n, f n ω = W (min s (Vj.dfl n (τ ω))) ω := fun n =>
      hYon _ ω hω ((min_le_right _ _).trans (Vj.dfl_le n _))
    have ht : Tendsto (fun n => min s (Vj.dfl n (τ ω))) atTop (𝓝 (min s (τ ω))) :=
      tendsto_const_nhds.min (Vj.tendsto_dfl _)
    exact (((hWc ω).tendsto _).comp ht).congr fun n => (hval n).symm
  · simp only [hω, ↓reduceIte]
    have h0 : ∀ n, f n ω = 0 := fun n => hYoff _ ω hω
    simp only [h0]
    exact tendsto_const_nhds

/-- **The threshold is measurable** for every σ-algebra the driver and the word are measurable for. -/
theorem measurable_thr_of_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ r, Measurable[𝒢] (B r)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) : Measurable[𝒢] (FCDet.thr ρL ρR B xL xR) := by
  have hBa : StronglyAdapted (Filtration.const ℝ≥0 𝒢 h𝒢) B := fun r => (hBm r).stronglyMeasurable
  have hle : ∀ T : ℝ≥0, MeasurableSet[𝒢] {ω | FCDet.thr ρL ρR B xL xR ω ≤ T} := fun T =>
    FCDet.measurableSet_thr_le (mΩ := mΩ) (𝓗 := Filtration.const ℝ≥0 𝒢 h𝒢) hBc hBa hxL hxR T
  refine measurable_of_Iic (mδ := 𝒢) fun T => ?_
  induction T using ENNReal.recTopCoe with
  | top => simp only [Iic_top, preimage_univ]; exact @MeasurableSet.univ _ 𝒢
  | coe T => exact hle T

/-- The threshold is at most any time of the threshold set. -/
theorem thr_le_of_mem {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω} {T : ℝ≥0}
    (hT : T ∈ MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)) : FCDet.thr ρL ρR W xL xR ω ≤ T := by
  unfold FCDet.thr MartChar.thresholdTime
  rw [if_pos ⟨T, hT⟩]
  exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hT)

/-- **Whether the threshold is at most `τ` depends only on the driver on `[0, τ]`.** -/
theorem thr_le_iff_of_eqOn {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hBc : ∀ ω, Continuous fun t => B t ω) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) {ω : Ω} {τ : ℝ≥0} (h : ∀ s ≤ τ, W s ω = B s ω) :
    FCDet.thr ρL ρR W xL xR ω ≤ τ ↔ FCDet.thr ρL ρR B xL xR ω ≤ τ := by
  have key : ∀ {W B : ℝ≥0 → Ω → ℝ}, (∀ ω, Continuous fun t => W t ω) → (∀ ω, Continuous fun t => B t ω) →
      (∀ s ≤ τ, W s ω = B s ω) → FCDet.thr ρL ρR W xL xR ω ≤ τ → FCDet.thr ρL ρR B xL xR ω ≤ τ := by
    intro W B hWc hBc h hle
    obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, FCDet.thr ρL ρR W xL xR ω = T :=
      ⟨_, (ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hle)).symm⟩
    have hTτ : T ≤ τ := by rw [hT] at hle; exact ENNReal.coe_le_coe.1 hle
    have hmem := FCDet.thr_mem_thresholdSet hWc xL xR hT
    have hmem' : T ∈ MartChar.thresholdSet ρL ρR (fun t => B t ω) (fun i t => geomLW B xL i t ω)
        (fun j t => geomRW B xR j t ω) :=
      (RLC.OrdModel.threshold_congr (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (hBc ω)
        fun s hs => h s (hs.trans hTτ)).1 hmem
    exact (thr_le_of_mem hmem').trans (ENNReal.coe_le_coe.2 hTτ)
  exact ⟨key hWc hBc h, key hBc hWc fun s hs => (h s hs).symm⟩

/-- The scale-one drive is the driver read on `ℝ`. -/
theorem drive_one {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    QuantumZipper.drive 1 B ω = fun s : ℝ => B s.toNNReal ω := by
  funext s
  simp only [QuantumZipper.drive, Real.sqrt_one, one_mul]

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The safe event of the frozen driver for a closed set is an event of the completed line filtration.** -/
theorem measurableSet_safe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {a : ℝ≥0 → Ω → ℝ≥0∞}
    (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)) (hac : ∀ ω, Continuous fun t => a t ω)
    (ham : ∀ ω, Monotone fun t => a t ω)
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t)
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0)))
    {W : ℝ≥0 → Ω → ℝ} {G : Set Ω} (hGm : MeasurableSet G) (hGnull : P Gᶜ = 0) (hWm : ∀ q, Measurable (W q))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun q => W q ω)
    (hWoff : ∀ q ω, ω ∉ G ∩ D.event → W q ω = 0)
    (hWon : ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
      IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = Vk.relLife κ b jumps E k u η ζ ω ∧
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vk.relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ t, Measurable[D.lineFiltC HP t] xL) (hxR : ∀ t, Measurable[D.lineFiltC HP t] xR)
    {K : Set ℂ} (hK : IsClosed K) (t : ℝ≥0) :
    MeasurableSet[D.lineFiltC HP t] {ω | a t ω < FCDet.thr ρL ρR W xL xR ω ∧
      Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
  classical
  obtain ⟨Eg, -, hEgsub, hEgae, hY⟩ := exists_goodReading h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0
    hWc hWoff hWon
  set τ : Ω → ℝ≥0 := fun ω => (a t ω).toNNReal with hτdef
  have hτm : Measurable[D.lineFiltC HP t] τ := ENNReal.measurable_toNNReal.comp (ha t)
  set B : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ Eg then W (min s (τ ω)) ω else 0 with hBdef
  have hBm : ∀ s, Measurable[D.lineFiltC HP t] (B s) := fun s =>
    measurable_stopped hWc hτm (Y := fun v => (Eg ∩ {ω | (v : ℝ≥0∞) ≤ a t ω}).indicator (W v))
      (fun v => hY v t)
      (fun v ω hω hv => by
        have hva : (v : ℝ≥0∞) ≤ a t ω := by
          by_cases htop : a t ω = ⊤
          · rw [htop]; exact le_top
          · rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hv
        exact indicator_of_mem (show ω ∈ Eg ∩ {ω | (v : ℝ≥0∞) ≤ a t ω} from ⟨hω, hva⟩) _)
      (fun v ω hω => indicator_of_notMem (fun h' => hω h'.1) _) s
  have hBc : ∀ ω, Continuous fun s => B s ω := fun ω => by
    by_cases hω : ω ∈ Eg
    · simp only [hBdef, hω, ↓reduceIte]
      exact (hWc ω).comp (continuous_id.min continuous_const)
    · simp only [hBdef, hω, ↓reduceIte]
      exact continuous_const
  -- the stopped driver's event
  have hSB : MeasurableSet[D.lineFiltC HP t] {ω | a t ω < FCDet.thr ρL ρR B xL xR ω ∧
      Disjoint K (fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ))} :=
    (measurableSet_lt (ha t) (measurable_thr_of_le ((D.lineFiltC HP).le t) ρL ρR hBc hBm (hxL t) (hxR t))).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hBc hBm (measurable_coe_nnreal_real.comp hτm)
        (fun ω => (τ ω).2) hK)
  -- the event itself is ambient-measurable
  have hxL0 : Measurable xL := (hxL 0).mono ((D.lineFiltC HP).le 0) le_rfl
  have hxR0 : Measurable xR := (hxR 0).mono ((D.lineFiltC HP).le 0) le_rfl
  have hS : MeasurableSet {ω | a t ω < FCDet.thr ρL ρR W xL xR ω ∧
      Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
    have h1 := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (m := mΩ) hWc hWm
      (measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp ((ha t).mono ((D.lineFiltC HP).le t) le_rfl)))
      (fun ω => ((a t ω).toNNReal).2) hK
    simp only [drive_one] at h1
    exact (measurableSet_lt ((ha t).mono ((D.lineFiltC HP).le t) le_rfl)
      (measurable_thr_of_le le_rfl ρL ρR hWc hWm hxL0 hxR0)).inter h1
  refine Vf.lineFiltC_closed D HP t hS hSB ?_
  filter_upwards [hEgae] with ω hω
  apply propext
  show (a t ω < _ ∧ _) ↔ (a t ω < _ ∧ _)
  by_cases hev : ω ∈ D.event
  · have hωE := hω hev
    have hBW : ∀ s ≤ τ ω, W s ω = B s ω := fun s hs => by
      simp only [hBdef, hωE, ↓reduceIte, min_eq_left hs]
    have hhull : fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω : ℝ) =
        fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ) := by
      rw [drive_one]
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((hWc ω).comp continuous_real_toNNReal)
        ((hBc ω).comp continuous_real_toNNReal) (τ ω).2 fun r hr => hBW _ ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    have hthr : a t ω < FCDet.thr ρL ρR W xL xR ω ↔ a t ω < FCDet.thr ρL ρR B xL xR ω := by
      by_cases htop : a t ω = ⊤
      · rw [htop]; simp only [not_top_lt]
      · rw [← ENNReal.coe_toNNReal htop, ← not_le, ← not_le]
        exact not_congr (thr_le_iff_of_eqOn hWc hBc xL xR hBW)
    rw [hthr]
    show _ ∧ Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω : ℝ)) ↔ _
    rw [hhull]
  · have hW0' : ∀ s, W s ω = 0 := fun s => hWoff s ω fun h' => hev h'.2
    have hB0 : ∀ s, B s ω = 0 := fun s => by
      simp only [hBdef, show ω ∉ Eg from fun h' => hev (hEgsub h').2, ↓reduceIte]
    have hthr : FCDet.thr ρL ρR W xL xR ω = FCDet.thr ρL ρR B xL xR ω :=
      FCDet.thr_congr (fun s => by rw [hW0' s, hB0 s]) rfl rfl
    have hdr : QuantumZipper.drive 1 B ω = fun s : ℝ => W s.toNNReal ω := by
      rw [drive_one]; funext s; rw [hW0', hB0]
    rw [hthr, hdr]

/-- **`Vk.SB2DriverAdaptStatement` from Theorem 1.3 and S3.** -/
theorem sb2DriverAdaptStatement (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) : Vk.SB2DriverAdaptStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ D a ha hac ham ha0 hae ρ W G hρm hρ hGm hGnull hWm hW0 hWc
    hWoff hWon
  have hword : ∀ t, Measurable[D.lineFiltC HP t] I.word := fun t =>
    (I.word_measurable.mono D.past_le_marks le_rfl).mono (D.marks_le_lineFiltC HP t) le_rfl
  refine ⟨stronglyAdapted_frozen h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon,
    fun w _ φ t => ?_, fun w _ Fb t => ?_⟩
  · exact measurableSet_safe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon
      (typedRhoL w) (typedRhoR w) (fun t => measurable_cellXL (hword t) w) (fun t => measurable_cellXR (hword t) w)
      (isClosed_tsupport _) t
  · exact measurableSet_safe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon
      (typedRhoL w) (typedRhoR w) (fun t => measurable_cellXL (hword t) w) (fun t => measurable_cellXR (hword t) w)
      (Set.Finite.isClosed_biUnion Fb.finite_toSet fun _ _ => isClosed_closedBall) t

end

/-- **SB2(1)'s line version** (`Lv.SB2LineVersionRStatement`) from Theorem 1.3, S3, E7 and the relative endpoint
(`Vk.SB2DriverAdaptStatement` discharged). -/
theorem sb2LineVersionRStatement_of_endpoint (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (hE7 : Vh.SB2RemainderLifeStatement.{u})
    (hEnd : Vk.SB2RelEndpointStatement.{u}) : Lv.SB2LineVersionRStatement.{u} :=
  Vk.sb2LineVersionRStatement_of_adapt h13 hS3 hE7 hEnd (sb2DriverAdaptStatement h13 hS3)


end InteractingSLE.Theorem14.SB.Vm
