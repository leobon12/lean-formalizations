/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsGood

/-!
# SB2(1)'s stops and frozen drivers (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19).

* **`SB2StopData`**: the clock, the driven family, a measurable conull set of good samples and the reading of the
  family's canonical driver from the completed line filtration; **`exists_stopData`** (from Theorem 1.3, S3 and the
  relative seed; the only place of this file where S3 enters).
* Derived objects: the good event `Gs`, the family `ρ'` (the vertical line off `Gs`), its canonical driver `Wr`, the
  record `sb2Rec`, the stops `Vstop m` of the rule along `Wr`, the drivers `W m` frozen at `Vstop m` (and `0` off
  `Gs`), and the rule stops `V m` of `W m`, equal to `Vstop m` on `Gs`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Sec7.PocketTraversal Supp8.Q3Stop Supp8.GB6.HullId

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The data of SB2(1)'s stops**: the clock, the driven family, a measurable conull set of samples which are
good when on the entrance event, and the reading of the family's canonical driver from the completed line filtration
(`exists_segReading`). -/
structure SB2StopData (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) where
  a : ℝ≥0 → Ω → ℝ≥0∞
  ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)
  hac : ∀ ω, Continuous fun t => a t ω
  ham : ∀ ω, Monotone fun t => a t ω
  ha0 : ∀ ω, a 0 ω = 0
  hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
    ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t
  ρ : Ω → ℝ → ℂ
  hρm : ∀ r, 0 ≤ r → Measurable fun ω => ρ ω r
  hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
    (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
    (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
      ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))
  G : Set Ω
  hGm : MeasurableSet G
  hGnull : P Gᶜ = 0
  hgood : ∀ ω ∈ G ∩ D.event, GoodAt η ζ I a ρ ω
  read : ∃ Eg : Set Ω, (∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg) ∧ Eg ⊆ G ∩ D.event ∧
    (∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ Eg) ∧ (∀ ω ∈ Eg, ∀ t, a t ω ≤ Sec7.Lemma71C.capLife (ρ ω)) ∧
    ∀ t r : ℝ≥0, Measurable[D.lineFiltC HP t]
      ((Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}).indicator fun ω => Sec7.Lemma71C.segDrv (ρ ω) r)

/-- **The stop data exist.** -/
theorem exists_stopData (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (hseedS : SB2RelSeedAdmStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    Nonempty (SB2StopData HP I D) := by
  obtain ⟨a, ha, hac, ham, ha0, hae⟩ := Vg.exists_versionClock h13 hS3 HP I D
  have ha' : ∀ t, Measurable (a t) := fun t => (ha t).mono ((D.lineFiltC HP).le t) le_rfl
  obtain ⟨ρ, hρm, hρ⟩ := Vk.exists_drivenFamily h13 hS3 HP I D ha' hae
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull (ae_goodAt h13 hS3 hseedS HP I D hae hρ)
  have hgood : ∀ ω ∈ G ∩ D.event, GoodAt η ζ I a ρ ω := fun ω hω => hG ω hω.1 hω.2
  exact ⟨⟨a, ha, hac, ham, ha0, hae, ρ, hρm, hρ, G, hGm, hGnull, hgood,
    exists_segReading h13 hS3 HP I D ha hac ham hae hρ hGm hGnull fun ω hω =>
      ⟨(hgood ω hω).launch, (hgood ω hω).ent, (hgood ω hω).driven, (hgood ω hω).life⟩⟩⟩

namespace SB2StopData

variable {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀} (S : SB2StopData HP I D)

/-- The good event. -/
def Gs : Set Ω := S.G ∩ D.event

include HP in
theorem measurableSet_event : MeasurableSet D.event :=
  (D.lineFiltC HP).le 0 _ (D.marks_le_lineFiltC HP 0 _ (D.measurableSet_event HP))

theorem measurableSet_Gs : MeasurableSet S.Gs := S.hGm.inter (measurableSet_event (HP := HP))

theorem Gs_subset : S.Gs ⊆ D.event := inter_subset_right

theorem ae_mem_Gs : ∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ S.Gs := by
  filter_upwards [ae_iff.2 S.hGnull] with ω hω hD
  exact ⟨by simpa using hω, hD⟩

theorem good {ω : Ω} (hω : ω ∈ S.Gs) : GoodAt η ζ I S.a S.ρ ω := S.hgood ω hω

open Classical in
/-- The family, replaced by the vertical line off the good event. -/
def ρ' (ω : Ω) : ℝ → ℂ := if ω ∈ S.Gs then S.ρ ω else fun t : ℝ => (t : ℂ) * Complex.I

theorem ρ'_eq {ω : Ω} (hω : ω ∈ S.Gs) : S.ρ' ω = S.ρ ω := by simp [ρ', hω]

theorem isDrivenCurve_ρ' (ω : Ω) : IsDrivenCurve (S.ρ' ω) := by
  by_cases hω : ω ∈ S.Gs
  · rw [S.ρ'_eq hω]; exact (S.good hω).driven
  · simp only [ρ', hω, ↓reduceIte]; exact Lk.isDrivenCurve_vert

theorem measurable_ρ' (t : ℝ) (ht : 0 ≤ t) : Measurable fun ω => S.ρ' ω t := by
  classical
  have e : (fun ω => S.ρ' ω t) = fun ω => if ω ∈ S.Gs then S.ρ ω t else (t : ℂ) * Complex.I := by
    funext ω; by_cases hω : ω ∈ S.Gs <;> simp [ρ', hω]
  rw [e]
  exact Measurable.ite S.measurableSet_Gs (S.hρm t ht) measurable_const

/-- The canonical driver of the family. -/
def Wr : ℝ≥0 → Ω → ℝ := Supp8.GB6.CoordB.drivenDriver S.ρ'

theorem measurable_Wr (q : ℝ≥0) : Measurable (S.Wr q) :=
  Supp8.GB6.CoordB.measurable_drivenDriver S.isDrivenCurve_ρ' S.measurable_ρ' q

theorem continuousOn_Wr (ω : Ω) :
    ContinuousOn (S.Wr · ω) {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ' ω)} :=
  Supp8.GB6.CoordB.continuousOn_drivenDriver S.isDrivenCurve_ρ' ω

theorem Wr_zero (ω : Ω) : S.Wr 0 ω = 0 := Supp8.GB6.CoordB.drivenDriver_zero S.isDrivenCurve_ρ' ω

theorem isGeneratingTrace_Wr (ω : Ω) {T : ℝ≥0∞} (hT : T < Sec7.Lemma71C.capLife (S.ρ' ω)) :
    IsGeneratingTrace (S.Wr · ω) T (capTrace (S.ρ' ω)) :=
  Sec5.CrossRestart.isGeneratingTrace_congr_drive ((S.isDrivenCurve_ρ' ω).isGeneratingTrace hT)
    fun _ ht => Supp8.GB6.CoordB.drivenDriver_eq (lt_trans ht hT)

/-- The stops of the rule along the canonical driver. -/
def Vstop (m : ℕ) (ω : Ω) : ℝ≥0∞ := stopRule m (sb2Rec I ω, fun s => S.Wr s ω)

include HP D in
theorem measurable_rec : Measurable (sb2Rec I : Ω → RecData) :=
  (measurable_sb2Rec I).mono ((D.past_le_marks).trans (D.marks_le HP)) le_rfl

theorem measurable_path_Wr : Measurable fun ω => fun s => S.Wr s ω :=
  measurable_pi_iff.2 fun s => S.measurable_Wr s

theorem measurable_Vstop (m : ℕ) : Measurable (S.Vstop m) :=
  (measurable_stopRule m).comp ((measurable_rec (HP := HP) (D := D)).prodMk S.measurable_path_Wr)

/-- **The stops along a good sample** (`sb2_sample`). -/
theorem sample {ω : Ω} (hω : ω ∈ S.Gs) (m : ℕ) :
    0 < S.Vstop m ω ∧ S.Vstop m ω < Sec7.Lemma71C.capLife (S.ρ ω) ∧ S.Vstop m ω ≠ ⊤ ∧
      (∀ n, annRules gaugeRead m n (sb2Rec I ω, fun s => S.Wr s ω) < S.Vstop m ω) ∧
      ⨆ n, annRules gaugeRead m n (sb2Rec I ω, fun s => S.Wr s ω) = S.Vstop m ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.Vstop m ω →
        capTrace (S.ρ ω) t ∉ badSet (cellXL κ ψ I.word (angleWordType κ ψ (I.word ω)) ω)
          (cellXR κ ψ I.word (angleWordType κ ψ (I.word ω)) ω) (typedRhoL (angleWordType κ ψ (I.word ω)))
          (typedRhoR (angleWordType κ ψ (I.word ω))) := by
  have hg := S.good hω
  have hρω := S.ρ'_eq hω
  have hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife (S.ρ ω) → IsGeneratingTrace (S.Wr · ω) T (capTrace (S.ρ ω)) :=
    fun T hT => by have := S.isGeneratingTrace_Wr ω (T := T) (by rw [hρω]; exact hT); rwa [hρω] at this
  have hWrc : ContinuousOn (S.Wr · ω) {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ ω)} := by
    have := S.continuousOn_Wr ω; rwa [hρω] at this
  exact sb2_sample I hg.ent hg.fam1 hg.fam2 hg.driven hg.life hgen hWrc (S.Wr_zero ω) (S.hac ω) (S.ham ω)
    hg.clock hg.c0 hg.mono hg.inv hg.chart hg.cont hg.trans hg.tip hg.avoid hg.cover rfl hg.seed m

open Classical in
/-- **The driver frozen at the `m`-th stop** (`0` off the good event). -/
def W (m : ℕ) (q : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ S.Gs then S.Wr (min q (S.Vstop m ω).toNNReal) ω else 0

theorem W_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) (q : ℝ≥0) :
    S.W m q ω = S.Wr (min q (S.Vstop m ω).toNNReal) ω := by simp [W, hω]

theorem W_of_notMem {m : ℕ} {ω : Ω} (hω : ω ∉ S.Gs) (_q : ℝ≥0) : S.W m _q ω = 0 := by simp [W, hω]

theorem Vstop_toNNReal_lt {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) :
    ((S.Vstop m ω).toNNReal : ℝ≥0∞) < Sec7.Lemma71C.capLife (S.ρ' ω) := by
  rw [ENNReal.coe_toNNReal (S.sample hω m).2.2.1, S.ρ'_eq hω]; exact (S.sample hω m).2.1

theorem W_zero (m : ℕ) (ω : Ω) : S.W m 0 ω = 0 := by
  by_cases hω : ω ∈ S.Gs
  · rw [S.W_of_mem hω, zero_min, S.Wr_zero]
  · exact S.W_of_notMem hω 0

theorem continuous_W (m : ℕ) (ω : Ω) : Continuous (S.W m · ω) := by
  by_cases hω : ω ∈ S.Gs
  · have e : (S.W m · ω) = fun q => S.Wr (min q (S.Vstop m ω).toNNReal) ω := funext (S.W_of_mem hω)
    rw [e]
    exact (S.continuousOn_Wr ω).comp_continuous (continuous_id.min continuous_const)
      fun q => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt (S.Vstop_toNNReal_lt hω)
  · have e : (S.W m · ω) = fun _ => 0 := funext (S.W_of_notMem hω)
    rw [e]; exact continuous_const

theorem W_eq_Wr {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ S.Vstop m ω) :
    S.W m q ω = S.Wr q ω := by
  rw [S.W_of_mem hω, min_eq_left]
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (S.sample hω m).2.2.1]; exact hq

/-- The rule stops of the frozen drivers. -/
def V (m : ℕ) (ω : Ω) : ℝ≥0∞ := stopRule m (sb2Rec I ω, fun s => S.W m s ω)

theorem V_eq {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) : S.V m ω = S.Vstop m ω :=
  isPathRule_stopRule m _ _ _ fun _ hq => (S.W_eq_Wr hω hq).symm

theorem measurable_W (m : ℕ) (q : ℝ≥0) : Measurable (S.W m q) := by
  obtain ⟨Y, hYm, hYoff, hYon⟩ := exists_frozen_reading (𝒢 := mΩ) (Eg := S.Gs) (τ := fun _ => ⊤)
    (Wr := S.Wr) (rec := sb2Rec I) (R := stopRule m) S.measurableSet_Gs measurable_const
    (fun r => (S.measurable_Wr r).indicator (S.measurableSet_Gs.inter (measurableSet_lt measurable_const
      measurable_const))) (measurable_rec (HP := HP) (D := D)) (measurable_stopRule m) (isPathRule_stopRule m)
    (U := fun ω => Sec7.Lemma71C.capLife (S.ρ' ω)) (fun ω _ => S.continuousOn_Wr ω)
    (fun ω hω => by rw [S.ρ'_eq hω]; exact (S.sample hω m).2.1) (fun ω _ => S.Wr_zero ω) q
  have e : S.W m q = Y := by
    funext ω
    by_cases hω : ω ∈ S.Gs
    · rw [S.W_of_mem hω, hYon ω hω le_top]; rfl
    · rw [S.W_of_notMem hω, hYoff ω hω]
  rw [e]; exact hYm

theorem measurable_path_W (m : ℕ) : Measurable fun ω => fun s => S.W m s ω :=
  measurable_pi_iff.2 fun s => S.measurable_W m s

theorem measurable_V (m : ℕ) : Measurable (S.V m) :=
  (measurable_stopRule m).comp ((measurable_rec (HP := HP) (D := D)).prodMk (S.measurable_path_W m))

end SB2StopData

end

end InteractingSLE.Theorem14.SB.Vs
