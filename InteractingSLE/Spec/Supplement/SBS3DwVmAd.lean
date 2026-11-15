/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VmAd
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkAsm
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink

/-!
# Successor of `SB2VmAd` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VmAd` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_monoLiftLe`;
* `exists_goodReadingLe`;
* `stronglyAdapted_frozenLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vm

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The lift's capacity clock is monotone before the remaining life**, almost surely at a launch on the entrance
event. -/
theorem ae_monoLiftLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ x y : ℝ, 0 ≤ x → x ≤ y →
        (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + y.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
        capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) x ≤
          capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) y := by
  filter_upwards [Vd.ae_clockDataLe h13 hS3 HP] with ω hcd hl hT x y hx hxy hyζ
  obtain ⟨-, hloc⟩ := hcd hl hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hy : 0 ≤ y := hx.trans hxy
  have hm := (hloc (TL.toNNReal + y.toNNReal) le_self_add hyζ).2
  have key : ∀ z, z ∈ Icc (0 : ℝ) y →
      z ∈ Icc (0 : ℝ) (((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ) - (TL.toNNReal : ℝ)) := fun z hz =>
    ⟨hz.1, by rw [NNReal.coe_add, Real.coe_toNNReal _ hy]; linarith [hz.2]⟩
  exact hm (key x ⟨hx, hxy⟩) (key y ⟨hy, le_rfl⟩) hxy

/-- **The frozen driver read from the completed line filtration**: a good event `Eg ⊆ G ∩ D.event`, in every
`D.lineFiltC t`, containing almost every point of `D.event`, on which `W q` is measurable for `D.lineFiltC t` on
`{q ≤ a t}`. -/
theorem exists_goodReadingLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
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
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vk.relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q) :
    ∃ Eg : Set Ω, (∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg) ∧ Eg ⊆ G ∩ D.event ∧
      (∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ Eg) ∧
      ∀ q t : ℝ≥0, Measurable[D.lineFiltC HP t] ((Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}).indicator (W q)) := by
  classical
  obtain ⟨G', hG'm, hG'null, hG'⟩ := Vi.exists_measurable_absLiftLe h13 hS3 HP I D
  obtain ⟨Gx, hGxm, hGxnull, hGx⟩ := Vf.exists_measurable_conull (hae.and (hρ.and
    ((Vi.ae_absLift_goodLe h13 hS3 HP I D).and (ae_monoLiftLe h13 hS3 HP))))
  set Eg := G ∩ G' ∩ Gx ∩ D.event with hEgdef
  have hEv : MeasurableSet[D.marks] D.event := D.measurableSet_event HP
  have hEg : ∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg := fun t =>
    (((Vf.measurableSet_cmpl_of_conull (𝒢 := D.absMarks (t : ℝ≥0∞)) hGm hGnull).inter
      (Vf.measurableSet_cmpl_of_conull (𝒢 := D.absMarks (t : ℝ≥0∞)) hG'm hG'null)).inter
      (Vf.measurableSet_cmpl_of_conull (𝒢 := D.absMarks (t : ℝ≥0∞)) hGxm hGxnull)).inter
      (D.marks_le_lineFiltC HP t _ hEv)
  -- the facts on the good event
  have hfact : ∀ ω ∈ Eg, ω ∈ G ∩ D.event ∧ ω ∈ G' ∩ D.event := fun ω hω =>
    ⟨⟨hω.1.1.1, hω.2⟩, ⟨hω.1.1.2, hω.2⟩⟩
  -- the clock is below the lifetime of the family
  have hlife : ∀ ω ∈ Eg, ∀ t, a t ω ≤ Sec7.Lemma71C.capLife (ρ ω) := fun ω hω t => by
    obtain ⟨hl, hT, -, hcl, -⟩ := hWon ω (hfact ω hω).1
    rw [(hGx ω hω.1.2).1 hl hT t, hcl]
    exact clockOf_le_relSup _ _ _ t
  -- the prefix events
  have hpre : ∀ (t r : ℝ≥0) (r'' : ℝ), 0 ≤ r'' → r'' ≤ r → ∀ (n : ℕ) (kk : ℤ × ℤ),
      MeasurableSet[D.lineFiltC HP t] ((Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}) ∩
        {ω | (Restart.dyadicSquare n kk ∩ ρ ω '' Icc 0 (capInv (ρ ω) r'')).Nonempty}) := by
    intro t r r'' hr0 hrr n kk
    set Q := Restart.dyadicSquare n kk with hQ
    set Rd : ℚ≥0 → Ω → ℂ := fun q ω => if ω ∈ G' ∩ D.event ∩ {ω | (((q : ℝ≥0) : ℝ≥0∞)) < ζ ω} then
      Vi.absLift κ b jumps E k u η ζ ω q else 0 with hRd
    have hRdm : ∀ q : ℚ≥0, Measurable[D.lineFiltC HP q] (Rd q) := fun q => hG' q
    have hiff : ∀ ω ∈ Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}, (Q ∩ ρ ω '' Icc 0 (capInv (ρ ω) r'')).Nonempty ↔
        ∀ m : ℕ, ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ a q ω ≤ ENNReal.ofReal (r'' + 1 / ((m : ℝ) + 1)) ∧
          infDist (Rd q ω) Q < 1 / ((m : ℝ) + 1) := by
      intro ω hω
      obtain ⟨hl, hT, hd, hcl, -⟩ := hWon ω (hfact ω hω.1).1
      obtain ⟨hclock, hρω, hgood, hmono⟩ := hGx ω hω.1.1.2
      have hclock' := hclock hl hT
      obtain ⟨h1, h2⟩ := hρω hl hT
      have hrt : ENNReal.ofReal r'' < a t ω :=
        lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hrr) hω.2
      have hrt' : ENNReal.ofReal r'' < Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t := by rw [← hclock']; exact hrt
      have himg : ρ ω '' Icc 0 (capInv (ρ ω) r'') =
          Vi.absLift κ b jumps E k u η ζ ω '' {T | a T ω ≤ ENNReal.ofReal r''} := by
        rw [image_capInv_eq hd hT h1 h2 (hmono hl hT) hr0 hrt' (by rw [← hclock']; exact hlife ω hω.1 t)]
        congr 1
        ext T
        simp only [mem_ofPred_eq, hclock' T]
      rw [himg]
      refine nonempty_inter_image_iff (Z := ζ ω) (Restart.isClosed_dyadicSquare n kk)
        (Sec7.Lemma71E.nonempty_dyadicSquare n kk) (hac ω) (ham ω) hrt (fun T hTt => ?_)
        (fun T hTζ => ((hgood hl hT) T hTζ).1) (fun q hq => ?_)
      · by_contra hc
        rw [not_lt] at hc
        have := clockOf_le_of_le (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal t hc
        rw [← hclock', ← hclock'] at this
        exact absurd hTt (not_lt.2 this)
      · have hmem : ω ∈ G' ∩ D.event ∩ {ω | (((q : ℝ≥0) : ℝ≥0∞)) < ζ ω} := ⟨(hfact ω hω.1).2, hq⟩
        simp only [hRd, hmem, ↓reduceIte]
    have e : (Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}) ∩ {ω | (Q ∩ ρ ω '' Icc 0 (capInv (ρ ω) r'')).Nonempty} =
        (Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}) ∩ ⋂ m : ℕ, ⋃ q : ℚ≥0, ⋃ (_ : (q : ℝ≥0) ≤ t),
          ({ω | a q ω ≤ ENNReal.ofReal (r'' + 1 / ((m : ℝ) + 1))} ∩
            {ω | infDist (Rd q ω) Q < 1 / ((m : ℝ) + 1)}) := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨hω, hne⟩
        exact ⟨hω, fun m => by
          obtain ⟨q, h1, h2, h3⟩ := (hiff ω hω).1 hne m
          exact ⟨q, h1, h2, h3⟩⟩
      · rintro ⟨hω, hm⟩
        exact ⟨hω, (hiff ω hω).2 fun m => by
          obtain ⟨q, h1, h2, h3⟩ := hm m
          exact ⟨q, h1, h2, h3⟩⟩
    rw [e]
    refine ((hEg t).inter (measurableSet_lt measurable_const (ha t))).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
    have hle : D.lineFiltC HP q ≤ D.lineFiltC HP t := (D.lineFiltC HP).mono hq
    exact (hle _ (measurableSet_le (ha q) measurable_const)).inter
      (hle _ (measurableSet_lt ((continuous_infDist_pt Q).measurable.comp (hRdm q)) measurable_const))
  -- the canonical driver below the clock is measurable for the completed line filtration
  have hZm : ∀ t r : ℝ≥0, Measurable[D.lineFiltC HP t]
      ((Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}).indicator fun ω => segDrv (ρ ω) r) := fun t r =>
    @measurable_indicator_segDrv_of_isDrivenCurve Ω (D.lineFiltC HP t) ρ r r.2 _
      (fun ω hω => (hWon ω (hfact ω hω.1).1).2.2.1)
      ((hEg t).inter (measurableSet_lt measurable_const (ha t)))
      (fun ω hω => by
        rw [ENNReal.ofReal_coe_nnreal]
        exact lt_of_lt_of_le hω.2 (hlife ω hω.1 t))
      (fun r'' hr0 hrr n kk => hpre t r r'' hr0 hrr n kk)
  -- the readings
  set Y : ℝ≥0 → ℝ≥0 → Ω → ℝ := fun q t => (Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}).indicator (W q) with hYdef
  have hY : ∀ q t, Measurable[D.lineFiltC HP t] (Y q t) := by
    intro q t
    have hC : MeasurableSet[D.lineFiltC HP t] (Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) :=
      (hEg t).inter (measurableSet_le measurable_const (ha t))
    rcases (zero_le : (0 : ℝ≥0) ≤ q).eq_or_lt with hq | hq
    · have e : Y q t = fun _ => 0 := by
        funext ω
        have hW0' : W q = fun _ => 0 := funext fun ω' => by rw [← hq]; exact hW0 ω'
        show (Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}).indicator (W q) ω = 0
        rw [hW0', Set.indicator_apply]
        split_ifs <;> rfl
      rw [e]; exact measurable_const
    · set rn : ℕ → ℝ≥0 := fun n => q * (1 - (1 / 2 : ℝ≥0) ^ (n + 1)) with hrn
      have hrnq : ∀ n, rn n < q := fun n =>
        mul_lt_of_lt_one_right hq (tsub_lt_self one_pos (pow_pos (by norm_num) _))
      have hrnt : Tendsto rn atTop (𝓝 q) := (Vk.tendsto_frac_nhdsLT hq).mono_right nhdsWithin_le_nhds
      set g : ℕ → Ω → ℝ := fun n => (Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}).indicator
        ((Eg ∩ {ω | (rn n : ℝ≥0∞) < a t ω}).indicator fun ω => segDrv (ρ ω) (rn n)) with hgdef
      have hgm : ∀ n, Measurable[D.lineFiltC HP t] (g n) := fun n => (hZm t (rn n)).indicator hC
      refine @measurable_of_tendsto_metrizable Ω ℝ (D.lineFiltC HP t) _ _ _ _ g _ hgm
        (tendsto_pi_nhds.2 fun ω => ?_)
      by_cases hω : ω ∈ Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}
      · have hval : ∀ n, g n ω = W (rn n) ω := fun n => by
          have hmem : ω ∈ Eg ∩ {ω | (rn n : ℝ≥0∞) < a t ω} :=
            ⟨hω.1, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (hrnq n)) hω.2⟩
          simp only [hgdef, indicator_of_mem hω, indicator_of_mem hmem]
          obtain ⟨-, -, -, hcl, hseg⟩ := hWon ω (hfact ω hω.1).1
          rw [hseg (rn n) (by rw [← hcl]; exact lt_of_lt_of_le hmem.2 (hlife ω hω.1 t))]
          rfl
        simp only [hYdef, indicator_of_mem hω]
        exact ((hWc ω).tendsto q).comp hrnt |>.congr fun n => (hval n).symm
      · simp only [hgdef, hYdef, indicator_of_notMem hω]
        exact tendsto_const_nhds
  refine ⟨Eg, hEg, fun ω hω => (hfact ω hω).1, ?_, hY⟩
  filter_upwards [ae_iff.2 hGnull, ae_iff.2 hG'null, ae_iff.2 hGxnull] with ω hωG hωG' hωGx hev
  exact ⟨⟨⟨hωG, hωG'⟩, hωGx⟩, hev⟩

/-- **The frozen driver is adapted to the time-changed completed line filtration.** -/
theorem stronglyAdapted_frozenLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
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
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vk.relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q) :
    StronglyAdapted (Tc.tcFilt (D.lineFiltC HP) a ha) W := by
  classical
  obtain ⟨Eg, -, hEgsub, hEgae, hY⟩ := exists_goodReadingLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0
    hWc hWoff hWon
  refine Vf.stronglyAdapted_tcFilt_of_ae_read (fun t s s' hs hs' he => Vf.lineFiltC_closed D HP t hs hs' he)
    hWm (fun q t => (Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}).indicator (W q)) hY fun q t => ?_
  filter_upwards [hEgae] with ω hω hqa
  by_cases hev : ω ∈ D.event
  · rw [indicator_of_mem (show ω ∈ Eg ∩ {ω | (q : ℝ≥0∞) ≤ a t ω} from ⟨hω hev, hqa⟩)]
  · rw [indicator_of_notMem (fun h' => hev (hEgsub h'.1).2)]
    exact hWoff q ω fun h' => hev h'.2

end

end InteractingSLE.Theorem14.SB.Vm
