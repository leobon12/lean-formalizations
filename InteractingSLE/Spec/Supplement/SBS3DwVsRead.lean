/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsRead
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
import InteractingSLE.Spec.Supplement.SBS3DwVmAd
import InteractingSLE.Spec.Supplement.SBS3DwVmSafe
import InteractingSLE.Spec.Supplement.SBS3DwVnEnd
import InteractingSLE.Spec.Supplement.SBS3DwVnTr
import InteractingSLE.Spec.Supplement.SBS3DwVrStopAe

/-!
# Successor of `SB2VsRead` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VsRead` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `exists_segReadingLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C Vm

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The canonical driver read from the completed line filtration** (`Vm.exists_goodReadingLe` without a global
driver): a good event `Eg ⊆ G ∩ D.event`, in every `D.lineFiltC t`, containing almost every point of `D.event`, below
whose clock the canonical driver of the family at every capacity `r < a t` is measurable for `D.lineFiltC t`. -/
theorem exists_segReadingLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
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
    {G : Set Ω} (hGm : MeasurableSet G) (hGnull : P Gᶜ = 0)
    (hWon : ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
      IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = Vk.relLife κ b jumps E k u η ζ ω) :
    ∃ Eg : Set Ω, (∀ t : ℝ≥0, MeasurableSet[D.lineFiltC HP t] Eg) ∧ Eg ⊆ G ∩ D.event ∧
      (∀ᵐ ω ∂P, ω ∈ D.event → ω ∈ Eg) ∧
      (∀ ω ∈ Eg, ∀ t, a t ω ≤ Sec7.Lemma71C.capLife (ρ ω)) ∧
      ∀ t r : ℝ≥0, Measurable[D.lineFiltC HP t]
        ((Eg ∩ {ω | (r : ℝ≥0∞) < a t ω}).indicator fun ω => segDrv (ρ ω) r) := by
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
    obtain ⟨hl, hT, -, hcl⟩ := hWon ω (hfact ω hω).1
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
      obtain ⟨hl, hT, hd, hcl⟩ := hWon ω (hfact ω hω.1).1
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
  refine ⟨Eg, hEg, fun ω hω => (hfact ω hω).1, ?_, hlife, hZm⟩
  filter_upwards [ae_iff.2 hGnull, ae_iff.2 hG'null, ae_iff.2 hGxnull] with ω hωG hωG' hωGx hev
  exact ⟨⟨⟨hωG, hωG'⟩, hωGx⟩, hev⟩

end

end InteractingSLE.Theorem14.SB.Vs
