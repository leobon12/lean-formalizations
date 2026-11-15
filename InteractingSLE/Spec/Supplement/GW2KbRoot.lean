/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbNil
import InteractingSLE.Spec.Supplement.GW2LaterChain

/-!
# Claim(k)'s base (GEOM2 round 12): the root piece's union mean at `P`

Packet PROVE-GW2-GEOM2, round 12. The stage-start union of the history `l = []` is the retained counterflow hull
together with the ROOT piece up to its end `T` (`schedUnionS_nil_eq`). The root piece is the piece of index `0`: its
conditional law given the empty past is `P`, its launch chart is `Chart.id.recenter 0` (root `0`), and the launch
datum is Theorem 1.3's (`Wk = W'`, `ℓ = id`). STAGEMEAN's abstract per-sample assembly `GW2Omx.kernel_launch_mean`
(here with the counterflow word given, `kernel_launch_meanW`) applies at `ν = P` with RELDET's `P`-level kernel of the
union (`GW2Omx.exists_kernel_union_mean` at `l = []`, `t = 0`).

* `bhe_angle_sub` (`uθ − u₀ = θχ`; STAGEMEAN's `GW2Psm.sub_eq_of_bhe_angle`, re-proved because that file has not
  landed);
* **`ae_root_union_form`**: a local-set mean `g` of the stage-start union of `l = []` such that, almost surely, on
  success, with an interior counterflow tip at `s` and no contact before `T`, every harmonic representative of `g` off
  the union is GW2's union form `UnionFormAt` of the root piece at `(s, T)` in the word `cw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Kb

open GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart

/-- **`uθ − u₀ = θχ`** on `ℍ` (STAGEMEAN's `GW2Psm.sub_eq_of_bhe_angle`). -/
theorem bhe_angle_sub {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ} {u' uθ : ℂ → ℝ} (hu' : IsBoundedHarmonicExtension b J u')
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uθ) :
    ∀ z ∈ H, uθ z - u' z = θ * chiC κ := by
  set S : Set ℝ := (J : Set ℝ) ∪ {0} ∪ forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0) with hS
  have hSf : S.Finite :=
    ((J.finite_toSet.union (Set.finite_singleton 0)).union (GW2Sdm.finite_forceJumpSet _ _))
  have h1 : IsBoundedHarmonicExtension (fun x => b x + θ * chiC κ) S (fun z => u' z + θ * chiC κ) :=
    Sec5.Aux61Win.IsBoundedHarmonicExtension.mono_set
      (Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu' (θ * chiC κ)) fun x hx => Or.inl (Or.inl hx)
  have h2 : IsBoundedHarmonicExtension (fun x => b x + θ * chiC κ) S uθ := by
    have h := Sec5.Aux61Win.IsBoundedHarmonicExtension.mono_set huθ (S' := S) fun x hx => Or.inr hx
    refine (Restart.isBoundedHarmonicExtension_congr (fun y hy => ?_) uθ).2 h
    have hyJ : y ∉ J := fun h => hy (Or.inl (Or.inl h))
    have hy0 : y ≠ 0 := fun h => hy (Or.inl (Or.inr h))
    rw [Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ b J θ 0 y, Sec4.forceBoundaryData_flowLine hκ hb hy0 hyJ]
    ring
  intro z hz
  have := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hSf h1 h2 hz
  simp only at this
  linarith

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The root piece's union mean at `P`** (root `0`, history `l = []`). -/
theorem ae_root_union_form (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) (hr0 : rootPt r.1 = 0)
    {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r [] a 0) (schedUnionS c r [] a 0) (centredField c.h u₀) c.P) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (schedUnionS c r [] a 0) (centredField c.h u₀) c.P g ∧
      (∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω) (H \ schedUnionS c r [] a 0 ω)) ∧
      ∃ (γ : Ω → ℝ≥0 → ℂ) (uθ : ℂ → ℝ),
        IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ c.b c.jumps 0 (rootEntry r.1).1)
          (flowLineRhoR c.κ c.b c.jumps 0 (rootEntry r.1).1) (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0))
          (forceJumpSet (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)) uθ ∧
        (∀ᵐ ω ∂c.P, c.ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => c.W t ω) ⊤ (γ ω)) ∧
        ∀ᵐ ω ∂c.P, ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < (futFam c r [] a 0 ω).2 → γ ω c.s ∈ H →
          0 < historyTime c r [] →
          ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (GW2aSingle.chosenTrace
              (fun t ω => (futFam c r [] a 0 ω).1 t) (fun ω => (futFam c r [] a 0 ω).2) ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 c.s) →
          ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ schedUnionS c r [] a 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ schedUnionS c r [] a 0 ω →
              g ω φ = ∫ z, w z * φ z) →
            UnionFormAt c.κ (rootEntry r.1).1 c.b c.jumps cw c.W c.ζ (fun t ω => (futFam c r [] a 0 ω).1 t) uθ
              ω c.s (historyTime c r []) w (H \ schedUnionS c r [] a 0 ω) := by
  classical
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  obtain ⟨g, 𝓜, hg, -, -, -, hB𝓜, -, hMh, hkP, -⟩ := exists_kernel_union_mean c r [] a hu₀.1 hh0 0 hloc₀
  have hBc : ∀ ω, schedUnionS c r [] a 0 ω ⊆ H ∧ IsOpen (H \ schedUnionS c r [] a 0 ω) :=
    fun ω => schedUnionS_subset_isOpen c r [] a 0 ω
  have hmh : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω) (H \ schedUnionS c r [] a 0 ω) := by
    filter_upwards [hMh] with ω hω
    have h2 := LocalSets.IsHarmonicDistOn.sub' (hBc ω).2 hω
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu₀.1) sdiff_subset)
    simpa only [add_sub_cancel_right] using h2
  refine ⟨g, hg, hmh, ?_⟩
  set x := rootPt r.1 with hx
  set L := futureProgram c r [] a with hL
  set spec := futSpec c r [] a with hspec
  set E := futFam c r [] a with hEdef
  set T : ℝ≥0 := historyTime c r [] with hT
  set B := schedUnionS c r [] a 0 with hB
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  -- the root piece is a flow line of `h`
  have hfl0 := hS.isFlowLineDriver_first_root c.hκ c.hb c.hh (futSpec_nil_prog c r a)
  have hx0 : spec.1 = 0 := hr0
  have hfl : IsFlowLineDriver c.κ c.b c.jumps (rootEntry r.1).1 c.P c.h (fun t ω => (E 0 ω).1 t)
      (fun ω => (E 0 ω).2) := by
    have e1 : (fun y => c.b (y + spec.1)) = c.b := funext fun y => by rw [hx0, add_zero]
    have e2 : c.jumps.image (· - spec.1) = c.jumps := by
      rw [hx0]
      simp
    have e3 : (fun ω => Exist.flowField spec.1 0 (c.h ω)) = c.h :=
      funext fun ω => by rw [hx0, Sec7.Prop74B.flowField_zero_zero]
    rw [e1, e2, e3] at hfl0
    exact hfl0
  have hcfreg := GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ
  have huθ := LocalExt.isBoundedHarmonicExtension_bheAt c.κ (flowLineRhoL c.κ c.b c.jumps 0 (rootEntry r.1).1)
    (flowLineRhoR c.κ c.b c.jumps 0 (rootEntry r.1).1) (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)
  obtain ⟨-, -, -, -, -, -, γ0, -, -, -, -, hcomp0, -⟩ := counterflow_packW h13 c.hκ c.hκ4 c.hb c.hh hcw c.hζ
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL c.κ c.b c.jumps 0 (rootEntry r.1).1)
    (flowLineRhoR c.κ c.b c.jumps 0 (rootEntry r.1).1) 0 (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)
  · -- the root piece dies at once: nothing to prove
    have hfl'' := hfl
    obtain ⟨Xθ', 𝓕', VL', VR', B', htr'', hC⟩ := hfl''
    have hz := Coupling.ae_zeta_eq_zero_of_threshold hC.1 hseed
    refine ⟨γ0, _, huθ, hcomp0, ?_⟩
    filter_upwards [hz] with ω hzω htζ
    rw [hzω] at htζ
    exact absurd htζ not_lt_zero
  -- RELDET's kernel for the centred field
  have hk : ∀ ψ : TestOn upperHalfPlaneOpens,
      c.P[fun ω => Complex.exp (Complex.I * (centredField c.h u₀ ω ψ : ℂ)) | 𝓜.1] =ᵐ[c.P]
        fun ω => rangeKerCF (g ω) (H \ B ω) ψ := by
    intro ψ
    set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u₀ with hSdef
    have hsplit : (fun ω => Complex.exp (Complex.I * (centredField c.h u₀ ω ψ : ℂ))) =
        Complex.exp (-(Complex.I * (S ψ : ℂ))) • fun ω => Complex.exp (Complex.I * (c.h ω ψ : ℂ)) := by
      funext ω
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
      simp only [centredField, sub_apply, hSdef]
      push_cast
      ring_nf
    rw [hsplit]
    filter_upwards [condExp_smul (Complex.exp (-(Complex.I * (S ψ : ℂ))))
      (fun ω => Complex.exp (Complex.I * (c.h ω ψ : ℂ))) 𝓜.1 (μ := c.P), hkP ψ] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, rangeKerCF, rangeKerCF, ← Complex.exp_add, add_apply]
    congr 1
    push_cast
    ring
  have hLl : IsHistoryAvoidanceLocal 𝓜.1 B (centredField c.h u₀) c.P :=
    WFS.isHistoryAvoidanceLocal_of_retainedKernel 𝓜.2 (measurable_centredField c.hh.1 u₀) hB𝓜
      (Eventually.of_forall hBc) hmh hk
  -- the launch datum at the root (Theorem 1.3: the counterflow itself, `ℓ = id`)
  have hd : ∀ᵐ ω ∂c.P, c.ζ ω = ⊤ ∧ Continuous ((fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω) ∧
      StrictMono ((fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω) ∧
      range ((fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω) =
        {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => c.W s ω) {(0 : ℂ)}} ∧
      ∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter 0).trans infinitySourceChart).tipAt (fun s => c.W s ω) q z ↔
        infinitySourceChart.tipAt (fun s => c.W s ω) ((fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω q) z := by
    filter_upwards [hcfreg, c.hζ] with ω hω hζω
    obtain ⟨γ', hγ', hc, h0, -⟩ := hω
    refine ⟨hζω, continuous_id, strictMono_id, ?_, fun q z => GW2Later.tipAt_recenter_zero_trans⟩
    rw [firstTipTime_zero_eq_top hγ' hc h0, range_id]
    ext t
    simp only [mem_univ, mem_ofPred_eq, ENNReal.coe_lt_top]
  have hW' : ∀ᵐ ω ∂c.P, Continuous (fun t => c.W t ω) ∧ c.W 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => c.W t ω) ⊤ γ' := by
    filter_upwards [hcfreg] with ω hω
    obtain ⟨γ', hγ', hc, h0, -⟩ := hω
    exact ⟨hc, h0, γ', hγ'⟩
  have hα := (GW2aSingle.ae_chosenTrace h13 c.hκ hfl).mono fun _ h => h.1
  have hfut := Gm.ae_futureJoined_trace h13 c r
  have hpr := hR.ae_pieceRegular
  -- the two localization hypotheses, with `I = univ` (off success the union is `ℍ`)
  have hsub : ∀ᵐ ω ∂c.P, ω ∈ (univ : Set Ω) → ∃ t₀ : ℝ≥0, (fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω t₀ = c.s ∧
      ∀ v ≤ t₀, ∀ u ≤ T, (u : ℝ≥0∞) < (E 0 ω).2 →
        Supp8.Q3Rel.invHull (fun q : ℝ => c.W q.toNNReal ω) (v : ℝ) ∪
          fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) (u : ℝ) ⊆ B ω := by
    filter_upwards [hcfreg, c.hζ, hfut, hpr] with ω hcfω hζω hfutω hprω _
    obtain ⟨γ', hγ', hWc, hW0, -⟩ := hcfω
    refine ⟨c.s, rfl, fun v hv u hu huζ => ?_⟩
    by_cases hold : oldSuccess c r [] ω
    · obtain ⟨hgood, -⟩ := hfutω [] a hold
      have hc0 := stopDrv_cont_of_oldSuccess c r [] a hold hprω 0 (by simp [curIdx])
      rw [hB, schedUnionS_nil_eq c r a hold hgood hc0 (hreg 0 ω) hW0 hWc.continuousOn
        (by rw [hζω]; exact ENNReal.coe_lt_top)]
      exact union_subset_union (GW2Omx.invHull_mono (by exact_mod_cast hv))
        (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hu))
    · have hBH : B ω = H := by
        rw [hB]
        unfold schedUnionS
        simp only [hold, ↓reduceIte]
      rw [hBH]
      refine union_subset (GW2Shr.invHull_subset_H (hWc.comp continuous_real_toNNReal) v.coe_nonneg) ?_
      exact Exist.fwdHull_subset_H u.coe_nonneg
  have heq : ∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, (fun _ : Ω => (id : ℝ≥0 → ℝ≥0)) ω t₀ = c.s → (T : ℝ≥0∞) < (E 0 ω).2 →
      ω ∈ (univ : Set Ω) ∧ B ω = Supp8.Q3Rel.invHull (fun q : ℝ => c.W q.toNNReal ω) (t₀ : ℝ) ∪
        fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) (T : ℝ) := by
    filter_upwards [hcfreg, c.hζ, hfut, hpr] with ω hcfω hζω hfutω hprω t₀ ht₀ hTζ
    obtain ⟨γ', hγ', hWc, hW0, -⟩ := hcfω
    have hold : oldSuccess c r [] ω := (oldSuccess_nil_iff c r a ω).2 hTζ
    obtain ⟨hgood, -⟩ := hfutω [] a hold
    have hc0 := stopDrv_cont_of_oldSuccess c r [] a hold hprω 0 (by simp [curIdx])
    have ht : t₀ = c.s := ht₀
    refine ⟨mem_univ ω, ?_⟩
    rw [ht, hB, schedUnionS_nil_eq c r a hold hgood hc0 (hreg 0 ω) hW0 hWc.continuousOn
      (by rw [hζω]; exact ENNReal.coe_lt_top)]
  have hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets c.P] (univ : Set Ω) := MeasurableSet.univ
  obtain ⟨Xθ, γ, -, hcomp, hmain⟩ := kernel_launch_meanW h12 h13 c.hκ c.hκ4 c.hb c.hh hu₀ hcw hW'
    (GW1P.hasProperBdryExt_recenter_id 0) hd c.s hfl hα hseed huθ 𝓜 hB𝓜 hBc hLl hmh hk hI T hsub heq
  refine ⟨γ, _, huθ, hcomp, ?_⟩
  filter_upwards [hmain] with ω h hTζ hγH hpos hfc w hw hpair
  exact h c.s rfl hTζ hγH hpos hfc w hw hpair

end InteractingSLE.Theorem14.GW2Kb
