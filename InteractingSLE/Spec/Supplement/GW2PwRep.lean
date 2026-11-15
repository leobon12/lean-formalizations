/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmClaimS
import InteractingSLE.Spec.Supplement.GW2PsmPairI

/-!
# Claim(k) at almost every sample: the explicit stage-start mean represents every local-set mean of `B 0`

Packet PROVE-GW2-STAGEMEAN, R122 round (D46). Claim(k) (`GW2Psm.ClaimAt`) is a pairing statement for each test
function. At almost every live sample it holds for all test functions at once, and the explicit stage-start mean
`stgMeanR … 0` is harmonic off `B 0` (root `0`):

* **`ae_stage_rep0`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Pw

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe GW2Psm

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- **Claim(k) at almost every live sample, for all test functions at once** (root `0`). -/
theorem ae_stage_rep0 (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (w : WordType) (hclaim : ClaimAt c r l a GT hA ch w) {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hg₀ : IsLocalSetMean (GW2Sdi.schedUnionS c r l a 0) (centredField c.h ch.u₀) c.P g₀) :
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      InnerProductSpace.HarmonicOnNhd (stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
          ch.u₀ ch.σa) (H \ GW2Sdi.schedUnionS c r l a 0 ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l a 0 ω →
        g₀ ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
          ch.u₀ ch.σa z * φ z := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  set I := GW2Rv.schedInstSX c r l a GT hA ch with hIdef
  have hB : I.B 0 = GW2Sdi.schedUnionS c r l a 0 := funext fun ω => schedUnionSX_eq_schedUnionS c r l a hr0 0 ω
  have hv := hA.1.1
  have hρ := hA.1.2.choose_spec
  set G : Set Ω := liveEvRec c.κ w ch.β I.E (I.srecX c r l (rootPt r.1)) with hGdef
  set m : Ω → ℂ → ℝ := fun ω => stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1))
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
          (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
          (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω)) ω 0)
      ch.u₀ ch.σa with hm
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  -- the explicit stage-start mean is harmonic off `B 0` on the live event
  have hmh : ∀ᵐ ω ∂c.P, ω ∈ G → InnerProductSpace.HarmonicOnNhd (m ω) (H \ GW2Sdi.schedUnionS c r l a 0 ω) := by
    filter_upwards [hEgood, hGT.2.2, ae_shape_root0 c r l a hr0 hs0 hGT.1 hv] with ω hEω hGTω hshapeω hωG
    obtain ⟨hgx, hlt⟩ := hEω hωG.1
    have hωGT : ω ∈ GT := hGTω.2 hgx
    have hsucc : oldSuccess c r l ω := (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).1 hωG.1.1.2
    have hRc : Continuous fun u => R u ω := hv.2.1 ω
    have hR0 : R 0 ω = 0 := hv.2.2.1 ω
    have hdc : Continuous fun q => I.drvX c (rootPt r.1) q ω := continuous_stgDrv hRc _
    have hd0 : I.drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
    have hU₀ := bhe_bheProc_typedX_zero (r := r) (l := l) I (rootPt r.1) w ω hdc hd0
    have hlt0 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + 0) ω) (V ω) <
        V ω := by rw [add_zero]; exact hlt
    have hsh0 := hshapeω hωGT hsucc 0 hlt0
    rw [hsh0, capA_zero]
    have hi := stgChart_inv_image (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) hRc hR0
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
    rw [add_zero] at hi
    rw [← hi]
    exact harmonicOnNhd_stgMeanR c.κ _ hRc hR0 _ le_rfl hU₀.1 hu₀.1 ch.σa
  -- the pairing for all test functions at once
  have hg₀' : IsLocalSetMean (I.B 0) (centredField c.h ch.u₀) c.P g₀ := by rw [hB]; exact hg₀
  have hBc := GW2Sdi.schedUnionS_subset_isOpen c r l a
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then GW2Sdi.schedUnionS c r l a 0 ω else H with hA'
  set m' : Ω → ℂ → ℝ := fun ω => if ω ∈ G then m ω else 0 with hm'
  have hφ' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ ⊆ H \ A' ω →
      g₀ ω φ = ∫ z, m' ω z * φ z := by
    intro φ
    filter_upwards [hclaim g₀ hg₀' φ, hEgood] with ω h1 hEω hsupp
    by_cases hω : ω ∈ G
    · simp only [hA', hω, ↓reduceIte] at hsupp
      simp only [hm', hω, ↓reduceIte]
      have hcap : (0 : ℝ≥0∞) < I.capX c (rootPt r.1) ω := by
        obtain ⟨-, hlt⟩ := hEω hω.1
        have hne : stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
          ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
        show (0 : ℝ≥0∞) < V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω).toNNReal : ℝ≥0∞)
        rw [ENNReal.coe_toNNReal hne]
        exact tsub_pos_of_lt hlt
      rw [hB] at h1
      exact h1 hω hcap hsupp
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self] at hsupp
      have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hsupp hz)
      have hφ0 : φ = 0 := by
        ext z
        exact h0 z
      rw [hφ0, map_zero]
      have e : (fun z => m' ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
        funext z
        rw [← hφ0, h0 z, mul_zero]
      rw [e, integral_zero]
  have hharm' : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g₀ ω) (H \ A' ω) := by
    filter_upwards [hg₀.2.1] with ω h
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using h
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact GW2Scl.isHarmonicDistOn_empty _
  have hopen' : ∀ᵐ ω ∂c.P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using (hBc 0 ω).2
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self, isOpen_empty]
  have hm'h : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m' ω) (H \ A' ω) := by
    filter_upwards [hmh] with ω hω'
    by_cases hω : ω ∈ G
    · simp only [hA', hm', hω, ↓reduceIte]
      exact hω' hω
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact fun z hz => absurd hz (notMem_empty z)
  filter_upwards [WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm'h hφ', hmh] with ω hω hmω hωG
  refine ⟨hmω hωG, fun φ hsupp => ?_⟩
  have h := hω φ (by simpa only [hA', hωG, ↓reduceIte] using hsupp)
  simpa only [hm', hωG, ↓reduceIte] using h

end InteractingSLE.Theorem14.GW2Pw
