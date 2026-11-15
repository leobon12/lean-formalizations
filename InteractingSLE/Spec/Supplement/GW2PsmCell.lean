/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmCapL

/-!
# GW2's open lines: the Claim(k) step on one cell (prefix version and prefix word type)

Packet PROVE-GW2-STAGEMEAN, R121 round. **`claim_cell`**: `ClaimAt` for the history `e :: l'` (current candidate
`a`, any announced version `(R, V)`, word type `w`) on a cell `E` of samples, from `ClaimAt` for the prefix `l'` at a
candidate `a'` of `e`'s angle (any announced version `(R', V')`, choice with GEOM2's word map, word type `w'`) and
(R1) (`PrefixLifeStatement`), given on `E`: the history's success, the prefix's live event with `clock'(δ) < cap'`,
the agreement of the two versions up to the history's stage start with `a₀' + q' = a₀`, and GEOM2's word recursion
`β (srec) = upW (θa χ) (stopWord (base word of the prefix, e.1, record of the entry))`.

Proof: `pair_instS` at the prefix (`t = δ`, restricted to `E`; life from (R1)), the explored identity
`eqOn_explored_typed`, the prefix shape at `δ` = the history's union at `0` (`schedUnionS_cons_eq`,
`ae_compl_eq_dom_root0`), `claim_of_prefix_pair` (transfer + restart), then the version conversion
`integral_stgMeanR_zero_conv` with `eqOn_typed_upW_mean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The Claim(k) step on one cell.** -/
theorem claim_cell (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (hR1 : PrefixLifeStatement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l')) (hδ0 : 0 < δ)
    (hδcap : δ < candidateCap c r a')
    -- the current instance
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a)
      (schedTr c r (e :: l') a) c.α ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hσa : ch.σa = specOffset c.κ + candAngle c r (e :: l') a * chiC c.κ) (w : WordType)
    -- the prefix instance
    {GT' : Set Ω} (hGT' : (∀ ω ∈ GT', PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
      (schedTr c r l' a') c.α ω) ∧ MeasurableSet GT' ∧
      (∀ᵐ ω ∂c.P, ω ∈ GT' ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA' : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V')
    (hV' : ∀ ω, V' ω ≠ ⊤) (ch' : GW2Sdh.SchedChoice Ω) (hu₀' : ch'.u₀ = ch.u₀) (hkc' : ch'.kc = chiC c.κ)
    (hβm' : Measurable ch'.β) (hE₀' : MeasurableSet ch'.E₀) (c' : BoundaryWord)
    (hN' : (historyProgram c r l').length = (entryList l').length + 1)
    (hβ' : ch'.β = GW2Wm.schedWordMapX c.κ c' (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
      hN' (candAngle c r l' a'))
    (hσa' : ch'.σa = specOffset c.κ + candAngle c r l' a' * chiC c.κ) (w' : WordType)
    (hIH : ClaimAt c r l' a' GT' hA' ch' w')
    -- the cell
    {E : Set Ω} (hEm : MeasurableSet E) (hEs : ∀ ω ∈ E, oldSuccess c r (e :: l') ω)
    (hE : ∀ᵐ ω ∂c.P, ω ∈ E →
      (ω ∈ liveEvRec c.κ w' ch'.β (GW2Rv.schedInstSX c r l' a' GT' hA' ch').E
          ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1)) ∧
        (GW2Rv.schedInstSX c r l' a' GT' hA' ch').clockX c (rootPt r.1) δ ω <
          (GW2Rv.schedInstSX c r l' a' GT' hA' ch').capX c (rootPt r.1) ω) ∧
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' V' (historyTime c r l') ω +
          ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').clockX c (rootPt r.1) δ ω).toNNReal =
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω) ∧
      (∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω,
        R' u ω = R u ω) ∧
      ch.β ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
        GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ)
          (stopWord c.κ (GW2Wm.baseWordX c.κ c' (rootPt r.1) c.s (historyProgram c r l')
            ((entryList l').length + 1) hN' ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω),
            (e.1 : ℝ), recOf (((GW2Rv.schedInstSX c r l' a' GT' hA' ch').clockX c (rootPt r.1) δ ω).toNNReal :
              ℝ≥0∞) (fun q => stgDrv (fun u => R' u ω)
                (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' V' (historyTime c r l') ω) q, ⊤))))
    (g₀ : Ω → DistOn upperHalfPlaneOpens)
    (hg₀ : IsLocalSetMean ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).B 0) (centredField c.h ch.u₀) c.P g₀)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ E →
      ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
        ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
      (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω →
      tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).B 0 ω →
      g₀ ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
        (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω) 0
        (bheProc c.κ (typedRhoL w) (typedRhoR w)
          ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).drvX c (rootPt r.1))
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
            ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω,
              relVar (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).Hr
                ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).drvX c (rootPt r.1))
                ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1)) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
            ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω,
              relVar (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).Hr
                ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).drvX c (rootPt r.1))
                ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
        ch.u₀ ch.σa z * φ z := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  have hv := hA.1.1
  have hv' := hA'.1.1
  have hB : ∀ q : ℝ≥0, (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).B q = GW2Sdi.schedUnionS c r (e :: l') a q :=
    fun q => funext fun ω => schedUnionSX_eq_schedUnionS c r (e :: l') a hr0 q ω
  have hB' : ∀ q : ℝ≥0, (GW2Rv.schedInstSX c r l' a' GT' hA' ch').B q = GW2Sdi.schedUnionS c r l' a' q :=
    fun q => funext fun ω => schedUnionSX_eq_schedUnionS c r l' a' hr0 q ω
  have hcandθ : candAngle c r l' a' = (e.1 : ℝ) := by
    show specAngle (schedSpec (rootPt r.1) (historyProgram c r l' ++ [((candidateAngle c r a' : ℝ),
      historyTime c r l' + candidateCap c r a')])) (historyProgram c r l').length = _
    rw [RootH29.specAngle_last, hθ]
  have hu₀p : IsBoundedHarmonicExtension c.b c.jumps ch'.u₀ := hu₀' ▸ hu₀
  -- the prefix's pairing at the entry's end, on the cell
  have hlife' : ∀ᵐ ω ∂c.P, ω ∈ E → ω ∈ liveEvRec c.κ w' ch'.β (GW2Rv.schedInstSX c r l' a' GT' hA' ch').E
        ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l' a' GT' hA' ch').clockX c (rootPt r.1) δ ω <
        (GW2Rv.schedInstSX c r l' a' GT' hA' ch').capX c (rootPt r.1) ω →
      (δ : ℝ≥0∞) < candLife c r l' a' ω := Eventually.of_forall fun ω hωE _ _ => by
    have h := hR1 c r e l' a' hθ hcap ω (hEs ω hωE)
    have hd : historyTime c r (e :: l') - historyTime c r l' = δ := by rw [← hδ]; simp
    rwa [hd] at h
  have hfar' := ae_farR_srecX c r l' a' hGT' hA' hV' ch' c' hN' (candAngle c r l' a') hβ' w'
  set G : Set Ω := E ∩ (liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
      ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) ∩
    {ω | (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω}) with hGdef
  have hGS : ∀ ω ∈ G, oldSuccess c r (e :: l') ω := fun ω hω => hEs ω hω.1
  -- the prefix's data
  set a₀' : Ω → ℝ≥0 := fun ω => stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' V' (historyTime c r l') ω
    with ha₀'
  set q : Ω → ℝ≥0 := fun ω => ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').clockX c (rootPt r.1) δ ω).toNNReal
    with hqdef
  set U' : Ω → ℂ → ℝ := fun ω => bheProc c.κ (typedRhoL w') (typedRhoR w')
      ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').drvX c (rootPt r.1))
      (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w' (ch'.β y.1)) i t
        ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω,
          relVar (GW2Rv.schedInstSX c r l' a' GT' hA' ch').Hr
            ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').drvX c (rootPt r.1))
            ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').capX c (rootPt r.1)) ω))
      (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w' (ch'.β y.1)) j t
        ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω,
          relVar (GW2Rv.schedInstSX c r l' a' GT' hA' ch').Hr
            ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').drvX c (rootPt r.1))
            ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').capX c (rootPt r.1)) ω)) ω (q ω) with hU'def
  have hP : ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (GW2Sdi.schedUnionS c r l' a' δ) (centredField c.h ch.u₀) c.P g →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G →
        tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l' a' δ ω →
        g ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun u => R' u ω) (a₀' ω) (q ω : ℝ) (U' ω) ch.u₀ ch'.σa z *
          φ z := by
    intro g hg φ
    have hg' : IsLocalSetMean ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').B δ) (centredField c.h ch'.u₀) c.P g := by
      rw [hB' δ, hu₀']
      exact hg
    filter_upwards [pair_instS h12 h13 h12₀ h13₀ c r l' a' hr0 hord' hs0 hGT' hA' hV' ch' hu₀p hkc' hβm' hE₀' w' δ
      hδ0 hδcap hEm hlife' hfar' hIH g hg' φ, hE] with ω h1 h2 hωG hsupp
    obtain ⟨⟨hlive', hclk'⟩, -⟩ := h2 hωG.1
    rw [← hB' δ] at hsupp
    rw [h1 hωG.1 hlive' hclk' hsupp, hu₀']
  -- the word of the history and the samples
  set Wd' : Ω → BoundaryWord := fun ω => GW2Wm.baseWordX c.κ c' (rootPt r.1) c.s (historyProgram c r l')
    ((entryList l').length + 1) hN' ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω)
    with hWd'
  set Wd : Ω → BoundaryWord := fun ω => stopWord c.κ (Wd' ω, (e.1 : ℝ),
    recOf ((q ω : ℝ≥0) : ℝ≥0∞) (fun t => stgDrv (fun u => R' u ω) (a₀' ω) t, ⊤)) with hWd
  have hρ' := hA'.1.2.choose_spec
  have hfin' : ∀ᵐ ω ∂c.P, (GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω ∈
      (GW2Rv.schedInstSX c r l' a' GT' hA' ch').E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ (GW2Rv.schedInstSX c r l' a' GT' hA' ch').W
        (GW2Rv.schedInstSX c r l' a' GT' hA' ch').GT (GW2Rv.schedInstSX c r l' a' GT' hA' ch').V
        (GW2Rv.schedInstSX c r l' a' GT' hA' ch').T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV' ω) (min_le_right _ _)
  have hEgood' := StageInst.E_good_of_recordX (GW2Rv.schedInstSX c r l' a' GT' hA' ch') hv' hρ'.2.1 hρ'.2.2
    inter_subset_right hfin'
  have hsamp : ∀ᵐ ω ∂c.P, ω ∈ G → Continuous (fun u => R' u ω) ∧ R' 0 ω = 0 ∧
      (∀ z ∈ H, (Wd ω).mean z = U' ω z + (specOffset c.κ - ch'.σa)) ∧
      H \ GW2Sdi.schedUnionS c r (e :: l') a 0 ω ⊆
        ((stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun u => R' u ω) (a₀' ω + q ω)).dom : Set ℂ) := by
    filter_upwards [hE, hEgood', hGT'.2.2, ae_compl_eq_dom_root0 c r l' a' hr0 hs0 hGT'.1 hv',
      Gm.ae_futureJoined_trace h13 c r] with ω hEω hEgω hGTω hdomω htrω hωG
    obtain ⟨⟨hlive', hclk'⟩, -⟩ := hEω hωG.1
    have hsucc := hEs ω hωG.1
    have hsucc' := oldSuccess_of_cons c r e l' ω hsucc
    have hωGT' : ω ∈ GT' := hGTω.2 (hEgω hlive'.1).1
    have hRc' : Continuous fun u => R' u ω := hv'.2.1 ω
    have hR0' : R' 0 ω = 0 := hv'.2.2.1 ω
    refine ⟨hRc', hR0', ?_, ?_⟩
    · -- the explored identity
      have hdc' : Continuous fun t => (GW2Rv.schedInstSX c r l' a' GT' hA' ch').drvX c (rootPt r.1) t ω :=
        continuous_stgDrv hRc' _
      have hd0' : (GW2Rv.schedInstSX c r l' a' GT' hA' ch').drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
      have hbhe := bhe_bheProc_typedX (r := r) (l := l') (GW2Rv.schedInstSX c r l' a' GT' hA' ch') (rootPt r.1) w' ω
        hdc' hd0' (q ω)
      have hβω : (GW2Rv.schedInstSX c r l' a' GT' hA' ch').β
          ((GW2Rv.schedInstSX c r l' a' GT' hA' ch').srecX c r l' (rootPt r.1) ω) =
          GW2Rd.upW ((e.1 : ℝ) * chiC c.κ) (Wd' ω) := by
        show ch'.β _ = _
        rw [hβ']
        unfold GW2Wm.schedWordMapX
        rw [hcandθ]
      have hw : wordType c.κ (GW2Rd.upW ((e.1 : ℝ) * chiC c.κ) (Wd' ω)) = w' := by
        rw [← hβω]
        exact hlive'.2
      rw [hβω] at hbhe
      have hexp := eqOn_explored_typed (θ := (e.1 : ℝ)) (c := Wd' ω) hw
        (S := stgDrv (fun u => R' u ω) (a₀' ω)) (continuous_stgDrv hRc' _) (stgDrv_zero _ _) (q ω) hbhe
      intro z hz
      have h1 := hexp hz
      simp only at h1
      rw [hσa', hcandθ]
      show (Wd ω).mean z = U' ω z + _
      rw [show U' ω z = _ from h1]
      ring
    · -- the domain
      have heq := schedUnionS_cons_eq c r e l' a a' ω hord hord' hsucc (htrω (e :: l') a hsucc).1
        (htrω l' a' hsucc').1 hθ hcap δ hδ
      have hlt' := min_lt_of_clockX_lt_capX c r l' a' hA' ch' (hV' ω) hclk'
      have hd := hdomω hωGT' hsucc' δ hlt'
      have e' : ((q ω : ℝ≥0) : ℝ) = (capA (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' V' (historyTime c r l')
          δ ω : ℝ) - a₀' ω :=
        coe_toNNReal_stgClockX hGT'.1 hs0 hx (historyTime c r l') δ (hV' ω)
      have hsum : a₀' ω + q ω = capA (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' V' (historyTime c r l') δ ω := by
        apply NNReal.eq
        rw [NNReal.coe_add, e']
        ring
      rw [heq, hd, hsum]
  -- Claim(k) at the history in the prefix version
  have hg₀' : IsLocalSetMean (GW2Sdi.schedUnionS c r (e :: l') a 0) (centredField c.h ch.u₀) c.P g₀ := by
    rw [← hB 0]
    exact hg₀
  have hstep := claim_of_prefix_pair h12 h13 c r e l' a a' hr0 hord hord' hθ hcap δ hδ hu₀ hGS (R := R')
    (a₀' := a₀') (q := q) (U' := U') (σa' := ch'.σa) (Wd := Wd) hP hsamp g₀ hg₀' φ
  -- converted to the history's version
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω ∈
      (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).W
        (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).GT (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).V
        (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX (GW2Rv.schedInstSX c r (e :: l') a GT hA ch) hv hρ.2.1 hρ.2.2
    inter_subset_right hfin
  filter_upwards [hstep, hE, hEgood, hGT.2.2, ae_compl_eq_dom_root0 c r (e :: l') a hr0 hs0 hGT.1 hv]
    with ω h1 h2 hEgω hGTω hdomω hωE hlive hcap0 hsupp
  have hωG : ω ∈ G := ⟨hωE, hlive, hcap0⟩
  have hsucc := hEs ω hωE
  have hωGT : ω ∈ GT := hGTω.2 (hEgω hlive.1).1
  rw [hB 0] at hsupp
  rw [h1 hωG hsupp]
  obtain ⟨-, hsumE, hRR, hβE⟩ := h2 hωE
  rw [hsumE]
  have hRc : Continuous fun u => R u ω := hv.2.1 ω
  have hR0 : R 0 ω = 0 := hv.2.2.1 ω
  -- the history's typed function is the word's mean raised by the angle
  have hdc : Continuous fun t => (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).drvX c (rootPt r.1) t ω :=
    continuous_stgDrv hRc _
  have hd0 : (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
  have hbhe0 := bhe_bheProc_typedX_zero (r := r) (l := e :: l') (GW2Rv.schedInstSX c r (e :: l') a GT hA ch)
    (rootPt r.1) w ω hdc hd0
  have hβω : (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).β
      ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
      GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ) (Wd ω) := hβE
  have hw : wordType c.κ (GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ) (Wd ω)) = w := by
    rw [← hβω]
    exact hlive.2
  rw [hβω] at hbhe0
  have hU := eqOn_typed_upW_mean c.hκ (Wd ω) (isSorted_stopWord _ _) _ hw hbhe0
  -- the support lies in the history's stage chart's domain
  have hclk0 : (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).clockX c (rootPt r.1) 0 ω <
      (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω := by
    show stgClockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) 0 ω < _
    rw [stgClock_zeroX]
    exact hcap0
  have hlt0 := min_lt_of_clockX_lt_capX c r (e :: l') a hA ch (hV ω) hclk0
  have hd := hdomω hωGT hsucc 0 hlt0
  rw [capA_zero] at hd
  have hφ : tsupport φ ⊆ ((stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun u => R u ω)
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω)).dom :
        Set ℂ) := by
    rw [← hd]
    exact hsupp
  rw [integral_stgMeanR_zero_conv c.κ _ hRc hR0 (hv'.2.1 ω) hRR hU φ hφ, hσa]
  rfl

end InteractingSLE.Theorem14.GW2Psm
