/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmCell

/-!
# GW2's open lines: the Claim(k) induction step

Packet PROVE-GW2-STAGEMEAN, R121 round.

* `measurableSet_live_clock`: the live event of a word type below the cap at a stage time is measurable;
* **`claim_step`**: `ClaimAt` at the history `e :: l'` (any announced version, any word type) from `ClaimAt` at the
  prefix `l'` for every version `n` of a family and every word type (the induction hypothesis), (R1)
  (`PrefixLifeStatement`), the cover `hcover` of the history's live event by the prefix's live events below the cap at
  the entry's duration (R3 of the handoff), and on them `hF`: the version agreement up to the history's stage start
  (via ROOTX's `GW2Ru.version_eq_of_drv_eq` and (R2)) and GEOM2's word recursion (R4). The cells
  (prefix version `n`, prefix word type `w'`, countably many) are handled by `claim_cell`.
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
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- **The live event of a word type below the cap at a stage time is measurable** (root `x ≥ 0`). -/
theorem measurableSet_live_clock (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (hx : (0 : ℝ) ≤ rootPt r.1) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀) (w : WordType) (t : ℝ≥0) :
    MeasurableSet (liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) ∩
      {ω | (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω}) := by
  have hver : IsRelVersionXR (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V := hA.1
  have hv := hver.1
  have hWm : ∀ q, Measurable (schedW c r l a q) := measurable_schedW c r l a
  have hGTm : ∀ q, MeasurableSet[physFilt (measurable_gb6Rec_src c) hWm c.P q] GT :=
    measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) R) :=
    (measurable_stgPreRecX hGT.1 hs0 hx (measurable_gb6Rec_src c) hWm hGTm hver (historyTime c r l)).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le _) le_rfl
  have hsrec : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) :=
    measurable_augRec (measurable_stageEncRec c r l) hpre
  have hstart := measurable_stgStartX_of_pre hpre
  have hclk : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t) :=
    (measurable_stgClockX hGT.1 hs0 hx (measurable_gb6Rec_src c) hWm hGTm hver (historyTime c r l) t).mono
      ((shiftFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) (historyTime c r l)).le t) le_rfl
  have hcap : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) :=
    hv.2.2.2.2.1.sub (measurable_coe_nnreal_ennreal.comp hstart)
  have hEm : MeasurableSet (GW2Rv.schedInstSX c r l a GT hA ch).E :=
    (hE₀.inter (GW2Sdi.measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hA.1.2.choose_spec.1)
  refine (hsrec (hEm.inter ?_)).inter (measurableSet_lt hclk hcap)
  exact ((measurable_wordType c.κ).comp hβm) (measurableSet_singleton w)

/-- **The Claim(k) step**: Claim(k) at the history `e :: l'` from Claim(k) at the prefix `l'` for every version of a
family and every word type, (R1), the cover of the history's live event by the prefix's live events below the cap at
the entry's duration (`hcover`), and on them the version agreement and GEOM2's word recursion (`hF`). -/
theorem claim_step (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (hR1 : PrefixLifeStatement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l')) (hδ0 : 0 < δ)
    (hδcap : δ < candidateCap c r a')
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a)
      (schedTr c r (e :: l') a) c.α ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀)
    (hσa : ch.σa = specOffset c.κ + candAngle c r (e :: l') a * chiC c.κ) (w : WordType)
    {GT' : Set Ω} (hGT' : (∀ ω ∈ GT', PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
      (schedTr c r l' a') c.α ω) ∧ MeasurableSet GT' ∧
      (∀ᵐ ω ∂c.P, ω ∈ GT' ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R' : ℕ → ℝ≥0 → Ω → ℝ} {V' : ℕ → Ω → ℝ≥0∞}
    (hA' : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α (R' n) (V' n))
    (hV' : ∀ n ω, V' n ω ≠ ⊤) (ch' : GW2Sdh.SchedChoice Ω) (hu₀' : ch'.u₀ = ch.u₀) (hkc' : ch'.kc = chiC c.κ)
    (hβm' : Measurable ch'.β) (hE₀' : MeasurableSet ch'.E₀) (c' : BoundaryWord)
    (hN' : (historyProgram c r l').length = (entryList l').length + 1)
    (hβ' : ch'.β = GW2Wm.schedWordMapX c.κ c' (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
      hN' (candAngle c r l' a'))
    (hσa' : ch'.σa = specOffset c.κ + candAngle c r l' a' * chiC c.κ)
    (hIH : ∀ (n : ℕ) (w' : WordType), ClaimAt c r l' a' GT' (hA' n) ch' w')
    (hcover : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
        ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
      (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω →
      ∃ n, (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').srecX c r l' (rootPt r.1) ω ∈
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').E ∧
        (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').clockX c (rootPt r.1) δ ω <
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').capX c (rootPt r.1) ω)
    (hF : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
        ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
      (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω → ∀ n : ℕ,
      (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').srecX c r l' (rootPt r.1) ω ∈
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').E →
      (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').clockX c (rootPt r.1) δ ω <
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').capX c (rootPt r.1) ω →
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' (V' n) (historyTime c r l') ω +
          ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').clockX c (rootPt r.1) δ ω).toNNReal =
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω) ∧
      (∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω,
        R' n u ω = R u ω) ∧
      ch.β ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
        GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ)
          (stopWord c.κ (GW2Wm.baseWordX c.κ c' (rootPt r.1) c.s (historyProgram c r l')
            ((entryList l').length + 1) hN'
              ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').srecX c r l' (rootPt r.1) ω),
            (e.1 : ℝ), recOf (((GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').clockX c (rootPt r.1) δ ω).toNNReal :
              ℝ≥0∞) (fun q => stgDrv (fun u => R' n u ω)
                (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' (V' n) (historyTime c r l') ω) q, ⊤)))) :
    ClaimAt c r (e :: l') a GT hA ch w := by
  classical
  intro g₀ hg₀ φ
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  set S' : Set WordType := range fun y => wordType c.κ (ch'.β y) with hS'
  have hS'c : S'.Countable := by
    rw [hS', hβ']
    exact (GW2Wm.schedWordMapX_targets c.κ c' (rootPt r.1) c.s (historyProgram c r l') _ hN'
      (candAngle c r l' a') c.κ).2.1
  have : Countable S' := hS'c.to_subtype
  set E : ℕ → S' → Set Ω := fun n w' => {ω | oldSuccess c r (e :: l') ω} ∩
    (((liveEvRec c.κ w'.1 ch'.β (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').E
        ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').srecX c r l' (rootPt r.1)) ∩
      {ω | (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').clockX c (rootPt r.1) δ ω <
        (GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').capX c (rootPt r.1) ω}) ∩
    (liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
        ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) ∩
      {ω | (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).clockX c (rootPt r.1) 0 ω <
        (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω}))) with hEdef
  have hEm : ∀ n w', MeasurableSet (E n w') := fun n w' =>
    (measurableSet_oldSuccess c r (e :: l')).inter
      ((measurableSet_live_clock c r l' a' hx hs0 hGT' (hA' n) ch' hβm' hE₀' w'.1 δ).inter
      (measurableSet_live_clock c r (e :: l') a hx hs0 hGT hA ch hβm hE₀ w 0))
  have hclk0 : ∀ ω, (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).clockX c (rootPt r.1) 0 ω = 0 := fun ω =>
    stgClock_zeroX _ ω
  have hcell : ∀ n (w' : S'), ∀ᵐ ω ∂c.P, ω ∈ E n w' →
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
    intro n w'
    refine claim_cell h12 h13 h12₀ h13₀ hR1 c r e l' a a' hr0 hs0 hord hord' hθ hcap δ hδ hδ0 hδcap hGT hA hV ch hu₀
      hσa w hGT' (hA' n) (hV' n) ch' hu₀' hkc' hβm' hE₀' c' hN' hβ' hσa' w'.1 (hIH n w'.1) (hEm n w')
      (fun ω hω => hω.1) ?_ g₀ hg₀ φ
    filter_upwards [hF] with ω hFω hω
    have hcap0 : (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω := by
      have h := hω.2.2.2
      simp only [mem_ofPred_eq, hclk0] at h
      exact h
    exact ⟨hω.2.1, hFω hω.2.2.1 hcap0 n hω.2.1.1.1 hω.2.1.2⟩
  have hall := ae_all_iff.2 fun n => ae_all_iff.2 fun w' => hcell n w'
  filter_upwards [hall, hcover] with ω hallω hcov hlive hcap0 hsupp
  obtain ⟨n, hsrec, hclk⟩ := hcov hlive hcap0
  have hsucc : oldSuccess c r (e :: l') ω := (GW2Sdi.augRec_mem_succRec_iff c r (e :: l') _ ω).1 hlive.1.1.2
  set w' : S' := ⟨wordType c.κ (ch'.β ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) ch').srecX c r l' (rootPt r.1) ω)),
    ⟨_, rfl⟩⟩ with hw'
  have hωE : ω ∈ E n w' := by
    refine ⟨hsucc, ⟨⟨hsrec, rfl⟩, hclk⟩, hlive, ?_⟩
    show (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).clockX c (rootPt r.1) 0 ω <
      (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω
    rw [hclk0]
    exact hcap0
  exact hallω n w' hωE hlive hcap0 hsupp

end InteractingSLE.Theorem14.GW2Psm
