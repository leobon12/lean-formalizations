/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterLaw
import InteractingSLE.Spec.Sec5.CrossCondStagedCandLaw

/-!
# Prop 5.9's root stage: the killed comparison clause of PROVE-PROP59-PIECES' root candidate

Packet PROVE-STAGED-REP2. **`compClauseK_rootCand`**: for every rational `q > 0`, the stage-0 candidate of
PIECES' root experiment (`rootCand … q 0 t`, the dilated joint-chart image of the angle-`π/2` code flow line, killed
at its first contact with the counterflow stopped at `q`) satisfies the comparison clause of the killed stage law
(`IsStageLawFarK`, R78) for the past `rootBase q` (the counterflow history stopped at `q`), the root start and the root
word `(rootρL, rootρR)` with far marks the junctions.

Route: the glued-space clause of the dilated image word (`compClauseK_img_dil`, PROVE-STAGED-REP's representation with
the standard noise space) is carried to PIECES' space by STAGED7's `compClause_of_map_eq` through the pair
`(qField, counterflow history)`: its laws agree (`map_pair_eq_glue`), and on both spaces the (start, samples) record is
almost surely the Borel function `gamObs` of the pair (`glueObs_eq_gamObs`, `rootObs_eq_gamObs`).

Named inputs: the deterministic `StagedRep.KilledArcSwallowStatement` (PROVE-KILLARC) and R74's `h44`. R48: nothing
here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec4 GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces StagedKCand StagedKill
open StagedRep

section Main

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **The root past at the counterflow time `q`**: the counterflow history stopped at `q`. -/
abbrev rootBase (q : ℚ) : MeasurableSpace (Ω × Ωa) :=
  MeasurableSpace.comap (fun ω' : Ω × Ωa => cfStop (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω'.1)) inferInstance

/-- The past on `Gam`: the history stopped at `r`. -/
abbrev gamPast (r : ℝ≥0) : MeasurableSpace Gam :=
  MeasurableSpace.comap (fun γ : Gam => cfStop r γ.2) inferInstance

theorem gamPast_le (r : ℝ≥0) : gamPast r ≤ (inferInstance : MeasurableSpace Gam) := by
  rintro s ⟨t, ht, rfl⟩
  exact (show Measurable fun γ : Gam => cfStop r γ.2 from (measurable_cfStop r).comp measurable_snd) ht

/-- The good samples of PIECES' space for the root stage: the root good set and good (field, history) pairs. -/
theorem ae_rootGood_pieceZ (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) (r : ℝ≥0) :
    ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      pieceZ x₀ κ h W ζ ω' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
  obtain ⟨γ, htr⟩ := exists_cfTrace hκ hb hG hcf
  have h1 := ae_mem_rootGood x₀ h44 hκ hκ4 hb hA hG hcf htr hE hR (r := r)
  have h2 := ae_cfHistory_mem_goodHitSet hA hκ hκ4 hb hG hcf htr
  have h3 := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSched j t)
  have h0 : ∀ᵐ ω ∂P, ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
    filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
    exact ⟨hω1, hω2.1, fun j t hv k hk => hω3 j t hv k hk⟩
  exact Measure.quasiMeasurePreserving_fst.ae h0

/-- **The killed comparison clause of PIECES' root candidate** (stage `0`, any rational `q > 0`). -/
theorem compClauseK_rootCand (hsw : KilledArcSwallowStatement) (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) {q : ℚ} (hq : 0 < q) (t : Fin 0 → ℝ≥0) :
    CompClauseK κ (P.prod Pa) (rootBase W ζ (Ωa := Ωa) q) univ (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (Fin.last (flowLineNL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0))
      (Fin.last (flowLineNR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0))
      (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).ζ := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set r : ℝ≥0 := (q : ℝ).toNNReal with hr
  have hr0 : 0 < r := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  obtain ⟨htop, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  set k := condDistrib (Cond44Ref.cfHistory W ζ) (qField x₀ κ h) P with hkdef
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) = P.map (qField x₀ κ h) ⊗ₘ k :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hXq : (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) = qField x₀ κ h :=
    funext fun ω => cfField_rootField ω
  have hlaw : P.map (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) = P.map (qField x₀ κ h) := by
    rw [hXq]
  have hxLs : StrictAnti (flowLineXL c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXL_lt c.fn c.jumps 0 hij
  have hxRs : StrictMono (flowLineXR c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXR_lt c.fn c.jumps 0 hij
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hglue := compClauseK_img_dil hsw hκ hκ4 hF h44' hxLs hxRs hC hcfc hlaw k hk hr0 measurable_startC
    startC_ne_zero
  set μ := glueMeasure P k (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω))
    ((Cond44Ref.measurable_cfField κ).comp hC.2.1) with hμ
  set Z := pieceZ (Ωa := Ωa) x₀ κ h W ζ with hZdef
  set Z' : Ω × HistorySpace 0 0 → Gam := fun p => (qField x₀ κ h p.1, p.2) with hZ'def
  have hZ := measurable_pieceZ (Ωa := Ωa) x₀ hhm hcf
  have hZ' : Measurable Z' := (hqm.comp measurable_fst).prodMk measurable_snd
  -- the laws of the pair agree
  have hlawZ : (P.prod Pa).map Z = μ.map Z' := by
    have h1 : (P.prod Pa).map Z = P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) := by
      have e : Z = (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) ∘ Prod.fst := rfl
      rw [e, ← Measure.map_map (hqm.prodMk hcfm) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    have hk' : P.map (fun ω => (Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω),
        Cond44Ref.cfHistory W ζ ω)) =
        P.map (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) ⊗ₘ k := by
      simpa only [cfField_rootField] using hk
    rw [h1, StagedCand.map_pair_eq_glue ((Cond44Ref.measurable_cfField κ).comp hC.2.1) hcfm k hk' measurable_id
      (Eventually.of_forall fun ω => (cfField_rootField ω).symm)]
    rfl
  -- good samples
  have hgP := ae_rootGood_pieceZ x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hG hcf hE hR r
  have hgamP : ∀ᵐ γ ∂((P.prod Pa).map Z), γ ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb :=
    (ae_map_iff hZ.aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).2 (hgP.mono fun _ h => h.2)
  have hgZ' : ∀ᵐ p ∂μ, Z' p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
    rw [hlawZ] at hgamP
    exact (ae_map_iff hZ'.aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).1 hgamP
  set W₀ : ℝ≥0 → Ω → ℝ := fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t with hW₀
  set ζ₀ : Ω → ℝ≥0∞ := fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2 with hζ₀
  have hgE : ∀ᵐ p ∂μ, p ∈ glueGood μ r ζ₀ W₀ := by
    have hae : ∀ᵐ p ∂μ, IsGood49 r ζ₀ W₀ p := by
      filter_upwards [cfGlueAE_isGood49 r hr0 κ hκ hκ4 _ _ _ _ hF h44' P 𝓕 W₀ VL VR B ζ₀ _ hC P
        (qField x₀ κ h) W ζ hcfc hlaw k hk] with p hp
      exact isGood49_of_mem hp.1 hp.2
    exact ae_mem_glueGood hae
  have htopG : ∀ᵐ p ∂μ, (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h p.1).2 = ⊤ :=
    WangWu.ae_glue_fst k ((Cond44Ref.measurable_cfField κ).comp hC.2.1) htop
  -- the clause on the glued space for the observable
  have h𝓜Z' : (gamPast r).comap Z' =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop r p.2) inferInstance := by
    rw [MeasurableSpace.comap_comp]; rfl
  have h𝓜Z : (gamPast r).comap Z = rootBase W ζ (Ωa := Ωa) q := by
    rw [MeasurableSpace.comap_comp]; rfl
  have h' : ∀ S : Set (Start (rootNL c + 0) (rootNR c + 0) × Samp (rootNL c + 0) (rootNR c + 0)), MeasurableSet S →
      ∀ p : ℝ≥0∞, CompPremiseFarK κ (rootρL κ c) (rootρR κ c) (Fin.last (flowLineNL c.fn c.jumps 0))
        (Fin.last (flowLineNR c.fn c.jumps 0)) univ S p → ∀ A : Set (Ω × HistorySpace 0 0),
        MeasurableSet[(gamPast r).comap Z'] A → A ⊆ Z' ⁻¹' univ →
        p * μ A ≤ μ (A ∩ {p' | gamObs h44 hκ hκ4 (x₀ := x₀) hb r (Z' p') ∈ S}) := by
    intro S hS p hp A hA _
    rw [h𝓜Z'] at hA
    refine (hglue S hS p hp A hA (subset_univ _)).trans (le_of_eq (measure_congr ?_))
    filter_upwards [hgE, hgZ', htopG] with p' hpE hpZ htp
    have he := glueObs_eq_gamObs h44 hκ hκ4 hb r (E := glueGood μ r ζ₀ W₀) hpE hpZ htp
    show (p' ∈ A ∧ _ ∈ S) = (p' ∈ A ∧ _ ∈ S)
    rw [he]
  have key := StagedCand.compClause_of_map_eq hZ hZ' hlawZ (gamPast_le r) MeasurableSet.univ
    (measurable_gamObs h44 hκ hκ4 hb r) h'
  intro S hS p hp A hA hAR
  rw [← h𝓜Z] at hA
  refine (key S hS p hp A hA (fun _ _ => mem_univ _)).trans (le_of_eq (measure_congr ?_))
  filter_upwards [hgP] with ω' hω'
  have he := rootObs_eq_gamObs x₀ h44 hκ hκ4 hb hhm hcf noise (Ωa := Ωa) t hω'.1 hω'.2
  show (ω' ∈ A ∧ _ ∈ S) = (ω' ∈ A ∧ _ ∈ S)
  rw [he]

end Main

end InteractingSLE.Sec5.CrossCond.StagedRepLater
