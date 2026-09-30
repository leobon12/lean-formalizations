import QuantumZipper.Proofs.Thm18.RTMeasRead
import QuantumZipper.Proofs.Thm18.RTMeasArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS, part 4: the Borel reading of the scale, and `DownLenScaleFieldReadStmt`

The scale (1.8) of the unzipped pieces (Sheffield, arXiv:1012.4797, p. 26: `B₁(0)` has area one
in the transformed quantum measure) is `areaScale` of the area of the pieces on `ℍ ∖ K_t` pushed
forward by `f_t`. The mass of `B_r(0) ∩ ℍ` is the area of `f_t⁻¹(B_r(0) ∩ ℍ)`, and

* `f_t⁻¹(B_r(0) ∩ ℍ)` is the section of the image `SR r` of `{t ≥ 0, w ∈ B_r(0) ∩ ℍ}` under the
  injective jointly measurable map `(a, t, w) ↦ (a, t, Psi a t w)` of the dyadic driver code; the
  image is Borel by Lusin–Souslin (mathlib `MeasurableSet.image_of_measurable_injOn`, Kechris,
  *Classical Descriptive Set Theory*, Thm 15.1), as in `G4Core.measurableSet_image_fst_of_partialGraph`;
* the area of a jointly measurable random set is measurable in the parameter on the Borel set
  where the area of the pieces is a genuine local limit, finite on the compacts of `ℍ`
  (`RTMeas.measurable_measure_section`, `RTMeas.measurable_areaN`).

`downLenScaleFieldReadStmt_of_reg`: `DownLenScaleFieldReadStmt` from the two regularity
statements of the pieces, `PiecesLenRegStmt` (lengths) and `AreaRegStmt` (area).

Own elementary bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core

/-! ## The driver read from its dyadic code -/

theorem continuous_drvOfData {d : E6.FullData} (hc : Continuous d.2) : Continuous (drvOfData d) := by
  unfold drvOfData
  exact hc.comp (Continuous.subtype_mk (by fun_prop) _)

theorem wg_eq_drvOfData {d : E6.FullData} (hc : Continuous d.2) (hg : GoodDrv (lcode d).2) :
    wg (lcode d).2 = drvOfData d := by
  have hpa : pa (lcode d).2 = fun r : ℝ≥0 => drvOfData d r := by
    funext r; simp only [pa, wread_lcode, drvOfData_eq_readDrv hc]
  have hW0 : ∀ s : ℝ, drvOfData d s = drvOfData d (s.toNNReal : ℝ) := by
    intro s
    simp only [drvOfData, Real.coe_toNNReal', max_eq_left (le_max_right s 0)]
  unfold wg
  rw [if_pos hg, hpa, F1.readDrv_eq (continuous_drvOfData hc) hW0]

theorem goodDrv_of_pathGoodAll {d : E6.FullData} (hp : F1.PathGoodAll d.2) : GoodDrv (lcode d).2 := by
  have hc := F1.continuous_readDrv_of_dyUC hp.1
  have hpa : pa (lcode d).2 = fun r : ℝ≥0 => F1.readDrv d.2 r := by
    funext r; simp only [pa, wread_lcode]
  have hW0 : ∀ s : ℝ, F1.readDrv d.2 s = F1.readDrv d.2 (s.toNNReal : ℝ) := by
    intro s
    rw [F1.readDrv_eq_limUnder, F1.readDrv_eq_limUnder]
    simp only [← rdx_toNNReal]
  have hrd : F1.readDrv (pa (lcode d).2) = F1.readDrv d.2 := by
    rw [hpa]; exact F1.readDrv_eq hc hW0
  refine ⟨?_, by rw [hrd]; exact hp.2.1⟩
  rw [hpa]; exact F1.dyUC_of_continuous (hc.comp NNReal.continuous_coe)

/-! ## The pulled-back balls, by Lusin–Souslin -/

/-- The source set `{t ≥ 0, w ∈ B_r(0) ∩ ℍ}`. -/
def pushSrc (r : ℝ) : Set ((ℕ → ℝ) × ℝ × ℂ) := {x | 0 ≤ x.2.1 ∧ x.2.2 ∈ ball (0 : ℂ) r ∩ H}

theorem measurableSet_pushSrc (r : ℝ) : MeasurableSet (pushSrc r) :=
  (measurableSet_le measurable_const measurable_snd.fst).inter
    (measurable_snd.snd (measurableSet_ball.inter isOpen_H.measurableSet))

/-- The pull-back map `(a, t, w) ↦ (a, t, f_t⁻¹(w))` of the coded driver. -/
def pullMap (x : (ℕ → ℝ) × ℝ × ℂ) : (ℕ → ℝ) × ℝ × ℂ := (x.1, x.2.1, Psi x.1 x.2.1 x.2.2)

theorem measurable_pullMap : Measurable pullMap :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (Measurable.comp
    (g := fun p : ((ℕ → ℝ) × ℝ) × ℂ => Psi p.1.1 p.1.2 p.2)
    (f := fun x : (ℕ → ℝ) × ℝ × ℂ => ((x.1, x.2.1), x.2.2)) measurable_Psi
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)))

theorem Psi_eq_fwdMapInv (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    Psi a t w = fwdMapInv (wg a) t w := by
  rw [Psi, selC_of_mem hw, fwdMapInv_eq_psiR a ht hw]

theorem injOn_pullMap (r : ℝ) : InjOn pullMap (pushSrc r) := by
  rintro ⟨a, t, w⟩ ⟨ht, hw⟩ ⟨a', t', w'⟩ ⟨-, hw'⟩ he
  simp only [pullMap, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, he⟩ := he
  rw [Psi_eq_fwdMapInv a ht hw.2, Psi_eq_fwdMapInv a ht hw'.2] at he
  have h1 := RS.fwdMap_fwdMapInv (continuous_wg a) (wg_zero a) ht hw.2
  have h2 := RS.fwdMap_fwdMapInv (continuous_wg a) (wg_zero a) ht hw'.2
  rw [he] at h1
  simp only [Prod.mk.injEq, true_and]
  exact h1.symm.trans h2

/-- The graph of the pulled-back balls. -/
def SR (r : ℝ) : Set ((ℕ → ℝ) × ℝ × ℂ) := pullMap '' pushSrc r

theorem measurableSet_SR (r : ℝ) : MeasurableSet (SR r) :=
  (measurableSet_pushSrc r).image_of_measurable_injOn measurable_pullMap (injOn_pullMap r)

theorem SR_mono {r r' : ℝ} (h : r ≤ r') : SR r ⊆ SR r' :=
  image_mono fun _ hx => ⟨hx.1, ball_subset_ball h hx.2.1, hx.2.2⟩

theorem mem_SR_iff {d : E6.FullData} (hc : Continuous d.2) (hg : GoodDrv (lcode d).2) {t : ℝ}
    (ht : 0 ≤ t) (r : ℝ) (z : ℂ) :
    ((lcode d).2, t, z) ∈ SR r ↔
      z ∈ fwdMap (drvOfData d) t ⁻¹' (ball 0 r ∩ H) ∩ (H \ fwdHull (drvOfData d) t) := by
  have hW := wg_eq_drvOfData hc hg
  set a := (lcode d).2
  rw [← hW]
  constructor
  · rintro ⟨⟨a', t', w⟩, ⟨ht', hw⟩, he⟩
    simp only [pullMap, Prod.mk.injEq] at he
    obtain ⟨h1, h2, h3⟩ := he
    subst h3
    rw [h1, h2] at *
    rw [Psi_eq_fwdMapInv a ht hw.2]
    refine ⟨?_, RS.fwdMapInv_mem_compl_fwdHull (continuous_wg a) (wg_zero a) ht hw.2⟩
    rw [mem_preimage, RS.fwdMap_fwdMapInv (continuous_wg a) (wg_zero a) ht hw.2]
    exact hw
  · rintro ⟨hz1, hz2⟩
    refine ⟨(a, t, fwdMap (wg a) t z), ⟨ht, hz1⟩, ?_⟩
    simp only [pullMap, Prod.mk.injEq, true_and]
    rw [Psi_eq_fwdMapInv a ht hz1.2, RS.fwdMapInv_fwdMap (continuous_wg a) (wg_zero a) ht hz2]

/-! ## The mass reader and the scale reader -/

/-- The random pulled-back balls over `PX × ℝ`. -/
def Sfull (r : ℝ) : Set ((PX × ℝ) × ℂ) := {q | ((pcode q.1.1).2, q.1.2, q.2) ∈ SR r}

theorem measurableSet_Sfull (r : ℝ) : MeasurableSet (Sfull r) :=
  (measurableSet_SR r).preimage (((measurable_snd.comp (measurable_pcode.comp
    (measurable_fst.comp measurable_fst))).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

/-- The read mass of `B_r(0) ∩ ℍ` for the pushed area. -/
def massRd (γ : ℝ) (GA : Set PX) (r : ℝ) (x : PX × ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, areaN γ GA N x.1 (Prod.mk x ⁻¹' Sfull r)

theorem measurable_massRd (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) (r : ℝ) : Measurable (massRd γ GA r) :=
  Measurable.iSup fun N => measurable_measure_section (ν := fun x : PX × ℝ => areaN γ GA N x.1)
    ((measurable_areaN γ hGAm hGA N).comp measurable_fst)
    (fun x => areaN_univ_lt_top hGA N x.1) (measurableSet_Sfull r)

theorem massRd_mono (γ : ℝ) (GA : Set PX) (x : PX × ℝ) {r r' : ℝ} (h : r ≤ r') :
    massRd γ GA r x ≤ massRd γ GA r' x :=
  iSup_mono fun _ => measure_mono fun _ hz => SR_mono h hz

theorem massRd_eq {γ : ℝ} {GA : Set PX} {d : E6.FullData} (hd : πd d ∈ GA) (hc : Continuous d.2)
    (hg : GoodDrv (lcode d).2) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    massRd γ GA r (πd d, t) = (zipCapDownA γ t (configOfData γ d)).area (ball 0 r ∩ H) := by
  set W := drvOfData d with hWdef
  have hWc : Continuous W := continuous_drvOfData hc
  set A := fwdMap W t ⁻¹' (ball 0 r ∩ H) ∩ (H \ fwdHull W t) with hA
  have hsec : Prod.mk (πd d, t) ⁻¹' Sfull r = A := by
    ext z
    exact mem_SR_iff hc hg ht r z
  have hAH : A ⊆ H := fun z hz => hz.2.1
  have hK : MeasurableSet (H \ fwdHull W t) := E6.measurableSet_compl_fwdHull hWc ht
  have hf : AEMeasurable (fwdMap W t) ((areaOfData γ d).restrict (H \ fwdHull W t)) :=
    (E6.continuousOn_fwdMap_compl hWc ht).aemeasurable hK
  have hpush : (zipCapDownA γ t (configOfData γ d)).area (ball 0 r ∩ H) = areaOfData γ d A := by
    show (((areaOfData γ d).restrict (H \ fwdHull W t)).map (fwdMap W t)) (ball 0 r ∩ H) = _
    rw [Measure.map_apply_of_aemeasurable hf (measurableSet_ball.inter isOpen_H.measurableSet),
      Measure.restrict_apply' hK]
  rw [hpush]
  unfold massRd areaN
  simp only [if_pos hd, hsec]
  have e : ∀ N : ℕ, ((areaOfData γ (dfull (πd d))).restrict (LQGMeas.hExh N)) A =
      areaOfData γ d (A ∩ LQGMeas.hExh N) := fun N =>
    Measure.restrict_apply' (LQGMeas.isOpen_hExh N).measurableSet
  simp only [e]
  rw [← Monotone.measure_iUnion (fun m n hmn => inter_subset_inter_right _ (LQGMeas.hExh_mono hmn)),
    ← inter_iUnion, inter_eq_left.2 (hAH.trans LQGMeas.H_subset_iUnion_hExh)]

/-- The scale reader. -/
def scRd (γ : ℝ) (GA : Set PX) (x : PX × ℝ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ 1 ≤ massRd γ GA a x}

theorem measurable_scRd (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) : Measurable (scRd γ GA) := by
  refine LQGMeas.measurable_sInf_upClosed _ (fun q => ?_) ?_ ?_
  · by_cases hq : (0 : ℝ) < q
    · simp only [mem_ofPred_eq, hq, true_and]
      exact measurableSet_le measurable_const (measurable_massRd γ hGAm hGA q)
    · simp [hq]
  · rintro x a b ⟨ha, h1⟩ hab
    exact ⟨ha.trans_le hab, h1.trans (massRd_mono γ GA x hab)⟩
  · rintro x a ⟨ha, -⟩
    exact ha

theorem scRd_eq {γ : ℝ} {GA : Set PX} {d : E6.FullData} (hd : πd d ∈ GA) (hc : Continuous d.2)
    (hg : GoodDrv (lcode d).2) {t : ℝ} (ht : 0 ≤ t) :
    scRd γ GA (πd d, t) = areaScale (zipCapDownA γ t (configOfData γ d)).area := by
  unfold scRd areaScale
  simp only [massRd_eq hd hc hg ht]

/-! ## The regularity of the area of the pieces, and the assembly -/

/-- **Regularity of the area of the pieces** (open): a Borel set of full law on which the area
of the pieces is a genuine local limit on `ℍ ∖ curve`, finite on the compacts of `ℍ`
(`AreaGood`). -/
def AreaRegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
      ∃ GA : Set PX, MeasurableSet GA ∧ (∀ d : E6.FullData, πd d ∈ GA → AreaGood γ d) ∧
        ∀ᵐ ω ∂P, πd (offData (wedgeAConfig γ B Y ω).toPair) ∈ GA

theorem scaleReadStmt_of (hR : PiecesLenRegStmt) (hA : AreaRegStmt) : ScaleReadStmt := by
  intro γ Ω _ P _ B Y hSet hIn ℓ _
  obtain ⟨G, hGm, hGp, haeG⟩ := hR γ P B Y hSet hIn
  obtain ⟨GA, hGAm, hGA, haeA⟩ := hA γ P B Y hSet hIn
  have hGA' : ∀ p ∈ GA, AreaGood γ (dfull p) := fun p hp => hGA (dfull p) hp
  refine ⟨{x | x.1 ∈ GA ∧ GoodDrv (pcode x.1).2 ∧ 0 ≤ x.2}, scRd γ GA,
    (hGAm.preimage measurable_fst).inter ((measurableSet_goodDrv.preimage
      ((measurable_snd.comp measurable_pcode).comp measurable_fst)).inter
      (measurableSet_le measurable_const measurable_snd)),
    measurable_scRd γ hGAm hGA', fun d t hd hc => scRd_eq hd.1 hc hd.2.1 hd.2.2, ?_⟩
  filter_upwards [haeG, haeA] with ω h1 h2
  exact ⟨h2, goodDrv_of_pathGoodAll (hGp _ h1).1, Real.sInf_nonneg fun s hs => hs.1⟩

/-- **RT-MEAS: `DownLenScaleFieldReadStmt` from the regularity of the pieces.** -/
theorem downLenScaleFieldReadStmt_of_reg (hR : PiecesLenRegStmt) (hA : AreaRegStmt) :
    DownLenScaleFieldReadStmt :=
  downLenScaleFieldReadStmt_of hR (scaleReadStmt_of hR hA)

end RTMeas
end R18
end QuantumZipper
