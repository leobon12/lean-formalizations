import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G2FixMixRootR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM, node B1 (Palm average): quantile change of variables; B1 from B0 + measurability

Deterministic core of `G1PalmAvgStmt` (G1ZoomNodes.lean) for the left side: for a measure `m`
on `ℝ` without atoms, charging every nondegenerate interval of `(−∞,0]`, finite on the segments
`[b,0]`, and with mass at least `U` on some `[−δ,0]`, the quantile map `ℓ ↦ lenLeft m ℓ` turns
the Lebesgue integral over `ℓ ∈ (0,U]` into the `m`-integral over the Palm window
`{b < 0 : m[b,0] ≤ U}` (`g1Win`):

  `∫_{(0,U]} F(lenLeft m ℓ) dℓ = ∫_{b < 0, m[b,0] ≤ U} F(b) m(db)`.

Source: the quantile transform `map_lenLeft_restrict_Ioc` (G2FullMixCampbell.lean, own elementary
proof there: inverse transform sampling for a Stieltjes measure) and `measure_Icc_lenLeft_eq`
(G2FixMixRoot.lean); the identification of the window with `[lenLeft m U, 0)` is an own
elementary argument (strict monotonicity of `b ↦ m[b,0]`). The right side is the mirror image
(`g1_setLIntegral_lenRight_eq_win`, via `lenRight_eq_neg_lenLeft`).

`g1PalmAvgStmt_of : G1SideBdryRegStmt → G1SideTranslMeasStmt → G1PalmAvgStmt` (Tonelli,
`lintegral_lintegral_swap`, then the pathwise identity for a.e. `ω`), and the headline variants
`g1ZoomPartStmt_of_nodes'`, `g1Stmt_of_N2_zoomNodes'_regRep`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-- The left Palm window is `[lenLeft m U, 0)`. -/
theorem g1_leftWin_eq_Ico {m : Measure ℝ} {U : ℝ}
    (hpos : ∀ u v : ℝ, u < v → v ≤ 0 → 0 < m (Ioo u v))
    (hmass : m (Icc (lenLeft m U) 0) = ENNReal.ofReal U) :
    {b : ℝ | b < 0 ∧ m (Icc b 0) ≤ ENNReal.ofReal U} = Ico (lenLeft m U) 0 := by
  set x := lenLeft m U with hx
  have hx0 : x ≤ 0 := lenLeft_nonpos m U
  ext b
  simp only [mem_ofPred_eq, mem_Ico]
  constructor
  · rintro ⟨hb0, hb⟩
    refine ⟨?_, hb0⟩
    by_contra hbx'
    have hbx : b < x := not_le.1 hbx'
    have hdisj : Disjoint (Ioo b x) (Icc x 0) :=
      Set.disjoint_left.2 fun y hy hy' => (not_lt.2 hy'.1) hy.2
    have hsub : Ioo b x ∪ Icc x 0 ⊆ Icc b 0 := union_subset
      (fun y hy => ⟨hy.1.le, hy.2.le.trans hx0⟩) (Icc_subset_Icc_left hbx.le)
    have h1 : m (Ioo b x) + ENNReal.ofReal U ≤ m (Icc b 0) := by
      rw [← hmass, ← measure_union hdisj measurableSet_Icc]
      exact measure_mono hsub
    have h2 : ENNReal.ofReal U < m (Ioo b x) + ENNReal.ofReal U :=
      (ENNReal.lt_add_right ENNReal.ofReal_ne_top (hpos b x hbx hx0).ne').trans_eq (add_comm _ _)
    exact absurd (h2.trans_le (h1.trans hb)) (lt_irrefl _)
  · rintro ⟨hxb, hb0⟩
    exact ⟨hb0, hmass ▸ measure_mono (Icc_subset_Icc_left hxb)⟩

/-- **B1, pathwise, left side**: the quantile change of variables onto the Palm window. -/
theorem g1_setLIntegral_lenLeft_eq_win {m : Measure ℝ} {U : ℝ} (hU : 0 < U)
    (hatom : ∀ t : ℝ, m {t} = 0) (hpos : ∀ u v : ℝ, u < v → v ≤ 0 → 0 < m (Ioo u v))
    (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤)
    (hbig : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal U ≤ m (Icc (-δ) 0))
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ℓ in Ioc 0 U, F (lenLeft m ℓ) =
      ∫⁻ b in {b : ℝ | b < 0 ∧ m (Icc b 0) ≤ ENNReal.ofReal U}, F b ∂m := by
  obtain ⟨δ₀, hδ₀, hU₀⟩ := hbig
  set x := lenLeft m U with hx
  have hx0 : x ≤ 0 := lenLeft_nonpos m U
  have hmass : m (Icc x 0) = ENNReal.ofReal U :=
    measure_Icc_lenLeft_eq hδ₀ hfin (fun t _ => hatom t) hU₀
  have hxneg : x < 0 := by
    refine lt_of_le_of_ne hx0 fun h => ?_
    rw [h, Icc_self, hatom] at hmass
    exact (ENNReal.ofReal_pos.2 hU).ne' hmass.symm
  have hδ : 0 < -x := neg_pos.2 hxneg
  have hmap := map_lenLeft_restrict_Ioc hδ hfin
  rw [neg_neg, hmass, ENNReal.toReal_ofReal hU.le] at hmap
  rw [← lintegral_map hF (measurable_lenLeft_left m), hmap, g1_leftWin_eq_Ico hpos hmass]
  exact setLIntegral_congr (Ico_ae_eq_Icc' (hatom 0)).symm

/-- **B1, pathwise, right side** (mirror of the left side through `x ↦ −x`,
`lenRight_eq_neg_lenLeft`, G2FixMixRootR.lean). -/
theorem g1_setLIntegral_lenRight_eq_win {m : Measure ℝ} {U : ℝ} (hU : 0 < U)
    (hatom : ∀ t : ℝ, m {t} = 0) (hpos : ∀ u v : ℝ, u < v → 0 ≤ u → 0 < m (Ioo u v))
    (hfin : ∀ b : ℝ, m (Icc 0 b) ≠ ⊤)
    (hbig : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal U ≤ m (Icc 0 δ))
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ℓ in Ioc 0 U, F (lenRight m ℓ) =
      ∫⁻ b in {b : ℝ | 0 < b ∧ m (Icc 0 b) ≤ ENNReal.ofReal U}, F b ∂m := by
  set m' := m.map fun x : ℝ => -x with hm'
  have hIcc : ∀ a b : ℝ, m' (Icc a b) = m (Icc (-b) (-a)) := map_neg_Icc m
  have hatom' : ∀ t : ℝ, m' {t} = 0 := fun t => by
    rw [← Icc_self, hIcc, Icc_self, hatom]
  have hpos' : ∀ u v : ℝ, u < v → v ≤ 0 → 0 < m' (Ioo u v) := fun u v huv hv => by
    have hpre : (fun x : ℝ => -x) ⁻¹' Ioo u v = Ioo (-v) (-u) := by
      ext y
      simp only [mem_preimage, mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hm', Measure.map_apply measurable_neg measurableSet_Ioo, hpre]
    exact hpos (-v) (-u) (neg_lt_neg huv) (neg_nonneg.2 hv)
  have hfin' : ∀ b : ℝ, m' (Icc b 0) ≠ ⊤ := fun b => by
    rw [hIcc, neg_zero]; exact hfin _
  have hbig' : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal U ≤ m' (Icc (-δ) 0) := by
    obtain ⟨δ, hδ, h⟩ := hbig
    exact ⟨δ, hδ, by rw [hIcc, neg_zero, neg_neg]; exact h⟩
  have hL := g1_setLIntegral_lenLeft_eq_win hU hatom' hpos' hfin' hbig'
    (hF.comp measurable_neg)
  have hanti : Antitone fun b : ℝ => m' (Icc b 0) := fun a b hab =>
    measure_mono (Icc_subset_Icc_left hab)
  have hS : MeasurableSet {b : ℝ | b < 0 ∧ m' (Icc b 0) ≤ ENNReal.ofReal U} :=
    measurableSet_lt measurable_id measurable_const |>.inter
      (measurableSet_le hanti.measurable measurable_const)
  have hset : (fun x : ℝ => -x) ⁻¹' {b : ℝ | b < 0 ∧ m' (Icc b 0) ≤ ENNReal.ofReal U} =
      {b : ℝ | 0 < b ∧ m (Icc 0 b) ≤ ENNReal.ofReal U} := by
    ext b
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hIcc, neg_zero, neg_neg, neg_lt_zero]
  simp only [lenRight_eq_neg_lenLeft]
  refine hL.trans ((setLIntegral_map hS (hF.comp measurable_neg) measurable_neg).trans ?_)
  rw [hset]
  simp only [Function.comp_apply, neg_neg]

/-- Infinite mass on a set covered by an increasing sequence: some member has mass above `U`. -/
theorem g1_exists_mass_gt {m : Measure ℝ} {S : Set ℝ} {s : ℕ → Set ℝ} (hs : Monotone s)
    (hS : S ⊆ ⋃ n, s n) (htop : m S = ⊤) (U : ℝ) : ∃ n, ENNReal.ofReal U < m (s n) := by
  have hU : m (⋃ n, s n) = ⊤ := top_unique (htop ▸ measure_mono hS)
  have ht := tendsto_measure_iUnion_atTop (μ := m) hs
  rw [hU] at ht
  exact (ht.eventually (lt_mem_nhds ENNReal.ofReal_lt_top)).exists

/-- **Node B1-MEAS (measurability for Tonelli and for the pathwise change of variables)**:
for every `R`, a.s. the local canonical data of the side field translated to `b` are Borel in
`b`, and the rerooted local canonical data are a.e.-measurable jointly in `(ω, ℓ)`. -/
def G1SideTranslMeasStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ R : ℕ,
    (∀ᵐ ω ∂P, Measurable fun b : ℝ =>
      locFieldFull R (canonical γ (translate (g1SideField γ B Y left ω) (b : ℂ)))) ∧
    AEMeasurable (fun p : Ω × ℝ => locFieldFull R (canonical γ (translate
      (g1SideField γ B Y left p.1) (g1SidePt γ left (g1SideField γ B Y left p.1) p.2 : ℂ))))
      (P.prod volume)

/-- **Node B1 (Palm average) from the boundary regularity B0 and the measurability B1-MEAS**
(Tonelli, then the pathwise quantile change of variables on each side). -/
theorem g1PalmAvgStmt_of (hB0 : G1SideBdryRegStmt) (hM : G1SideTranslMeasStmt) :
    G1PalmAvgStmt := by
  intro γ Ω _ P _ B Y hS hIn left U hU R Γ hΓ hΓ1
  obtain ⟨hm1, hm2⟩ := hM γ P B Y hS hIn left R
  have hjoint : AEMeasurable (Function.uncurry fun (ω : Ω) (ℓ : ℝ) =>
      Γ (locFieldFull R (canonical γ (translate (g1SideField γ B Y left ω)
        (g1SidePt γ left (g1SideField γ B Y left ω) ℓ : ℂ)))))
      (P.prod (volume.restrict (Ioc (0 : ℝ) U))) := by
    have he : P.prod (volume.restrict (Ioc (0 : ℝ) U)) =
        (P.prod volume).restrict (univ ×ˢ Ioc 0 U) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [he]
    exact hΓ.comp_aemeasurable hm2.restrict
  unfold g1RerootInt g1PalmInt
  rw [← lintegral_lintegral_swap hjoint]
  refine lintegral_congr_ae ?_
  filter_upwards [hB0 γ P B Y hS hIn left, hm1] with ω hreg hmeasω
  obtain ⟨hat, hpos, hfin, hinf⟩ := hreg
  have hF := hΓ.comp hmeasω
  set x := g1SideField γ B Y left ω with hx
  cases left with
  | true =>
    set m := g1SideNu γ true x with hm
    have e1 : ∀ ℓ, g1SidePt γ true x ℓ = lenLeft m ℓ := fun _ => rfl
    have e2 : g1Win γ true x U = {b : ℝ | b < 0 ∧ m (Icc b 0) ≤ ENNReal.ofReal U} := rfl
    simp only [e1, e2]
    refine g1_setLIntegral_lenLeft_eq_win hU hat
      (fun u v huv hv => hpos u v huv fun y hy => (show y < 0 from hy.2.trans_le hv))
      (fun b => ?_) ?_ hF
    · by_cases hb : b < 0
      · exact (hfin b hb).ne
      · have hsub : Icc b 0 ⊆ {0} := fun y hy =>
          le_antisymm hy.2 ((not_lt.1 hb).trans hy.1)
        exact ne_top_of_le_ne_top ENNReal.zero_ne_top
          ((measure_mono hsub).trans (hat 0).le)
    · obtain ⟨n, hn⟩ := g1_exists_mass_gt (m := m) (S := Iio 0)
        (s := fun n : ℕ => Icc (-((n : ℝ) + 1)) 0)
        (fun a b hab => Icc_subset_Icc_left (by
          have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
        (fun y hy => by
          obtain ⟨n, hn⟩ := exists_nat_gt (-y)
          exact mem_iUnion.2 ⟨n, ⟨by linarith, (show y < 0 from hy).le⟩⟩)
        hinf U
      exact ⟨(n : ℝ) + 1, by positivity, hn.le⟩
  | false =>
    set m := g1SideNu γ false x with hm
    have e1 : ∀ ℓ, g1SidePt γ false x ℓ = lenRight m ℓ := fun _ => rfl
    have e2 : g1Win γ false x U = {b : ℝ | 0 < b ∧ m (Icc 0 b) ≤ ENNReal.ofReal U} := rfl
    simp only [e1, e2]
    refine g1_setLIntegral_lenRight_eq_win hU hat
      (fun u v huv hu => hpos u v huv fun y hy => (show 0 < y from hu.trans_lt hy.1))
      (fun b => ?_) ?_ hF
    · by_cases hb : 0 < b
      · exact (hfin b hb).ne
      · have hsub : Icc 0 b ⊆ {0} := fun y hy =>
          le_antisymm (hy.2.trans (not_lt.1 hb)) hy.1
        exact ne_top_of_le_ne_top ENNReal.zero_ne_top
          ((measure_mono hsub).trans (hat 0).le)
    · obtain ⟨n, hn⟩ := g1_exists_mass_gt (m := m) (S := Ioi 0)
        (s := fun n : ℕ => Icc 0 ((n : ℝ) + 1))
        (fun a b hab => Icc_subset_Icc_right (by
          have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
        (fun y hy => by
          obtain ⟨n, hn⟩ := exists_nat_gt y
          exact mem_iUnion.2 ⟨n, ⟨(show 0 < y from hy).le, by linarith⟩⟩)
        hinf U
      exact ⟨(n : ℝ) + 1, by positivity, hn.le⟩

end Thm18Asm
end QuantumZipper
