import SmallGammaGeodesics.CC.ExtensionPull
import SmallGammaGeodesics.CC.ConfMetric
import LQGMetric.Field.ExistGFF
import LQGMetric.Field.CameronMartin

/-!
# T1: the `σ₀` internal-metric functional (track CC, packet CC12a; GA4 A10)

Source: planning audit `planning/audits/GA4-sections-7-8.md`, Details **A10** ("construction and
validity of 𝔡_U"), and `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) D17 item 2.

For a strong γ-LQG metric `D` and an open `U`, `exists_isSigma0Metric` produces a measurable
`d : (TestC0On U → ℝ) → ℂ → ℂ → ℝ≥0∞` with `CC.IsSigma0Metric D U d`: for every whole-plane GFF
`h` and every test function `g`, a.s. `D_{h+g}(·,·;U) = c · d(pair0On U (h + g))` on `U × U` for
some `c ∈ (0, ∞)`.

Construction (GA4 A10, made measurable and exact):
1. `ρ ∈ 𝓓(U)` with `∫ ρ = 1`; the recentring `x ↦ x − ⟨x, ρ⟩` (`GFFLaw.recenter`).
2. A reference whole-plane GFF `h₀` (`GFFExist.exists_wholePlaneGFF`); Axiom II for the recentred
   field `h₁ = h₀ − ⟨h₀, ρ⟩` on `U` gives a measurable `F : 𝒟'(U) → (ℂ → ℂ → [0,∞])` with
   `D_{h₁}(·,·;U) = F(h₁|_U)` a.s.
3. Doob–Dynkin (`Measurable.exists_eq_measurable_comp`, `𝒟'(U)` standard Borel): the map
   `x ↦ (x − ⟨x, ρ⟩)|_U` is `σ(pair0On U)`-measurable, so it equals `R ∘ pair0On U` for a measurable
   `R : (TestC0On U → ℝ) → 𝒟'(U)`.
4. `d X := regLim q (F (R X))`, where `regLim q` reads a function only on the countable dense set
   `{q k}` of `U` and recovers it at every point of continuity (`regLim_eq`).

Validity for `y = h + g`: Weyl scaling by the constant `a = ⟨y, ρ⟩`
(`ae_internal_addFun_of_eq_const`) gives `D_y(·,·;U) = e^{ξ a} D_{y − a}(·,·;U)`. For each pair
`(q k, q k')` the event `{chainInf ≠ F(·|_U)}` of the recentred field is `σ₀`-measurable
(`measurable_recenter_sigma0`), null for `h₀` (locality and `internal_eq_chainInf`), hence null for
`y` because the law of the mean-zero pairings of `h + g` is absolutely continuous with respect to
that of `h` (Cameron–Martin, `lawPair0_addFun_ac`), which equals that of `h₀`
(`GFFLaw.map_pairProc_eq`). Since
`D_{y − a}(·,·;U)` is a.s. continuous on `U × U` (`continuousOn_internal`), `regLim` recovers it
from the countably many values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Function TopologicalSpace Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Recovering a function from its values on a countable dense set -/

section Reg

/-- The regularization of `m : ℂ → ℂ → [0,∞]` along a sequence `q`:
`⨆ₙ ⨅ {m (q k) (q k') : |q k − z| < 1/(n+1), |q k' − w| < 1/(n+1)}`. -/
def regLim (q : ℕ → ℂ) (m : ℂ → ℂ → ℝ≥0∞) (z w : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ k : ℕ × ℕ,
    if dist (q k.1) z < 1 / ((n : ℝ) + 1) ∧ dist (q k.2) w < 1 / ((n : ℝ) + 1) then
      m (q k.1) (q k.2) else ⊤

theorem measurable_regLim (q : ℕ → ℂ) : Measurable (regLim q) := by
  refine measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w => ?_
  refine Measurable.iSup fun n => Measurable.iInf fun k => ?_
  by_cases hk : dist (q k.1) z < 1 / ((n : ℝ) + 1) ∧ dist (q k.2) w < 1 / ((n : ℝ) + 1)
  · simp only [hk, and_self, ite_true]
    exact (measurable_pi_apply (q k.2)).comp (measurable_pi_apply (q k.1))
  · simp only [hk, ite_false]
    exact measurable_const

/-- `regLim q m` only reads `m` on `{q k} × {q k'}`. -/
theorem regLim_congr (q : ℕ → ℂ) {m m' : ℂ → ℂ → ℝ≥0∞}
    (h : ∀ k k' : ℕ, m (q k) (q k') = m' (q k) (q k')) : regLim q m = regLim q m' := by
  funext z w
  unfold regLim
  congr 1
  funext n
  congr 1
  funext k
  rw [h k.1 k.2]

/-- **Recovery at points of continuity.** If every `q k` lies in `U`, `{q k}` is dense in `U`, and
`m` is continuous within `U × U` at `(z, w) ∈ U × U`, then `regLim q m z w = m z w`. -/
theorem regLim_eq {U : Set ℂ} {q : ℕ → ℂ} (hqU : ∀ k, q k ∈ U)
    (hqd : ∀ z ∈ U, ∀ ε : ℝ, 0 < ε → ∃ k, dist (q k) z < ε) {m : ℂ → ℂ → ℝ≥0∞} {z w : ℂ}
    (hz : z ∈ U) (hw : w ∈ U)
    (hm : ContinuousWithinAt (fun p : ℂ × ℂ => m p.1 p.2) (U ×ˢ U) (z, w)) :
    regLim q m z w = m z w := by
  -- an open-neighbourhood bound near `(z, w)` along `U × U`
  have hnear : ∀ s : Set ℝ≥0∞, IsOpen s → m z w ∈ s → ∃ δ > 0, ∀ a b : ℂ, a ∈ U → b ∈ U →
      dist a z < δ → dist b w < δ → m a b ∈ s := by
    intro s hs hms
    have hev : ∀ᶠ p in 𝓝[U ×ˢ U] (z, w), m p.1 p.2 ∈ s := hm.preimage_mem_nhdsWithin
      (hs.mem_nhds hms)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    refine ⟨δ, hδ, fun a b ha hb haz hbw => ?_⟩
    have hmem : (a, b) ∈ ball (z, w) δ ∩ U ×ˢ U := by
      refine ⟨?_, ha, hb⟩
      rw [mem_ball, Prod.dist_eq]
      exact max_lt haz hbw
    exact hball hmem
  apply le_antisymm
  · -- `≤`: every infimum is at most `m z w`
    refine iSup_le fun n => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hδm⟩ := hnear (Iio (⨅ k : ℕ × ℕ,
      if dist (q k.1) z < 1 / ((n : ℝ) + 1) ∧ dist (q k.2) w < 1 / ((n : ℝ) + 1) then
        m (q k.1) (q k.2) else ⊤)) isOpen_Iio hlt
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k₁, hk₁⟩ := hqd z hz (min δ (1 / ((n : ℝ) + 1))) (lt_min hδ hn)
    obtain ⟨k₂, hk₂⟩ := hqd w hw (min δ (1 / ((n : ℝ) + 1))) (lt_min hδ hn)
    have h1 := hδm (q k₁) (q k₂) (hqU k₁) (hqU k₂) (hk₁.trans_le (min_le_left _ _))
      (hk₂.trans_le (min_le_left _ _))
    have h2 := iInf_le (fun k : ℕ × ℕ =>
      if dist (q k.1) z < 1 / ((n : ℝ) + 1) ∧ dist (q k.2) w < 1 / ((n : ℝ) + 1) then
        m (q k.1) (q k.2) else ⊤) (k₁, k₂)
    simp only [hk₁.trans_le (min_le_right _ _), hk₂.trans_le (min_le_right _ _), and_self,
      ite_true] at h2
    exact (lt_irrefl _ (h2.trans_lt h1))
  · -- `≥`: below `m z w`, eventually every admissible value is larger
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨b, hcb, hb⟩ := exists_between hc
    obtain ⟨δ, hδ, hδm⟩ := hnear (Ioi b) isOpen_Ioi hb
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine hcb.trans_le (le_iSup_of_le n (le_iInf fun k => ?_))
    split_ifs with hk
    · exact (hδm _ _ (hqU k.1) (hqU k.2) (hk.1.trans hn) (hk.2.trans hn)).le
    · exact le_top

end Reg

/-! ## 2. The recentred restriction factors through the mean-zero pairings -/

section Factor

/-- The recentred restriction `x ↦ (x − ⟨x, ρ⟩)|_U` is a measurable function of the mean-zero
pairings `pair0On U x` (Doob–Dynkin; `𝒟'(U)` is standard Borel). -/
theorem exists_measurable_restrict_recenter (O : Opens ℂ) {ρ : TestC}
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ : ∫ x, ρ x = 1) :
    ∃ R : (TestC0On (O : Set ℂ) → ℝ) → DistOn O, Measurable R ∧
      ∀ x : DistC, R (pair0On O x) = restrictTo O (GFFLaw.recenter ρ x) := by
  have hG : Measurable[MeasurableSpace.comap (pair0On (O : Set ℂ)) MeasurableSpace.pi]
      fun x : DistC => restrictTo O (GFFLaw.recenter ρ x) := by
    refine (@measurable_distOn_iff O DistC
      (MeasurableSpace.comap (pair0On (O : Set ℂ)) MeasurableSpace.pi)
      (fun x : DistC => restrictTo O (GFFLaw.recenter ρ x))).2 fun φ => ?_
    set e : TestC0On (O : Set ℂ) :=
      ⟨⟨recTest O ρ φ, integral_recTest O hρ φ⟩, tsupport_recTest_subset O hρO φ⟩
    have he : (fun x : DistC => restrictTo O (GFFLaw.recenter ρ x) φ) =
        (fun X : TestC0On (O : Set ℂ) → ℝ => X e) ∘ pair0On (O : Set ℂ) := by
      funext x
      show GFFLaw.recenter ρ x (inclTest O φ) = x (recTest O ρ φ)
      rw [GFFLaw.recenter_apply]
      rfl
    rw [he]
    exact (measurable_pi_apply e).comp (comap_measurable _)
  obtain ⟨R, hR, hRe⟩ := hG.exists_eq_measurable_comp
  exact ⟨R, hR, fun x => (congrFun hRe x).symm⟩

end Factor

/-! ## 3. Algebra of recentring -/

section Algebra

theorem recenter_addFun_testCont (ρ : TestC) (x : DistC) (g : TestC) :
    GFFLaw.recenter ρ (addFun x (testCont g)) =
      addFun (addConst x (-(addFun x (testCont g) ρ))) (testCont g) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFLaw.recenter, GFFInv.addConst_apply]
  show addFun x (testCont g) φ + (∫ y, φ y) * -(addFun x (testCont g) ρ) =
    addConst x (-(addFun x (testCont g) ρ)) φ + ofCont (testCont g) φ
  rw [GFFInv.addConst_apply]
  show x φ + ofCont (testCont g) φ + (∫ y, φ y) * -(addFun x (testCont g) ρ) =
    x φ + (∫ y, φ y) * -(addFun x (testCont g) ρ) + ofCont (testCont g) φ
  ring

theorem addConst_recenter (ρ : TestC) (y : DistC) :
    addConst (GFFLaw.recenter ρ y) (y ρ) = y := by
  rw [GFFLaw.recenter, GFFLaw.addConst_addConst, neg_add_cancel, GFFLaw.addConst_zero']

end Algebra

/-! ## 4. T1 -/

/-- **T1 (GA4 A10): the `σ₀` internal-metric functional.** For a strong γ-LQG metric `D` and an
open set `U` there is a measurable `d : (TestC0On U → ℝ) → ℂ → ℂ → [0,∞]` such that, for every
whole-plane GFF `h` and every test function `g`, a.s. `D_{h+g}(·,·;U) = c · d(pair0On U (h + g))`
on `U × U` for some `c ∈ (0, ∞)` (`IsSigma0Metric D U d`). -/
theorem exists_isSigma0Metric {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {U : Set ℂ} (hU : IsOpen U) : ∃ d, IsSigma0Metric D U d := by
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · refine ⟨fun _ _ _ => 0, measurable_const, fun P _ h g _ => ae_of_all _ fun ω =>
      ⟨1, one_pos, ENNReal.one_lt_top, fun z hz => ?_⟩⟩
    rw [hUe] at hz
    exact hz.elim
  -- the data
  obtain ⟨ρ, hρU, hρ⟩ := exists_testC_integral_eq_one hU hUne
  set O : Opens ℂ := ⟨U, hU⟩ with hOdef
  obtain ⟨Ω₀, mΩ₀, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  set h₁ : Ω₀ → DistC := fun ω => GFFLaw.recenter ρ (h₀ ω) with hh₁def
  have hh₁ : IsWholePlaneGFF h₁ P₀ :=
    hh₀.addConst ((GFFInv.measurable_pair ρ).comp hh₀.measurable).neg
  obtain ⟨F, hFm, hF⟩ := hD.locality P₀ h₁ (isGFFPlusCont_of_wp hh₁) O
  have hlen₁ := hD.length P₀ h₁ (isGFFPlusCont_of_wp hh₁)
  obtain ⟨R, hRm, hR⟩ := exists_measurable_restrict_recenter O hρU hρ
  have : Nonempty U := hUne.to_subtype
  set q : ℕ → ℂ := fun k => (TopologicalSpace.denseSeq U k : ℂ) with hqdef
  have hqU : ∀ k, q k ∈ U := fun k => (TopologicalSpace.denseSeq U k).2
  have hqd : ∀ z ∈ U, ∀ ε : ℝ, 0 < ε → ∃ k, dist (q k) z < ε := by
    intro z hz ε hε
    obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq U).exists_dist_lt ⟨z, hz⟩ hε
    exact ⟨k, by rw [dist_comm]; exact hk⟩
  refine ⟨fun X => regLim q (F (R X)), (measurable_regLim q).comp (hFm.comp hRm), ?_⟩
  -- validity
  intro Ω _ P _ h g hh
  set y : Ω → DistC := fun ω => addFun (h ω) (testCont g) with hydef
  set a : Ω → ℝ := fun ω => y ω ρ with hadef
  set X₂ : Ω → DistC := fun ω => GFFLaw.recenter ρ (y ω) with hX₂def
  have hym : Measurable y := measurable_addFun.comp (hh.measurable.prodMk measurable_const)
  have ham : Measurable a := (GFFInv.measurable_pair ρ).comp hym
  -- `X₂` is a whole-plane GFF plus a continuous function
  have hX₂ : IsGFFPlusCont X₂ P := by
    have h1 := isGFFPlusCont_addFun_of_wp (hh.addConst ham.neg)
      (measurable_const : Measurable fun _ : Ω => testCont g)
    have e : (fun ω => addFun (addConst (h ω) ((-a) ω)) (testCont g)) = X₂ := by
      funext ω
      exact (recenter_addFun_testCont ρ (h ω) g).symm
    rwa [e] at h1
  -- the a.s. events
  have hlen₂ := hD.length P X₂ hX₂
  have hweyl := hD.ae_internal_addFun_of_eq_const hX₂
  -- transfer of the locality identity at the countably many pairs `(q k, q k')`
  have htr : ∀ k k' : ℕ, ∀ᵐ ω ∂P,
      (D (X₂ ω)).chainInf U (q k) (q k') = F (restrictTo O (X₂ ω)) (q k) (q k') := by
    intro k k'
    set u := q k
    set v := q k'
    have hf1 : Measurable fun x' : DistC => (D x').chainInf U u v :=
      (ContMetric.measurable_chainInf U).comp
        (hD.measurable.prodMk (measurable_const (a := (u, v))))
    have hf2 : Measurable fun x' : DistC => F (restrictTo O x') u v :=
      (measurable_pi_apply v).comp ((measurable_pi_apply u).comp
        (hFm.comp (measurable_restrictTo O)))
    have hB' : MeasurableSet {x' : DistC | (D x').chainInf U u v ≠ F (restrictTo O x') u v} :=
      (measurableSet_eq_fun hf1 hf2).compl
    have hB : MeasurableSet[GFFLaw.sigma0]
        (GFFLaw.recenter ρ ⁻¹' {x' : DistC | (D x').chainInf U u v ≠ F (restrictTo O x') u v}) :=
      GFFLaw.measurable_recenter_sigma0 hρ hB'
    obtain ⟨T, hT, hTB⟩ := MeasurableSpace.measurableSet_comap.1 hB
    -- null for the reference field
    have h0 : lawPair0 h₀ P₀ T = 0 := by
      rw [lawPair0, Measure.map_apply (measurable_pair0_comp hh₀) hT]
      have e : (fun ω => pair0 (h₀ ω)) ⁻¹' T = h₀ ⁻¹' (GFFLaw.ev0 ⁻¹' T) := rfl
      rw [e, hTB, measure_eq_zero_iff_ae_notMem]
      filter_upwards [hlen₁, hF] with ω hl hFω
      show ¬ ((D (h₁ ω)).chainInf U u v ≠ F (restrictTo O (h₁ ω)) u v)
      rw [not_not, ← ContMetric.internal_eq_chainInf _ hl hU]
      exact hFω u (hqU k) v (hqU k')
    -- the laws of the mean-zero pairings
    have hlaw : lawPair0 h P = lawPair0 h₀ P₀ := GFFLaw.map_pairProc_eq hh hh₀
    have hac := lawPair0_addFun_ac hh g
    have h0y : lawPair0 (fun ω => addFun (h ω) (testCont g)) P T = 0 := hac (hlaw ▸ h0)
    rw [lawPair0, Measure.map_apply (measurable_pair0_addFun hh g) hT] at h0y
    have e : (fun ω => pair0 (addFun (h ω) (testCont g))) ⁻¹' T = y ⁻¹' (GFFLaw.ev0 ⁻¹' T) := rfl
    rw [e, hTB] at h0y
    refine (measure_eq_zero_iff_ae_notMem.1 h0y).mono fun ω hω => ?_
    have hω' : ¬ ((D (X₂ ω)).chainInf U u v ≠ F (restrictTo O (X₂ ω)) u v) := hω
    exact not_not.1 hω'
  have htr' : ∀ᵐ ω ∂P, ∀ k k' : ℕ,
      (D (X₂ ω)).chainInf U (q k) (q k') = F (restrictTo O (X₂ ω)) (q k) (q k') := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact htr k
  filter_upwards [hlen₂, hweyl, htr'] with ω hl hw ht
  refine ⟨ENNReal.ofReal (Real.exp (xiGamma γ * a ω)), ENNReal.ofReal_pos.2 (Real.exp_pos _),
    ENNReal.ofReal_lt_top, fun z hz w hw' => ?_⟩
  -- Weyl scaling by the constant `a ω`
  have hy : addFun (X₂ ω) (ContinuousMap.const ℂ (a ω)) = y ω :=
    addConst_recenter ρ (y ω)
  have h1 := hw (ContinuousMap.const ℂ (a ω)) U (xiGamma γ * a ω) hU (fun _ _ => rfl) z w
  rw [hy] at h1
  show (D (y ω)).internal U z w = _
  rw [h1]
  congr 1
  -- recovery of the internal metric of `X₂ ω` from its countably many values
  have hRX : R (pair0On U (y ω)) = restrictTo O (X₂ ω) := hR (y ω)
  show (D (X₂ ω)).internal U z w = regLim q (F (R (pair0On U (y ω)))) z w
  rw [hRX, ← regLim_congr q (m := fun z w => (D (X₂ ω)).internal U z w) fun k k' => by
    rw [ContMetric.internal_eq_chainInf _ hl hU]
    exact ht k k']
  exact (regLim_eq hqU hqd hz hw'
    ((ContMetric.continuousOn_internal _ hl hU) (z, w) ⟨hz, hw'⟩)).symm

end SmallGammaGeodesics.CC
