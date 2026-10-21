import SmallGammaGeodesics.CC.GoodAnnulusMeasForm
import SmallGammaGeodesics.CC.LocalityConf

/-!
# [3] Lemma 3.8: the good-annulus event of `(D_h, D^ϕ)` is local modulo constants (CC9a, T2)

Source: Gwynne–Miller arXiv:1905.00384 ([3]), Lemma 3.8, in the corrected form of
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D14**: `E_r(z)` is a.s. an
event of `σ((h − h_{4r}(z))|_{𝔸_{r/2,2r}(z)})`, for a coupling `(h, h̄, f)` of `(ϕ, W, V)` and
`𝔸_{r/2,2r}(z) ⊆ V`.

The proof is GM's (`GM.gm_L3_7meas`, l. 1345–1360) with three changes:
* **modulo constants**: `J = D_h(·,·;𝔸)` and `J' = D^ϕ(·,·;𝔸)` are a.s. measurable functions of
  `(h − h_{4r}(z))|_𝔸` once multiplied by `e^{−ξ h_{4r}(z)}` (CC2's
  `exists_internal_eq_restrict_addConst`, `exists_confMetric_eq_restrict_addConst`), and the
  event is invariant under multiplying both by one constant (`goodAnnulusI_smul`);
* **the second function**: `J'` is not a metric on `ℂ`. The event is read on the countably many
  values of `J'` at the pairs of a dense sequence `q` of `𝔸`, through the regularization
  `denseUp q` (`CC/GoodAnnulusDense.lean`): a.s. `J'` is continuous on `𝔸 × 𝔸`, so
  `denseUp q (J'(q·, q·)) = J'` on `𝔸 × 𝔸` (`denseUp_eq`), and only these values enter the event
  (`goodAnnulusI_congr_right`). The `bdFun` of a regularization is a countable formula
  (`bdFun_denseUp`), which makes the D-form of condition 2 coanalytic;
* **universal measurability**: on the Borel set where `D_h` is a boundedly compact length metric,
  the event is `gaCompareD ∧ gaLongD ∧ gaAround` (`goodAnnulusI_iff_dForm`), which is universally
  measurable (`CC/GoodAnnulusMeasForm.lean`). Saturation (`LocalEvent.aeEventIn_of_saturated`)
  closes the argument, with `Y = (h, h̄ + f)` and the data `R` = the scaled values of `J`, `J'` at
  the dense pairs.

Main results:
* `aeEventIn_confGoodAnnulus`: Lemma 3.8 for one annulus;
* **T2** `isAnnulusLocal_confGoodEvent`: the event family `confGoodEvent` (activated where
  `𝔸_{r/2,2r}(w) ⊆ V`) is `IsAnnulusLocal` with `c₀ = 4` and any `s₁ ≤ 1/8`, `s₂ ≥ 1/2`; in
  particular with CC7's parameters `(4, 1/16, 1/2)` (`isAnnulusLocal_confGoodEvent_cc7`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-- a dense sequence of a nonempty subset of `ℂ` -/
lemma exists_denseSeq_of_nonempty {S : Set ℂ} (hS : S.Nonempty) :
    ∃ q : ℕ → ℂ, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  have : Nonempty S := hS.to_subtype
  refine ⟨fun n => (TopologicalSpace.denseSeq S n : ℂ), fun n => (TopologicalSpace.denseSeq S n).2,
    fun x hx => ?_⟩
  rw [_root_.mem_closure_iff]
  intro o ho hxo
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
  exact ⟨_, hn, n, rfl⟩

lemma annulus_nonempty (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (annulus z (r / 2) (2 * r) : Set ℂ).Nonempty := by
  refine ⟨z + (r : ℂ), ?_⟩
  show r / 2 < ‖z + (r : ℂ) - z‖ ∧ ‖z + (r : ℂ) - z‖ < 2 * r
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
  constructor <;> linarith

section Meas
variable {γ : ℝ} {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}

/-- **[3] Lemma 3.8** (CC0 D14): for a coupling `(h, h̄, f)` of `(ϕ, W, V)` and
`𝔸_{r/2,2r}(z) ⊆ V`, the event `E_r(z)` is a.s. an event of
`σ((h − h_{4r}(z))|_{𝔸_{r/2,2r}(z)})`. -/
theorem aeEventIn_confGoodAnnulus (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω))
    {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (A C' : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) z))
      (annulus z (r / 2) (2 * r)))
      {ω | confGoodAnnulus D ϕ α A C' r z (h ω) (hbar ω) (f ω)} := by
  set U := annulus z (r / 2) (2 * r) with hUdef
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have hϕU : IsConfNbhd ϕ W U := hϕ.mono hUo hUV
  -- the random constant `c = −h_{4r}(z)` and CC2's locality modulo constants
  set c : Ω → ℝ := fun ω => -circleAvg (h ω) (4 * r) z with hcdef
  have hcm : Measurable c := ((measurable_circleAvg_left (4 * r) z).comp hh.measurable).neg
  obtain ⟨G₁, hG₁, hG₁ae⟩ := exists_internal_eq_restrict_addConst hD U hh hcm
  obtain ⟨G₂, hG₂, hG₂ae⟩ := exists_confMetric_eq_restrict_addConst hD hϕ U hUV hhb hf hc hcm
  -- a dense sequence of `U`
  obtain ⟨q, hqU, hqd⟩ := exists_denseSeq_of_nonempty (annulus_nonempty z hr)
  -- the data
  have hDm : Measurable D := hD.measurable
  let k : DistC → ℝ≥0∞ := fun g => ENNReal.ofReal (Real.exp (xiGamma γ * -circleAvg g (4 * r) z))
  have hk : Measurable k := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_circleAvg_left (4 * r) z).neg))
  have hk0 : ∀ g, k g ≠ 0 := fun g => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hkt : ∀ g, k g ≠ ⊤ := fun g => ENNReal.ofReal_ne_top
  let x' : DistC → ℕ × ℕ → ℝ≥0∞ := fun g' p => (D g').chainInf (ϕ '' U) (ϕ (q p.1)) (ϕ (q p.2))
  have hx' : Measurable x' := measurable_pi_iff.2 fun p =>
    GM.measurable_chainInf_comp hDm measurable_const measurable_const (ϕ '' U)
  let Y : Ω → DistC × DistC := fun ω => (h ω, addFun (hbar ω) (f ω))
  have hY : Measurable Y := hh.measurable.prodMk (measurable_addFun.comp (hhb.measurable.prodMk hf))
  let R : DistC × DistC → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := fun b =>
    (fun p => k b.1 * (D b.1).chainInf U (q p.1) (q p.2), fun p => k b.1 * x' b.2 p)
  have hR : Measurable R := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun p => ?_) (measurable_pi_iff.2 fun p => ?_)
    · exact (hk.comp measurable_fst).mul
        (GM.measurable_chainInf_comp (hDm.comp measurable_fst) measurable_const measurable_const _)
    · exact (hk.comp measurable_fst).mul ((measurable_pi_apply p).comp (hx'.comp measurable_snd))
  let G : DistOn U → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := fun x =>
    (fun p => G₁ x (q p.1) (q p.2), fun p => G₂ x (q p.1) (q p.2))
  have hG : Measurable G := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun p => ?_) (measurable_pi_iff.2 fun p => ?_)
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hG₁)
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hG₂)
  have hV : Measurable[fieldSigma (fun ω => addConst (h ω) (c ω)) U]
      fun ω => G (restrictTo U (addConst (h ω) (c ω))) :=
    hG.comp (Measurable.of_comap_le le_rfl)
  have hVR : ∀ᵐ ω ∂P, G (restrictTo U (addConst (h ω) (c ω))) = R (Y ω) := by
    filter_upwards [hG₁ae, hG₂ae, hD.length P h (isGFFPlusCont_of_wp hh),
      ae_confMetric_eq_chainInf hD hhb hf] with ω h1 h2 h3 h4
    refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
    · show G₁ _ (q p.1) (q p.2) = k (h ω) * (D (h ω)).chainInf U (q p.1) (q p.2)
      rw [← h1 _ (hqU _) _ (hqU _), (D (h ω)).internal_eq_chainInf h3 hUo]
    · show G₂ _ (q p.1) (q p.2) = k (h ω) * x' (addFun (hbar ω) (f ω)) p
      rw [← h2 _ (hqU _) _ (hqU _), h4 ϕ W U hϕU]
  -- the Borel set carrying the law
  set Wb : Set (DistC × DistC) := {b | D b.1 ∈ LocalEvent.lenSet} with hWbdef
  have hW : MeasurableSet Wb := LocalEvent.measurableSet_lenSet.preimage (hDm.comp measurable_fst)
  have hYW : ∀ᵐ ω ∂P, Y ω ∈ Wb :=
    GM.ae_mem_lenSet dfgpsLem3_8_holds hγ hγ2 (GM.gm_eq1_15 hγ hD) P h hh
  -- the event in terms of `Y`
  set B : Set (DistC × DistC) :=
    {b | GM.goodAnnulusI ((D b.1).internal U) (denseUp q (x' b.2)) α A C' r z} with hBdef
  have hF : Measurable fun p : (DistC × DistC) × ℂ × ℂ => denseUp q (x' p.1.2) p.2.1 p.2.2 :=
    measurable_denseUp_comp q (hx'.comp measurable_fst.snd) measurable_snd.fst measurable_snd.snd
  have hFb : Measurable fun p : (DistC × DistC) × ℂ =>
      GM.bdFun (denseUp q (x' p.1.2)) (annulus z (r / 2) (2 * r)) p.2 := by
    have e : (fun p : (DistC × DistC) × ℂ =>
        GM.bdFun (denseUp q (x' p.1.2)) (annulus z (r / 2) (2 * r)) p.2) =
        fun p => denseBd q U (x' p.1.2) p.2 := funext fun p => bdFun_denseUp hUo hqd _ _
    rw [e]
    have hpair : Measurable fun p : (DistC × DistC) × ℂ => (x' p.1.2, p.2) :=
      Measurable.prodMk (Measurable.comp (g := x') (f := fun p : (DistC × DistC) × ℂ => p.1.2)
        hx' measurable_fst.snd) measurable_snd
    exact Measurable.comp (g := fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ => denseBd q U p.1 p.2)
      (f := fun p : (DistC × DistC) × ℂ => (x' p.1.2, p.2)) (measurable_denseBd q U) hpair
  set S : Set (DistC × DistC) := {b | gaCompareD (D b.1) (denseUp q (x' b.2)) α C' r z} ∩
    ({b | gaLongD (D b.1) (denseUp q (x' b.2)) α r z} ∩ Prod.fst ⁻¹' GM.gaAround D α A r z)
    with hSdef
  have hD1 : Measurable fun b : DistC × DistC => D b.1 := hDm.comp measurable_fst
  have hSU : UMeasurableSet S :=
    (uMeasurableSet_gaCompareD (Dm := fun b : DistC × DistC => D b.1)
      (F := fun b : DistC × DistC => denseUp q (x' b.2)) hD1 hF α C' r z).inter
      ((uMeasurableSet_gaLongD (Dm := fun b : DistC × DistC => D b.1)
        (F := fun b : DistC × DistC => denseUp q (x' b.2)) hD1 hF α r z hFb).inter
        ((GM.uMeasurableSet_gaAround hDm α A r z).preimage measurable_fst))
  have hBW : ∀ b ∈ Wb, (b ∈ B ↔ b ∈ S) := by
    rintro ⟨g, g'⟩ hb
    have hl := LocalEvent.isLength_of_mem_lenSet hb
    have := GM.properSpace_of_bcpt _ (LocalEvent.bcpt_of_mem_lenSet hb)
    exact goodAnnulusI_iff_dForm hl (denseUp q (x' g')) hα hα1 hr
  have hB : NullMeasurableSet B (P.map Y) := by
    refine (hSU.nullMeasurableSet (P.map Y)).congr ?_
    filter_upwards [(ae_map_iff hY.aemeasurable hW).2 hYW] with b hb
    exact propext (hBW b hb).symm
  -- saturation: equal data give the same event
  have hsat : ∀ b₁ ∈ Wb, ∀ b₂ ∈ Wb, R b₁ = R b₂ → b₁ ∈ B → b₂ ∈ B := by
    rintro ⟨g₁, g₁'⟩ hb₁ ⟨g₂, g₂'⟩ hb₂ he hB1
    have l1 := LocalEvent.isLength_of_mem_lenSet hb₁
    have l2 := LocalEvent.isLength_of_mem_lenSet hb₂
    have eJ : ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
        k g₁ * (D g₁).internal U u v = k g₂ * (D g₂).internal U u v := by
      have hE : EqOn (fun p : ℂ × ℂ => k g₁ * (D g₁).internal U p.1 p.2)
          (fun p : ℂ × ℂ => k g₂ * (D g₂).internal U p.1 p.2) ((U : Set ℂ) ×ˢ (U : Set ℂ)) := by
        refine EqOn.of_subset_closure (s := range (Prod.map q q)) ?_
          ((ENNReal.continuous_const_mul (hkt g₁)).comp_continuousOn
            ((D g₁).continuousOn_internal l1 hUo))
          ((ENNReal.continuous_const_mul (hkt g₂)).comp_continuousOn
            ((D g₂).continuousOn_internal l2 hUo)) ?_ ?_
        · rintro _ ⟨⟨i, j⟩, rfl⟩
          have e1 := congrFun (congrArg Prod.fst he) (i, j)
          show k g₁ * (D g₁).internal U (q i) (q j) = k g₂ * (D g₂).internal U (q i) (q j)
          rw [(D g₁).internal_eq_chainInf l1 hUo, (D g₂).internal_eq_chainInf l2 hUo]
          exact e1
        · rintro _ ⟨⟨i, j⟩, rfl⟩
          exact ⟨hqU i, hqU j⟩
        · rw [range_prodMap, closure_prod_eq]
          exact prod_mono hqd hqd
      exact fun u hu v hv => hE (mk_mem_prod hu hv)
    have eJ' : ∀ u v, k g₁ * denseUp q (x' g₁') u v = k g₂ * denseUp q (x' g₂') u v := by
      intro u v
      have hx : (fun p => k g₁ * x' g₁' p) = fun p => k g₂ * x' g₂' p := congrArg Prod.snd he
      rw [← denseUp_const_mul (hk0 g₁) (hkt g₁), ← denseUp_const_mul (hk0 g₂) (hkt g₂), hx]
    have hB1' : GM.goodAnnulusI ((D g₁).internal U) (denseUp q (x' g₁')) α A C' r z := hB1
    have h1 := (goodAnnulusI_smul (hk0 g₁) (hkt g₁)).2 hB1'
    have h2 := (goodAnnulusI_congr hα hα1 hr eJ (fun u _ v _ => eJ' u v)).1 h1
    exact (goodAnnulusI_smul (hk0 g₂) (hkt g₂)).1 h2
  obtain ⟨F, hFm, hFae⟩ := LocalEvent.aeEventIn_of_saturated hY hR hV hVR hW hB hYW hsat
  refine ⟨F, hFm, EventuallyEq.trans ?_ hFae⟩
  -- a.s. the event equals `Y⁻¹ B`
  filter_upwards [ae_isLength_addFun hD hhb hf] with ω hL'
  have hcont := continuousOn_confMetric hϕU hL'
  have e : ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
      confMetric D ϕ U (hbar ω) (f ω) u v = denseUp q (x' (addFun (hbar ω) (f ω))) u v := by
    intro u hu v hv
    have hx : x' (addFun (hbar ω) (f ω)) =
        fun ij => confMetric D ϕ U (hbar ω) (f ω) (q ij.1) (q ij.2) := by
      funext ij
      show (D (addFun (hbar ω) (f ω))).chainInf (ϕ '' U) (ϕ (q ij.1)) (ϕ (q ij.2)) =
        (D (addFun (hbar ω) (f ω))).internal (ϕ '' U) (ϕ (q ij.1)) (ϕ (q ij.2))
      rw [(D (addFun (hbar ω) (f ω))).internal_eq_chainInf hL' hϕU.isOpen_image]
    rw [hx, denseUp_eq hUo hqd hcont hu hv]
  exact propext (goodAnnulusI_congr_right hα hα1 hr e)

/-- **T2 ([3] Lemma 3.8, CC0 D14)**: the event family `w, r ↦ E_r(w)` (activated by `act`, with
`act w r → 𝔸_{r/2,2r}(w) ⊆ V`) is annulus-local in the sense of CC7's covering lemma, with `c₀ = 4`
and any `s₁ ≤ 1/8`, `s₂ ≥ 1/2`. -/
theorem isAnnulusLocal_confGoodEvent (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω))
    {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (A C' : ℝ) {act : ℂ → ℝ → Prop}
    (hact : ∀ w r, 0 < r → act w r → (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ≤ 1 / 8) (hs₂ : 1 / 2 ≤ s₂) :
    IsAnnulusLocal P h (confGoodEvent D ϕ α A C' act h hbar f) 4 s₁ s₂ := by
  intro w r hr
  by_cases ha : act w r
  · obtain ⟨F, hF, hFae⟩ :=
      aeEventIn_confGoodAnnulus hγ hγ2 hD hϕ hh hhb hf hc hα hα1 A C' hr (hact w r hr ha)
    refine ⟨F, GM.fieldSigma_mono _ ?_ _ hF, ?_⟩
    · intro x hx
      have hx' : r / 2 < ‖x - w‖ ∧ ‖x - w‖ < 2 * r := hx
      show s₁ * (4 * r) < ‖x - w‖ ∧ ‖x - w‖ < s₂ * (4 * r)
      have h1 : s₁ * (4 * r) ≤ 1 / 8 * (4 * r) := mul_le_mul_of_nonneg_right hs₁ (by positivity)
      have h2 : 1 / 2 * (4 * r) ≤ s₂ * (4 * r) := mul_le_mul_of_nonneg_right hs₂ (by positivity)
      constructor <;> linarith [hx'.1, hx'.2]
    · rw [confGoodEvent_of_act ha]
      exact hFae
  · refine ⟨univ, MeasurableSet.univ, ?_⟩
    rw [confGoodEvent_of_not_act ha]

/-- **T2 with CC7's parameters** `(c₀, s₁, s₂) = (4, 1/16, 1/2)` (CC7 suggestion 3, `N = 16`) -/
theorem isAnnulusLocal_confGoodEvent_cc7 (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω))
    {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (A C' : ℝ) {act : ℂ → ℝ → Prop}
    (hact : ∀ w r, 0 < r → act w r → (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V) :
    IsAnnulusLocal P h (confGoodEvent D ϕ α A C' act h hbar f) 4 (1 / 16) (1 / 2) :=
  isAnnulusLocal_confGoodEvent hγ hγ2 hD hϕ hh hhb hf hc hα hα1 A C' hact (by norm_num) le_rfl

end Meas

end SmallGammaGeodesics.CC
