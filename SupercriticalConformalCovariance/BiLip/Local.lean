import SupercriticalConformalCovariance.BiLip.LocalTools
import SupercriticalConformalCovariance.BiLip.Lemma21
import SupercriticalConformalCovariance.BiLip.Port.FieldShift
import SupercriticalConformalCovariance.Lemma31.Realized

/-!
# Lemma 2.1, step 4: the good events are local modulo an additive constant

Paper l. 136–138: "The events are local modulo an additive constant, so the annular near-independence
estimate applies to the nonlinear pullback as well." This module proves `GoodEventsLocal`
(`goodEventsLocal_proved`). For one instance and a small pair `(z, r)` (`GeomGood`), with
`c = h_{3r}(z)` and `h_c = h − c` (the centred field of `localSigma`):

1. **Source.** `D_h = e^{ξ c} D_{h_c}` (Weyl, SLU `ae_addConst_eq_mul`), so `D_h(across)` and
   `D_h(around)` are `e^{ξ c}` times those of `D_{h_c}`; the latter are pathwise local on the annulus
   `A_0 = A_{3r/7, 9r/4}(z)` and Borel, hence a.s. a measurable function of `h_c|_{A_0}` (the Lemma 3.3 proof's single-law
   local functional).
2. **Target.** The shifted target field `h_c^φ = h^φ − c` has the realization `(g₀, k − c)` (
   `isDomainRealization_forward_add_const`); with the cut-off whole-plane field `G_c = g₀ + χ_m (k − c)`, the
   target round-annulus quantities are `e^{ξ c}` times the whole-plane `aroundDist`/`acr` of `D_{G_c}`
   (`WeylCmp`, `m = M = c`). These are pathwise local on `W = A_{17ρ/32, 63ρ/32}(φ z)`, where
   `G_c|_W = h_c^φ|_W` is a measurable function of `h_c|_{A_0}` for every field (
   `exists_measurable_forward_restrict`, since `W ⊆ φ(A_0)`).
3. The common factor `e^{ξ c}` cancels, so each good event is a.s. equal to an event of `σ(h_c|_{A_0})`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale aroundDist EuclideanAnnulus IsStrongLQGMetric
  IsLFPPExponent)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr around cann ann)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open LQGMetric (DistC DistOn restrictTo addFun addConst ofCont IsGFFPlusCont circleAvg)
open LQGMetric.Blueprint (AEEventIn fieldSigma annulus)
open SupercriticalConformalCovariance.Cover (localSigma)
open SupercriticalConformalCovariance.Domain (exW exWO cutF restrictOn)
open SupercriticalConformalCovariance.BiLip.PortTan (locCoord)
open SupercriticalConformalCovariance.BiLip.PortT (constOn)

/-! ## Restrictions of constant shifts -/

theorem restrictTo_addConst_eq (U : Opens ℂ) (h : DistC) (t : ℝ) :
    restrictTo U (addConst h t) = restrictTo U h + constOn U t := by
  ext φ
  have hcoe : ⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) = ⇑φ :=
    SupercriticalConformalCovariance.Domain.coe_monoCLM le_top φ
  show addConst h t (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) =
    h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) + constOn U t φ
  rw [SupercriticalConformalCovariance.BiLip.PortT.constOn_apply]
  show (h + ofCont (ContinuousMap.const ℂ t)) _ = _
  rw [add_apply, LQGMetric.ofCont_apply, hcoe]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [ContinuousMap.const_apply]
  ring

/-! ## The geometry of the locality annuli -/

section Geometry

variable {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r ε : ℝ}

/-- the target locality window `A_{17ρ/32, 63ρ/32}(φ z)` -/
def tgtWindow (φ : ℂ → ℂ) (z : ℂ) (r : ℝ) : Opens ℂ :=
  annulus (φ z) (17 / 32 * (r * ‖deriv φ z‖)) (63 / 32 * (r * ‖deriv φ z‖))

/-- the source locality annulus of `localSigma`, `A_{3r/7, 9r/4}(z)` -/
def srcWindow (z : ℂ) (r : ℝ) : Opens ℂ := annulus z (1 / 7 * (3 * r)) (3 / 4 * (3 * r))

theorem mem_annulus_iff {c y : ℂ} {a b : ℝ} : y ∈ (annulus c a b : Set ℂ) ↔ a < ‖y - c‖ ∧ ‖y - c‖ < b :=
  Iff.rfl

theorem tgtWindow_subset_closedBall (hr : 0 < r) (hφd : deriv φ z ≠ 0) :
    (tgtWindow φ z r : Set ℂ) ⊆ closedBall (φ z) (3 * (r * ‖deriv φ z‖)) := by
  intro y hy
  have hy' : 17 / 32 * (r * ‖deriv φ z‖) < ‖y - φ z‖ ∧ ‖y - φ z‖ < 63 / 32 * (r * ‖deriv φ z‖) := hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  have : 0 < r * ‖deriv φ z‖ := mul_pos hr (norm_pos_iff.2 hφd)
  linarith [hy'.2]

/-- the target window lies in `φ(A_0)` -/
theorem tgtWindow_subset_image (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32) (hinj : InjOn φ U) :
    (tgtWindow φ z r : Set ℂ) ⊆ φ '' (srcWindow z r : Set ℂ) := by
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  intro y hy
  have hyB := tgtWindow_subset_closedBall hr hG.2.1 hy
  obtain ⟨hxB, hφx, hup, hlo, -⟩ := geom_inv hG hinj hyB
  have hy' : 17 / 32 * (r * ‖deriv φ z‖) < ‖y - φ z‖ ∧ ‖y - φ z‖ < 63 / 32 * (r * ‖deriv φ z‖) := hy
  refine ⟨Function.invFunOn φ U y, ?_, hφx⟩
  have h1 : 17 / 32 * r < ‖y - φ z‖ / ‖deriv φ z‖ := by rw [lt_div_iff₀ hφd]; nlinarith [hy'.1]
  have h2 : ‖y - φ z‖ / ‖deriv φ z‖ < 63 / 32 * r := by rw [div_lt_iff₀ hφd]; nlinarith [hy'.2]
  show 1 / 7 * (3 * r) < ‖Function.invFunOn φ U y - z‖ ∧
    ‖Function.invFunOn φ U y - z‖ < 3 / 4 * (3 * r)
  constructor <;> nlinarith

theorem annulus_toSet_subset_tgtWindow {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (h1 : 17 / 32 * (r * ‖deriv φ z‖) < a) (h2 : b < 63 / 32 * (r * ‖deriv φ z‖)) :
    SupercriticalLQGUniqueness.EuclideanAnnulus.toSet
      (⟨(φ z, a, b), ha, hab⟩ : EuclideanAnnulus) ⊆ tgtWindow φ z r := by
  intro y hy
  rw [annulus_toSet_mem ha hab, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hy
  simp only [dist_eq_norm] at hy
  show 17 / 32 * (r * ‖deriv φ z‖) < ‖y - φ z‖ ∧ ‖y - φ z‖ < 63 / 32 * (r * ‖deriv φ z‖)
  constructor <;> linarith [hy.1, hy.2]

theorem cann_subset_tgtWindow {a b : ℝ} (h1 : 17 / 32 * (r * ‖deriv φ z‖) < a)
    (h2 : b < 63 / 32 * (r * ‖deriv φ z‖)) : cann (φ z) a b ⊆ tgtWindow φ z r := by
  intro y hy
  have hy' : a ≤ dist y (φ z) ∧ dist y (φ z) ≤ b := hy
  rw [dist_eq_norm] at hy'
  show 17 / 32 * (r * ‖deriv φ z‖) < ‖y - φ z‖ ∧ ‖y - φ z‖ < 63 / 32 * (r * ‖deriv φ z‖)
  constructor <;> linarith [hy'.1, hy'.2]

theorem cann_subset_srcWindow (hr : 0 < r) : cann z (r / 2) r ⊆ srcWindow z r := by
  intro y hy
  have hy' : r / 2 ≤ dist y z ∧ dist y z ≤ r := hy
  rw [dist_eq_norm] at hy'
  show 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r)
  constructor <;> linarith [hy'.1, hy'.2]

theorem ann_subset_srcWindow : ann z r (2 * r) ⊆ srcWindow z r := by
  intro y hy
  have hy' : r < dist y z ∧ dist y z < 2 * r := hy
  rw [dist_eq_norm] at hy'
  show 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r)
  constructor <;> linarith [hy'.1, hy'.2]

theorem srcWindow_closure_subset (hG : GeomGood φ U z r ε) :
    closure (srcWindow z r : Set ℂ) ⊆ U := by
  have hr := hG.1
  refine (closure_minimal ?_ isClosed_closedBall).trans
    ((closedBall_subset_closedBall (by linarith : 3 / 4 * (3 * r) ≤ 4 * r)).trans hG.2.2.1)
  intro y hy
  have hy' : 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r) := hy
  rw [Metric.mem_closedBall, dist_eq_norm]; exact hy'.2.le

theorem srcWindow_bounded (z : ℂ) (r : ℝ) : Bornology.IsBounded (srcWindow z r : Set ℂ) := by
  refine (isBounded_ball (x := z) (r := 3 / 4 * (3 * r))).subset fun y hy => ?_
  have hy' : 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r) := hy
  rw [Metric.mem_ball, dist_eq_norm]; exact hy'.2

end Geometry

/-! ## The centred field and its scaling -/

/-- the circle-average constant of `localSigma` and the centred field -/
def ctr (h : DistC) (z : ℂ) (r : ℝ) : ℝ := circleAvg h (3 * r) z

theorem addConst_ctr_eq (h : DistC) (c : ℝ) : addConst (addConst h (-c)) c = h := by
  rw [LQGMetric.GFFLaw.addConst_addConst, neg_add_cancel, LQGMetric.GFFLaw.addConst_zero']

section Source

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

/-- **Source scaling**: `D_h = e^{ξ c} D_{h − c}`, so the source annulus costs scale by `e^{ξ c}`. -/
theorem ae_source_scale (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    (z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂P,
      acrAt (D (h ω)) z r = ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) *
          acr (D (addConst (h ω) (-ctr (h ω) z r))) z (r / 2) r ∧
      aroundHit (D (h ω)) z r = ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) *
          around (D (addConst (h ω) (-ctr (h ω) z r))) z r (2 * r) := by
  have hcm : Measurable fun ω => ctr (h ω) z r :=
    (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  have hhc : IsGFFPlusCont (fun ω => addConst (h ω) (-ctr (h ω) z r)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (hh.addConst hcm.neg)
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  filter_upwards [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P _ hhc
    ξ Q D hW (fun ω => ctr (h ω) z r)] with ω hω
  have hscale : ∀ x y : ℂ, D (h ω) (x, y) =
      ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) * D (addConst (h ω) (-ctr (h ω) z r)) (x, y) := by
    intro x y
    have := hω (x, y)
    rwa [addConst_ctr_eq] at this
  have h0 : ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) ≠ 0 := ofReal_exp_ne_zero _
  exact ⟨acr_eq_mul_of_dist_scale _ _ _ h0 ENNReal.ofReal_ne_top hscale z (r / 2) r,
    around_eq_mul_of_dist_scale _ _ _ h0 ENNReal.ofReal_ne_top hscale z r (2 * r)⟩

/-- **Source locality**: the centred source annulus costs are a.s. measurable functions of the centred
field on `A_0 = A_{3r/7, 9r/4}(z)`. -/
theorem source_local (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ Ψ₁ Ψ₂ : DistOn (srcWindow z r) → ℝ≥0∞, Measurable Ψ₁ ∧ Measurable Ψ₂ ∧ ∀ᵐ ω ∂P,
      acr (D (addConst (h ω) (-ctr (h ω) z r))) z (r / 2) r =
          Ψ₁ (restrictTo (srcWindow z r) (addConst (h ω) (-ctr (h ω) z r))) ∧
      around (D (addConst (h ω) (-ctr (h ω) z r))) z r (2 * r) =
          Ψ₂ (restrictTo (srcWindow z r) (addConst (h ω) (-ctr (h ω) z r))) := by
  have hcm : Measurable fun ω => ctr (h ω) z r :=
    (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  have hhc : IsGFFPlusCont (fun ω => addConst (h ω) (-ctr (h ω) z r)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (hh.addConst hcm.neg)
  obtain ⟨Φ₁, hΦ₁, h₁⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_local_functional_single (srcWindow z r)
    (measurable_acr_comp hD z (r / 2) r) (isPathwiseLocal_acr hD _ z (r / 2) r (cann_subset_srcWindow hr))
    P hhc
  obtain ⟨Φ₂, hΦ₂, h₂⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_local_functional_single (srcWindow z r)
    (measurable_around_comp hD z hr (by linarith)) (isPathwiseLocal_around hD _ z hr (by linarith)
      ann_subset_srcWindow) P hhc
  refine ⟨fun x => Φ₁ (LQGMetric.pairJ _ x), fun x => Φ₂ (LQGMetric.pairJ _ x),
    hΦ₁.comp (LQGMetric.measurable_pairJ _), hΦ₂.comp (LQGMetric.measurable_pairJ _), ?_⟩
  filter_upwards [h₁, h₂] with ω e₁ e₂
  exact ⟨e₁, e₂⟩

end Source

/-! ## The target side -/

section Target

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

/-- the open set `φ(A_0)` -/
def imgWindow {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V) (z : ℂ) (r : ℝ)
    (hA : (srcWindow z r : Set ℂ) ⊆ U) : Opens ℂ :=
  ⟨φ '' (srcWindow z r : Set ℂ), by
    have hψ := (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ).1.continuousOn
    have hset : φ '' (srcWindow z r : Set ℂ) =
        (V : Set ℂ) ∩ Function.invFunOn φ U ⁻¹' (srcWindow z r : Set ℂ) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨hφ.2.mapsTo (hA hx), ?_⟩
        rw [mem_preimage, hφ.2.injOn.leftInvOn_invFunOn (hA hx)]
        exact hx
      · rintro ⟨hyV, hyA⟩
        refine ⟨_, hyA, ?_⟩
        have hy : y ∈ φ '' (U : Set ℂ) := hφ.2.image_eq.symm ▸ hyV
        exact Function.invFunOn_eq hy
    rw [hset]
    exact hψ.isOpen_inter_preimage V.isOpen (srcWindow z r).isOpen⟩

/-- **Target locality**: for a small pair `(z, r)`, the target round-annulus quantities of the good events
are a.s. `e^{ξ c}` times measurable functions of the centred source field on `A_0`. -/
theorem target_local (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hI : IsInstance Q U V hφ P h g₀ k) {z : ℂ} {r ε : ℝ} (hG : GeomGood φ U z r ε)
    (hε : ε ≤ 1 / 32) {m : ℕ}
    (hm : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ exW V m) :
    ∃ Ψ₁ Ψ₂ : DistOn (srcWindow z r) → ℝ≥0∞, Measurable Ψ₁ ∧ Measurable Ψ₂ ∧ ∀ᵐ ω ∂P,
      tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖)) =
          ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) *
            Ψ₁ (restrictTo (srcWindow z r) (addConst (h ω) (-ctr (h ω) z r))) ∧
      tAcr (D (g₀ ω)) ξ (k ω) (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)) =
          ENNReal.ofReal (Real.exp (ξ * ctr (h ω) z r)) *
            Ψ₂ (restrictTo (srcWindow z r) (addConst (h ω) (-ctr (h ω) z r))) := by
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  set ρ := r * ‖deriv φ z‖ with hρ
  have hρpos : 0 < ρ := mul_pos hr hφd
  obtain ⟨hhn, hR⟩ := hI
  have hh := hhn.1
  set c : Ω → ℝ := fun ω => ctr (h ω) z r with hcdef
  have hcm : Measurable c := (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  -- the shifted realization `(g₀, k − c)` of the target field of `h − c`
  have hR' := SupercriticalConformalCovariance.BiLip.PortT.isDomainRealization_forward_add_const hφ Q hR hcm.neg
  set kc : Ω → C(V, ℝ) := fun ω => k ω + ContinuousMap.const V (-c ω) with hkcdef
  have hkcm : Measurable kc := hR'.2.2.1
  set F : Ω → C(ℂ, ℝ) := fun ω => cutF V m (kc ω) with hFdef
  have hFm : Measurable F :=
    SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) m) hkcm
  set Gc : Ω → DistC := fun ω => addFun (g₀ ω) (F ω) with hGcdef
  have hGc : IsGFFPlusCont Gc P := SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable hR.2.1 hFm
  -- windows
  set W : Opens ℂ := tgtWindow φ z r with hWdef
  have hWball := tgtWindow_subset_closedBall hr hG.2.1 (φ := φ) (z := z)
  have hWE : W ≤ exWO V m := fun y hy => hm (hWball hy)
  have hAU : (srcWindow z r : Set ℂ) ⊆ U := subset_closure.trans (srcWindow_closure_subset hG)
  set B : Opens ℂ := imgWindow hφ z r hAU with hBdef
  have hWB : W ≤ B := tgtWindow_subset_image hG hε hφ.2.injOn
  have hBV : B ≤ V := by
    rintro _ ⟨x, hx, rfl⟩; exact hφ.2.mapsTo (hAU hx)
  obtain ⟨Rm, hRm, hRmeq⟩ := SupercriticalConformalCovariance.BiLip.PortT.exists_measurable_forward_restrict Q hφ
    (A := srcWindow z r) (B := B) hAU (srcWindow_closure_subset hG) (srcWindow_bounded z r) rfl hBV
  -- the two annuli
  have ha₁ : 0 < 9 / 8 * ρ := by positivity
  have hab₁ : 9 / 8 * ρ < 15 / 8 * ρ := by linarith
  set A₁ : EuclideanAnnulus := ⟨(φ z, 9 / 8 * ρ, 15 / 8 * ρ), ha₁, hab₁⟩ with hA₁
  obtain ⟨Φ₁, hΦ₁, h₁⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_local_functional_single W
    (measurable_aroundDist_comp hD A₁)
    (isPathwiseLocal_aroundDist hD W A₁ (annulus_toSet_subset_tgtWindow ha₁ hab₁
      (by linarith) (by linarith))) P hGc
  obtain ⟨Φ₂, hΦ₂, h₂⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_local_functional_single W
    (measurable_acr_comp hD (φ z) (5 / 8 * ρ) (7 / 8 * ρ))
    (isPathwiseLocal_acr hD W (φ z) _ _ (cann_subset_tgtWindow (by linarith) (by linarith))) P hGc
  refine ⟨fun x => Φ₁ (LQGMetric.pairJ W (restrictOn hWB (Rm x))),
    fun x => Φ₂ (LQGMetric.pairJ W (restrictOn hWB (Rm x))),
    hΦ₁.comp ((LQGMetric.measurable_pairJ W).comp ((SupercriticalConformalCovariance.Domain.measurable_restrictOn hWB).comp hRm)),
    hΦ₂.comp ((LQGMetric.measurable_pairJ W).comp ((SupercriticalConformalCovariance.Domain.measurable_restrictOn hWB).comp hRm)),
    ?_⟩
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hR.2.1,
    SupercriticalConformalCovariance.Domain.ae_restrictTo_cutF hR' m, h₁, h₂] with ω hs hcut e₁ e₂
  obtain ⟨hf₀, hL₀, hWeyl⟩ := hs
  -- the restriction chain
  have hTc : confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
      (restrictTo U (h ω) + constOn U (-c ω)) =
      confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
        (restrictTo U (addConst (h ω) (-c ω))) := by
    rw [restrictTo_addConst_eq]
  have hres : restrictTo W (Gc ω) =
      restrictOn hWB (Rm (restrictTo (srcWindow z r) (addConst (h ω) (-c ω)))) := by
    have h1 : restrictTo (exWO V m) (Gc ω) = restrictOn (SupercriticalConformalCovariance.Domain.exWO_le V m)
        (confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
          (restrictTo U (h ω) + constOn U (-c ω))) := by
      ext φ'
      exact hcut φ'
    rw [← SupercriticalConformalCovariance.Domain.restrictOn_restrictTo hWE, h1, SupercriticalConformalCovariance.Lemma31.restrictOn_restrictOn, hTc]
    have h2 := hRmeq (restrictTo U (addConst (h ω) (-c ω)))
    have h3 : restrictOn hAU (restrictTo U (addConst (h ω) (-c ω))) =
        restrictTo (srcWindow z r) (addConst (h ω) (-c ω)) :=
      SupercriticalConformalCovariance.Domain.restrictOn_restrictTo hAU _
    rw [h3] at h2
    rw [← h2, SupercriticalConformalCovariance.Lemma31.restrictOn_restrictOn]
  -- the Weyl identification `e = e^{ξ c} · D_{G_c}` on `exW V m`
  have hE : ∀ q, D (Gc ω) q = weylScale (ξ : ℝ) (F ω) (D (g₀ ω)) q := fun q =>
    (congrFun (hWeyl (F ω)) q).symm
  have hkF : ∀ y (hy : y ∈ exW (V : Set ℂ) m), c ω ≤ k ω ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hy⟩ - F ω y ∧
      k ω ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hy⟩ - F ω y ≤ c ω := by
    intro y hy
    have : F ω y = k ω ⟨y, SupercriticalConformalCovariance.Domain.exW_subset _ m hy⟩ - c ω := by
      rw [hFdef]; simp only
      rw [SupercriticalConformalCovariance.Domain.cutF_eq V m (kc ω) y hy]
      simp [hkcdef, sub_eq_add_neg]
    rw [this]; constructor <;> linarith
  have hξ0 : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  have hR1 : ball (φ z) (15 / 8 * ρ) \ closedBall (φ z) (9 / 8 * ρ) ⊆ exW (V : Set ℂ) m := by
    intro y hy
    refine hm (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy.1))
  have hR2 : closedBall (φ z) (7 / 8 * ρ) \ ball (φ z) (5 / 8 * ρ) ⊆ exW (V : Set ℂ) m := by
    intro y hy
    exact hm (closedBall_subset_closedBall (by linarith) hy.1)
  have hexV := SupercriticalConformalCovariance.Domain.exW_subset (V : Set ℂ) m
  have eq₁ : tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * ρ) (15 / 8 * ρ) =
      ENNReal.ofReal (Real.exp (ξ * c ω)) * aroundDist (D (Gc ω)) A₁ :=
    le_antisymm (tAround_le (k ω) hξ0 hf₀ V.isOpen hE hexV hkF (φ z) ha₁ hab₁ hR1)
      (le_tAround (k ω) hξ0 hf₀ hL₀ V.isOpen hE hexV hkF (φ z) ha₁ hab₁ hR1)
  have eq₂ : tAcr (D (g₀ ω)) ξ (k ω) (φ z) (5 / 8 * ρ) (7 / 8 * ρ) =
      ENNReal.ofReal (Real.exp (ξ * c ω)) * acr (D (Gc ω)) (φ z) (5 / 8 * ρ) (7 / 8 * ρ) :=
    le_antisymm (tAcr_le (k ω) hξ0 hf₀ V.isOpen hE hexV hkF (φ z) _ _ hR2)
      (le_tAcr (k ω) hξ0 hf₀ hL₀ V.isOpen hE hexV hkF (φ z) _ _ hR2)
  refine ⟨?_, ?_⟩
  · rw [eq₁, e₁]
    show _ = _ * Φ₁ (LQGMetric.pairJ W (restrictOn hWB (Rm _)))
    rw [← hres]; rfl
  · rw [eq₂, e₂]
    show _ = _ * Φ₂ (LQGMetric.pairJ W (restrictOn hWB (Rm _)))
    rw [← hres]; rfl

end Target

/-! ## Step 4 -/

section Main

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

/-- **The good events are annulus-local** at a small pair `(z, r)`. -/
theorem aeEventIn_goodEvents (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hI : IsInstance Q U V hφ P h g₀ k) (K : ℝ≥0∞) {z : ℂ} {r ε : ℝ} (hG : GeomGood φ U z r ε)
    (hε : ε ≤ 1 / 32) {m : ℕ} (hm : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ exW V m) :
    AEEventIn P (localSigma h z r) (goodEvent₁ D (ξ : ℝ) φ h g₀ k K z r) ∧
      AEEventIn P (localSigma h z r) (goodEvent₂ D (ξ : ℝ) φ h g₀ k K z r) := by
  have hr := hG.1
  obtain ⟨Ψ₁, Ψ₂, hΨ₁, hΨ₂, hT⟩ := target_local hD hφ hI hG hε hm
  obtain ⟨S₁f, S₂f, hS₁f, hS₂f, hS⟩ := source_local hD P hI.1.1 z hr
  have hsc := ae_source_scale hD P hI.1.1 z r
  set X : Ω → DistOn (srcWindow z r) := fun ω =>
    restrictTo (srcWindow z r) (addConst (h ω) (-ctr (h ω) z r)) with hX
  have hS₁ : MeasurableSet {x : DistOn (srcWindow z r) | Ψ₁ x < K * S₁f x} :=
    measurableSet_lt hΨ₁ (measurable_const.mul hS₁f)
  have hS₂ : MeasurableSet {x : DistOn (srcWindow z r) | S₂f x < K * Ψ₂ x} :=
    measurableSet_lt hS₂f (measurable_const.mul hΨ₂)
  have hmeas : ∀ S : Set (DistOn (srcWindow z r)), MeasurableSet S →
      MeasurableSet[localSigma h z r] (X ⁻¹' S) := fun S hS => ⟨S, hS, rfl⟩
  have hcancel : ∀ (e a b : ℝ≥0∞), e ≠ 0 → e ≠ ⊤ → (e * a < K * (e * b) ↔ a < K * b) := by
    intro e a b h0 ht
    rw [mul_left_comm]; exact ENNReal.mul_lt_mul_iff_right h0 ht
  refine ⟨⟨X ⁻¹' {x | Ψ₁ x < K * S₁f x}, hmeas _ hS₁, ?_⟩,
    ⟨X ⁻¹' {x | S₂f x < K * Ψ₂ x}, hmeas _ hS₂, ?_⟩⟩
  · filter_upwards [hT, hS, hsc] with ω ht hs hc
    show goodPair₁ (D (h ω)) (D (g₀ ω)) ξ (k ω) φ K z r = (Ψ₁ (X ω) < K * S₁f (X ω))
    refine propext ?_
    unfold goodPair₁
    rw [ht.1, hc.1, hs.1]
    exact hcancel _ _ _ (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top
  · filter_upwards [hT, hS, hsc] with ω ht hs hc
    show goodPair₂ (D (h ω)) (D (g₀ ω)) ξ (k ω) φ K z r = (S₂f (X ω) < K * Ψ₂ (X ω))
    refine propext ?_
    unfold goodPair₂
    rw [ht.2, hc.2, hs.2]
    exact hcancel _ _ _ (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top

/-- **Step 4, proved** (l. 136–138): the transported locality of the good events. -/
theorem goodEventsLocal_proved (hD : IsStrongLQGMetric ξ Q D) : GoodEventsLocal ξ Q D := by
  intro U V φ hφ Ω _ P _ h g₀ k hI K _ _ L hL hLU
  obtain ⟨r₁, hr₁, hgeom⟩ := geomGood_on_compact U.isOpen hφ.1 hφ.2.injOn hL hLU
    (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨r₁, hr₁, fun z hz r hr => ?_⟩
  have hG := hgeom z (self_subset_cthickening L hz) r hr
  have hsub : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ (V : Set ℂ) := by
    intro y hy
    obtain ⟨x, hx, hφx, -, -⟩ := hG.2.2.2.2 y hy
    rw [← hφx]; exact hφ.2.mapsTo (hG.2.2.1 hx)
  obtain ⟨m, hm⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen (isCompact_closedBall _ _) hsub
  exact aeEventIn_goodEvents hD hφ hI K hG le_rfl hm

end Main

end SupercriticalConformalCovariance.BiLip
