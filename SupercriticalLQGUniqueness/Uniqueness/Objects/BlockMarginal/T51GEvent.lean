import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.BoundaryClauseI
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClauseTools
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.EventMeas
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal




 





















set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

theorem half_lt_self_of_pos {s : ℝ} (hs : 0 < s) : s / 2 < s := by linarith

 
def GEv (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (w : ℂ) (s : Ioi (0 : ℝ)) (g : DistC) : Prop :=
  Objects.Shadow.circleOuter w (s : ℝ).toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere w (s : ℝ), ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s w <
        Objects.BoundaryDecay.annulusBoundaryCost (D g) (half_lt_self_of_pos s.2) ⟨x, hx⟩} ≤
      ENNReal.ofReal ((lam / 2) * s) ∧
    Objects.CorrectedEvent.around (D g) w ((1 / 2) * s) (1 * s) ≤ ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s w ∧
    ENNReal.ofReal R⁻¹ * Objects.AnnulusTails.nrm ξ Q g s w ≤ Objects.CorrectedEvent.acr (D g) w ((1 / 2) * s) (1 * s)

 

 
abbrev annK (c : ℂ) (r₁ r₂ : ℝ) : Set ℂ := closedBall c r₂ \ ball c r₁

theorem isCompact_annK (c : ℂ) (r₁ r₂ : ℝ) : IsCompact (annK c r₁ r₂) :=
  (isCompact_closedBall c r₂).diff isOpen_ball

theorem mem_annK_of_outer {c x : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂) (hx : x ∈ sphere c r₂) :
    x ∈ annK c r₁ r₂ := by
  refine ⟨sphere_subset_closedBall hx, fun hb => ?_⟩
  rw [mem_ball, mem_sphere.mp hx] at hb
  linarith

theorem mem_annK_of_inner {c y : ℂ} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) (hy : y ∈ sphere c r₁) :
    y ∈ annK c r₁ r₂ := by
  refine ⟨mem_closedBall.mpr ((mem_sphere.mp hy).le.trans hr), fun hb => ?_⟩
  rw [mem_ball, mem_sphere.mp hy] at hb
  exact lt_irrefl _ hb

 
def annCostK (c : ℂ) (r₁ r₂ : ℝ) (p : LSCMetric × annK c r₁ r₂) : ℝ≥0∞ :=
  ⨅ y ∈ {y : annK c r₁ r₂ | (y : ℂ) ∈ sphere c r₁}, p.1.internal (annK c r₁ r₂) (p.2, y)

 

theorem lsc_iInf_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X × Y → ℝ≥0∞} (hf : LowerSemicontinuous f) {S : Set Y} (hS : IsCompact S) :
    LowerSemicontinuous (fun x => ⨅ y ∈ S, f (x, y)) := by
  intro x t ht
  obtain ⟨t', htt', ht'⟩ := exists_between ht
  have hP : ∀ y ∈ S, ∀ᶠ z : X × Y in 𝓝 (x, y), t' < f (z.1, z.2) := by
    intro y hy
    exact hf (x, y) t' (lt_of_lt_of_le ht' (iInf₂_le y hy))
  filter_upwards [hS.eventually_forall_of_forall_eventually (P := fun x' y => t' < f (x', y)) hP]
    with x' hx'
  exact lt_of_lt_of_le htt' (le_iInf₂ fun y hy => (hx' y hy).le)

theorem lowerSemicontinuous_annCostK (c : ℂ) (r₁ r₂ : ℝ) :
    LowerSemicontinuous (annCostK c r₁ r₂) := by
  have hK := isCompact_annK c r₁ r₂
  have hf : LowerSemicontinuous
      ((fun p : LSCMetric × (annK c r₁ r₂ × annK c r₁ r₂) =>
          p.1.internal (annK c r₁ r₂) (p.2.1, p.2.2)) ∘
        (fun q : (LSCMetric × annK c r₁ r₂) × annK c r₁ r₂ =>
          ((q.1.1, (q.1.2, q.2)) : LSCMetric × (annK c r₁ r₂ × annK c r₁ r₂)))) := by
    apply LowerSemicontinuous.comp (Toolkit.MovingEndpoints.internal_compact_joint_lsc hK)
    exact continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  have hS : IsCompact {y : annK c r₁ r₂ | (y : ℂ) ∈ sphere c r₁} := by
    have : CompactSpace (annK c r₁ r₂) := isCompact_iff_compactSpace.mp hK
    exact (isClosed_sphere.preimage continuous_subtype_val).isCompact
  have h := lsc_iInf_compact hf hS
  have heq : annCostK c r₁ r₂ = fun x => ⨅ y ∈ {y : annK c r₁ r₂ | (y : ℂ) ∈ sphere c r₁},
      ((fun p : LSCMetric × (annK c r₁ r₂ × annK c r₁ r₂) =>
          p.1.internal (annK c r₁ r₂) (p.2.1, p.2.2)) ∘
        (fun q : (LSCMetric × annK c r₁ r₂) × annK c r₁ r₂ =>
          ((q.1.1, (q.1.2, q.2)) : LSCMetric × (annK c r₁ r₂ × annK c r₁ r₂)))) (x, y) := by
    funext p
    rfl
  rw [heq]
  exact h

theorem annulusBoundaryCost_eq_annCostK (D : LSCMetric) {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (x : sphere c r₂) :
    Objects.BoundaryDecay.annulusBoundaryCost D hr x = annCostK c r₁ r₂ (D, ⟨x, mem_annK_of_outer hr x.2⟩) := by
  unfold Objects.BoundaryDecay.annulusBoundaryCost annCostK
  apply le_antisymm
  · exact le_iInf₂ fun y hy => iInf₂_le_of_le (y : ℂ) hy le_rfl
  · exact le_iInf₂ fun y hy => iInf₂_le_of_le ⟨y, mem_annK_of_inner hr.le hy⟩ hy le_rfl

 

theorem circlePt_mem_sphere (w : ℂ) {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    w + (((s.toNNReal : NNReal) : ℝ) : ℂ) * Complex.exp (θ * Complex.I) ∈ sphere w s := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.coe_toNNReal s hs, Real.norm_eq_abs,
    abs_of_nonneg hs]

theorem measurableSet_badCircle (ξ Q R : ℝ) (D : DistC → LSCMetric) (hD : Measurable D)
    (w : ℂ) (s : Ioi (0 : ℝ)) :
    MeasurableSet {p : DistC × ℝ | p.2 ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) ∧
      w + (((s : ℝ).toNNReal : NNReal) : ℝ) * Complex.exp (p.2 * Complex.I) ∈
        {x : ℂ | ∃ hx : x ∈ sphere w (s : ℝ), ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s w <
          Objects.BoundaryDecay.annulusBoundaryCost (D p.1) (half_lt_self_of_pos s.2) ⟨x, hx⟩}} := by
  have hs0 : (0 : ℝ) ≤ s := s.2.le
  have hpt : Measurable (fun θ : ℝ => (⟨w + (((s : ℝ).toNNReal : NNReal) : ℝ) *
      Complex.exp (θ * Complex.I), mem_annK_of_outer (half_lt_self_of_pos s.2)
        (circlePt_mem_sphere w hs0 θ)⟩ : annK w ((s : ℝ) / 2) s)) := by
    apply Measurable.subtype_mk
    fun_prop
  have hF : Measurable (annCostK w ((s : ℝ) / 2) s) :=
    (lowerSemicontinuous_annCostK w ((s : ℝ) / 2) s).measurable
  have hcost : Measurable (fun p : DistC × ℝ => annCostK w ((s : ℝ) / 2) s
      (D p.1, ⟨w + (((s : ℝ).toNNReal : NNReal) : ℝ) * Complex.exp (p.2 * Complex.I),
        mem_annK_of_outer (half_lt_self_of_pos s.2) (circlePt_mem_sphere w hs0 p.2)⟩)) :=
    hF.comp ((hD.comp measurable_fst).prodMk (hpt.comp measurable_snd))
  have hN : Measurable (fun p : DistC × ℝ => ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s w) :=
    measurable_const.mul ((Objects.BoundaryUnion.measurable_nrm ξ Q s w).comp measurable_fst)
  have hset : {p : DistC × ℝ | p.2 ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) ∧
      w + (((s : ℝ).toNNReal : NNReal) : ℝ) * Complex.exp (p.2 * Complex.I) ∈
        {x : ℂ | ∃ hx : x ∈ sphere w (s : ℝ), ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s w <
          Objects.BoundaryDecay.annulusBoundaryCost (D p.1) (half_lt_self_of_pos s.2) ⟨x, hx⟩}} =
      {p : DistC × ℝ | p.2 ∈ Ico (0 : ℝ) (0 + 2 * Real.pi)} ∩
        {p : DistC × ℝ | ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s w < annCostK w ((s : ℝ) / 2) s
          (D p.1, ⟨w + (((s : ℝ).toNNReal : NNReal) : ℝ) * Complex.exp (p.2 * Complex.I),
            mem_annK_of_outer (half_lt_self_of_pos s.2) (circlePt_mem_sphere w hs0 p.2)⟩)} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, hx, h2⟩
      refine ⟨h1, ?_⟩
      rw [annulusBoundaryCost_eq_annCostK] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, circlePt_mem_sphere w hs0 p.2, ?_⟩
      rw [annulusBoundaryCost_eq_annCostK]
      exact h2
  rw [hset]
  exact (measurableSet_Ico.preimage measurable_snd).inter (measurableSet_lt hN hcost)

theorem measurable_clauseI (ξ Q R : ℝ) (D : DistC → LSCMetric) (hD : Measurable D)
    (w : ℂ) (s : Ioi (0 : ℝ)) :
    Measurable (fun g : DistC => Objects.Shadow.circleOuter w (s : ℝ).toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere w (s : ℝ), ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s w <
        Objects.BoundaryDecay.annulusBoundaryCost (D g) (half_lt_self_of_pos s.2) ⟨x, hx⟩}) := by
  unfold Objects.Shadow.circleOuter
  exact measurable_const.mul
    (measurable_measure_prodMk_left (measurableSet_badCircle ξ Q R D hD w s))

theorem measurableSet_GEv (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (hD : Measurable D)
    (w : ℂ) (s : Ioi (0 : ℝ)) : MeasurableSet {g | GEv ξ Q lam R D w s g} := by
  have hs := s.2
  have hN : Measurable (fun g : DistC => Objects.AnnulusTails.nrm ξ Q g s w) := Objects.BoundaryUnion.measurable_nrm ξ Q s w
  have hs' : (0 : ℝ) < s := hs
  have hA := (Objects.ClauseMeasurability.measurable_around w ((1 / 2) * (s : ℝ)) (1 * s) (by linarith)
    (by linarith)).comp hD
  have hC := (Objects.ClauseMeasurability.measurable_acr w ((1 / 2) * (s : ℝ)) (1 * s)).comp hD
  exact (measurableSet_le (measurable_clauseI ξ Q R D hD w s) measurable_const).inter
    ((measurableSet_le hA (measurable_const.mul hN)).inter
      (measurableSet_le (measurable_const.mul hN) hC))

 

 
abbrev gCarrier (w : ℂ) (s : ℝ) : Set ℂ := annK w (s / 2) s

theorem annulusBoundaryCost_congr (D₁ D₂ : LSCMetric) {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (h : D₁.internal (annK c r₁ r₂) = D₂.internal (annK c r₁ r₂)) (x : sphere c r₂) :
    Objects.BoundaryDecay.annulusBoundaryCost D₁ hr x = Objects.BoundaryDecay.annulusBoundaryCost D₂ hr x := by
  unfold Objects.BoundaryDecay.annulusBoundaryCost
  simp only [annK] at h
  simp only [h]

theorem GEv_iff_of_local (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (w : ℂ) (s : Ioi (0 : ℝ))
    (g₁ g₂ : DistC) (hB₁ : BiLipschitz.Barrier.Barrier (D g₁)) (hB₂ : BiLipschitz.Barrier.Barrier (D g₂))
    (hL₁ : (D g₁).IsLengthSpace) (hL₂ : (D g₂).IsLengthSpace) {ε : ℝ} (hε : 0 < ε)
    (hint : (D g₁).internal (thickening ε (gCarrier w s)) =
      (D g₂).internal (thickening ε (gCarrier w s)))
    (hres : restrictTo (nbhdO ε (gCarrier w s)) g₁ = restrictTo (nbhdO ε (gCarrier w s)) g₂) :
    GEv ξ Q lam R D w s g₁ ↔ GEv ξ Q lam R D w s g₂ := by
  have hs : (0 : ℝ) < s := s.2
  have hKU : gCarrier w s ⊆ thickening ε (gCarrier w s) := self_subset_thickening hε _
  have hcann : Objects.CorrectedEvent.cann w ((1 / 2) * (s : ℝ)) (1 * s) ⊆ gCarrier w s := by
    intro x hx
    refine ⟨mem_closedBall.mpr (by linarith [hx.2]), fun hb => ?_⟩
    rw [mem_ball] at hb
    linarith [hx.1]
  have hann : Objects.CorrectedEvent.ann w ((1 / 2) * (s : ℝ)) (1 * s) ⊆ gCarrier w s := by
    intro x hx
    exact hcann ⟨hx.1.le, hx.2.le⟩
  have hsph : sphere w |(s : ℝ)| ⊆ gCarrier w s := by
    rw [abs_of_pos hs]
    exact fun x hx => mem_annK_of_outer (half_lt_self_of_pos hs) hx
  have hK : (D g₁).internal (gCarrier w s) = (D g₂).internal (gCarrier w s) :=
    Toolkit.InternalMetrics.internal_eq_of_internal_eq (D g₁) (D g₂) hKU hint
  have hacr : Objects.CorrectedEvent.acr (D g₁) w ((1 / 2) * (s : ℝ)) (1 * s) =
      Objects.CorrectedEvent.acr (D g₂) w ((1 / 2) * (s : ℝ)) (1 * s) :=
    acr_eq_of_internal_eq (D g₁) (D g₂) hB₁ hB₂ hL₁ hL₂ _ hint w (by linarith)
      (by linarith) (hcann.trans hKU)
  have haround : Objects.CorrectedEvent.around (D g₁) w ((1 / 2) * (s : ℝ)) (1 * s) =
      Objects.CorrectedEvent.around (D g₂) w ((1 / 2) * (s : ℝ)) (1 * s) :=
    around_eq_of_internal_eq (D g₁) (D g₂) _ hint w (by linarith) (by linarith)
      (hann.trans hKU)
  have hN : Objects.AnnulusTails.nrm ξ Q g₁ s w = Objects.AnnulusTails.nrm ξ Q g₂ s w := by
    unfold Objects.AnnulusTails.nrm
    rw [circleAvg_eq_of_restrictTo_eq hres hε (thickening_subset_of_subset ε hsph)]
  have hcost : ∀ x : sphere w (s : ℝ),
      Objects.BoundaryDecay.annulusBoundaryCost (D g₁) (half_lt_self_of_pos s.2) x =
        Objects.BoundaryDecay.annulusBoundaryCost (D g₂) (half_lt_self_of_pos s.2) x :=
    annulusBoundaryCost_congr (D g₁) (D g₂) _ hK
  unfold GEv
  simp only [hN, hcost, hacr, haround]

 

theorem scale_lt_iff {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤) (a x y : ℝ≥0∞) :
    a * (e * x) < e * y ↔ a * x < y := by
  rw [mul_left_comm a e x, ENNReal.mul_lt_mul_iff_right he0 heTop]

theorem annulusBoundaryCost_scale (D E : LSCMetric) {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤)
    (hscale : ∀ x y : ℂ, E (x, y) = e * D (x, y)) {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (x : sphere c r₂) :
    Objects.BoundaryDecay.annulusBoundaryCost E hr x = e * Objects.BoundaryDecay.annulusBoundaryCost D hr x := by
  unfold Objects.BoundaryDecay.annulusBoundaryCost
  simp only [Positivity.Witnesses.internal_eq_mul_of_dist_scale D E e he0 heTop hscale,
    ENNReal.mul_iInf_of_ne he0 heTop]

theorem GEv_iff_of_scale (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (w : ℂ) (s : Ioi (0 : ℝ))
    (g₁ g₂ : DistC) {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤)
    (hscale : ∀ x y : ℂ, D g₂ (x, y) = e * D g₁ (x, y))
    (hN : Objects.AnnulusTails.nrm ξ Q g₂ s w = e * Objects.AnnulusTails.nrm ξ Q g₁ s w) :
    GEv ξ Q lam R D w s g₂ ↔ GEv ξ Q lam R D w s g₁ := by
  have hcost : ∀ x : sphere w (s : ℝ),
      Objects.BoundaryDecay.annulusBoundaryCost (D g₂) (half_lt_self_of_pos s.2) x =
        e * Objects.BoundaryDecay.annulusBoundaryCost (D g₁) (half_lt_self_of_pos s.2) x :=
    annulusBoundaryCost_scale (D g₁) (D g₂) he0 heTop hscale _
  unfold GEv
  simp only [hN, hcost, Objects.ProbabilityS3.around_eq_mul_of_dist_scale (D g₁) (D g₂) e he0 heTop hscale,
    Objects.ProbabilityS3.acr_eq_mul_of_dist_scale (D g₁) (D g₂) e he0 heTop hscale,
    scale_lt_iff he0 heTop, scale_le_iff he0 heTop, scale_le_iff' he0 heTop]

theorem nrm_addConst {ξ Q : ℝ} {g : DistC} {s : ℝ} {w : ℂ} {c : ℝ}
    (hc : LQGMetric.circleAvg (addConst g c) s w = LQGMetric.circleAvg g s w + c) :
    Objects.AnnulusTails.nrm ξ Q (addConst g c) s w = ENNReal.ofReal (Real.exp (ξ * c)) * Objects.AnnulusTails.nrm ξ Q g s w := by
  unfold Objects.AnnulusTails.nrm
  rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

 
theorem aeEventIn_GEv (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam R : ℝ) (w : ℂ) (s : Ioi (0 : ℝ)) :
    AEEventIn μ (fieldSigmaClosed0 id (gCarrier w s)) {g | GEv ξ Q lam R D w s g} := by
  have hs : (0 : ℝ) < s := s.2
  have hne : ((LQGMetric.Blueprint.annulus w ((s : ℝ) / 2) s : TopologicalSpace.Opens ℂ) :
      Set ℂ).Nonempty := by
    refine ⟨w + ((3 * (s : ℝ) / 4 : ℝ) : ℂ), ?_⟩
    change (s : ℝ) / 2 < ‖w + ((3 * (s : ℝ) / 4 : ℝ) : ℂ) - w‖ ∧
      ‖w + ((3 * (s : ℝ) / 4 : ℝ) : ℂ) - w‖ < s
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    constructor <;> linarith
  obtain ⟨ψ, hψ, hψ1⟩ := LQGMetric.GermSplit.exists_test_unit hne
  have hψK : tsupport (ψ : ℂ → ℝ) ⊆ gCarrier w s := by
    refine hψ.trans fun x hx => ?_
    change (s : ℝ) / 2 < ‖x - w‖ ∧ ‖x - w‖ < s at hx
    refine ⟨mem_closedBall.mpr (by rw [dist_eq_norm]; exact hx.2.le), fun hb => ?_⟩
    rw [mem_ball, dist_eq_norm] at hb
    linarith [hx.1]
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (gCarrier w s) ψ hψK hψ1 _
    (measurableSet_GEv ξ Q lam R D hD.measurable w s) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint hres h1
    exact (GEv_iff_of_local ξ Q lam R D w s g₁ g₂ hB₁ hB₂ hL₁ hL₂ hε hint hres).mp h1
  · have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
      LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
    filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD (fun g => -(g ψ)),
      LQGMetric.CircleAvg.ae_circleAvg_addConst hμ.1 w hs] with g hg hc
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    exact GEv_iff_of_scale (ξ : ℝ) Q lam R D w s g (addConst g (-(g ψ))) he0
      ENNReal.ofReal_ne_top (fun x y => hg (x, y)) (nrm_addConst (hc (-(g ψ))))

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
