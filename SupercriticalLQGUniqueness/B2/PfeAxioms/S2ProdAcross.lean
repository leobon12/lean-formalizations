import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdLusin
import SupercriticalLQGUniqueness.B2.PfeAxioms.UniformLimsupLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteGeometry
import SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCover
import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleLowerTailAny
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.PfeWeyl.GeoAnnuli
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsS1

 























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal
open LQGMetric (DistC normGFFLaw)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem acrossDist_le_of_inside_outside (G : LSCMetric) (hlen : G.IsLengthSpace)
    (hpath : FinitePathsEuclideanContinuous G) (A : EuclideanAnnulus) {x y : ℂ}
    (hx : dist x A.center ≤ A.innerRadius) (hy : A.outerRadius ≤ dist y A.center) :
    acrossDist G A ≤ G (x, y) := by
  by_cases htop : G (x, y) = ⊤
  · rw [htop]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨P, a, b, hP, hPa, hPb, hlenP⟩ :=
    hlen x y (lt_top_iff_ne_top.2 htop) (δ : ℝ) (NNReal.coe_pos.2 hδ)
  have hfin : G.len P a b < ⊤ :=
    lt_of_le_of_lt hlenP (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 htop, ENNReal.ofReal_lt_top⟩)
  have hc := hpath P a b hP hfin
  calc acrossDist G A ≤ G.len P a b :=
        PfeWeyl.acrossDist_le_len_of_crossing G A hP.1 hc (by rw [hPa]; exact hx)
          (by rw [hPb]; exact hy)
    _ ≤ G (x, y) + ENNReal.ofReal (δ : ℝ) := hlenP
    _ = G (x, y) + (δ : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

 
theorem limsup_acrossDist_le_of_tendsto {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) (hlen : ∀ n, (G n).IsLengthSpace)
    (hpath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (A B : EuclideanAnnulus) (hc : B.center = A.center)
    (hin : A.innerRadius < B.innerRadius) (hout : B.outerRadius < A.outerRadius) :
    limsup (fun n => acrossDist (G n) B) atTop ≤ acrossDist D A := by
  rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff, LSCFun.tendsto_iff_lscTendsto] at hG
  obtain ⟨-, hrec⟩ := hG
  refine le_of_forall_gt_imp_ge_of_dense fun T hT => ?_
  unfold acrossDist at hT
  simp only [iInf_lt_iff] at hT
  obtain ⟨x, hx, y, hy, hxy⟩ := hT
  obtain ⟨p, hp, hpconv⟩ := hrec (x, y)
  have hev1 : ∀ᶠ n in atTop, (G n).toLSCFun.1 (p n) < ((T : ℝ≥0∞) : EReal) :=
    hpconv.eventually (gt_mem_nhds (EReal.coe_ennreal_lt_coe_ennreal_iff.2 hxy))
  have hx' : dist x B.center < B.innerRadius := by
    rw [hc]; rw [EuclideanAnnulus.innerBoundary, Metric.mem_sphere] at hx; linarith
  have hy' : B.outerRadius < dist y B.center := by
    rw [hc]; rw [EuclideanAnnulus.outerBoundary, Metric.mem_sphere] at hy; linarith
  have hev2 : ∀ᶠ n in atTop, dist (p n).1 B.center < B.innerRadius :=
    ((continuous_fst.tendsto (x, y)).comp hp).eventually
      ((continuous_id.dist continuous_const).continuousAt.eventually_lt continuousAt_const hx')
  have hev3 : ∀ᶠ n in atTop, B.outerRadius < dist (p n).2 B.center :=
    ((continuous_snd.tendsto (x, y)).comp hp).eventually
      (continuousAt_const.eventually_lt (continuous_id.dist continuous_const).continuousAt hy')
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev1, hev2, hev3] with n h1 h2 h3
  have h4 : (G n) (p n) < T := EReal.coe_ennreal_lt_coe_ennreal_iff.1 h1
  refine le_trans ?_ h4.le
  have := acrossDist_le_of_inside_outside (G n) (hlen n) (hpath n) B (x := (p n).1) (y := (p n).2)
    h2.le h3.le
  simpa only [Prod.mk.eta] using this

 
def centeredDoubleAnnulus (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨((0 : ℂ), (r, 2 * r)), hr, by linarith⟩

theorem mem_dilate_unitCircle {r : ℝ} (hr : 0 < r) {q : ℚ} (hq : 0 < q) {x : ℂ}
    (hx : x ∈ Metric.sphere (0 : ℂ) (r * q)) :
    x ∈ (B2.Polylog.dilateHomeo hr) '' Metric.sphere (0 : ℂ) (q : ℝ) := by
  refine ⟨(r⁻¹ : ℝ) • x, ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr]
    rw [Metric.mem_sphere, dist_zero_right] at hx
    rw [hx]; field_simp
  · rw [B2.Polylog.dilateHomeo_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

 
theorem setDist_le_acrossDist_dilate (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (r : Ioi (1 : ℝ)) :
    LQGMetric.Blueprint.setDist (B2.DG20Lim.normalizedContLFPP ξ a φ)
        ((B2.Polylog.dilateHomeo (lt_trans one_pos r.property)) ''
          B2.DG20Lim.unitInnerCircle.toSet)
        ((B2.Polylog.dilateHomeo (lt_trans one_pos r.property)) ''
          B2.DG20Lim.unitOuterCircle.toSet) ≤
      acrossDist (PfeWeyl.normalizedLFPPMetric ξ a φ)
        (centeredDoubleAnnulus (r : ℝ) (lt_trans one_pos r.property)) := by
  have hr : (0 : ℝ) < r := lt_trans one_pos r.property
  have hin : B2.DG20Lim.unitInnerCircle.toSet = Metric.sphere (0 : ℂ) ((1 : ℚ) : ℝ) := by
    simp only [B2.DG20Lim.RatCircle.toSet, B2.DG20Lim.RatCircle.center,
      B2.DG20Lim.unitInnerCircle]
    congr 1
    · apply Complex.ext <;> simp
  have hout : B2.DG20Lim.unitOuterCircle.toSet = Metric.sphere (0 : ℂ) ((2 : ℚ) : ℝ) := by
    simp only [B2.DG20Lim.RatCircle.toSet, B2.DG20Lim.RatCircle.center,
      B2.DG20Lim.unitOuterCircle]
    congr 1
    · apply Complex.ext <;> simp
  unfold acrossDist
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hx' : x ∈ (B2.Polylog.dilateHomeo hr) '' B2.DG20Lim.unitInnerCircle.toSet := by
    rw [hin]
    refine mem_dilate_unitCircle hr (by norm_num) ?_
    simpa [centeredDoubleAnnulus, EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius] using hx
  have hy' : y ∈ (B2.Polylog.dilateHomeo hr) '' B2.DG20Lim.unitOuterCircle.toSet := by
    rw [hout]
    refine mem_dilate_unitCircle hr (by norm_num) ?_
    have := hy
    simp only [centeredDoubleAnnulus, EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
      EuclideanAnnulus.outerRadius] at this
    rw [Metric.mem_sphere] at this ⊢
    rw [this]; push_cast; ring
  have hpoint : ENNReal.ofReal ((B2.DG20Lim.normalizedContLFPP ξ a φ).1 (x, y)) =
      PfeWeyl.normalizedLFPPMetric ξ a φ (x, y) := by
    rw [B2.DG20Lim.normalizedContLFPP, LQGMetric.ContMetric.smulPos_apply,
      LQGMetric.LFPP.lfppContMetric_apply,
      ENNReal.ofReal_mul (inv_pos.mpr a.property).le,
      ENNReal.ofReal_toReal (LQGMetric.LFPP.lfppD_ne_top φ.continuous x y),
      PfeWeyl.normalizedLFPPMetric_apply, B2.LscTop.lfppDistance_eq_lfppD]
  rw [← hpoint]
  calc LQGMetric.Blueprint.setDist (B2.DG20Lim.normalizedContLFPP ξ a φ) _ _
      ≤ edist ((B2.DG20Lim.normalizedContLFPP ξ a φ).pt x)
          ((B2.DG20Lim.normalizedContLFPP ξ a φ).pt y) :=
        LQGMetric.MetricGeometry.setEDist_le_edist (mem_image_of_mem _ hx') (mem_image_of_mem _ hy')
    _ = ENNReal.ofReal ((B2.DG20Lim.normalizedContLFPP ξ a φ).1 (x, y)) := by
        rw [edist_dist]; rfl

 
theorem normalizedAcrossTails_of_normalizedLscLimit
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (e : ℕ → Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric) (hlsc : PfeWeyl.NormalizedLscLimit ξ m e Φ) :
    PfeWeyl.NormalizedAcrossTails Φ := by
  intro Ω _ P _ h hh k T hT η hη
  by_cases hηtop : η = ⊤
  · exact Eventually.of_forall fun R => hηtop ▸ le_top
  set T' : ℝ := T.toReal + 1 with hT'
  have hT'pos : 0 < T' := by positivity
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨R₀, ε₀, hR₀, hε₀, htail⟩ := B2.DG20Lim.exists_large_circle_lower_tail_any_of_inputs
    hS4 hPerc hPos ξ Q hQ m hm (2 * T') η.toReal (by positivity) hηr
  
  let X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    (exists_heatVersion hh (δ : ℝ) δ.property).choose
  have hX : ∀ δ, IsHeatSmoothing P h δ (X δ) := fun δ =>
    (exists_heatVersion hh (δ : ℝ) δ.property).choose_spec.2
  
  set r₀ : ℝ := max R₀ (2 * ((k : ℝ) + 1) + 1) with hr₀
  have hr₀1 : 1 < r₀ := lt_of_lt_of_le hR₀ (le_max_left _ _)
  let r : Ioi (1 : ℝ) := ⟨r₀, hr₀1⟩
  have hrpos : (0 : ℝ) < r₀ := lt_trans one_pos hr₀1
  
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 ((he.eventually (gt_mem_nhds hε₀)).and
    (he.eventually (gt_mem_nhds one_pos))))
  
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (X (e (n + N₀)) ω)) atTop (𝓝 (Φ (h ω))) := by
    filter_upwards [hlsc P h hh X hX] with ω hω
    exact ((PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun n => m (e n))
      (fun n => X (e n) ω) (Φ (h ω))).2 hω).comp (tendsto_add_atTop_nat N₀)
  refine eventually_atTop.2 ⟨⟨2 * r₀ + 1, by
    have : 2 * ((k : ℝ) + 1) < r₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    show 2 * ((k : ℝ) + 1) < 2 * r₀ + 1
    linarith⟩, fun R hR => ?_⟩
  have hR' : 2 * r₀ < (R : ℝ) := by
    have : (2 * r₀ + 1 : ℝ) ≤ R := hR
    linarith
  set Abig := PfeWeyl.outerAnnulus ((k : ℝ) + 1) (Nat.cast_add_one_pos k) R
  set Asm := centeredDoubleAnnulus r₀ hrpos
  have hlim : ∀ᵐ ω ∂P, limsup (fun n => acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m (e (n + N₀))) (X (e (n + N₀)) ω)) Asm) atTop ≤ acrossDist (Φ (h ω)) Abig := by
    filter_upwards [hconv] with ω hω
    exact limsup_acrossDist_le_of_tendsto hω
      (fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
      (fun n => finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _) Abig Asm rfl
      (by
        show 2 * ((k : ℝ) + 1) < r₀
        exact lt_of_lt_of_le (by linarith) (le_max_right _ _))
      (by show 2 * r₀ < (R : ℝ); exact hR')
  have hfin : ∀ n, P {ω | acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (X (e (n + N₀)) ω)) Asm < ENNReal.ofReal (2 * T')} ≤ ENNReal.ofReal η.toReal := by
    intro n
    obtain ⟨h1, h2⟩ := hN₀ (n + N₀) (Nat.le_add_left _ _)
    have hT := htail P h hh X hX r ⟨(e (n + N₀) : ℝ), (e (n + N₀)).property, h2⟩
      (le_max_left _ _) h1
    refine le_trans (measure_mono fun ω hω => ?_) hT
    exact lt_of_le_of_lt (setDist_le_acrossDist_dilate (ξ : ℝ) _ _ r) hω
  have hfinal := uniform_lower_tail_of_ae_limsup_le P
    (fun (_ : Unit) n ω => acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (X (e (n + N₀)) ω)) Asm)
    (fun (_ : Unit) ω => acrossDist (Φ (h ω)) Abig) (2 * T') η.toReal (by positivity)
    (fun _ n => hfin n) (fun _ => hlim) ()
  rw [ENNReal.ofReal_toReal hηtop] at hfinal
  refine le_trans (measure_mono fun ω hω => ?_) hfinal
  have hω' : acrossDist (Φ (h ω)) Abig ≤ T := hω
  show acrossDist (Φ (h ω)) Abig < ENNReal.ofReal (2 * T' / 2)
  have h2 : 2 * T' / 2 = T.toReal + 1 := by rw [hT']; ring
  rw [h2]
  calc acrossDist (Φ (h ω)) Abig ≤ T := hω'
    _ = ENNReal.ofReal T.toReal := (ENNReal.ofReal_toReal hT).symm
    _ < ENNReal.ofReal (T.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

end SupercriticalLQGUniqueness.B2.PfeAxioms
