import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaAnnulusGeom
import SupercriticalLQGUniqueness.B2.PfeLocal.CircleMin
import Mathlib.Analysis.Normed.Module.Connected

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem sphere_meets_separator (A : EuclideanAnnulus) {K : Set ℂ}
    (hsep : Disconnects K A.innerBoundary A.outerBoundary) {c₀ : ℂ} {r₀ : ℝ}
    {a : ℂ} (ha : a ∈ Metric.sphere c₀ r₀) (hain : dist a A.center < A.innerRadius)
    (hR : A.outerRadius < r₀) : (Metric.sphere c₀ r₀ ∩ K).Nonempty := by
  by_contra hK
  rw [Set.not_nonempty_iff_eq_empty] at hK
  have hpre : IsPreconnected (Metric.sphere c₀ r₀) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c₀ r₀
  set p : ℂ := 2 * c₀ - a with hpdef
  have hp : p ∈ Metric.sphere c₀ r₀ := by
    rw [Metric.mem_sphere] at ha ⊢
    rw [hpdef, dist_eq_norm] at *
    rw [show 2 * c₀ - a - c₀ = -(a - c₀) by ring, norm_neg]
    exact ha
  have hpa : dist p a = 2 * r₀ := by
    rw [Metric.mem_sphere, dist_eq_norm] at ha
    rw [hpdef, dist_eq_norm, show 2 * c₀ - a - a = -(2 * (a - c₀)) by ring, norm_neg,
      norm_mul, ha]
    norm_num
  have hpfar : A.outerRadius < dist p A.center := by
    have := dist_triangle p A.center a
    rw [dist_comm A.center a] at this
    linarith [A.innerRadius_lt_outerRadius]
  have hcont : ContinuousOn (fun x => dist x A.center) (Metric.sphere c₀ r₀) :=
    (continuous_id.dist continuous_const).continuousOn
  have hivt := hpre.intermediate_value ha hp hcont
  obtain ⟨x, hx, hxd⟩ := hivt ⟨hain.le, (A.innerRadius_lt_outerRadius.trans hpfar).le⟩
  obtain ⟨y, hy, hyd⟩ := hivt ⟨(hain.trans A.innerRadius_lt_outerRadius).le, hpfar.le⟩
  refine hsep ⟨Metric.sphere c₀ r₀, hpre, fun z hz hzK => ?_, ⟨x, hx, hxd⟩, ⟨y, hy, hyd⟩⟩
  exact (Set.eq_empty_iff_forall_notMem.1 hK) z ⟨hz, hzK⟩

 
theorem sphere_setDistance_tendsto_of_lsc
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (hsmall : ∀ k : ℕ,
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    {c c' : ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    Tendsto (fun n => setDistance (G n) (Metric.sphere c r) (Metric.sphere c' r')) atTop
      (𝓝 (setDistance D (Metric.sphere c r) (Metric.sphere c' r'))) := by
  set O := Metric.sphere c r with hOdef
  set O' := Metric.sphere c' r' with hO'def
  have hlow := setDistance_liminf_of_compact hG (isCompact_sphere c r) (isCompact_sphere c' r')
  refine tendsto_of_le_liminf_of_limsup_le hlow ?_
  by_cases hmeet : (O ∩ O').Nonempty
  · obtain ⟨p, hpO, hpO'⟩ := hmeet
    have h0 : ∀ n, setDistance (G n) O O' = 0 := fun n =>
      le_antisymm (iInf₂_le_of_le p hpO (iInf₂_le_of_le p hpO' ((G n).isExtMetric.1 p).le))
        bot_le
    simp only [h0]
    rw [limsup_const]
    exact bot_le
  have hdisj : Disjoint O O' :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
  obtain ⟨a, ha, b, hb, hab⟩ := PfeLocal.setDistance_eq_at_min D (isCompact_sphere c r)
    (isCompact_sphere c' r') (NormedSpace.sphere_nonempty.mpr hr.le)
    (NormedSpace.sphere_nonempty.mpr hr'.le)
  change setDistance D O O' = D (a, b) at hab
  by_cases htop : D (a, b) = ⊤
  · rw [hab, htop]
    exact le_top
  have hne : a ≠ b := fun h => Set.disjoint_left.1 hdisj ha (h ▸ hb)
  have hdab : 0 < dist a b := dist_pos.2 hne
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  set δ : ℝ := (η : ℝ) / 4 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a ∈ Metric.closedBall (0 : ℂ) k ∧ b ∈ Metric.closedBall (0 : ℂ) k := by
    obtain ⟨k, hk⟩ := exists_nat_ge (max (dist a 0) (dist b 0))
    exact ⟨k, Metric.mem_closedBall.2 ((le_max_left _ _).trans hk),
      Metric.mem_closedBall.2 ((le_max_right _ _).trans hk)⟩
  set ρ : ℝ := min (min r r') (dist a b) / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρr : ρ < r := by
    have := min_le_left (min r r') (dist a b)
    have := min_le_left r r'
    linarith
  have hρr' : ρ < r' := by
    have := min_le_left (min r r') (dist a b)
    have := min_le_right r r'
    linarith
  have hρab : 2 * ρ < dist a b := by
    have := min_le_right (min r r') (dist a b)
    linarith
  have hfin : D (a, b) < ⊤ := lt_top_iff_ne_top.2 htop
  have hfin' : D (b, a) < ⊤ := by rwa [D.isExtMetric.2.2.1 b a]
  obtain ⟨A, -, hAin, hAout, -, hAev⟩ := hsmall k a hk.1 ⟨b, hne.symm, hfin⟩ δ hδ ρ hρ
  obtain ⟨B, -, hBin, hBout, -, hBev⟩ := hsmall k b hk.2 ⟨a, hne, hfin'⟩ δ hδ ρ hρ
  obtain ⟨p, hp, hGp⟩ := (LSCMetric.tendsto_iff.1 hG).2 (a, b)
  have hp1 : Tendsto (fun n => (p n).1) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hp
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 b) := (continuous_snd.tendsto _).comp hp
  have hA1 := PfeAxioms.eventually_inside_annulus A a hAin hp1
  have hA2 := PfeAxioms.eventually_outside_annulus A a b hAin
    (by linarith [hAout]) hp2
  have hB2 := PfeAxioms.eventually_inside_annulus B b hBin hp2
  have hB1 := PfeAxioms.eventually_outside_annulus B b a hBin
    (by rw [dist_comm]; linarith [hBout]) hp1
  have hGlt : ∀ᶠ n in atTop, G n (p n) < D (a, b) + ENNReal.ofReal δ :=
    (tendsto_order.1 hGp).2 _ (ENNReal.lt_add_right htop (ENNReal.ofReal_pos.2 hδ).ne')
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hA1, hA2, hB1, hB2, hAev, hBev, hGlt] with n hn1 hn2 hn3 hn4 hnA hnB hnG
  obtain ⟨πa, sa, ta, hπa, -, hsepa, hlena⟩ := aroundDist_exists_curve_lt (G n) A hnA
  obtain ⟨πb, sb, tb, hπb, -, hsepb, hlenb⟩ := aroundDist_exists_curve_lt (G n) B hnB
  
  obtain ⟨xa, hxaO, hxaπ⟩ := sphere_meets_separator A hsepa ha hAin
    (hAout.trans hρr)
  obtain ⟨xb, hxbO, hxbπ⟩ := sphere_meets_separator B hsepb hb hBin
    (hBout.trans hρr')
  
  have hpfin : G n ((p n).1, (p n).2) < ⊤ := by
    rw [Prod.mk.eta]
    exact hnG.trans_le le_top
  obtain ⟨Q, L, hQ, hu, hQ0, hQL, hlenQ⟩ :=
    exists_near_min_ordinary_curve (G n) (hGlen n) _ _ hpfin hδ
  rw [Prod.mk.eta] at hlenQ
  have hQc := continuousOn_of_isCurve_of_forget _ (hGforget n) hQ
  have hsepa' := (disconnects_iff_lqgMetric_disconnects hπa.isClosed_image).1 hsepa
  have hsepb' := (disconnects_iff_lqgMetric_disconnects hπb.isClosed_image).1 hsepb
  obtain ⟨q₁, hq₁, hQq₁⟩ := inside_to_outside_hits_separator hQ.1 hQc
    A.innerRadius_lt_outerRadius.le hsepa' (by rw [hQ0]; exact hn1) (by rw [hQL]; exact hn2)
  obtain ⟨q₂, hq₂, hQq₂⟩ := outside_to_inside_hits_separator hQ.1 hQc
    B.innerRadius_lt_outerRadius.le hsepb' (by rw [hQ0]; exact hn3) (by rw [hQL]; exact hn4)
  obtain ⟨s₁, hs₁, rfl⟩ := hxaπ
  obtain ⟨s₂, hs₂, hs₂eq⟩ := hQq₁
  obtain ⟨s₄, hs₄, rfl⟩ := hxbπ
  obtain ⟨s₃, hs₃, hs₃eq⟩ := hQq₂
  
  have h1 : G n (πa s₁, πa s₂) ≤ (G n).len πa sa ta :=
    eVariationOn.edist_le ((G n).pt ∘ πa) hs₁ hs₂
  have h2 : G n (Q q₁, Q q₂) ≤ (G n).len Q 0 L :=
    eVariationOn.edist_le ((G n).pt ∘ Q) hq₁ hq₂
  have h3 : G n (πb s₃, πb s₄) ≤ (G n).len πb sb tb :=
    eVariationOn.edist_le ((G n).pt ∘ πb) hs₃ hs₄
  have htri : G n (πa s₁, πb s₄) ≤
      G n (πa s₁, πa s₂) + G n (Q q₁, Q q₂) + G n (πb s₃, πb s₄) := by
    rw [hs₂eq, hs₃eq]
    calc G n (πa s₁, πb s₄) ≤ G n (πa s₁, Q q₁) + G n (Q q₁, πb s₄) :=
          (G n).isExtMetric.2.2.2 _ _ _
      _ ≤ G n (πa s₁, Q q₁) + (G n (Q q₁, Q q₂) + G n (Q q₂, πb s₄)) := by
          gcongr
          exact (G n).isExtMetric.2.2.2 _ _ _
      _ = _ := by rw [add_assoc]
  calc setDistance (G n) O O' ≤ G n (πa s₁, πb s₄) := iInf₂_le_of_le _ hxaO (iInf₂_le _ hxbO)
    _ ≤ (G n).len πa sa ta + (G n).len Q 0 L + (G n).len πb sb tb :=
        htri.trans (add_le_add (add_le_add h1 h2) h3)
    _ ≤ ENNReal.ofReal δ + (D (a, b) + ENNReal.ofReal δ + ENNReal.ofReal δ) +
          ENNReal.ofReal δ :=
        add_le_add (add_le_add hlena.le (hlenQ.le.trans (add_le_add hnG.le le_rfl))) hlenb.le
    _ = setDistance D O O' + (η : ℝ≥0∞) := by
        rw [hab]
        have h4 : ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ =
            (η : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le,
            ← ENNReal.ofReal_add (by positivity) hδ.le, hδdef]
          rw [show (η : ℝ) / 4 + η / 4 + η / 4 + η / 4 = η by ring]
          exact ENNReal.ofReal_coe_nnreal
        rw [← h4]
        ring

 



theorem subseqLimitNormalized_of_inputs
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hlsc : NormalizedLscLimit ξ m ε D) (hsmall : NormalizedSmallAnnuli ξ m ε D)
    (hpts : NormalizedPointCircles ξ m ε D) :
    SubseqLimitNormalized ξ m ε D := by
  intro Ω _ P _ h hh X hX
  refine ⟨hlsc P h hh X hX, fun O O' hO hO' => ?_⟩
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  by_cases hpos : 0 < r ∧ 0 < r'
  · filter_upwards [hlsc P h hh X hX, ae_all_iff.2 (hsmall P h hh X hX)] with ω hω hS
    have hG := (tendsto_normalizedLFPP_iff_lscTendsto _ _ _ _).2 hω
    have hc := sphere_setDistance_tendsto_of_lsc hG
      (fun n => isLengthSpace_normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
      (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric (ξ : ℝ) (m (ε n)) _)
      hS (c := Complex.mk (x : ℝ) (y : ℝ)) (c' := Complex.mk (x' : ℝ) (y' : ℝ))
      (Rat.cast_pos.2 hpos.1) (Rat.cast_pos.2 hpos.2)
    simp only [setDistance_normalizedLFPPMetric] at hc
    exact hc
  · have hzero : r = 0 ∨ r' = 0 := by
      rcases not_and_or.1 hpos with h1 | h1
      · exact Or.inl (le_antisymm (not_lt.1 h1) hr)
      · exact Or.inr (le_antisymm (not_lt.1 h1) hr')
    exact hpts P h hh X hX x y r x' y' r' hr hr' hzero

 


theorem subseqLimit_of_normalizedLsc_of_pfeWeak
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hPfe : IsPfeWeakMetric ξ D c)
    (hlsc : NormalizedLscLimit ξ m ε D) (hgeo : NormalizedLimitGeometry D)
    (htail : NormalizedAcrossTails D) (hsmall : NormalizedSmallAnnuli ξ m ε D)
    (hpts : NormalizedPointCircles ξ m ε D) :
    SubseqLimit ξ m ε D :=
  subseqLimit_of_normalized_of_pfeWeak ξ m ε hε D c hPfe
    (subseqLimitNormalized_of_inputs ξ m ε D hlsc hsmall hpts) hgeo htail hsmall

end SupercriticalLQGUniqueness.B2.PfeWeyl
