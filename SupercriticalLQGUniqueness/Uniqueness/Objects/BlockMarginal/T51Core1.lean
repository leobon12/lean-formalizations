import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Geo
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Union
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths.T51ThreePath
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths.T51CrossCost
import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldBilipInternal




 














set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

 
theorem exists_first_exit {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    {z : ℂ} {s : ℝ} (ha : dist (P a) z < s) (hb : s ≤ dist (P b) z) :
    ∃ t ∈ Icc a b, dist (P t) z = s ∧ ∀ r ∈ Icc a t, dist (P r) z ≤ s := by
  let f : ℝ → ℝ := fun r => dist (P r) z
  have hf : ContinuousOn f (Icc a b) := (continuous_id.dist continuous_const).comp_continuousOn hP
  let S : Set ℝ := Icc a b ∩ f ⁻¹' Ici s
  have hSc : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hSb : BddBelow S := ⟨a, fun r hr => hr.1.1⟩
  have htS : sInf S ∈ S := hSc.csInf_mem hSne hSb
  set t := sInf S with htdef
  have hat : a ≤ t := htS.1.1
  have htb : t ≤ b := htS.1.2
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hat (hf.mono (Icc_subset_Icc le_rfl htb))
    ⟨ha.le, htS.2⟩
  have htc : t ≤ c := csInf_le hSb ⟨⟨hc.1, hc.2.trans htb⟩, (show s ≤ f c from hfc.ge)⟩
  have hct : c = t := le_antisymm hc.2 htc
  have hft : f t = s := hct ▸ hfc
  refine ⟨t, ⟨hat, htb⟩, hft, fun r hr => ?_⟩
  rcases hr.2.lt_or_eq with hrt | hrt
  · by_contra hcon
    push Not at hcon
    have : t ≤ r := csInf_le hSb ⟨⟨hr.1, hr.2.trans htb⟩, hcon.le⟩
    linarith
  · rw [hrt]
    exact hft.le

 

theorem acr_le_setDist (D : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {z u : ℂ} {s ρ : ℝ} (hu : dist u z ≤ s / 2)
    (hball : closedBall z s ⊆ ball u ρ) :
    Objects.CorrectedEvent.acr D z ((1 / 2) * s) (1 * s) ≤ OptimalConstants.Ratios.setDist D {u} (sphere u ρ) := by
  unfold OptimalConstants.Ratios.setDist
  refine le_iInf₂ fun u' hu' => le_iInf₂ fun y hy => ?_
  rw [mem_singleton_iff] at hu'
  subst hu'
  have hyz : s < dist y z := by
    by_contra hcon
    push Not at hcon
    have := hball (mem_closedBall.mpr hcon)
    rw [mem_ball, mem_sphere.mp hy] at this
    exact lt_irrefl _ this
  by_cases htop : D (u', y) = ⊤
  · rw [htop]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ :=
    hL u' y (lt_top_iff_ne_top.mpr htop) ε (by exact_mod_cast hε)
  have h1 := Objects.BlockPaths.acr_le_len_of_inner_outer_path D hP (hcont P a b hP) (c := z)
    (r₁ := (1 / 2) * s) (r₂ := 1 * s) (by linarith [dist_nonneg (x := u') (y := z)])
    (by rw [hPa, ← dist_eq_norm]; linarith) (by rw [hPb, ← dist_eq_norm]; linarith)
  calc Objects.CorrectedEvent.acr D z ((1 / 2) * s) (1 * s) ≤ D.len P a b := h1
    _ ≤ D (u', y) + ENNReal.ofReal ε := hlen
    _ = D (u', y) + ε := by rw [ENNReal.ofReal_coe_nnreal]

 
theorem exists_exit_path (D : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {z u : ℂ} {s ρ : ℝ} (hu : dist u z < s)
    (hball : closedBall z s ⊆ ball u ρ) {X : ℝ≥0∞}
    (hX : OptimalConstants.Ratios.setDist D {u} (sphere u ρ) < X) :
    ∃ (P : ℝ → ℂ) (a t : ℝ), D.IsCurve P a t ∧ P a = u ∧ P t ∈ sphere z s ∧
      MapsTo P (Icc a t) (closedBall z s) ∧ D.len P a t < X := by
  unfold OptimalConstants.Ratios.setDist at hX
  simp only [iInf_lt_iff, mem_singleton_iff, exists_prop] at hX
  obtain ⟨u', rfl, y, hy, hDy⟩ := hX
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hDy
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hL u' y (hDy.trans_le le_top) r (by exact_mod_cast hr0)
  have hyz : s ≤ dist y z := by
    by_contra hcon
    push Not at hcon
    have := hball (mem_closedBall.mpr hcon.le)
    rw [mem_ball, mem_sphere.mp hy] at this
    exact lt_irrefl _ this
  obtain ⟨t, ht, hPt, hpre⟩ := exists_first_exit hP.1 (hcont P a b hP)
    (by rw [hPa]; exact hu) (by rw [hPb]; exact hyz)
  refine ⟨P, a, t, ⟨ht.1, hP.2.mono (Icc_subset_Icc le_rfl ht.2)⟩, hPa, mem_sphere.mpr hPt,
    fun q hq => mem_closedBall.mpr (hpre q hq), ?_⟩
  calc D.len P a t ≤ D.len P a b := eVariationOn.mono _ (Icc_subset_Icc le_rfl ht.2)
    _ ≤ D (u', y) + ENNReal.ofReal r := hlen
    _ < X := by rw [ENNReal.ofReal_coe_nnreal]; exact hr

theorem exists_around_loop (D : LSCMetric) (w : ℂ) (a b : ℝ) {X : ℝ≥0∞}
    (hX : Objects.CorrectedEvent.around D w a b < X) :
    ∃ (P : ℝ → ℂ) (t u : ℝ), D.IsCurve P t u ∧ P '' Icc t u ⊆ Objects.CorrectedEvent.ann w a b ∧
      LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b) ∧ D.len P t u < X := by
  unfold Objects.CorrectedEvent.around at hX
  simp only [iInf_lt_iff] at hX
  obtain ⟨P, t, u, hP, hsub, hdisc, hlen⟩ := hX
  exact ⟨P, t, u, hP, hsub, hdisc, hlen⟩

theorem exists_inner_path (D : LSCMetric) {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂) (x : sphere c r₂)
    {X : ℝ≥0∞} (hX : Objects.BoundaryDecay.annulusBoundaryCost D hr x < X) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P a = x ∧ P b ∈ sphere c r₁ ∧
      (∀ t ∈ Icc a b, P t ∈ annK c r₁ r₂) ∧ D.len P a b < X := by
  unfold Objects.BoundaryDecay.annulusBoundaryCost at hX
  simp only [iInf_lt_iff] at hX
  obtain ⟨y, hy, hint⟩ := hX
  unfold LSCMetric.internal at hint
  simp only [iInf_lt_iff] at hint
  obtain ⟨P, a, b, hP, hPK, hPa, hPb, hlen⟩ := hint
  exact ⟨P, a, b, hP, hPa, by rw [hPb]; exact hy, hPK, hlen⟩

 
theorem internal_ball_le_three (D : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {z u : ℂ} {s ρ : ℝ} (hs : 0 < s) (hu : dist u z < s / 2)
    (hball : closedBall z s ⊆ ball u ρ) (x : sphere z s) {A₁ A₂ A₃ : ℝ≥0∞}
    (h₁ : Objects.BoundaryDecay.annulusBoundaryCost D (half_lt_self_of_pos hs) x ≤ A₁)
    (h₂ : Objects.CorrectedEvent.around D z ((1 / 2) * s) (1 * s) ≤ A₂)
    (h₃ : OptimalConstants.Ratios.setDist D {u} (sphere u ρ) ≤ A₃) (hA₁ : A₁ ≠ ⊤) (hA₂ : A₂ ≠ ⊤) (hA₃ : A₃ ≠ ⊤)
    (hxK : (x : ℂ) ∈ closedBall z s) (huK : u ∈ closedBall z s) :
    D.internal (closedBall z s) (⟨x, hxK⟩, ⟨u, huK⟩) ≤ A₁ + A₂ + A₃ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ≥0∞ := (ε : ℝ≥0∞) / 3 with hηdef
  have hη : η ≠ 0 := (ENNReal.div_pos (by exact_mod_cast hε.ne') (by norm_num)).ne'
  obtain ⟨α, a₁, b₁, hα, hαa, hαb, hαK, hαlen⟩ := exists_inner_path D (half_lt_self_of_pos hs) x
    (X := A₁ + η) (h₁.trans_lt (ENNReal.lt_add_right hA₁ hη))
  obtain ⟨π, t₁, u₁, hπ, hπsub, hπdisc, hπlen⟩ := exists_around_loop D z _ _
    (X := A₂ + η) (h₂.trans_lt (ENNReal.lt_add_right hA₂ hη))
  obtain ⟨β, a₂, t₂, hβ, hβa, hβt, hβK, hβlen⟩ := exists_exit_path D hcont hL
    (by linarith) hball (X := A₃ + η) (h₃.trans_lt (ENNReal.lt_add_right hA₃ hη))
  have hαK' : MapsTo α (Icc a₁ b₁) (closedBall z s) := fun t ht => (hαK t ht).1
  have hπK' : MapsTo π (Icc t₁ u₁) (closedBall z s) := by
    intro t ht
    have := hπsub ⟨t, ht, rfl⟩
    exact mem_closedBall.mpr (by have := this.2; linarith)
  have hsep : LQGMetric.Disconnects (π '' Icc t₁ u₁) (sphere z (s / 2)) (sphere z s) := by
    have h12 : (1 / 2 : ℝ) * s = s / 2 := by ring
    rw [h12, one_mul] at hπdisc
    exact hπdisc
  have hjoin := Objects.BlockPaths.internal_le_three_path_join D (closedBall z s) (isCompact_closedBall z s)
    hα hαK' hβ hβK hπ hπK' (r := s / 2) (R := s) (by linarith) hsep
    (by rw [hαa]; exact (mem_sphere.mp x.2).ge) (by rw [mem_sphere.mp hαb])
    (by rw [hβa]; linarith) (mem_sphere.mp hβt).ge
  have hpt : ((⟨α a₁, hαK' (left_mem_Icc.mpr hα.1)⟩, ⟨β a₂, hβK (left_mem_Icc.mpr hβ.1)⟩) :
      closedBall z s × closedBall z s) = (⟨x, hxK⟩, ⟨u, huK⟩) := by
    ext
    · exact hαa
    · exact hβa
  rw [hpt] at hjoin
  calc D.internal (closedBall z s) (⟨x, hxK⟩, ⟨u, huK⟩)
      ≤ D.len α a₁ b₁ + D.len π t₁ u₁ + D.len β a₂ t₂ := hjoin
    _ ≤ (A₁ + η) + (A₂ + η) + (A₃ + η) :=
        add_le_add (add_le_add hαlen.le hπlen.le) hβlen.le
    _ = A₁ + A₂ + A₃ + 3 * η := by ring
    _ = A₁ + A₂ + A₃ + ε := by
        rw [hηdef, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

 
theorem F3_of_G (D D' : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D'.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D'.IsLengthSpace) {cm : ℝ} (hcm : 0 < cm)
    (hcomp : ∀ p : ℂ × ℂ, D p ≤ ENNReal.ofReal cm⁻¹ * D' p)
    {lam R t : ℝ} (hlam : 0 < lam) (hR : 0 < R) (ht : 0 ≤ t)
    (hnum : (2 * R ^ 2 + 1) * t ≤ lam ^ 2) (hlamcm : lam ≤ cm)
    {z u : ℂ} {s ρ : ℝ} (hs : 0 < s) (hu : dist u z < s / 2) (hball : closedBall z s ⊆ ball u ρ)
    {N d : ℝ≥0∞} (hN : N ≠ ⊤) (hd : d ≠ ⊤)
    (hG1 : Objects.Shadow.circleOuter z s.toNNReal 0
      {x | ∃ hx : x ∈ sphere z s, ENNReal.ofReal R * N <
        Objects.BoundaryDecay.annulusBoundaryCost D' (half_lt_self_of_pos hs) ⟨x, hx⟩} ≤
      ENNReal.ofReal ((lam / 2) * s))
    (hG2 : Objects.CorrectedEvent.around D' z ((1 / 2) * s) (1 * s) ≤ ENNReal.ofReal R * N)
    (hG3 : ENNReal.ofReal R⁻¹ * N ≤ Objects.CorrectedEvent.acr D' z ((1 / 2) * s) (1 * s))
    (hEL : OptimalConstants.Ratios.setDist D' {u} (sphere u ρ) ≤ ENNReal.ofReal t * d) :
    ∃ hu' : u ∈ closedBall z s, Objects.Shadow.circleOuter z s.toNNReal 0
      (sphere z s \ Objects.Producer.goodSet D z u s (lam * d.toReal) hu') ≤ ENNReal.ofReal (lam * s / 2) := by
  have huK : u ∈ closedBall z s := mem_closedBall.mpr (by linarith [hu.le])
  refine ⟨huK, ?_⟩
  
  have hacr := acr_le_setDist D' hcont hL hu.le hball
  have hN3 : N ≤ ENNReal.ofReal R * (ENNReal.ofReal t * d) := by
    have h := hG3.trans (hacr.trans hEL)
    calc N = ENNReal.ofReal R * (ENNReal.ofReal R⁻¹ * N) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hR.le, mul_inv_cancel₀ hR.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal R * (ENNReal.ofReal t * d) := by gcongr
  
  set dr : ℝ := d.toReal with hdr
  have hd' : d = ENNReal.ofReal dr := (ENNReal.ofReal_toReal hd).symm
  have hdr0 : 0 ≤ dr := ENNReal.toReal_nonneg
  have hRN : ENNReal.ofReal R * N ≤ ENNReal.ofReal (R * (R * (t * dr))) := by
    calc ENNReal.ofReal R * N ≤ ENNReal.ofReal R * (ENNReal.ofReal R * (ENNReal.ofReal t * d)) := by
          gcongr
      _ = ENNReal.ofReal (R * (R * (t * dr))) := by
          rw [hd', ← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul hR.le, ← ENNReal.ofReal_mul hR.le]
  have hsum : ENNReal.ofReal R * N + ENNReal.ofReal R * N + ENNReal.ofReal t * d ≤
      ENNReal.ofReal (R * (R * (t * dr)) + R * (R * (t * dr)) + t * dr) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), hd', ← ENNReal.ofReal_mul ht]
    gcongr
  have hfinal : ENNReal.ofReal cm⁻¹ *
      ENNReal.ofReal (R * (R * (t * dr)) + R * (R * (t * dr)) + t * dr) ≤
        ENNReal.ofReal (lam * dr) := by
    rw [← ENNReal.ofReal_mul (inv_pos.mpr hcm).le]
    apply ENNReal.ofReal_le_ofReal
    have h1 : R * (R * (t * dr)) + R * (R * (t * dr)) + t * dr = ((2 * R ^ 2 + 1) * t) * dr := by
      ring
    rw [h1]
    have h2 : (2 * R ^ 2 + 1) * t * dr ≤ lam ^ 2 * dr := mul_le_mul_of_nonneg_right hnum hdr0
    have h3 : cm⁻¹ * (lam ^ 2 * dr) ≤ lam * dr := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hdr0
      rw [inv_mul_le_iff₀ hcm, sq]
      exact mul_le_mul_of_nonneg_right hlamcm hlam.le
    calc cm⁻¹ * ((2 * R ^ 2 + 1) * t * dr) ≤ cm⁻¹ * (lam ^ 2 * dr) :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hcm).le
      _ ≤ lam * dr := h3
  
  have hsub : sphere z s \ Objects.Producer.goodSet D z u s (lam * dr) huK ⊆
      {x | ∃ hx : x ∈ sphere z s, ENNReal.ofReal R * N <
        Objects.BoundaryDecay.annulusBoundaryCost D' (half_lt_self_of_pos hs) ⟨x, hx⟩} := by
    rintro x ⟨hx, hxg⟩
    refine ⟨hx, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hxg
    refine ⟨hx, sphere_subset_closedBall hx, ?_⟩
    have hint' := internal_ball_le_three D' hcont hL hs hu hball ⟨x, hx⟩ hcon hG2 hEL
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) (sphere_subset_closedBall hx) huK
    have hint := Objects.Shield.internal_le_mul_of_pointwise D' D cm⁻¹ (inv_pos.mpr hcm) hcomp
      (closedBall z s) ⟨x, sphere_subset_closedBall hx⟩ ⟨u, huK⟩
    calc D.internal (closedBall z s) (⟨x, sphere_subset_closedBall hx⟩, ⟨u, huK⟩)
        ≤ ENNReal.ofReal cm⁻¹ *
            D'.internal (closedBall z s) (⟨x, sphere_subset_closedBall hx⟩, ⟨u, huK⟩) := hint
      _ ≤ ENNReal.ofReal cm⁻¹ *
            (ENNReal.ofReal R * N + ENNReal.ofReal R * N + ENNReal.ofReal t * d) := by gcongr
      _ ≤ ENNReal.ofReal cm⁻¹ *
            ENNReal.ofReal (R * (R * (t * dr)) + R * (R * (t * dr)) + t * dr) := by gcongr
      _ ≤ ENNReal.ofReal (lam * dr) := hfinal
  calc Objects.Shadow.circleOuter z s.toNNReal 0 (sphere z s \ Objects.Producer.goodSet D z u s (lam * dr) huK)
      ≤ Objects.Shadow.circleOuter z s.toNNReal 0
          {x | ∃ hx : x ∈ sphere z s, ENNReal.ofReal R * N <
            Objects.BoundaryDecay.annulusBoundaryCost D' (half_lt_self_of_pos hs) ⟨x, hx⟩} :=
        Objects.Shadow.circleOuter_mono hsub
    _ ≤ ENNReal.ofReal ((lam / 2) * s) := hG1
    _ = ENNReal.ofReal (lam * s / 2) := by ring_nf

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
