import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Core1




 















set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open LQGMetric.Blueprint
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

 

 
def HtHalf (D D' : DistC → LSCMetric) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1)
    (C θ : Ioi (0 : ℝ)) (n : ℂ) (g : DistC) : Prop :=
  ∃ u v : ℂ, u ∈ sphere (0 : ℂ) (a * r) ∧ v ∈ sphere (0 : ℂ) r ∧
    D' g (u, v) ≤ ENNReal.ofReal C * D g (u, v) ∧
    (∃ (P : ℝ → ℂ) (s t : ℝ), OptimalConstants.Ratios.Geodesic (D' g) P s t u v ∧
      (∀ q ∈ Icc s t, P q ∈ closedBall (0 : ℂ) r \ ball 0 (a * r)) ∧
      ∀ q ∈ Icc s t, halfOK n (P q)) ∧
    OptimalConstants.Ratios.EndpointLoop (D' g) r a θ u v u ∧ OptimalConstants.Ratios.EndpointLoop (D' g) r a θ u v v

 
theorem htilde_half_cover (D D' : DistC → LSCMetric) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) (g : DistC)
    (h : OptimalConstants.Ratios.HtildeEvent D D' ξ Q r a C θ g) : ∃ i : Fin 4, HtHalf D D' r a C θ (orient i) g := by
  obtain ⟨_, _, u, v, hu, hv, _, _, hratio, P, s, t, hgeo, htrace, hdiam, _, hELu, hELv⟩ := h
  have hr : (0 : ℝ) < r := r.2
  have ha : (3 / 4 : ℝ) < a := a.2.1
  have htrace' : ∀ q ∈ Icc s t, P q ∈ closedBall (0 : ℂ) r \ ball 0 (a * r) := htrace
  have hSsub : P '' Icc s t ⊆ closedBall (0 : ℂ) r := by
    rintro _ ⟨q, hq, rfl⟩
    exact (htrace' q hq).1
  have hbdd : Bornology.IsBounded (P '' Icc s t) := isBounded_closedBall.subset hSsub
  have hlow : ∀ w ∈ P '' Icc s t, 3 / 4 * (r : ℝ) ≤ ‖w‖ := by
    rintro _ ⟨q, hq, rfl⟩
    have h2 := (htrace' q hq).2
    rw [mem_ball, dist_zero_right, not_lt] at h2
    nlinarith
  have hdist : ∀ x ∈ P '' Icc s t, ∀ y ∈ P '' Icc s t, ‖x - y‖ ≤ (r : ℝ) / 100 := by
    intro x hx y hy
    rw [← dist_eq_norm]
    exact (dist_le_diam_of_mem hbdd hx hy).trans hdiam
  obtain ⟨i, hi⟩ := exists_orient_of_small_diam (S := P '' Icc s t) hr
    ⟨P s, s, left_mem_Icc.mpr hgeo.1.1, rfl⟩ hlow hdist
  exact ⟨i, u, v, hu, hv, hratio, ⟨P, s, t, hgeo, htrace', fun q hq => hi (P q) ⟨q, hq, rfl⟩⟩,
    hELu, hELv⟩

 

 

def coreAt (lam b α : ℝ) (n : ℂ) (ψu ψv s Cmid0 : ℝ) (D D' : LSCMetric) : Prop :=
  ∃ u v : ℂ, ‖u‖ = α * b ∧ dist u ((b : ℂ) * n * Objects.CorrectedEvent.polar α ψu) < s / 2 ∧
    ‖v‖ = b ∧ dist v ((b : ℂ) * n * Objects.CorrectedEvent.polar 1 ψv) < s / 2 ∧
    D' (u, v) ≤ ENNReal.ofReal Cmid0 * D (u, v) ∧
    D' (u, v) < ⊤ ∧
    (∃ (P : ℝ → ℂ) (a₀ b₀ : ℝ), D'.IsCurve P a₀ b₀ ∧ P a₀ = u ∧ P b₀ = v ∧
      (∀ t ∈ Icc a₀ b₀, P t ∈ closure (blockShapeAt b α n)) ∧ D'.len P a₀ b₀ = D' (u, v)) ∧
    (∃ hu : u ∈ closedBall ((b : ℂ) * n * Objects.CorrectedEvent.polar α ψu) s,
      Objects.Shadow.circleOuter ((b : ℂ) * n * Objects.CorrectedEvent.polar α ψu) s.toNNReal 0
          (sphere ((b : ℂ) * n * Objects.CorrectedEvent.polar α ψu) s \
            Objects.Producer.goodSet D ((b : ℂ) * n * Objects.CorrectedEvent.polar α ψu) u s (lam * (D' (u, v)).toReal) hu) ≤
        ENNReal.ofReal (lam * s / 2)) ∧
    (∃ hv : v ∈ closedBall ((b : ℂ) * n * Objects.CorrectedEvent.polar 1 ψv) s,
      Objects.Shadow.circleOuter ((b : ℂ) * n * Objects.CorrectedEvent.polar 1 ψv) s.toNNReal 0
          (sphere ((b : ℂ) * n * Objects.CorrectedEvent.polar 1 ψv) s \
            Objects.Producer.goodSet D ((b : ℂ) * n * Objects.CorrectedEvent.polar 1 ψv) v s (lam * (D' (u, v)).toReal) hv) ≤
        ENNReal.ofReal (lam * s / 2))

 
def shieldData (lam b : ℝ) (Ksh : ℕ) (D : LSCMetric) : Prop :=
  ∃ k ∈ Finset.Icc 1 Ksh,
    Objects.CorrectedEvent.around D 0 (3 * 8 ^ (Ksh - k) * b) (2 * (3 * 8 ^ (Ksh - k) * b)) < ⊤ ∧
      Objects.CorrectedEvent.around D 0 (3 * 8 ^ (Ksh - k) * b) (2 * (3 * 8 ^ (Ksh - k) * b)) ≤
        ENNReal.ofReal lam * Objects.CorrectedEvent.acr D 0 (2 * (3 * 8 ^ (Ksh - k) * b)) (3 * (3 * 8 ^ (Ksh - k) * b))

theorem blockRaw_iff_core_shield (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D D' : DistC → LSCMetric) (g : DistC) {lam b α ψu ψv s : ℝ} {n : ℂ}
    (hlam : C.lamConst = lam) (hb : T.rho * T.r = b) (hα : T.alpha = α) (hn : T.orientation = n)
    (hu : T.psiU = ψu) (hv : T.psiV = ψv) (hs : T.blockRadius = s) :
    Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g ↔
      coreAt lam b α n ψu ψv s Cmid0 (D g) (D' g) ∧ shieldData lam b Ksh (D g) := by
  subst hlam hb hα hn hu hv hs
  exact Iff.rfl

theorem shield_iff_shieldData (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (D : LSCMetric)
    {lam b : ℝ} (hlam : C.lamConst = lam) (hb : T.rho * T.r = b) :
    Objects.Excursions.shield C T Ksh D ↔ shieldData lam b Ksh D := by
  subst hlam hb
  exact Iff.rfl

 

theorem common_good_scale {Ω : Type} (E₁ E₂ : ℕ → Set Ω) (K : ℕ) (hK : 1 ≤ K) (ω : Ω)
    (h₁ : 3 / 4 * (K : ℝ) ≤ countOcc E₁ K ω) (h₂ : 3 / 4 * (K : ℝ) ≤ countOcc E₂ K ω) :
    ∃ k ∈ Finset.Icc 1 K, ω ∈ E₁ k ∧ ω ∈ E₂ k := by
  classical
  by_contra hne
  push Not at hne
  unfold countOcc at h₁ h₂
  have hdisj : Disjoint ((Finset.Icc 1 K).filter fun k => ω ∈ E₁ k)
      ((Finset.Icc 1 K).filter fun k => ω ∈ E₂ k) :=
    Finset.disjoint_left.2 fun k hk1 hk2 =>
      hne k (Finset.mem_filter.1 hk1).1 (Finset.mem_filter.1 hk1).2 (Finset.mem_filter.1 hk2).2
  have hsub : ((Finset.Icc 1 K).filter fun k => ω ∈ E₁ k) ∪
      ((Finset.Icc 1 K).filter fun k => ω ∈ E₂ k) ⊆ Finset.Icc 1 K :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : ((Finset.Icc 1 K).filter fun k => ω ∈ E₁ k).card +
      ((Finset.Icc 1 K).filter fun k => ω ∈ E₂ k).card ≤ K := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card hsub).trans (by simp)
  have hcard' : (((Finset.Icc 1 K).filter fun k => ω ∈ E₁ k).card : ℝ) +
      ((Finset.Icc 1 K).filter fun k => ω ∈ E₂ k).card ≤ K := by exact_mod_cast hcard
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

 

theorem quarter_pow_sub_one (m k : ℕ) (hk : 1 ≤ k) :
    4 * (1 / 4 : ℝ) ^ (m + k) = (1 / 4 : ℝ) ^ (m + k - 1) := by
  rw [show m + k = (m + k - 1) + 1 by omega, pow_succ]
  simp only [Nat.add_sub_cancel]
  ring

 
theorem core_of_half {ξ Q lam R cm : ℝ} (D D' : DistC → LSCMetric) (g : DistC)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), (D' g).IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : (D' g).IsLengthSpace) (hcm : 0 < cm)
    (hcomp : ∀ p : ℂ × ℂ, D g p ≤ ENNReal.ofReal cm⁻¹ * D' g p)
    (b : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) (m : ℕ) (i : Fin 4)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 100) (hlamcm : lam ≤ cm) (hR : 1 ≤ R)
    (hm1 : 2 * (1 / 4 : ℝ) ^ m ≤ (1 - (a : ℝ)) ^ 2)
    (hE20 : (2 * R ^ 2 + 1) * (2 * (1 / 4 : ℝ) ^ m) ^ (θ : ℝ) ≤ lam ^ 2)
    (hH : HtHalf D D' b a C θ (orient i) g)
    (hU : UEv ξ Q lam R D' b b.2 a (lam * Objects.Density.endptScale m) m g) :
    ∃ j ∈ shapeData (lam * Objects.Density.endptScale m) m,
      coreAt lam b a (orient i) j.2.1 j.2.2 (j.1 * b) C (D g) (D' g) := by
  obtain ⟨u, v, hu, hv, hratio, ⟨P, s₀, t₀, hgeo, htrace, hhalf⟩, hELu, hELv⟩ := hH
  have hb : (0 : ℝ) < b := b.2
  have ha0 : (0 : ℝ) < a := by linarith [a.2.1]
  have ha1 : (a : ℝ) < 1 := a.2.2
  have hR0 : 0 < R := by linarith
  set δ : ℝ := lam * Objects.Density.endptScale m with hδdef
  have hA : 0 < Objects.Density.endptScale m := Objects.Density.endptScale_pos m
  have hAeq : Objects.Density.endptScale m = (1 / 16 : ℝ) ^ m := rfl
  have hδ : 0 < δ := mul_pos hlam hA
  have hq4 : (0 : ℝ) < (1 / 4 : ℝ) ^ m := pow_pos (by norm_num) m
  have h16le4 : (1 / 16 : ℝ) ^ m ≤ (1 / 4 : ℝ) ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) m
  
  have hu_norm : ‖u‖ = a * b := by rw [← dist_zero_right]; exact mem_sphere.mp hu
  have hv_norm : ‖v‖ = b := by rw [← dist_zero_right]; exact mem_sphere.mp hv
  have hst : s₀ ≤ t₀ := hgeo.1.1
  have hhalf_u : halfOK (orient i) u := by
    rw [← hgeo.2.1]; exact hhalf s₀ (left_mem_Icc.mpr hst)
  have hhalf_v : halfOK (orient i) v := by
    rw [← hgeo.2.2.1]; exact hhalf t₀ (right_mem_Icc.mpr hst)
  have hd : D' g (u, v) ≠ ⊤ := hgeo.2.2.2.2.ne
  
  obtain ⟨ψu, hψu, hu_close⟩ := grid_point_near (ρ := a * b) (mul_pos ha0 hb) (orient_norm i)
    hu_norm hhalf_u hδ
  obtain ⟨ψv, hψv, hv_close⟩ := grid_point_near (ρ := b) hb (orient_norm i) hv_norm hhalf_v hδ
  set z₁ : ℂ := (b : ℂ) * orient i * Objects.CorrectedEvent.polar a ψu with hz₁
  set z₂ : ℂ := (b : ℂ) * orient i * Objects.CorrectedEvent.polar 1 ψv with hz₂
  have hz₁eq : (((a : ℝ) * b : ℝ) : ℂ) * orient i * Complex.exp (ψu * Complex.I) = z₁ := by
    rw [hz₁, Objects.CorrectedEvent.polar]; push_cast; ring
  have hz₂eq : ((b : ℝ) : ℂ) * orient i * Complex.exp (ψv * Complex.I) = z₂ := by
    rw [hz₂, Objects.CorrectedEvent.polar]; push_cast; ring
  have hdu : dist u z₁ ≤ a * b * δ := by rw [dist_eq_norm, ← hz₁eq]; exact hu_close
  have hdv : dist v z₂ ≤ b * δ := by rw [dist_eq_norm, ← hz₂eq]; exact hv_close
  have hz₁W : z₁ ∈ gridCentres b a δ :=
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨(orient i, ψu),
      Finset.mem_product.2 ⟨orient_mem i, hψu⟩, rfl⟩)
  have hz₂W : z₂ ∈ gridCentres b a δ :=
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨(orient i, ψv),
      Finset.mem_product.2 ⟨orient_mem i, hψv⟩, rfl⟩)
  
  obtain ⟨k, hk, hG₁, hG₂⟩ := common_good_scale
    (fun k => {g | GEv ξ Q lam R D' z₁ (gScale b b.2 m k) g})
    (fun k => {g | GEv ξ Q lam R D' z₂ (gScale b b.2 m k) g}) (m + 1) (by omega) g
    (hU z₁ hz₁W) (hU z₂ hz₂W)
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  set ρ' : ℝ := (1 / 4 : ℝ) ^ (m + k - 1) with hρ'
  have hs_eq : ((gScale b b.2 m k : Ioi (0 : ℝ)) : ℝ) = ρ' * b := by
    change 4 * (b : ℝ) * (1 / 4 : ℝ) ^ (m + k) = ρ' * b
    rw [hρ', ← quarter_pow_sub_one m k hk1]
    ring
  have hρ'mem : ρ' ∈ radiusRatios m :=
    Finset.mem_image.2 ⟨m + k - 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
  have hρ'lo : (1 / 16 : ℝ) ^ m ≤ ρ' := by
    have h1 : (1 / 4 : ℝ) ^ (2 * m) ≤ ρ' :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 4 : ℝ) ^ (2 * m) = (1 / 16 : ℝ) ^ m := by
      rw [pow_mul]; norm_num
    linarith
  have hρ'hi : ρ' ≤ (1 / 4 : ℝ) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  set s : ℝ := ρ' * b with hsdef
  have hs : 0 < s := mul_pos (lt_of_lt_of_le (pow_pos (by norm_num) m) hρ'lo) hb
  
  set X : ℝ := (1 / 16 : ℝ) ^ m * b with hXdef
  have hX : 0 < X := mul_pos (pow_pos (by norm_num) m) hb
  have hXs : X ≤ s := by rw [hXdef, hsdef]; exact mul_le_mul_of_nonneg_right hρ'lo hb.le
  have hX4 : X ≤ (1 / 4 : ℝ) ^ m * b := mul_le_mul_of_nonneg_right h16le4 hb.le
  have hδu : (a : ℝ) * b * δ = a * lam * X := by rw [hδdef, hAeq, hXdef]; ring
  have hδv : (b : ℝ) * δ = lam * X := by rw [hδdef, hAeq, hXdef]; ring
  have hlamhalf : (a : ℝ) * lam < 1 / 2 := by nlinarith
  have hlamhalf' : lam < 1 / 2 := by linarith
  have hu1 : (a : ℝ) * lam * X < 1 / 2 * X := mul_lt_mul_of_pos_right hlamhalf hX
  have hv1 : lam * X < 1 / 2 * X := mul_lt_mul_of_pos_right hlamhalf' hX
  have hdu' : dist u z₁ < s / 2 := by linarith
  have hdv' : dist v z₂ < s / 2 := by linarith
  set δ₀ : ℝ := 2 * (1 / 4 : ℝ) ^ m with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  have hs_hi : s ≤ (1 / 4 : ℝ) ^ m * b := mul_le_mul_of_nonneg_right hρ'hi hb.le
  have hδ₀b : δ₀ * b = 2 * ((1 / 4 : ℝ) ^ m * b) := by rw [hδ₀]; ring
  have hball_u : closedBall z₁ s ⊆ ball u (δ₀ * b) := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball, hδ₀b]
    have h1 : dist y u ≤ dist y z₁ + dist z₁ u := dist_triangle _ _ _
    have h2 : dist z₁ u = dist u z₁ := dist_comm _ _
    linarith
  have hball_v : closedBall z₂ s ⊆ ball v (δ₀ * b) := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball, hδ₀b]
    have h1 : dist y v ≤ dist y z₂ + dist z₂ v := dist_triangle _ _ _
    have h2 : dist z₂ v = dist v z₂ := dist_comm _ _
    linarith
  
  obtain ⟨Au, -, -, -, hAu⟩ := hELu δ₀ hδ₀pos hm1
  obtain ⟨Av, -, -, -, hAv⟩ := hELv δ₀ hδ₀pos hm1
  have hELu' : OptimalConstants.Ratios.setDist (D' g) {u} (sphere u (δ₀ * b)) ≤
      ENNReal.ofReal (δ₀ ^ (θ : ℝ)) * D' g (u, v) := (le_max_left _ _).trans hAu
  have hELv' : OptimalConstants.Ratios.setDist (D' g) {v} (sphere v (δ₀ * b)) ≤
      ENNReal.ofReal (δ₀ ^ (θ : ℝ)) * D' g (u, v) := (le_max_left _ _).trans hAv
  have ht0 : 0 ≤ δ₀ ^ (θ : ℝ) := Real.rpow_nonneg hδ₀pos.le _
  
  have hG₁' : GEv ξ Q lam R D' z₁ (gScale b b.2 m k) g := hG₁
  have hG₂' : GEv ξ Q lam R D' z₂ (gScale b b.2 m k) g := hG₂
  have hsG : (0 : ℝ) < (gScale b b.2 m k : ℝ) := (gScale b b.2 m k).2
  obtain ⟨hGu1, hGu2, hGu3⟩ := hG₁'
  obtain ⟨hGv1, hGv2, hGv3⟩ := hG₂'
  have hF3u := F3_of_G (D g) (D' g) hcont hL hcm hcomp hlam hR0 ht0 hE20 hlamcm hsG
    (by rw [hs_eq]; exact hdu') (by rw [hs_eq]; exact hball_u) ENNReal.ofReal_ne_top hd
    hGu1 hGu2 hGu3 hELu'
  have hF3v := F3_of_G (D g) (D' g) hcont hL hcm hcomp hlam hR0 ht0 hE20 hlamcm hsG
    (by rw [hs_eq]; exact hdv') (by rw [hs_eq]; exact hball_v) ENNReal.ofReal_ne_top hd
    hGv1 hGv2 hGv3 hELv'
  rw [hs_eq] at hF3u hF3v
  
  have htrace' : ∀ q ∈ Icc s₀ t₀, P q ∈ closure (blockShapeAt b a (orient i)) := by
    intro q hq
    have h1 := (htrace q hq).1
    have h2 := (htrace q hq).2
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right, not_lt] at h2
    exact mem_closure_blockShapeAt hb ha0 ha1 (orient_norm i) h2 h1 (hhalf q hq)
  refine ⟨(ρ', ψu, ψv), Finset.mem_product.2 ⟨hρ'mem, Finset.mem_product.2 ⟨hψu, hψv⟩⟩, ?_⟩
  exact ⟨u, v, hu_norm, hdu', hv_norm, hdv', hratio, hgeo.2.2.2.2,
    ⟨P, s₀, t₀, hgeo.1, hgeo.2.1, hgeo.2.2.1, htrace', hgeo.2.2.2.1⟩, hF3u, hF3v⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
