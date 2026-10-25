import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C8Splice
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Regularity




 























set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 

theorem len_add (D : LSCMetric) (P : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    D.len P a b + D.len P b c = D.len P a c := by
  have := eVariationOn.Icc_add_Icc (D.pt ∘ P) (s := univ) hab hbc (mem_univ b)
  show eVariationOn (D.pt ∘ P) (Icc a b) + eVariationOn (D.pt ∘ P) (Icc b c) =
    eVariationOn (D.pt ∘ P) (Icc a c)
  simpa only [univ_inter] using this

theorem internal_le_len_sub (D : LSCMetric) {U : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hU : ∀ t ∈ Icc a b, P t ∈ U) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hst : s ≤ t) :
    D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩) ≤ D.len P s t :=
  BiLipschitz.Barrier.internal_le_len' D ⟨hst, hP.2.mono (Icc_subset_Icc hs.1 ht.2)⟩
    (fun u hu => hU u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩)

 

theorem geodesic_sub (D : LSCMetric) {U : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hU : ∀ t ∈ Icc a b, P t ∈ U)
    (hgeo : D.len P a b = D.internal U
      (⟨P a, hU a (left_mem_Icc.2 hP.1)⟩, ⟨P b, hU b (right_mem_Icc.2 hP.1)⟩))
    (hfin : D.len P a b ≠ ⊤) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    D.len P s t = D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩) := by
  refine le_antisymm ?_ (internal_le_len_sub D hP hU hs ht hst)
  have ha : a ∈ Icc a b := left_mem_Icc.2 hP.1
  have hb : b ∈ Icc a b := right_mem_Icc.2 hP.1
  have h1 := len_add D P hs.1 hst
  have h2 := len_add D P (hs.1.trans hst) ht.2
  have htri := (LSCMetric.isExtMetric_internal D U).2.2.2
  have hI : D.internal U (⟨P a, hU a ha⟩, ⟨P b, hU b hb⟩) ≤
      D.len P a s + D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩) + D.len P t b := by
    calc D.internal U (⟨P a, hU a ha⟩, ⟨P b, hU b hb⟩)
        ≤ D.internal U (⟨P a, hU a ha⟩, ⟨P t, hU t ht⟩) +
            D.internal U (⟨P t, hU t ht⟩, ⟨P b, hU b hb⟩) := htri _ _ _
      _ ≤ (D.internal U (⟨P a, hU a ha⟩, ⟨P s, hU s hs⟩) +
            D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩)) +
            D.internal U (⟨P t, hU t ht⟩, ⟨P b, hU b hb⟩) := by
          gcongr; exact htri _ _ _
      _ ≤ (D.len P a s + D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩)) + D.len P t b := by
          gcongr
          · exact internal_le_len_sub D hP hU ha hs hs.1
          · exact internal_le_len_sub D hP hU ht hb ht.2
  have hfin1 : D.len P a s ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [← h2, ← h1]
    exact le_add_right (le_add_right le_rfl)
  have hfin3 : D.len P t b ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [← h2]
    exact le_add_left le_rfl
  have key : D.len P a s + D.len P s t + D.len P t b ≤
      D.len P a s + D.internal U (⟨P s, hU s hs⟩, ⟨P t, hU t ht⟩) + D.len P t b := by
    rw [h1, h2, hgeo]
    exact hI
  have key2 := (ENNReal.add_le_add_iff_right hfin3).1 key
  exact (ENNReal.add_le_add_iff_left hfin1).1 key2

 

theorem norm_polar (s θ : ℝ) : ‖Objects.CorrectedEvent.polar s θ‖ = |s| := by
  rw [Objects.CorrectedEvent.polar, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_eq_abs]

theorem norm_orientation {T : Objects.CorrectedEvent.TubeData} (h : T.orientation ^ 4 = 1) : ‖T.orientation‖ = 1 := by
  have h4 : ‖T.orientation‖ ^ 4 = 1 := by rw [← norm_pow, h, norm_one]
  have h0 : 0 ≤ ‖T.orientation‖ := norm_nonneg _
  exact (pow_eq_one_iff_of_nonneg h0 (by norm_num)).1 h4

theorem norm_site (T : Objects.CorrectedEvent.TubeData) (hr : 0 < T.r) (k : Fin T.K) : ‖Objects.CorrectedEvent.site T k‖ = 2 * T.r := by
  rw [Objects.CorrectedEvent.site, norm_polar, abs_of_pos (by linarith)]

theorem norm_moduleMap_sub_site (T : Objects.CorrectedEvent.TubeData) (hρ : 0 < T.rho) (hr : 0 < T.r)
    (ho : ‖T.orientation‖ = 1) (k : Fin T.K) (w : ℂ) :
    ‖Objects.CorrectedEvent.moduleMap T k w - Objects.CorrectedEvent.site T k‖ = T.rho * T.r * ‖w‖ := by
  rw [Objects.CorrectedEvent.moduleMap, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, ho, mul_one,
    Real.norm_eq_abs, abs_of_pos (mul_pos hρ hr)]

 
theorem norm_cellCenter_sub (c : ℂ) {s : ℝ} (hs : 0 ≤ s) (l : Objects.CorrectedEvent.Cell) :
    ‖Objects.CorrectedEvent.cellCenter c s l - c‖ = s := by
  rw [Objects.CorrectedEvent.cellCenter, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]

 
theorem norm_exp_sub_exp_le (θ φ : ℝ) :
    ‖cexp (θ * I) - cexp (φ * I)‖ ≤ |θ - φ| := by
  have h : cexp (θ * I) - cexp (φ * I) = cexp (φ * I) * (cexp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans_eq (Real.norm_eq_abs _)

 
theorem supRadius_bounds (C : Objects.CorrectedEvent.Constants) {k : ℕ} (hk : k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C)) :
    8 * C.A_sup * C.r ≤ Objects.CorrectedEvent.supRadius C k ∧ Objects.CorrectedEvent.supRadius C k ≤ C.r / 8 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hsup := C.supPos
  have hr := C.rPos
  have h4k : (4 : ℝ) ≤ 4 ^ k := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hx : 1 ≤ 1 / (16 * C.A_sup) := by
    rw [le_div_iff₀ (by positivity)]
    have := C.supLe
    linarith
  have hlog : 0 ≤ Real.logb 4 (1 / (16 * C.A_sup)) :=
    Real.logb_nonneg (by norm_num) hx
  have hkle : (k : ℝ) ≤ Real.logb 4 (1 / (16 * C.A_sup)) := by
    have := Nat.floor_le hlog
    have hk2' : (k : ℝ) ≤ (Objects.CorrectedEvent.supK C : ℝ) := by exact_mod_cast hk2
    exact hk2'.trans (by simpa [Objects.CorrectedEvent.supK] using this)
  have h4kle : (4 : ℝ) ^ k ≤ 1 / (16 * C.A_sup) := by
    have h1 : (4 : ℝ) ^ k = (4 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 4 k).symm
    rw [h1]
    calc (4 : ℝ) ^ (k : ℝ) ≤ (4 : ℝ) ^ (Real.logb 4 (1 / (16 * C.A_sup))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hkle
      _ = 1 / (16 * C.A_sup) := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  unfold Objects.CorrectedEvent.supRadius
  constructor
  · have h8 : (4 : ℝ) * (2 * C.A_sup) ≤ 4 ^ k * (2 * C.A_sup) := by gcongr
    have h9 : (4 : ℝ) * (2 * C.A_sup) * C.r ≤ 4 ^ k * (2 * C.A_sup) * C.r := by gcongr
    linarith
  · have : (4 : ℝ) ^ k * (2 * C.A_sup) ≤ 1 / 8 := by
      calc (4 : ℝ) ^ k * (2 * C.A_sup) ≤ 1 / (16 * C.A_sup) * (2 * C.A_sup) := by gcongr
        _ = 1 / 8 := by field_simp; ring
    nlinarith

 
theorem cell_point_near (C : Objects.CorrectedEvent.Constants) {c : ℂ} {s : ℝ} (hs : 0 < s) {l : ℕ}
    {θ : ℝ} (hθ : θ ∈ Ico (Objects.CorrectedEvent.circleCell C s l).lo (Objects.CorrectedEvent.circleCell C s l).hi) :
    ‖(c + (s : ℂ) * cexp (θ * I)) - Objects.CorrectedEvent.cellCenter c s (Objects.CorrectedEvent.circleCell C s l)‖ ≤
      Objects.CorrectedEvent.supRadius C 1 / 160 := by
  have hR1 : 0 < Objects.CorrectedEvent.supRadius C 1 := by
    unfold Objects.CorrectedEvent.supRadius
    have := C.supPos; have := C.rPos
    positivity
  set N := Objects.CorrectedEvent.numCells C s with hN
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.2 (Objects.Splice.num_cells_pos C hs)
  have hwidth : (Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo =
      2 * Real.pi / N := by
    simp only [Objects.CorrectedEvent.circleCell, ← hN]
    push_cast
    field_simp
    ring
  have hNge : 2 * Real.pi / ((1 / 20 : ℝ) * Objects.CorrectedEvent.supRadius C 1 / (4 * s)) ≤ N := by
    rw [hN]
    exact Nat.le_ceil _
  have hden : 0 < (1 / 20 : ℝ) * Objects.CorrectedEvent.supRadius C 1 / (4 * s) := by positivity
  have hw : 2 * Real.pi / N ≤ (1 / 20 : ℝ) * Objects.CorrectedEvent.supRadius C 1 / (4 * s) := by
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hden] at hNge
    linarith
  have hmid : |θ - ((Objects.CorrectedEvent.circleCell C s l).lo + (Objects.CorrectedEvent.circleCell C s l).hi) / 2| ≤
      ((Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hdiff : (c + (s : ℂ) * cexp (θ * I)) - Objects.CorrectedEvent.cellCenter c s (Objects.CorrectedEvent.circleCell C s l) =
      (s : ℂ) * (cexp (θ * I) -
        cexp ((((Objects.CorrectedEvent.circleCell C s l).lo + (Objects.CorrectedEvent.circleCell C s l).hi) / 2 : ℝ) * I)) := by
    rw [Objects.CorrectedEvent.cellCenter]
    ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc s * ‖cexp (θ * I) -
        cexp ((((Objects.CorrectedEvent.circleCell C s l).lo + (Objects.CorrectedEvent.circleCell C s l).hi) / 2 : ℝ) * I)‖
      ≤ s * |θ - ((Objects.CorrectedEvent.circleCell C s l).lo + (Objects.CorrectedEvent.circleCell C s l).hi) / 2| := by
        gcongr
        exact norm_exp_sub_exp_le _ _
    _ ≤ s * (((Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo) / 2) := by gcongr
    _ ≤ s * (((1 / 20 : ℝ) * Objects.CorrectedEvent.supRadius C 1 / (4 * s)) / 2) := by
        gcongr
        rw [hwidth]
        exact hw
    _ = Objects.CorrectedEvent.supRadius C 1 / 160 := by field_simp; ring

theorem isCompact_cann (w : ℂ) (a b : ℝ) : IsCompact (Objects.CorrectedEvent.cann w a b) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {x : ℂ | a ≤ dist x w} := isClosed_le continuous_const (continuous_id.dist continuous_const)
    have h2 : IsClosed {x : ℂ | dist x w ≤ b} := isClosed_le (continuous_id.dist continuous_const) continuous_const
    exact h1.inter h2
  · exact (Metric.isBounded_closedBall (x := w) (r := b)).subset fun x hx => hx.2

 

 
def hitSet (P : ℝ → ℂ) (a b ε : ℝ) : Set ℂ := {x | ∃ t ∈ Icc a b, dist (P t) x < ε}

 



theorem c8_circle_le_badLength (C : Objects.CorrectedEvent.Constants) (hρ : C.ρ < 1 / 64)
    (D Db : LSCMetric) (f : C(ℂ, ℝ)) (hL : D.IsLengthSpace) (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {c : ℂ} {s : ℝ} (hs : 0 < s) (hsρ : s ≤ C.ρ * C.r)
    (hc1 : 2 * C.r - C.ρ * C.r ≤ ‖c‖) (hc2 : ‖c‖ ≤ 2 * C.r + C.ρ * C.r)
    {P : ℝ → ℂ} {a b : ℝ} (hPb : Db.IsCurve P a b)
    (hPK : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (hgeo : Db.len P a b = Db.internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
      (⟨P a, hPK a (left_mem_Icc.2 hPb.1)⟩, ⟨P b, hPK b (right_mem_Icc.2 hPb.1)⟩))
    (hfin : Db.len P a b ≠ ⊤) (ha : ‖P a‖ = 4 * C.r) (hb : ‖P b‖ = 4 * C.r) :
    Objects.Shadow.circleOuter c ⟨s, hs.le⟩ 0 (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (Objects.CorrectedEvent.badLength C D c s) := by
  have hr := C.rPos
  have hρ0 := C.rhoPos
  have hsup := C.supPos
  apply Objects.Splice.circle_outer_le_bad_length_of_good_cell_exclusion C D c hs
  intro l hl k hk hgood θ hθ hhit
  obtain ⟨t, ht, hdist⟩ := hhit
  obtain ⟨hRlo, hRhi⟩ := supRadius_bounds C hk
  have hR1lo : 8 * C.A_sup * C.r ≤ Objects.CorrectedEvent.supRadius C 1 :=
    (supRadius_bounds C (Finset.mem_Icc.2 ⟨le_rfl, (Finset.mem_Icc.1 hk).1.trans
      (Finset.mem_Icc.1 hk).2⟩)).1
  have hR1le : Objects.CorrectedEvent.supRadius C 1 ≤ Objects.CorrectedEvent.supRadius C k := by
    unfold Objects.CorrectedEvent.supRadius
    have h4 : (4 : ℝ) ^ 1 ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) (Finset.mem_Icc.1 hk).1
    gcongr
  set R := Objects.CorrectedEvent.supRadius C k with hRdef
  set w := Objects.CorrectedEvent.cellCenter c s (Objects.CorrectedEvent.circleCell C s l) with hw
  have hR : 0 < R := by nlinarith
  have hwc : ‖w - c‖ = s := norm_cellCenter_sub c hs.le _
  have hw1 : 2 * C.r - 2 * (C.ρ * C.r) ≤ ‖w‖ := by
    have := norm_sub_norm_le w c
    have h2 := norm_sub_norm_le c w
    rw [norm_sub_rev] at h2
    linarith
  have hw2 : ‖w‖ ≤ 2 * C.r + 2 * (C.ρ * C.r) := by
    have := norm_le_insert' w c
    linarith [norm_sub_rev w c]
  have hnear := cell_point_near C (c := c) hs hθ
  have hvisit : dist (P t) w ≤ (1 + 1 / 20) * R := by
    have h1 : dist (P t) w ≤ dist (P t) (c + (s : ℂ) * cexp (θ * I)) +
        dist (c + (s : ℂ) * cexp (θ * I)) w := dist_triangle _ _ _
    rw [dist_eq_norm (c + (s : ℂ) * cexp (θ * I)) w] at h1
    nlinarith
  have hfar : ∀ x : ℂ, ‖x‖ = 4 * C.r → x ∈ (ball w ((3 - 1 / 20) * R))ᶜ := by
    intro x hx
    rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm]
    have := norm_sub_norm_le x w
    nlinarith
  have hends := And.intro (hfar (P a) ha) (hfar (P b) hb)
  have hcarrier : Objects.CorrectedEvent.ann w ((2 + 1 / 20) * R) ((3 - 1 / 20) * R) ⊆ Objects.CorrectedEvent.cann 0 C.r (4 * C.r) := by
    intro x hx
    have hx2 : dist x w < (3 - 1 / 20) * R := hx.2
    rw [dist_eq_norm] at hx2
    refine ⟨?_, ?_⟩
    · rw [dist_zero_right]
      have := norm_sub_norm_le w x
      rw [norm_sub_rev] at this
      nlinarith
    · rw [dist_zero_right]
      have := norm_le_insert' x w
      nlinarith
  have hat : a < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · exfalso
      have hcon := hends.1
      rw [h, mem_compl_iff, mem_ball] at hcon
      exact hcon (lt_of_le_of_lt hvisit (by nlinarith))
    · exact h
  have htb : t < b := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · exfalso
      have hcon := hends.2
      rw [← h, mem_compl_iff, mem_ball] at hcon
      exact hcon (lt_of_le_of_lt hvisit (by nlinarith))
    · exact h
  exact Objects.Splice.good_cell_visit_impossible_of_weyl C D Db (Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) f
    hforget hWeyl hf hL c s (Objects.CorrectedEvent.circleCell C s l) k hR hgood
    hat htb hPb (isCompact_cann 0 C.r (4 * C.r)) hPK hends hvisit hcarrier
    (fun t₁ t₂ h₁ h₂ h12 => geodesic_sub Db hPb hPK hgeo hfin h₁ h₂ h12)

 

theorem kann_lt_one (C : Objects.CorrectedEvent.Constants) : C.K_ann < 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : C.lamConst * (1 - C.K_ann) * C.A_endpt * C.ρ ≤ 0 := by
    have hl := C.lamPos; have he := C.endptPos; have hr := C.rhoPos
    have : 1 - C.K_ann ≤ 0 := by linarith
    have h2 : C.lamConst * (1 - C.K_ann) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl.le this
    have h3 : C.lamConst * (1 - C.K_ann) * C.A_endpt ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 he.le
    exact mul_nonpos_of_nonpos_of_nonneg h3 hr.le
  have := C.narLe
  have := C.narPos
  linarith

 
theorem blockCentre_bounds (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (k : Fin T.K) :
    (2 * C.r - C.ρ * C.r ≤ ‖Objects.CorrectedEvent.innerCenter T k‖ ∧ ‖Objects.CorrectedEvent.innerCenter T k‖ ≤ 2 * C.r + C.ρ * C.r) ∧
    (2 * C.r - C.ρ * C.r ≤ ‖Objects.CorrectedEvent.outerCenter T k‖ ∧ ‖Objects.CorrectedEvent.outerCenter T k‖ ≤ 2 * C.r + C.ρ * C.r) := by
  obtain ⟨hTr, hTrho, -, -, hTalpha, -, horient, -⟩ := hData
  have hr := C.rPos
  have hρ := C.rhoPos
  have ho := norm_orientation horient
  have hK1 := kann_lt_one C
  have hsite := norm_site T (hTr ▸ hr) k
  rw [hTr] at hsite
  have hgen : ∀ w : ℂ, ‖w‖ ≤ 1 →
      2 * C.r - C.ρ * C.r ≤ ‖Objects.CorrectedEvent.moduleMap T k w‖ ∧ ‖Objects.CorrectedEvent.moduleMap T k w‖ ≤ 2 * C.r + C.ρ * C.r := by
    intro w hw
    have hd := norm_moduleMap_sub_site T (hTrho ▸ hρ) (hTr ▸ hr) ho k w
    rw [hTrho, hTr] at hd
    have hd' : ‖Objects.CorrectedEvent.moduleMap T k w - Objects.CorrectedEvent.site T k‖ ≤ C.ρ * C.r := by
      rw [hd]
      have : 0 < C.ρ * C.r := mul_pos hρ hr
      nlinarith [norm_nonneg w]
    constructor
    · have := norm_sub_norm_le (Objects.CorrectedEvent.site T k) (Objects.CorrectedEvent.moduleMap T k w)
      rw [norm_sub_rev] at this
      linarith
    · have := norm_le_insert' (Objects.CorrectedEvent.moduleMap T k w) (Objects.CorrectedEvent.site T k)
      linarith
  refine ⟨hgen _ ?_, hgen _ ?_⟩
  · rw [Objects.CorrectedEvent.uNorm, norm_polar, hTalpha, abs_of_nonneg hK]
    exact hK1.le
  · rw [Objects.CorrectedEvent.vNorm, norm_polar, abs_one]

 
theorem blockRadius_bounds (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hE : C.A_endpt ≤ 1) : 0 < T.blockRadius ∧ T.blockRadius ≤ C.ρ * C.r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlo, hhi, -⟩ := hData
  have hr := C.rPos
  have hρ := C.rhoPos
  have he := C.endptPos
  refine ⟨lt_of_lt_of_le (by positivity) hlo, hhi.trans ?_⟩
  have hsq : Real.sqrt C.A_endpt ≤ 1 := Real.sqrt_le_one.2 hE
  have : 0 < C.ρ * C.r := mul_pos hρ hr
  nlinarith

 



theorem c8_circle_bound (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (D Db : LSCMetric) (f : C(ℂ, ℝ)) (hL : D.IsLengthSpace) (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max) (hS8 : Objects.CorrectedEvent.S8 C T D)
    {P : ℝ → ℂ} {a b : ℝ} (hPb : Db.IsCurve P a b)
    (hPK : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (hgeo : Db.len P a b = Db.internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
      (⟨P a, hPK a (left_mem_Icc.2 hPb.1)⟩, ⟨P b, hPK b (right_mem_Icc.2 hPb.1)⟩))
    (hfin : Db.len P a b ≠ ⊤) (ha : ‖P a‖ = 4 * C.r) (hb : ‖P b‖ = 4 * C.r) (k : Fin T.K) :
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) ∧
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) := by
  obtain ⟨hs, hsρ⟩ := blockRadius_bounds C T hData hE
  obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := blockCentre_bounds C T hData hK k
  obtain ⟨hbu, hbv⟩ := hS8 k
  constructor
  · exact (c8_circle_le_badLength C hρ D Db f hL hforget hWeyl hf hs hsρ hu1 hu2 hPb hPK hgeo hfin
      ha hb).trans (ENNReal.ofReal_le_ofReal hbu)
  · exact (c8_circle_le_badLength C hρ D Db f hL hforget hWeyl hf hs hsρ hv1 hv2 hPb hPK hgeo hfin
      ha hb).trans (ENNReal.ofReal_le_ofReal hbv)

 


theorem c8_of_event (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (F : ℂ → LQGMetric.DistC → Prop) (D D' : LQGMetric.DistC → LSCMetric) (g : LQGMetric.DistC)
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) (hreg : MetricReg C.ξ D g)
    (f : C(ℂ, ℝ)) (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a b : ℝ} (hPb : (D (LQGMetric.addFun g (-f))).IsCurve P a b)
    (hPK : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (hgeo : (D (LQGMetric.addFun g (-f))).len P a b =
      (D (LQGMetric.addFun g (-f))).internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
        (⟨P a, hPK a (left_mem_Icc.2 hPb.1)⟩, ⟨P b, hPK b (right_mem_Icc.2 hPb.1)⟩))
    (hfin : (D (LQGMetric.addFun g (-f))).len P a b ≠ ⊤)
    (ha : ‖P a‖ = 4 * C.r) (hb : ‖P b‖ = 4 * C.r) (k : Fin T.K) :
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) ∧
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) := by
  have hWeyl : ∀ x y : ℂ, D (LQGMetric.addFun g (-f)) (x, y) = weylScale C.ξ (-f) (D g) (x, y) := by
    intro x y
    exact (congrFun (hreg.1.2 (-f)) (x, y)).symm
  exact c8_circle_bound C T hData hK hE hρ (D g) (D (LQGMetric.addFun g (-f))) f hreg.1.1
    (BiLipschitz.Barrier.continuous_forget_of_barrier _ hreg.2 hreg.1.1) hWeyl hf hev.2.2.2.2.2.2.2.1 hPb hPK hgeo hfin ha hb k

 

theorem c8_of_event' (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (F : ℂ → LQGMetric.DistC → Prop) (D D' : LQGMetric.DistC → LSCMetric) (g : LQGMetric.DistC)
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) (hreg : WeylReg C.ξ D g)
    (hforget : Continuous (BiLipschitz.Barrier.forget (D g)))
    (f : C(ℂ, ℝ)) (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a b : ℝ} (hPb : (D (LQGMetric.addFun g (-f))).IsCurve P a b)
    (hPK : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (hgeo : (D (LQGMetric.addFun g (-f))).len P a b =
      (D (LQGMetric.addFun g (-f))).internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
        (⟨P a, hPK a (left_mem_Icc.2 hPb.1)⟩, ⟨P b, hPK b (right_mem_Icc.2 hPb.1)⟩))
    (hfin : (D (LQGMetric.addFun g (-f))).len P a b ≠ ⊤)
    (ha : ‖P a‖ = 4 * C.r) (hb : ‖P b‖ = 4 * C.r) (k : Fin T.K) :
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) ∧
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P a b (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) := by
  have hWeyl : ∀ x y : ℂ, D (LQGMetric.addFun g (-f)) (x, y) = weylScale C.ξ (-f) (D g) (x, y) := by
    intro x y
    exact (congrFun (hreg.2 (-f)) (x, y)).symm
  exact c8_circle_bound C T hData hK hE hρ (D g) (D (LQGMetric.addFun g (-f))) f hreg.1 hforget
    hWeyl hf hev.2.2.2.2.2.2.2.1 hPb hPK hgeo hfin ha hb k

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
