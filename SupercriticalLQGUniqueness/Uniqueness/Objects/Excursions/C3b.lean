import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.C3




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 
theorem c3_core (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    (hS3 : Objects.CorrectedEvent.S3 C D)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεep : ε ≤ (2 : ℝ) ^ (-(C.k0 : ℝ)))
    {z : ℂ} (hProt : closedBall z (Real.sqrt ε * C.r) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    {P : ℝ → ℂ} {a s b : ℝ} (has : a < s) (hsb : s < b)
    (hcont : ContinuousOn P (Icc a b))
    (hdist : ∀ u v, a ≤ u → u ≤ v → v ≤ b → Db (P u, P v) = ENNReal.ofReal (v - u))
    (hpre : ∀ u v, a ≤ u → u ≤ v → v ≤ s → D.IsCurve P u v ∧ D.len P u v ≤ ENNReal.ofReal (v - u))
    (ha : Real.sqrt ε * C.r ≤ dist (P a) z) (hb : Real.sqrt ε * C.r ≤ dist (P b) z)
    (hs : dist (P s) z ≤ ε * C.r) :
    Objects.CorrectedEvent.around D z (ε * C.r) (Real.sqrt ε * C.r) ≤ ENNReal.ofReal (ε ^ theta C * (s - a)) := by
  classical
  obtain ⟨k, hk, hεlam, hlamε⟩ := exists_lam_index hε hεep
  have hk48 : 48 ≤ k := C.k0Large.trans hk
  have hr := C.rPos
  have hlampos : 0 < Objects.CorrectedEvent.lam k := by unfold Objects.CorrectedEvent.lam; positivity
  have hRadius := Objects.Network.reg_radius_le_sqrt k hk48 ε hε hεlam hlamε C.r C.rPos
  set x' := TwoScale.TwoSet.nearestGrid (Objects.CorrectedEvent.lam k * C.r / 4) z with hx'def
  have hsite : x' ∈ Objects.CorrectedEvent.regSites C k :=
    Objects.Network.nearestGrid_reg_site_of_radius_bound C k ε z hProt hRadius
  have hnear : dist x' z < Objects.CorrectedEvent.lam k * C.r / 4 := by
    rw [dist_comm, dist_eq_norm]
    exact TwoScale.TwoSet.nearestGrid_norm_lt (by positivity) z
  have hcount := hS3 k hk x' hsite
  obtain ⟨G, hGsub, hGgood, hGcard⟩ : ∃ G : Finset ℕ, G ⊆ Finset.Icc 1 (Objects.CorrectedEvent.regK k) ∧
      (∀ j ∈ G, Objects.CorrectedEvent.regGood C D (4 ^ j * Objects.CorrectedEvent.lam k * C.r) x') ∧
      Objects.CorrectedEvent.regK k ≤ 2 * G.card :=
    ⟨_, Finset.filter_subset _ _, fun j hj => (Finset.mem_filter.mp hj).2, hcount⟩
  
  set lo : ℕ → ℝ := fun j => 4 ^ j * Objects.CorrectedEvent.lam k * C.r with hlo
  set hi : ℕ → ℝ := fun j => 2 * (4 ^ j * Objects.CorrectedEvent.lam k * C.r) with hhi
  have hlo_pos : ∀ j, 0 < lo j := fun j => by simp only [hlo]; positivity
  have hlohi : ∀ j, lo j ≤ hi j := fun j => by simp only [hlo, hhi]; linarith [hlo_pos j]
  have hmono : ∀ i j, i < j → hi i ≤ lo j := by
    intro i j hij
    simp only [hlo, hhi]
    have h4 : (4 : ℝ) ^ (i + 1) ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hij
    rw [pow_succ] at h4
    have hlr : 0 < Objects.CorrectedEvent.lam k * C.r := by positivity
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) i]
  set Rout : ℝ := 2 * 4 ^ (Objects.CorrectedEvent.regK k) * Objects.CorrectedEvent.lam k * C.r with hRout
  have hhi_le : ∀ j ∈ G, hi j ≤ Rout := by
    intro j hj
    have hjK : j ≤ Objects.CorrectedEvent.regK k := (Finset.mem_Icc.mp (hGsub hj)).2
    have h4 : (4 : ℝ) ^ j ≤ 4 ^ (Objects.CorrectedEvent.regK k) := pow_le_pow_right₀ (by norm_num) hjK
    simp only [hhi, hRout]
    have hlr : 0 < Objects.CorrectedEvent.lam k * C.r := by positivity
    nlinarith
  have hj1 : ∀ j ∈ G, 1 ≤ j := fun j hj => (Finset.mem_Icc.mp (hGsub hj)).1
  
  have hfar : ∀ {t : ℝ}, Real.sqrt ε * C.r ≤ dist (P t) z → Rout ≤ dist (P t) x' := by
    intro t ht
    have htri := dist_triangle (P t) x' z
    linarith
  have hdeep : ∀ j ∈ G, dist (P s) x' ≤ lo j := by
    intro j hj
    have htri := dist_triangle (P s) z x'
    rw [dist_comm z x'] at htri
    have h4 : (4 : ℝ) ^ 1 ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) (hj1 j hj)
    have hεr : ε * C.r ≤ Objects.CorrectedEvent.lam k * C.r := mul_le_mul_of_nonneg_right hεlam hr.le
    simp only [hlo]
    have hlr : 0 < Objects.CorrectedEvent.lam k * C.r := by positivity
    nlinarith
  
  have hgood : ∀ j ∈ G, 0 < Objects.CorrectedEvent.around D x' (lo j) (hi j) ∧ Objects.CorrectedEvent.around D x' (lo j) (hi j) < ⊤ ∧
      0 < Objects.CorrectedEvent.acr D x' (lo j) (hi j) ∧ Objects.CorrectedEvent.acr D x' (lo j) (hi j) < ⊤ ∧
      Objects.CorrectedEvent.around D x' (lo j) (hi j) ≤ ENNReal.ofReal C.c_reg⁻¹ * Objects.CorrectedEvent.acr D x' (lo j) (hi j) :=
    fun j hj => hGgood j hj
  
  have htail : ∀ i ∈ G, ∑ j ∈ G.filter (· < i), Objects.CorrectedEvent.acr D x' (lo j) (hi j) ≤
      Objects.CorrectedEvent.around D x' (lo i) (hi i) := by
    intro i hi'
    exact tail_acr_le_around C D Db f hforget hWeyl hf has hsb hcont hdist hpre x' (hlohi i)
      ((hhi_le i hi').trans (hfar ha)) ((hhi_le i hi').trans (hfar hb)) (hdeep i hi')
      lo hi hlohi hmono _ (fun j hj => hmono j i (Finset.mem_filter.mp hj).2)
      (fun j hj => hdeep j (Finset.mem_filter.mp hj).1)
  
  set c := C.c_reg with hcdef
  have hc0 : 0 < c := C.regPos
  set X : ℕ → ℝ := fun j => (Objects.CorrectedEvent.around D x' (lo j) (hi j)).toReal with hX
  have hrec : ∀ i ∈ G, ∑ j ∈ G.filter (· < i), X j ≤ c⁻¹ * X i := by
    intro i hi'
    have hE : ∑ j ∈ G.filter (· < i), Objects.CorrectedEvent.around D x' (lo j) (hi j) ≤
        ENNReal.ofReal c⁻¹ * Objects.CorrectedEvent.around D x' (lo i) (hi i) := by
      calc ∑ j ∈ G.filter (· < i), Objects.CorrectedEvent.around D x' (lo j) (hi j)
          ≤ ∑ j ∈ G.filter (· < i), ENNReal.ofReal c⁻¹ * Objects.CorrectedEvent.acr D x' (lo j) (hi j) :=
            Finset.sum_le_sum fun j hj => (hgood j (Finset.mem_filter.mp hj).1).2.2.2.2
        _ = ENNReal.ofReal c⁻¹ * ∑ j ∈ G.filter (· < i), Objects.CorrectedEvent.acr D x' (lo j) (hi j) := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal c⁻¹ * Objects.CorrectedEvent.around D x' (lo i) (hi i) := by
            gcongr
            exact htail i hi'
    have hfinR : ENNReal.ofReal c⁻¹ * Objects.CorrectedEvent.around D x' (lo i) (hi i) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgood i hi').2.1.ne
    have hT := ENNReal.toReal_mono hfinR hE
    rw [ENNReal.toReal_sum (fun j hj => (hgood j (Finset.mem_filter.mp hj).1).2.1.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hc0.le)] at hT
    exact hT
  
  have hcard2 : 2 ≤ G.card := by
    have : 3 ≤ Objects.CorrectedEvent.regK k := by unfold Objects.CorrectedEvent.regK; omega
    omega
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  set m := G.min' hGne with hmdef
  set M := G.max' hGne with hMdef
  have hm : m ∈ G := Finset.min'_mem G hGne
  have hM : M ∈ G := Finset.max'_mem G hGne
  have hgrowth := growth_min_le c hc0 X G hm hM (fun j hj => Finset.min'_le G j hj)
    (fun j hj => Finset.le_max' G j hj) hrec
  
  have hacrM : Objects.CorrectedEvent.acr D x' (lo M) (hi M) ≤ ENNReal.ofReal (s - a) := by
    have hpre₀ := hpre a s le_rfl has.le le_rfl
    have hsum := sum_acr_le_len D P x' lo hi hlohi hmono {M} a s has.le hpre₀.1
      (hcont.mono (Icc_subset_Icc le_rfl hsb.le))
      (fun j hj => by rw [Finset.mem_singleton.mp hj]; exact (hhi_le M hM).trans (hfar ha))
      (fun j hj => by rw [Finset.mem_singleton.mp hj]; exact hdeep M hM)
    rw [Finset.sum_singleton] at hsum
    exact hsum.trans hpre₀.2
  have hXM : X M ≤ c⁻¹ * (s - a) := by
    have h1 : Objects.CorrectedEvent.around D x' (lo M) (hi M) ≤ ENNReal.ofReal (c⁻¹ * (s - a)) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc0.le)]
      exact (hgood M hM).2.2.2.2.trans (by gcongr)
    exact ENNReal.toReal_le_of_le_ofReal (by have := inv_pos.mpr hc0; nlinarith) h1
  
  have hnum := c3_numeric C hline4 hk hε hεlam hlamε hεep hGcard
  have hpowpos : 0 < (1 + c) ^ (G.card - 1) := by positivity
  have hXm : X m ≤ ε ^ theta C * (s - a) := by
    have h1 : X m ≤ (1 + c⁻¹) * X M / (1 + c) ^ (G.card - 1) := by
      rw [le_div_iff₀ hpowpos]
      linarith
    have h2 : (1 + c⁻¹) * X M ≤ (1 + c⁻¹) * (c⁻¹ * (s - a)) :=
      mul_le_mul_of_nonneg_left hXM (by positivity)
    have h3 : (1 + c⁻¹) * (c⁻¹ * (s - a)) / (1 + c) ^ (G.card - 1) =
        ((1 + c⁻¹) * c⁻¹ / (1 + c) ^ (G.card - 1)) * (s - a) := by ring
    calc X m ≤ (1 + c⁻¹) * X M / (1 + c) ^ (G.card - 1) := h1
      _ ≤ (1 + c⁻¹) * (c⁻¹ * (s - a)) / (1 + c) ^ (G.card - 1) :=
          div_le_div_of_nonneg_right h2 hpowpos.le
      _ = ((1 + c⁻¹) * c⁻¹ / (1 + c) ^ (G.card - 1)) * (s - a) := h3
      _ ≤ ε ^ theta C * (s - a) := mul_le_mul_of_nonneg_right hnum (by linarith)
  
  have hgeom := Objects.Compare.nested_annulus_geometry (y := z) (z := x') (a := ε * C.r)
    (b := Real.sqrt ε * C.r) (c := lo m) (d := hi m) (e := Objects.CorrectedEvent.lam k * C.r / 4)
    (by rw [dist_comm]; exact hnear.le)
    (by
      have h4 : (4 : ℝ) ^ 1 ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (hj1 m hm)
      have hεr : ε * C.r ≤ Objects.CorrectedEvent.lam k * C.r := mul_le_mul_of_nonneg_right hεlam hr.le
      simp only [hlo]
      have hlr : 0 < Objects.CorrectedEvent.lam k * C.r := by positivity
      nlinarith)
    (by have := hhi_le m hm; linarith)
  have hadm := Objects.Compare.around_le_of_nested_annuli D (hlohi m) hgeom.1 hgeom.2.1 hgeom.2.2
  calc Objects.CorrectedEvent.around D z (ε * C.r) (Real.sqrt ε * C.r) ≤ Objects.CorrectedEvent.around D x' (lo m) (hi m) := hadm
    _ = ENNReal.ofReal (X m) := (ENNReal.ofReal_toReal (hgood m hm).2.1.ne).symm
    _ ≤ ENNReal.ofReal (ε ^ theta C * (s - a)) := ENNReal.ofReal_le_ofReal hXm

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
