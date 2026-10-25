import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Rev
import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventRegularityNum




 





















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 
def theta (C : Objects.CorrectedEvent.Constants) : ℝ := Real.log (1 + C.c_reg) / (48 * Real.log 2)

theorem theta_pos (C : Objects.CorrectedEvent.Constants) : 0 < theta C := by
  unfold theta
  have h1 : 0 < Real.log (1 + C.c_reg) := Real.log_pos (by linarith [C.regPos])
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

 

section Charge

variable (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))

 


theorem tail_acr_le_around (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a s b : ℝ} (has : a < s) (hsb : s < b) (hcont : ContinuousOn P (Icc a b))
    (hdist : ∀ u v, a ≤ u → u ≤ v → v ≤ b → Db (P u, P v) = ENNReal.ofReal (v - u))
    (hpre : ∀ u v, a ≤ u → u ≤ v → v ≤ s → D.IsCurve P u v ∧ D.len P u v ≤ ENNReal.ofReal (v - u))
    (x : ℂ) {ρ R : ℝ} (hρR : ρ ≤ R)
    (ha : R ≤ dist (P a) x) (hb : R ≤ dist (P b) x) (hs : dist (P s) x ≤ ρ)
    (lo hi : ℕ → ℝ) (hlohi : ∀ j, lo j ≤ hi j) (hmono : ∀ i j, i < j → hi i ≤ lo j)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, hi j ≤ ρ) (hJs : ∀ j ∈ J, dist (P s) x ≤ lo j) :
    ∑ j ∈ J, Objects.CorrectedEvent.acr D x (lo j) (hi j) ≤ Objects.CorrectedEvent.around D x ρ R := by
  unfold Objects.CorrectedEvent.around
  refine le_iInf fun π => le_iInf fun p => le_iInf fun q => le_iInf fun hπ =>
    le_iInf fun htr => le_iInf fun hsep => ?_
  have hsK : P s ∉ π '' Icc p q := by
    intro h
    have := (htr h).1
    linarith
  obtain ⟨t₁, t₂, hat₁, ht₁s, hst₂, ht₂b, ht₁K, ht₂K⟩ :=
    Objects.Splice.separator_two_hits has hsb hρR hcont hsep
      (by simpa only [mem_compl_iff, mem_ball, not_lt] using ha)
      (by simpa only [mem_compl_iff, mem_ball, not_lt] using hb)
      (mem_closedBall.mpr hs) hsK
  have ht₁far : ρ < dist (P t₁) x := (htr ht₁K).1
  obtain ⟨p₁, hp₁, hp₁e⟩ := ht₁K
  obtain ⟨q₁, hq₁, hq₁e⟩ := ht₂K
  have hpre₁ := hpre t₁ s hat₁ ht₁s.le le_rfl
  have hlayers := sum_acr_le_len D P x lo hi hlohi hmono J t₁ s ht₁s.le hpre₁.1
    (hcont.mono (Icc_subset_Icc hat₁ hsb.le))
    (fun j hj => (hJ j hj).trans ht₁far.le) hJs
  have h12 : ENNReal.ofReal (s - t₁) ≤ ENNReal.ofReal (t₂ - t₁) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hd := hdist t₁ t₂ hat₁ (ht₁s.trans hst₂).le ht₂b
  have hπb : Db (P t₁, P t₂) ≤ D.len π p q := by
    rw [← hp₁e, ← hq₁e]
    exact bumped_dist_le_len C D Db f hforget hWeyl hf hπ hp₁ hq₁
  calc ∑ j ∈ J, Objects.CorrectedEvent.acr D x (lo j) (hi j) ≤ D.len P t₁ s := hlayers
    _ ≤ ENNReal.ofReal (s - t₁) := hpre₁.2
    _ ≤ ENNReal.ofReal (t₂ - t₁) := h12
    _ = Db (P t₁, P t₂) := hd.symm
    _ ≤ D.len π p q := hπb

end Charge

 

 

theorem growth_sum (c : ℝ) (hc : 0 < c) (X : ℕ → ℝ) (G : Finset ℕ) :
    (∀ i ∈ G, ∑ j ∈ G.filter (· < i), X j ≤ c⁻¹ * X i) →
      ∀ m ∈ G, (∀ j ∈ G, m ≤ j) → (1 + c) ^ (G.card - 1) * X m ≤ ∑ j ∈ G, X j := by
  induction G using Finset.induction_on_max with
  | empty => intro _ m hm; simp at hm
  | insert a s hlt ih =>
    intro hrec m hm hmin
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hfa : (insert a s).filter (· < a) = s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hja⟩
        · exact absurd hja (lt_irrefl _)
        · exact hj
      · intro hj
        exact ⟨Or.inr hj, hlt j hj⟩
    have hrec_a := hrec a (Finset.mem_insert_self a s)
    rw [hfa] at hrec_a
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Nat.add_sub_cancel]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      have hma : m = a := by simpa using hm
      subst hma
      simp
    · 
      have hms : m ∈ s := by
        rcases Finset.mem_insert.mp hm with h | h
        · obtain ⟨j, hj⟩ := hs
          have := hmin j (Finset.mem_insert_of_mem hj)
          have := hlt j hj
          omega
        · exact h
      have hrec_s : ∀ i ∈ s, ∑ j ∈ s.filter (· < i), X j ≤ c⁻¹ * X i := by
        intro i hi
        have hfi : (insert a s).filter (· < i) = s.filter (· < i) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hj, hji⟩
            · exact absurd (hji.trans (hlt i hi)) (lt_irrefl _)
            · exact ⟨hj, hji⟩
          · rintro ⟨hj, hji⟩
            exact ⟨Or.inr hj, hji⟩
        have := hrec i (Finset.mem_insert_of_mem hi)
        rwa [hfi] at this
      have hih := ih hrec_s m hms (fun j hj => hmin j (Finset.mem_insert_of_mem hj))
      have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
      have hca : c * ∑ j ∈ s, X j ≤ X a := by
        have := mul_le_mul_of_nonneg_left hrec_a hc.le
        rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
      have hpow : (1 + c) ^ s.card = (1 + c) ^ (s.card - 1) * (1 + c) := by
        rw [← pow_succ, Nat.sub_add_cancel hcard]
      rw [hpow]
      have h1c : 0 ≤ 1 + c := by linarith
      calc (1 + c) ^ (s.card - 1) * (1 + c) * X m
          = (1 + c) * ((1 + c) ^ (s.card - 1) * X m) := by ring
        _ ≤ (1 + c) * ∑ j ∈ s, X j := mul_le_mul_of_nonneg_left hih h1c
        _ = ∑ j ∈ s, X j + c * ∑ j ∈ s, X j := by ring
        _ ≤ ∑ j ∈ s, X j + X a := by linarith
        _ = X a + ∑ j ∈ s, X j := by ring

 
theorem growth_min_le (c : ℝ) (hc : 0 < c) (X : ℕ → ℝ) (G : Finset ℕ) {m M : ℕ} (hm : m ∈ G)
    (hM : M ∈ G) (hmin : ∀ j ∈ G, m ≤ j) (hmax : ∀ j ∈ G, j ≤ M)
    (hrec : ∀ i ∈ G, ∑ j ∈ G.filter (· < i), X j ≤ c⁻¹ * X i) :
    (1 + c) ^ (G.card - 1) * X m ≤ (1 + c⁻¹) * X M := by
  have h1 := growth_sum c hc X G hrec m hm hmin
  have hsplit : G = insert M (G.filter (· < M)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hj
      rcases eq_or_lt_of_le (hmax j hj) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hj, h⟩
    · rintro (rfl | ⟨hj, _⟩)
      · exact hM
      · exact hj
  have hnot : M ∉ G.filter (· < M) := by simp
  have h2 : ∑ j ∈ G, X j = X M + ∑ j ∈ G.filter (· < M), X j := by
    conv_lhs => rw [hsplit]
    rw [Finset.sum_insert hnot]
  have h3 := hrec M hM
  linarith

 

theorem lam_eq_inv_pow (k : ℕ) : Objects.CorrectedEvent.lam k = ((2 : ℝ) ^ k)⁻¹ := by
  unfold Objects.CorrectedEvent.lam
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

 
theorem exists_lam_index {ε : ℝ} (hε : 0 < ε) {k₀ : ℕ} (hεep : ε ≤ (2 : ℝ) ^ (-(k₀ : ℝ))) :
    ∃ k : ℕ, k₀ ≤ k ∧ ε ≤ Objects.CorrectedEvent.lam k ∧ Objects.CorrectedEvent.lam k < 2 * ε := by
  have hx : 1 ≤ ε⁻¹ := by
    have : ε ≤ 1 := hεep.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp))
    exact one_le_inv₀ hε |>.mpr this
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, ?_, ?_⟩
  · have h0 : (2 : ℝ) ^ k₀ ≤ ε⁻¹ := by
      have := (inv_le_inv₀ (by positivity) hε).mpr hεep
      rwa [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_inv] at this
    have hlt : (2 : ℝ) ^ k₀ < 2 ^ (k + 1) := h0.trans_lt hk2
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlt
    omega
  · rw [lam_eq_inv_pow]
    rw [le_inv_comm₀ hε (by positivity)]
    exact hk1
  · rw [lam_eq_inv_pow]
    have h3 : ((2 : ℝ) ^ k * 2)⁻¹ < ε := by
      rw [inv_lt_comm₀ (by positivity) hε]
      rwa [pow_succ] at hk2
    have h4 : ((2 : ℝ) ^ k)⁻¹ = 2 * ((2 : ℝ) ^ k * 2)⁻¹ := by
      field_simp
    linarith

 
theorem regK_ge (k : ℕ) (hk : 24 ≤ k) : ((k : ℝ) - 23) / 12 ≤ (Objects.CorrectedEvent.regK k : ℝ) := by
  unfold Objects.CorrectedEvent.regK
  have hq : 1 ≤ k / 12 := by omega
  have hdm := Nat.div_add_mod k 12
  have hmod := Nat.mod_lt k (by norm_num : 12 > 0)
  have hcast : ((k / 12 - 1 : ℕ) : ℝ) = ((k / 12 : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hcast]
  have h1 : (k : ℝ) = 12 * ((k / 12 : ℕ) : ℝ) + ((k % 12 : ℕ) : ℝ) := by
    exact_mod_cast hdm.symm
  have h2 : ((k % 12 : ℕ) : ℝ) ≤ 11 := by exact_mod_cast Nat.le_of_lt_succ hmod
  linarith

 

theorem c3_numeric (C : Objects.CorrectedEvent.Constants)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    {k n : ℕ} (hk : C.k0 ≤ k) {ε : ℝ} (hε : 0 < ε) (_hεlam : ε ≤ Objects.CorrectedEvent.lam k)
    (hlamε : Objects.CorrectedEvent.lam k < 2 * ε) (hεep : ε ≤ (2 : ℝ) ^ (-(C.k0 : ℝ)))
    (hn : Objects.CorrectedEvent.regK k ≤ 2 * n) :
    (1 + C.c_reg⁻¹) * C.c_reg⁻¹ / (1 + C.c_reg) ^ (n - 1) ≤ ε ^ theta C := by
  set c := C.c_reg with hcdef
  set θ := theta C with hθdef
  have hc0 : 0 < c := C.regPos
  have hθ : 0 < θ := theta_pos C
  have hk48 : 48 ≤ k := C.k0Large.trans hk
  have h1c : 1 ≤ 1 + c := by linarith
  have h1c' : 0 < 1 + c := by linarith
  
  have hreg := regK_ge k (by omega)
  have hnR : ((k : ℝ) - 23) / 24 ≤ (n : ℝ) := by
    have : (Objects.CorrectedEvent.regK k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn1 : 1 ≤ n := by
    have : 3 ≤ Objects.CorrectedEvent.regK k := by unfold Objects.CorrectedEvent.regK; omega
    omega
  
  have hpowR : (1 + c) ^ (n - 1) = (1 + c) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hn1, Nat.cast_one]
  set e : ℝ := ((k : ℝ) - 47) / 24 with he
  have hlow : (1 + c) ^ e ≤ (1 + c) ^ (n - 1) := by
    rw [hpowR]
    exact Real.rpow_le_rpow_of_exponent_le h1c (by rw [he]; linarith)
  have hepos : 0 < (1 + c) ^ e := Real.rpow_pos_of_pos h1c' e
  have hnum : 0 ≤ (1 + c⁻¹) * c⁻¹ := by positivity
  
  have halg : (1 + c⁻¹) * c⁻¹ / (1 + c) ^ e =
      c⁻¹ ^ 2 * ((1 + c) ^ ((71 : ℝ) / 24) * (1 + c) ^ (-(k : ℝ) / 24)) := by
    have hcexp : (1 + c⁻¹) * c⁻¹ = c⁻¹ ^ 2 * (1 + c) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      field_simp
      ring
    rw [hcexp, div_eq_mul_inv, ← Real.rpow_neg h1c'.le, mul_assoc, ← Real.rpow_add h1c',
      ← Real.rpow_add h1c']
    congr 2
    rw [he]
    ring
  
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : (1 + c) ^ (-(k : ℝ) / 24) = (Objects.CorrectedEvent.lam k) ^ (2 * θ) := by
    unfold Objects.CorrectedEvent.lam
    rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos h1c', Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [hθdef, theta, ← hcdef]
    field_simp
    ring
  have hlamθ : (Objects.CorrectedEvent.lam k) ^ (2 * θ) ≤ (2 * ε) ^ (2 * θ) :=
    Real.rpow_le_rpow (by unfold Objects.CorrectedEvent.lam; positivity) hlamε.le (by positivity)
  have h2ε : (2 * ε) ^ (2 * θ) = (2 : ℝ) ^ (2 * θ) * ε ^ θ * ε ^ θ := by
    rw [Real.mul_rpow (by norm_num) hε.le, mul_assoc, ← Real.rpow_add hε, two_mul]
  
  have h71 : (1 + c) ^ ((71 : ℝ) / 24) ≤ (1 + c) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1c (by norm_num)
  
  have hεθ : ε ^ θ ≤ ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ θ := Real.rpow_le_rpow hε.le hεep hθ.le
  have hεpos : 0 < ε ^ θ := Real.rpow_pos_of_pos hε θ
  have hline : c⁻¹ ^ 2 * (1 + c) ^ 3 * (2 : ℝ) ^ (2 * θ) * ε ^ θ ≤ 1 := by
    have hpos : 0 ≤ c⁻¹ ^ 2 * (1 + c) ^ 3 * (2 : ℝ) ^ (2 * θ) := by positivity
    exact (mul_le_mul_of_nonneg_left hεθ hpos).trans hline4
  have h71pos : 0 ≤ (1 + c) ^ ((71 : ℝ) / 24) := (Real.rpow_pos_of_pos h1c' _).le
  calc (1 + c⁻¹) * c⁻¹ / (1 + c) ^ (n - 1) ≤ (1 + c⁻¹) * c⁻¹ / (1 + c) ^ e :=
        div_le_div_of_nonneg_left hnum hepos hlow
    _ = c⁻¹ ^ 2 * ((1 + c) ^ ((71 : ℝ) / 24) * (1 + c) ^ (-(k : ℝ) / 24)) := halg
    _ ≤ c⁻¹ ^ 2 * ((1 + c) ^ 3 * ((2 : ℝ) ^ (2 * θ) * ε ^ θ * ε ^ θ)) := by
        rw [hkey, ← h2ε]
        have hlam0 : 0 ≤ (Objects.CorrectedEvent.lam k) ^ (2 * θ) := by
          apply Real.rpow_nonneg; unfold Objects.CorrectedEvent.lam; positivity
        gcongr
    _ = (c⁻¹ ^ 2 * (1 + c) ^ 3 * (2 : ℝ) ^ (2 * θ) * ε ^ θ) * ε ^ θ := by ring
    _ ≤ 1 * ε ^ θ := mul_le_mul_of_nonneg_right hline hεpos.le
    _ = ε ^ θ := one_mul _

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
