import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 























set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.T58Assembly

open SupercriticalLQGUniqueness
open LQGMetric (DistC)

 

 
def dyad (n : ℕ) : ℝ := (8 : ℝ) ^ (-(n : ℤ))

theorem dyad_pos (n : ℕ) : 0 < dyad n := zpow_pos (by norm_num) _

theorem dyad_eq_pow (n : ℕ) : dyad n = (1 / 8 : ℝ) ^ n := by
  rw [dyad, zpow_neg, zpow_natCast, one_div, inv_pow]

theorem dyad_add (m n : ℕ) : dyad (m + n) = dyad m * dyad n := by
  simp only [dyad_eq_pow, pow_add]

theorem dyad_lt_iff {m n : ℕ} : dyad m < dyad n ↔ n < m := by
  simp only [dyad_eq_pow]
  exact pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)

theorem dyad_le_iff {m n : ℕ} : dyad m ≤ dyad n ↔ n ≤ m := by
  simp only [dyad_eq_pow]
  exact pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)

theorem dyad_le_one (n : ℕ) : dyad n ≤ 1 := by
  rw [dyad_eq_pow]; exact pow_le_one₀ (by norm_num) (by norm_num)

 
def radiiSet (ρ : ℝ) (R₀ : Set ℝ) : Set ℝ := {r | ∃ s ∈ R₀, s < ρ ∧ r = ρ⁻¹ * s}

theorem admissible_of_dyadic {ρ : ℝ} (hρ : 0 < ρ) {R₀ : Set ℝ} (hR₀ : R₀ ⊆ range dyad) :
    radiiSet ρ R₀ ⊆ Ioo 0 1 ∧
      ∀ ⦃r s : ℝ⦄, r ∈ radiiSet ρ R₀ → s ∈ radiiSet ρ R₀ → r < s → 8 * r ≤ s := by
  refine ⟨?_, ?_⟩
  · rintro r ⟨s, hs, hsρ, rfl⟩
    obtain ⟨n, rfl⟩ := hR₀ hs
    refine ⟨mul_pos (inv_pos.2 hρ) (dyad_pos n), ?_⟩
    rw [inv_mul_lt_iff₀ hρ, mul_one]
    exact hsρ
  · rintro r s ⟨a, ha, -, rfl⟩ ⟨b, hb, -, rfl⟩ hab
    obtain ⟨m, rfl⟩ := hR₀ ha
    obtain ⟨n, rfl⟩ := hR₀ hb
    have hlt : dyad m < dyad n := by
      have := (mul_lt_mul_iff_of_pos_left (inv_pos.2 hρ)).1 hab
      exact this
    have hnm : n < m := dyad_lt_iff.1 hlt
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    have h8 : 8 * dyad (n + 1 + k) ≤ dyad n := by
      rw [dyad_add, dyad_add]
      have h1 : dyad 1 = 1 / 8 := by rw [dyad_eq_pow]; norm_num
      rw [h1]
      have hk : dyad k ≤ 1 := dyad_le_one k
      have hn : 0 < dyad n := dyad_pos n
      nlinarith
    calc 8 * (ρ⁻¹ * dyad (n + 1 + k)) = ρ⁻¹ * (8 * dyad (n + 1 + k)) := by ring
      _ ≤ ρ⁻¹ * dyad n := mul_le_mul_of_nonneg_left h8 (inv_nonneg.2 hρ.le)

 
def admissibleRadii {ρ : ℝ} (hρ : 0 < ρ) {R₀ : Set ℝ} (hR₀ : R₀ ⊆ range dyad) :
    EndSaving.Interfaces.AdmissibleRadii :=
  ⟨radiiSet ρ R₀, (admissible_of_dyadic hρ hR₀).1, (admissible_of_dyadic hρ hR₀).2⟩

 

 


def paramsOfConstants (ξ : Set.Ioi (0 : ℝ)) (Aac Aar Amax Aint Anar ARN Emax lam a : ℝ)
    (hac : 0 < Aac) (har : Aac < Aar) (hAmax : 0 < Amax) (hAint : 0 < Aint) (hAnar : 0 < Anar)
    (hlam : lam ≤ 1 / 16) (hw : Real.exp (-(ξ : ℝ) * Amax) * Aint ≤ lam * Aac) :
    EndSaving.Interfaces.Parameters ξ where
  Cmax := Amax
  Cacross := Aac
  Caround := Aar
  Crn := Real.exp (ARN + Emax / 2)
  Ctime := Aac ^ 2 / (4 * Aar)
  Cinc := Anar ^ a * Real.exp (-(ξ : ℝ) * Amax)
  Ctube := Aint
  max_pos := hAmax
  across_pos := hac
  around_pos := hac.trans har
  rn_pos := Real.exp_pos _
  time_pos := by have := hac.trans har; positivity
  inc_pos := mul_pos (Real.rpow_pos_of_pos hAnar a) (Real.exp_pos _)
  tube_pos := hAint
  around_gt_across := har
  strict_slack := by
    have har0 : 0 < Aar := hac.trans har
    have e1 : (2 * Aar / Aac) * (Aac ^ 2 / (4 * Aar)) = Aac / 2 := by
      field_simp
      ring
    rw [e1]
    have hlamAac : lam * Aac ≤ Aac / 16 := by nlinarith
    linarith

 

theorem setDist_anti (d : LSCMetric) {A A' B B' : Set ℂ} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    OptimalConstants.Ratios.setDist d A B ≤ OptimalConstants.Ratios.setDist d A' B' :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le_of_le x (hA hx) (iInf₂_le y (hB hy))

 
theorem gtilde_mono_kappa (d e : LSCMetric) (r κ κ' C : Set.Ioi (0 : ℝ))
    (hκ : (κ' : ℝ) ≤ κ) : OptimalConstants.Ratios.Gtilde d e r κ C → OptimalConstants.Ratios.Gtilde d e r κ' C := by
  rintro ⟨z, w, hz, hw, hp, hc⟩
  refine ⟨z, w, hz, hw, hp, hc.trans ?_⟩
  have hr : 0 ≤ (r : ℝ) := le_of_lt r.2
  have hb : ∀ x : ℂ, ball x ((κ' : ℝ) * r) ⊆ ball x ((κ : ℝ) * r) := fun x =>
    ball_subset_ball (mul_le_mul_of_nonneg_right hκ hr)
  exact mul_le_mul' le_rfl (setDist_anti d (hb z) (hb w))

 

 
theorem strip_ncard_le {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x) {M : ℕ} (hM : dyad M ≤ ρ) :
    {r | r ∈ range dyad ∧ ρ * x ≤ r ∧ r < x}.ncard ≤ M := by
  have hex : ∃ n, dyad n < x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (show (1 / 8 : ℝ) < 1 by norm_num)
    exact ⟨n, by rwa [dyad_eq_pow]⟩
  classical
  set n₁ := Nat.find hex with hn₁
  have hsub : {r | r ∈ range dyad ∧ ρ * x ≤ r ∧ r < x} ⊆
      dyad '' (Finset.Ico n₁ (n₁ + M) : Set ℕ) := by
    rintro r ⟨⟨n, rfl⟩, hlo, hhi⟩
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.coe_Ico, mem_Ico]
    refine ⟨Nat.find_min' hex hhi, ?_⟩
    by_contra hge
    push Not at hge
    have h1 : dyad n ≤ dyad (n₁ + M) := dyad_le_iff.2 hge
    have h2 : dyad (n₁ + M) < x * ρ := by
      rw [dyad_add]
      have h3 : dyad n₁ < x := Nat.find_spec hex
      nlinarith [dyad_pos n₁, dyad_pos M]
    linarith [mul_comm x ρ]
  calc {r | r ∈ range dyad ∧ ρ * x ≤ r ∧ r < x}.ncard
      ≤ (dyad '' (Finset.Ico n₁ (n₁ + M) : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (Finset.Ico n₁ (n₁ + M) : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = M := by rw [Set.ncard_coe_finset, Nat.card_Ico]; omega

 
theorem finite_dyadic_ge {R₀ : Set ℝ} (hR₀ : R₀ ⊆ range dyad) {lo hi : ℝ} (hlo : 0 < lo) :
    (R₀ ∩ Icc lo hi).Finite := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlo (show (1 / 8 : ℝ) < 1 by norm_num)
  refine ((Finset.range N).finite_toSet.image dyad).subset ?_
  rintro r ⟨hr, hrlo, -⟩
  obtain ⟨n, rfl⟩ := hR₀ hr
  refine ⟨n, ?_, rfl⟩
  simp only [Finset.coe_range, mem_Iio]
  by_contra hn
  push Not at hn
  have h1 : dyad n ≤ dyad N := dyad_le_iff.2 hn
  have h2 : dyad N = (1 / 8 : ℝ) ^ N := dyad_eq_pow N
  linarith

theorem log_inv_div_log8_ge {ε : ℝ} (hε : 0 < ε) {M : ℕ} (hεM : ε ≤ dyad (8 * M)) :
    (8 * M : ℝ) ≤ Real.log ε⁻¹ / Real.log 8 := by
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h8]
  have hd : dyad (8 * M) = ((8 : ℝ) ^ (8 * M))⁻¹ := by
    rw [dyad, zpow_neg, zpow_natCast]
  rw [hd] at hεM
  have hpos : 0 < (8 : ℝ) ^ (8 * M) := by positivity
  have h1 : (8 : ℝ) ^ (8 * M) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ hpos hε]; exact hεM
  have h2 := Real.log_le_log hpos h1
  rw [Real.log_pow] at h2
  push_cast at h2 ⊢
  linarith

 



theorem density_of_attainedGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric) (C' : Set.Ioi (0 : ℝ))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {R₀ : Set ℝ} (hR₀ : R₀ ⊆ range dyad)
    (hS36 : ∀ κ : Set.Ioi (0 : ℝ), (κ : ℝ) < 1 → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ j : ℕ,
        ENNReal.ofReal (κ : ℝ) ≤
          P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) κ C'} →
        (3 / 4 : ℝ) * (Real.log η⁻¹ / Real.log 8) ≤
          (R₀ ∩ Icc (η ^ 2 * dyad j) (η * dyad j)).ncard) :
    ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
        let b : Set.Ioi (0 : ℝ) := EndSaving.Interfaces.dyadicRadius j
        ENNReal.ofReal (κ : ℝ) ≤
          P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κ C'} →
        ∃ F : Finset ℝ,
          (F : Set ℝ) = radiiSet ρ R₀ ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
          (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card := by
  intro κ
  
  set κ' : Set.Ioi (0 : ℝ) :=
    ⟨min (κ : ℝ) (1 / 2), Set.mem_Ioi.mpr (lt_min (Set.mem_Ioi.mp κ.2) (by norm_num))⟩ with hκ'
  have hκ'le : (κ' : ℝ) ≤ κ := min_le_left _ _
  have hκ'1 : (κ' : ℝ) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨η₀, hη₀, hcount⟩ := hS36 κ' hκ'1
  
  obtain ⟨M, hMρ⟩ := exists_pow_lt_of_lt_one hρ0 (show (1 / 8 : ℝ) < 1 by norm_num)
  have hM : dyad M ≤ ρ := by rw [dyad_eq_pow]; exact hMρ.le
  set e₀ : ℝ := min (min η₀ (dyad (8 * M))) (1 / 2) with he₀
  have he₀pos : 0 < e₀ := lt_min (lt_min hη₀ (dyad_pos _)) (by norm_num)
  have he₀1 : e₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨⟨e₀, he₀pos, he₀1⟩, ?_⟩
  intro ε hε hεe j b hprem
  have hεη : ε ≤ η₀ := le_trans hεe (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεM : ε ≤ dyad (8 * M) := le_trans hεe (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεhalf : ε ≤ 1 / 2 := le_trans hεe (min_le_right _ _)
  have hbdef : (b : ℝ) = dyad j := rfl
  have hb0 : 0 < dyad j := dyad_pos j
  have hb1 : dyad j ≤ 1 := dyad_le_one j
  
  have hprem' : ENNReal.ofReal (κ' : ℝ) ≤
      P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) κ' C'} := by
    refine le_trans (ENNReal.ofReal_le_ofReal hκ'le) (le_trans hprem (measure_mono ?_))
    intro ω hω
    exact gtilde_mono_kappa _ _ _ κ κ' C' hκ'le hω
  
  set η : ℝ := ρ * ε with hηdef
  have hηpos : 0 < η := mul_pos hρ0 hε
  have hηle : η ≤ η₀ := by
    have : ρ * ε ≤ ε := by nlinarith
    linarith
  have hA := hcount η hηpos hηle j hprem'
  
  set A := R₀ ∩ Icc (η ^ 2 * dyad j) (η * dyad j) with hAdef
  set T := R₀ ∩ Icc (ρ * (ε ^ 2 * dyad j)) (ρ * (ε * dyad j)) with hTdef
  set S := {r | r ∈ range dyad ∧ ρ * (ρ * (ε ^ 2 * dyad j)) ≤ r ∧ r < ρ * (ε ^ 2 * dyad j)}
    with hSdef
  have hx : 0 < ρ * (ε ^ 2 * dyad j) := by positivity
  have hAsub : A ⊆ T ∪ S := by
    rintro r ⟨hr, hrlo, hrhi⟩
    by_cases hc : ρ * (ε ^ 2 * dyad j) ≤ r
    · left
      refine ⟨hr, hc, ?_⟩
      have : η * dyad j = ρ * (ε * dyad j) := by rw [hηdef]; ring
      linarith
    · right
      push Not at hc
      refine ⟨hR₀ hr, ?_, hc⟩
      have : η ^ 2 * dyad j = ρ * (ρ * (ε ^ 2 * dyad j)) := by rw [hηdef]; ring
      linarith
  have hTfin : T.Finite := finite_dyadic_ge hR₀ hx
  have hSfin : S.Finite := by
    refine (finite_dyadic_ge (R₀ := range dyad) subset_rfl
      (lo := ρ * (ρ * (ε ^ 2 * dyad j))) (hi := ρ * (ε ^ 2 * dyad j)) (by positivity)).subset ?_
    rintro r ⟨hr, hlo, hhi⟩
    exact ⟨hr, hlo, hhi.le⟩
  have hAle : A.ncard ≤ T.ncard + M := by
    calc A.ncard ≤ (T ∪ S).ncard := Set.ncard_le_ncard hAsub (hTfin.union hSfin)
      _ ≤ T.ncard + S.ncard := Set.ncard_union_le T S
      _ ≤ T.ncard + M := by
        have hSM : S.ncard ≤ M := strip_ncard_le hρ0 hx hM
        omega
  
  have hT_img : radiiSet ρ R₀ ∩ Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) =
      (fun s => ρ⁻¹ * s) '' T := by
    rw [hbdef]
    ext r
    constructor
    · rintro ⟨⟨s, hs, -, rfl⟩, hlo, hhi⟩
      refine ⟨s, ⟨hs, ?_, ?_⟩, rfl⟩
      · exact (le_inv_mul_iff₀ hρ0).1 hlo
      · exact (inv_mul_le_iff₀ hρ0).1 hhi
    · rintro ⟨s, ⟨hs, hlo, hhi⟩, rfl⟩
      have hslt : s < ρ := by
        have h1 : ε * dyad j ≤ 1 / 2 := by nlinarith
        have h2 : ρ * (ε * dyad j) < ρ := by nlinarith
        linarith
      refine ⟨⟨s, hs, hslt, rfl⟩, ?_, ?_⟩
      · rw [le_inv_mul_iff₀ hρ0]; exact hlo
      · rw [inv_mul_le_iff₀ hρ0]; exact hhi
  have hinj : Function.Injective (fun s : ℝ => ρ⁻¹ * s) := fun x y hxy =>
    mul_left_cancel₀ (inv_ne_zero hρ0.ne') hxy
  have hncard : (radiiSet ρ R₀ ∩ Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ))).ncard = T.ncard := by
    rw [hT_img, Set.ncard_image_of_injective _ hinj]
  have hfinR : (radiiSet ρ R₀ ∩ Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ))).Finite := by
    rw [hT_img]; exact hTfin.image _
  refine ⟨hfinR.toFinset, by simp, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfinR, hncard]
  
  have hL : (8 * M : ℝ) ≤ Real.log ε⁻¹ / Real.log 8 := log_inv_div_log8_ge hε hεM
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hηlog : Real.log ε⁻¹ / Real.log 8 ≤ Real.log η⁻¹ / Real.log 8 := by
    apply div_le_div_of_nonneg_right _ h8.le
    apply Real.log_le_log (inv_pos.2 hε)
    rw [inv_le_inv₀ hε hηpos]
    nlinarith
  have hAreal : (A.ncard : ℝ) ≤ T.ncard + M := by exact_mod_cast hAle
  linarith

 

 


theorem exists_good_representative {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} [Countable ι] (p : ι → Ω → Prop) (hp : ∀ i, ∀ᵐ ω ∂P, p i ω)
    {S E₀ : Set Ω} (hE₀ : MeasurableSet E₀) (hSE : E₀ =ᵐ[P] S) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ E₀ ∧ E ⊆ S ∧ (∀ ω ∈ E, ∀ i, p i ω) ∧ E =ᵐ[P] E₀ := by
  set B : Set Ω := {ω | ¬ ∀ i, p i ω} ∪ (E₀ \ S) with hB
  have hB0 : P B = 0 := by
    refine measure_union_null ?_ ?_
    · have : ∀ᵐ ω ∂P, ∀ i, p i ω := ae_all_iff.2 hp
      rwa [ae_iff] at this
    · exact (ae_eq_set.1 hSE).1
  set T := toMeasurable P B with hT
  have hT0 : P T = 0 := by rw [hT, measure_toMeasurable]; exact hB0
  refine ⟨E₀ \ T, hE₀.diff (measurableSet_toMeasurable P B), sdiff_subset, ?_, ?_, ?_⟩
  · rintro ω ⟨hω, hωT⟩
    by_contra hS
    exact hωT (subset_toMeasurable P B (Or.inr ⟨hω, hS⟩))
  · rintro ω ⟨-, hωT⟩ i
    by_contra hpi
    exact hωT (subset_toMeasurable P B (Or.inl fun h => hpi (h i)))
  · exact sdiff_null_ae_eq_self hT0

 

theorem fieldSigmaClosed0_le {Ω : Type*} [m : MeasurableSpace Ω] {h : Ω → DistC}
    (hh : Measurable h) (K : Set ℂ) : LQGMetric.Blueprint.fieldSigmaClosed0 h K ≤ m := by
  refine iInf₂_le_of_le 1 one_pos ?_
  unfold LQGMetric.Blueprint.fieldSigma0On
  refine Measurable.comap_le ?_
  exact measurable_pi_iff.mpr fun ψ => (LQGMetric.measurable_evalDist ψ.1.1).comp hh

 

 
theorem pathHit_imp_disconnects_of_isClosed {K E F : Set ℂ} (hK : IsClosed K)
    (h : LQGMetric.Disconnects K E F) : SupercriticalLQGUniqueness.Disconnects K E F := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
  have hxK : x ∈ Kᶜ := hSK hxS
  set C := connectedComponentIn Kᶜ x with hC
  have hSC : S ⊆ C := hS.subset_connectedComponentIn hxS hSK
  have hCo : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hxK
  have hCp : IsPathConnected C := (hCo.isConnected_iff_isPathConnected).1 hCc
  obtain ⟨γ, hγ⟩ := hCp.joinedIn x (hSC hxS) y (hSC hyS)
  obtain ⟨z, hz, hzK⟩ := h x y γ hxE hyF
  obtain ⟨t, rfl⟩ := hz
  exact connectedComponentIn_subset _ _ (hγ t) hzK

 
def IsOpenAnnularTube' (z : ℂ) (r : Set.Ioi (0 : ℝ)) (U : TopologicalSpace.Opens ℂ) : Prop :=
  (U : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)} ∧
  LQGMetric.Disconnects (U : Set ℂ) (Metric.sphere z r) (Metric.sphere z (3 * (r : ℝ)))

 
theorem isOpenAnnularTube'_of (z : ℂ) (r : Set.Ioi (0 : ℝ)) (U : TopologicalSpace.Opens ℂ)
    (hU : EndSaving.Interfaces.IsOpenAnnularTube z r U) : IsOpenAnnularTube' z r U :=
  ⟨hU.1, hU.2.2⟩

 
theorem isOpenAnnularTube'_of_sep (z : ℂ) (r : Set.Ioi (0 : ℝ)) (U : TopologicalSpace.Opens ℂ)
    {K : Set ℂ} (hKU : K ⊆ U) (hUA : (U : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)})
    (hK : LQGMetric.Disconnects K (Metric.sphere z r) (Metric.sphere z (3 * (r : ℝ)))) :
    IsOpenAnnularTube' z r U :=
  ⟨hUA, hK.mono hKU subset_rfl subset_rfl⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.T58Assembly

