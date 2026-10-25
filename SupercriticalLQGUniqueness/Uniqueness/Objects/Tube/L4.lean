import Mathlib




 















set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
theorem first_reach {f : ℝ → ℝ} {e t c : ℝ} (het : e ≤ t) (hf : ContinuousOn f (Icc e t))
    (he : f e < c) (ht : c ≤ f t) : ∃ q ∈ Ioc e t, f q = c ∧ ∀ u ∈ Icc e q, f u ≤ c := by
  set S := {u | u ∈ Icc e t ∧ c ≤ f u} with hS
  have hSc : IsClosed S := by
    have : S = Icc e t ∩ f ⁻¹' Ici c := by ext u; simp [hS]
    rw [this]; exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have htS : t ∈ S := ⟨⟨het, le_rfl⟩, ht⟩
  have hbdd : BddBelow S := ⟨e, fun u hu => hu.1.1⟩
  set q := sInf S with hq
  have hqS : q ∈ S := hSc.csInf_mem ⟨t, htS⟩ hbdd
  have heq : e ≤ q := hqS.1.1
  have hqt : q ≤ t := hqS.1.2
  have hqe : e < q := by
    rcases heq.lt_or_eq with h | h
    · exact h
    · exfalso; have := hqS.2; rw [← h] at this; linarith
  have hbelow : ∀ u ∈ Ico e q, f u < c := by
    intro u hu
    by_contra hcon
    have huS : u ∈ S := ⟨⟨hu.1, hu.2.le.trans hqt⟩, not_lt.mp hcon⟩
    have := csInf_le hbdd huS
    linarith [hu.2]
  have hfq : f q = c := by
    rcases (hqS.2).lt_or_eq with h | h
    · exfalso
      have hcont : ContinuousOn f (Icc e q) := hf.mono (Icc_subset_Icc le_rfl hqt)
      obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc heq hcont ⟨he.le, h.le⟩
      rcases hu.2.lt_or_eq with h' | h'
      · have := hbelow u ⟨hu.1, h'⟩; linarith
      · rw [h'] at hfu; linarith
    · exact h.symm
  refine ⟨q, ⟨hqe, hqt⟩, hfq, ?_⟩
  intro u hu
  rcases hu.2.lt_or_eq with h | h
  · exact (hbelow u ⟨hu.1, h⟩).le
  · rw [h, hfq]

 
theorem last_in_closed {g : ℝ → ℂ} {K : Set ℂ} {τ t : ℝ} (hτt : τ ≤ t)
    (hg : ContinuousOn g (Icc τ t)) (hK : IsClosed K) (hτ : g τ ∈ K) :
    ∃ e ∈ Icc τ t, g e ∈ K ∧ ∀ u ∈ Ioc e t, g u ∉ K := by
  set T := {u | u ∈ Icc τ t ∧ g u ∈ K} with hT
  have hTc : IsClosed T := by
    have : T = Icc τ t ∩ g ⁻¹' K := by ext u; simp [hT]
    rw [this]; exact hg.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hτT : τ ∈ T := ⟨⟨le_rfl, hτt⟩, hτ⟩
  have hbdd : BddAbove T := ⟨t, fun u hu => hu.1.2⟩
  have heT : sSup T ∈ T := hTc.csSup_mem ⟨τ, hτT⟩ hbdd
  refine ⟨sSup T, heT.1, heT.2, ?_⟩
  intro u hu hgu
  have : u ≤ sSup T := le_csSup hbdd ⟨⟨(heT.1.1).trans hu.1.le, hu.2⟩, hgu⟩
  linarith [hu.1]

 
theorem later_mem_open {g : ℝ → ℂ} {V : Set ℂ} {τ σ e t : ℝ} (hg : ContinuousOn g (Icc τ σ))
    (hV : IsOpen V) (hτe : τ ≤ e) (het : e < t) (htσ : t ≤ σ) (he : g e ∈ V) :
    ∃ u ∈ Ioc e t, g u ∈ V := by
  have heI : e ∈ Icc τ σ := ⟨hτe, het.le.trans htσ⟩
  have hmem : g ⁻¹' V ∈ nhdsWithin e (Icc τ σ) :=
    (hg e heI).preimage_mem_nhdsWithin (hV.mem_nhds he)
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨ε, hε, hsub⟩ := hmem
  set u := min (e + ε / 2) t with hu
  have h1 : e < u := lt_min (by linarith) het
  have h2 : u ≤ t := min_le_right _ _
  have h3 : dist u e < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith
    · have : u ≤ e + ε / 2 := min_le_left _ _
      linarith
  exact ⟨u, ⟨h1, h2⟩, hsub ⟨Metric.mem_ball.2 h3, ⟨hτe.trans h1.le, h2.trans htσ⟩⟩⟩

 
theorem L4_of_L3_C6 {P : ℝ → ℂ} {V W : Set ℂ} {τ σ r Anar N a lam : ℝ}
    (hP : ContinuousOn P (Icc τ σ)) (hV : IsOpen V) (hτ : P τ ∈ closure V)
    (hr : 0 < r) (hAnar : 0 < Anar) (hN : 0 < N) (ha : 0 < a) (hlam0 : 0 < lam)
    (hlam : 3 * lam < 1)
    (hloc : ∀ x y, y ∈ closure V → dist x y ≤ Anar * r → x ∈ W)
    (hC6 : ∀ s t, τ ≤ s → s ≤ t → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ V) → (∀ u ∈ Icc s t, P u ∈ W) →
      dist (P s) (P t) ≤ lam⁻¹ * (Anar * r) → (dist (P s) (P t) / r) ^ a * N ≤ t - s)
    (hL3 : σ - τ ≤ 3 * lam * Anar ^ a * N) :
    (∀ t ∈ Icc τ σ, ∃ y ∈ closure V, dist (P t) y < Anar * r) ∧
    (∀ s t, τ ≤ s → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ V) →
      ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, dist (P u) (P v) ≤ (3 * lam) ^ (1 / a) * Anar * r) := by
  have hAr : 0 < Anar * r := mul_pos hAnar hr
  have hAa : 0 < Anar ^ a * N := mul_pos (Real.rpow_pos_of_pos hAnar a) hN
  have hlam1 : Anar * r ≤ lam⁻¹ * (Anar * r) := by
    have : 1 ≤ lam⁻¹ := one_le_inv₀ hlam0 |>.mpr (by linarith)
    nlinarith
  
  have noexc : ∀ s q, τ ≤ s → s ≤ q → q ≤ σ → (∀ u ∈ Icc s q, P u ∉ V) →
      (∀ u ∈ Icc s q, P u ∈ W) → dist (P s) (P q) = Anar * r → False := by
    intro s q hs hsq hq hoff hW hd
    have := hC6 s q hs hsq hq hoff hW (by rw [hd]; exact hlam1)
    rw [hd, mul_div_assoc, div_self hr.ne', mul_one] at this
    have h3 : q - s ≤ σ - τ := by linarith
    nlinarith
  have part1 : ∀ t ∈ Icc τ σ, ∃ y ∈ closure V, dist (P t) y < Anar * r := by
    intro t ht
    have hPt : ContinuousOn P (Icc τ t) := hP.mono (Icc_subset_Icc le_rfl ht.2)
    obtain ⟨e, he, hPe, hafter⟩ := last_in_closed ht.1 hPt isClosed_closure hτ
    by_cases hd : dist (P t) (P e) < Anar * r
    · exact ⟨P e, hPe, hd⟩
    exfalso
    have hd' : Anar * r ≤ dist (P t) (P e) := not_lt.mp hd
    have het : e < t := by
      rcases he.2.lt_or_eq with h | h
      · exact h
      · rw [h, dist_self] at hd'; linarith
    have hPeV : P e ∉ V := by
      intro hV'
      obtain ⟨u, hu, hPu⟩ := later_mem_open hP hV he.1 het ht.2 hV'
      exact hafter u hu (subset_closure hPu)
    have hcont : ContinuousOn (fun u => dist (P u) (P e)) (Icc e t) :=
      continuous_dist.comp_continuousOn ((hP.mono (Icc_subset_Icc he.1 ht.2)).prodMk continuousOn_const)
    obtain ⟨q, hq, hfq, hle⟩ := first_reach het.le hcont (by simp [hAr]) hd'
    apply noexc e q he.1 hq.1.le (hq.2.trans ht.2)
    · intro u hu
      rcases hu.1.lt_or_eq with h | h
      · exact fun hV' => hafter u ⟨h, hu.2.trans hq.2⟩ (subset_closure hV')
      · rw [← h]; exact hPeV
    · intro u hu
      exact hloc (P u) (P e) hPe (hle u hu)
    · rw [dist_comm]; exact hfq
  refine ⟨part1, ?_⟩
  intro s t hs ht hoff
  
  have key : ∀ u v, u ∈ Icc s t → v ∈ Icc s t → u ≤ v →
      dist (P u) (P v) ≤ (3 * lam) ^ (1 / a) * Anar * r := by
    intro u v hu hv huv
    have hτu : τ ≤ u := hs.trans hu.1
    have hvσ : v ≤ σ := hv.2.trans ht
    have hoff' : ∀ w ∈ Icc u v, P w ∉ V := fun w hw => hoff w ⟨hu.1.trans hw.1, hw.2.trans hv.2⟩
    have hW : ∀ w ∈ Icc u v, P w ∈ W := by
      intro w hw
      obtain ⟨y, hy, hdy⟩ := part1 w ⟨hτu.trans hw.1, hw.2.trans hvσ⟩
      exact hloc (P w) y hy hdy.le
    have hsmall : dist (P u) (P v) ≤ Anar * r := by
      by_contra hcon
      have hcon' : Anar * r ≤ dist (P v) (P u) := by rw [dist_comm]; exact (not_le.mp hcon).le
      have hcont : ContinuousOn (fun w => dist (P w) (P u)) (Icc u v) :=
        continuous_dist.comp_continuousOn ((hP.mono (Icc_subset_Icc hτu hvσ)).prodMk continuousOn_const)
      obtain ⟨q, hq, hfq, -⟩ := first_reach huv hcont (by simp [hAr]) hcon'
      apply noexc u q hτu hq.1.le (hq.2.trans hvσ)
      · exact fun w hw => hoff' w ⟨hw.1, hw.2.trans hq.2⟩
      · exact fun w hw => hW w ⟨hw.1, hw.2.trans hq.2⟩
      · rw [dist_comm]; exact hfq
    have hC := hC6 u v hτu huv hvσ hoff' hW (hsmall.trans hlam1)
    have h3 : v - u ≤ σ - τ := by linarith
    set d := dist (P u) (P v) with hd
    have hd0 : 0 ≤ d / r := div_nonneg dist_nonneg hr.le
    have h4 : (d / r) ^ a ≤ 3 * lam * Anar ^ a := by
      have : (d / r) ^ a * N ≤ 3 * lam * Anar ^ a * N := by linarith
      exact le_of_mul_le_mul_right this hN
    have h5 : 3 * lam * Anar ^ a = ((3 * lam) ^ (1 / a) * Anar) ^ a := by
      rw [Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hAnar.le, ← Real.rpow_mul (by linarith),
        one_div_mul_cancel ha.ne', Real.rpow_one]
    rw [h5] at h4
    have h6 : d / r ≤ (3 * lam) ^ (1 / a) * Anar :=
      (Real.rpow_le_rpow_iff hd0 (mul_nonneg (Real.rpow_nonneg (by linarith) _) hAnar.le) ha).mp h4
    rw [div_le_iff₀ hr] at h6
    linarith
  intro u hu v hv
  rcases le_total u v with h | h
  · exact key u v hu hv h
  · rw [dist_comm]; exact key v u hv hu h

 
theorem theta_lt_one {lam a : ℝ} (hlam0 : 0 < lam) (hlam : 3 * lam < 1) (ha : 0 < a) :
    (3 * lam) ^ (1 / a) < 1 :=
  Real.rpow_lt_one (by linarith) hlam (by positivity)

 
theorem hjump_of_L4 {P : ℝ → ℂ} {V : Set ℂ} {τ σ r Anar a lam : ℝ} (hr : 0 < r)
    (hAnar : 0 < Anar) (ha : 0 < a) (hlam0 : 0 < lam) (hlam : 3 * lam < 1)
    (hL4 : ∀ s t, τ ≤ s → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ V) →
      ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, dist (P u) (P v) ≤ (3 * lam) ^ (1 / a) * Anar * r) :
    ∀ s t, τ ≤ s → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ V) →
      ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
        dist (P u) (P v) < ((1 + (3 * lam) ^ (1 / a)) / 2) * Anar * r := by
  intro s t hs ht hoff u hu v hv
  have h1 := hL4 s t hs ht hoff u hu v hv
  have h2 := theta_lt_one hlam0 hlam ha
  have hAr : 0 < Anar * r := mul_pos hAnar hr
  nlinarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
