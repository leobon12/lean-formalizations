import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA4




 













set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem cover_by_caps {P : ℝ → ℂ} {c : ℂ} {R₁ ε a b : ℝ} {W' : Set ℂ} (hR₁ : 0 < R₁) (hε : 0 < ε)
    (hcont : ContinuousOn P (Icc a b)) (hPa : ‖P a - c‖ = R₁) (hPb : ‖P b - c‖ = R₁)
    (hW' : ∀ w ∈ W', ∃ s ∈ Icc a b, R₁ + ε ≤ ‖P s - c‖ ∧
      w = LQGMetric.Topo.Crosscut.rproj c R₁ (P s))
    (hW's : W' ⊆ sphere c R₁) :
    W' ⊆ ⋃ e ∈ chargedExc P c R₁ ε a b W', sphere c R₁ ∩ closedBall (P e.1) (excReach P e) := by
  intro w hw
  obtain ⟨s, hs, hsfar, hws⟩ := hW' w hw
  obtain ⟨α, β, haα, hαs, hsβ, hβb, hα, hβ, hext⟩ :=
    Objects.Shadow.exists_excursion hcont hPa.le hPb.le hs (by linarith)
  have he : (α, β) ∈ chargedExc P c R₁ ε a b W' :=
    ⟨haα, hαs.trans hsβ, hβb, hα, hβ, hext, s, ⟨hαs.le, hsβ.le⟩, hsfar, w, hw, hws⟩
  refine mem_biUnion he ⟨hW's hw, ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  have hy : P α ∈ sphere c R₁ := by rw [mem_sphere, dist_eq_norm]; exact hα
  have h1 := Objects.Shadow.norm_rproj_sub_le hR₁ hy (by linarith : R₁ ≤ ‖P s - c‖)
  rw [← hws] at h1
  refine h1.trans ?_
  exact excReach_ge (P := P) (e := (α, β))
    (hcont.mono (Icc_subset_Icc haα hβb)) ⟨hαs.le, hsβ.le⟩

 
def cSel : ℝ := (1 - (Real.sqrt 2)⁻¹) / (112 * Real.pi)

theorem cSel_pos : 0 < cSel := by
  have h := Objects.ShadowChecks.inv_sqrt_two_lt_one
  unfold cSel
  have : 0 < 1 - (Real.sqrt 2)⁻¹ := by linarith [h.2]
  positivity

 
theorem exists_dyadic_bin {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) ≤ x ∧ x < (1 / 2 : ℝ) ^ k := by
  classical
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  set n := Nat.find hex with hn
  have hspec : (1 / 2 : ℝ) ^ n ≤ x := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hspec
    linarith
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hk] at hspec
  refine ⟨k, hspec, ?_⟩
  have hlt : k < Nat.find hex := by rw [← hn, hk]; exact Nat.lt_succ_self k
  have := Nat.find_min hex hlt
  push Not at this
  exact this

 
theorem dyadic_selection {P : ℝ → ℂ} {c : ℂ} {R₀ R₁ : NNReal} {θ₀ r ε η : ℝ}
    {S : Set (ℝ × ℝ)} {W' : Set ℂ} (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) (hr : 0 < r) (hε : 0 < ε)
    (hη1 : η < 1) (hS : S.Finite)
    (hreach : ∀ e ∈ S, ε * r ≤ excReach P e ∧ excReach P e < η * r)
    (hcen : ∀ e ∈ S, P e.1 ∈ sphere c (R₁ : ℝ))
    (hcover : W' ⊆ ⋃ e ∈ S, sphere c (R₁ : ℝ) ∩ closedBall (P e.1) (excReach P e))
    (hmass : ENNReal.ofReal ((R₀ : ℝ) / 16) ≤ Objects.Shadow.circleOuter c R₁ θ₀ W') :
    ∃ k : ℕ, ∃ T : Finset (ℝ × ℝ), (↑T : Set (ℝ × ℝ)) ⊆ S ∧
      (∀ e ∈ T, (1 / 2 : ℝ) ^ (k + 1) * r ≤ excReach P e ∧ excReach P e < (1 / 2 : ℝ) ^ k * r) ∧
      (∀ e ∈ T, ∀ e' ∈ T, e ≠ e' →
        Disjoint (closedBall (P e.1) (3 * excReach P e)) (closedBall (P e'.1) (3 * excReach P e'))) ∧
      cSel * ((R₀ : ℝ) / r) * Real.sqrt 2 ^ k ≤ T.card ∧
      (1 / 2 : ℝ) ^ (k + 1) < η := by
  classical
  have hR0r : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hR1r : (0 : ℝ) < R₁ := by exact_mod_cast hR₁
  
  set Sk : ℕ → Set (ℝ × ℝ) := fun k =>
    {e | e ∈ S ∧ (1 / 2 : ℝ) ^ (k + 1) * r ≤ excReach P e ∧ excReach P e < (1 / 2 : ℝ) ^ k * r}
    with hSk
  set cap : ℝ × ℝ → Set ℂ := fun e => sphere c (R₁ : ℝ) ∩ closedBall (P e.1) (excReach P e) with hcap
  obtain ⟨Kb, hKb⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hbin : ∀ e ∈ S, ∃ k ∈ Finset.range Kb, e ∈ Sk k := by
    intro e he
    obtain ⟨h1, h2⟩ := hreach e he
    have hx0 : 0 < excReach P e / r := div_pos (lt_of_lt_of_le (mul_pos hε hr) h1) hr
    have hx1 : excReach P e / r < 1 := by
      rw [div_lt_one hr]; nlinarith
    obtain ⟨k, hk1, hk2⟩ := exists_dyadic_bin hx0 hx1
    refine ⟨k, Finset.mem_range.2 ?_, he, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ Kb := pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
      have hεle : ε ≤ excReach P e / r := by rw [le_div_iff₀ hr]; exact h1
      linarith
    · rwa [le_div_iff₀ hr] at hk1
    · rwa [div_lt_iff₀ hr] at hk2
  
  set m : ℕ → ℝ≥0∞ := fun k => Objects.Shadow.circleOuter c R₁ θ₀ (⋃ e ∈ Sk k, cap e) with hm
  have hmfin : ∀ k, m k ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top ?_ (Objects.Shadow.circleOuter_mono (c := c) (R := R₁) (θ₀ := θ₀)
      (show (⋃ e ∈ Sk k, cap e) ⊆ sphere c (R₁ : ℝ) from fun z hz => by
        simp only [mem_iUnion] at hz
        obtain ⟨e, -, hze⟩ := hz
        exact hze.1))
    rw [Objects.Shadow.circleOuter_sphere]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hsum : ENNReal.ofReal ((R₀ : ℝ) / 16) ≤ ∑ k ∈ Finset.range Kb, m k := by
    refine hmass.trans ((Objects.Shadow.circleOuter_mono ?_).trans
      (Objects.Shadow.circleOuter_finset_iUnion_le (Finset.range Kb) (fun k => ⋃ e ∈ Sk k, cap e) c R₁ θ₀))
    intro z hz
    have := hcover hz
    simp only [mem_iUnion] at this ⊢
    obtain ⟨e, he, hze⟩ := this
    obtain ⟨k, hk, hek⟩ := hbin e he
    exact ⟨k, hk, e, hek, hze⟩
  have hsumR : (R₀ : ℝ) / 16 ≤ ∑ k ∈ Finset.range Kb, (m k).toReal := by
    rw [← ENNReal.toReal_sum (fun k _ => hmfin k)]
    have := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun k _ => hmfin k) hsum
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  set ρ := (Real.sqrt 2)⁻¹ with hρ
  have hρb := Objects.ShadowChecks.inv_sqrt_two_lt_one
  obtain ⟨k, hk, hmk⟩ := Objects.ShadowChecks.geom_pigeonhole hρb.1 (by positivity : (0 : ℝ) < (R₀ : ℝ) / 16) Kb
    (fun k => (m k).toReal) hsumR
  
  set h : ℝ := (1 / 2 : ℝ) ^ k * r with hhdef
  have hh : 0 < h := by positivity
  have hSkfin : (Sk k).Finite := hS.subset fun e he => he.1
  obtain ⟨T, hTsub, hTsep, -, hTmeas⟩ := Objects.Shadow.finite_greedy_cap_measure hSkfin (fun e => P e.1)
    (excReach P) (θ₀ := θ₀) hR₁ hh (fun e he => hcen e he.1) (fun e he => he.2.2)
  have hTmeasR : (m k).toReal ≤ T.card * (Real.pi * (7 * h)) := by
    have h1 : m k ≤ ∑ _e ∈ T, ENNReal.ofReal (Real.pi * (7 * h)) := hTmeas
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at h2
  refine ⟨k, T, fun e he => (hTsub he).1, fun e he => (hTsub he).2, ?_, ?_, ?_⟩
  · intro e he e' he' hne
    exact Objects.Shadow.triple_reach_disjoint (hTsub he).2.2 (hTsub he').2.2 (hTsep e he e' he' hne)
  · 
    have hsq : Real.sqrt 2 ^ k * ρ ^ k = 1 := by
      rw [← mul_pow, hρ, mul_inv_cancel₀ (by positivity), one_pow]
    have hhalf : (1 / 2 : ℝ) ^ k * Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = 1 := by
      rw [mul_assoc, ← mul_pow, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), ← mul_pow]
      norm_num
    have hpi : 0 < Real.pi := Real.pi_pos
    have hkey : (1 - ρ) * ρ ^ k * ((R₀ : ℝ) / 16) ≤ T.card * (Real.pi * (7 * h)) := hmk.trans hTmeasR
    unfold cSel
    rw [hhdef] at hkey
    have hρk : 0 < Real.sqrt 2 ^ k := by positivity
    have hgoal : (1 - ρ) / (112 * Real.pi) * ((R₀ : ℝ) / r) * Real.sqrt 2 ^ k =
        ((1 - ρ) * ρ ^ k * ((R₀ : ℝ) / 16)) / (Real.pi * (7 * ((1 / 2 : ℝ) ^ k * r))) := by
      field_simp
      nlinarith [hsq, hhalf]
    rw [hgoal, div_le_iff₀ (by positivity)]
    exact hkey
  · 
    have hpos : 0 < (m k).toReal := lt_of_lt_of_le (by
      have := hρb.2
      have : 0 < 1 - ρ := by linarith
      positivity) hmk
    have hne : (⋃ e ∈ Sk k, cap e).Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty] at hc
      have : m k = 0 := by
        simp only [hm, hc]
        unfold Objects.Shadow.circleOuter
        simp
      rw [this, ENNReal.toReal_zero] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨z, hz⟩ := hne
    simp only [mem_iUnion] at hz
    obtain ⟨e, he, -⟩ := hz
    have h1 := he.2.1
    have h2 := (hreach e he.1).2
    have : (1 / 2 : ℝ) ^ (k + 1) * r < η * r := lt_of_le_of_lt h1 h2
    exact lt_of_mul_lt_mul_right this hr.le

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
