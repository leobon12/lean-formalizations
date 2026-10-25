import SupercriticalLQGUniqueness.B2.PfeAxioms.RealRatioCompare

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem half_rpow_bounds (δ p : ℝ) (h1 : 1 / 2 < δ) (h2 : δ < 1) :
    Real.exp (-(Real.log 2 * |p|)) ≤ δ ^ p ∧
      δ ^ p ≤ Real.exp (Real.log 2 * |p|) := by
  have hδ : 0 < δ := lt_trans (by norm_num) h1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlo : -Real.log 2 ≤ Real.log δ := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1.le
    rwa [one_div, Real.log_inv] at h
  have hhi : Real.log δ ≤ 0 := Real.log_nonpos hδ.le h2.le
  have habs : |Real.log δ| ≤ Real.log 2 := abs_le.mpr ⟨hlo, by linarith⟩
  have hmul : |Real.log δ * p| ≤ Real.log 2 * |p| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg p)
  obtain ⟨hl, hu⟩ := abs_le.mp hmul
  rw [Real.rpow_def_of_pos hδ]
  exact ⟨Real.exp_le_exp.mpr hl, Real.exp_le_exp.mpr hu⟩

private theorem ratio_cancel_real' (δ q a b m : ℝ)
    (hq : q ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    (((δ * q) * a / m) / (q * b / m)) = δ * a / b := by
  field_simp

 




theorem real_ratio_compare_uniform_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℕ → Ioi (0 : ℝ)), Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) →
      ∀ (r q : Ioi (0 : ℝ)), (r : ℝ) < (q : ℝ) →
      ∀ (cr cq : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(e n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩ : ℝ) /
          (m (e n) : ℝ)) atTop (𝓝 (cr : ℝ)) →
        Tendsto (fun n => (q : ℝ) *
          (m ⟨(e n : ℝ) / (q : ℝ),
            Set.mem_Ioi.mpr (div_pos (e n).property q.property)⟩ : ℝ) /
          (m (e n) : ℝ)) atTop (𝓝 (cq : ℝ)) →
        C⁻¹ * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q + ζ) ≤
            (cr : ℝ) / (cq : ℝ) ∧
          (cr : ℝ) / (cq : ℝ) ≤
            C * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q - ζ) := by
  obtain ⟨C, hC, hbound⟩ := (hS ξ Q hQ m hm).2.1 ζ hζ
  refine ⟨C, hC, ?_⟩
  intro e he r q hrq cr cq hcr hcq
  let δ : Ioo (0 : ℝ) 1 :=
    ⟨(r : ℝ) / (q : ℝ), div_pos r.property q.property,
      (div_lt_one q.property).2 hrq⟩
  let A : ℕ → ℝ := fun n => (r : ℝ) *
    (m ⟨(e n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩ : ℝ) /
    (m (e n) : ℝ)
  let B : ℕ → ℝ := fun n => (q : ℝ) *
    (m ⟨(e n : ℝ) / (q : ℝ),
      Set.mem_Ioi.mpr (div_pos (e n).property q.property)⟩ : ℝ) /
    (m (e n) : ℝ)
  have hAB : Tendsto (fun n => A n / B n) atTop
      (𝓝 ((cr : ℝ) / (cq : ℝ))) :=
    hcr.div hcq (ne_of_gt cq.property)
  have hev : ∀ᶠ n in atTop, (e n : ℝ) < (r : ℝ) :=
    he.eventually (Iio_mem_nhds r.property)
  have hbounds : ∀ᶠ n in atTop,
      C⁻¹ * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q + ζ) ≤ A n / B n ∧
      A n / B n ≤ C * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q - ζ) := by
    filter_upwards [hev] with n hn
    let e' : Ioo (0 : ℝ) (δ : ℝ) :=
      ⟨(e n : ℝ) / (q : ℝ), div_pos (e n).property q.property,
        by dsimp [δ]; exact (div_lt_div_of_pos_right hn q.property)⟩
    have hstep := hbound δ e'
    have heA : (⟨(e n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩ : Ioi (0 : ℝ)) =
        ⟨(e' : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e'.property.1 δ.property.1)⟩ := by
      apply Subtype.ext
      dsimp [e', δ]
      field_simp [ne_of_gt (Set.mem_Ioi.mp r.property),
        ne_of_gt (Set.mem_Ioi.mp q.property)]
    have heB : (⟨(e n : ℝ) / (q : ℝ),
        Set.mem_Ioi.mpr (div_pos (e n).property q.property)⟩ : Ioi (0 : ℝ)) =
        ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩ := rfl
    have hcancel : A n / B n = (δ : ℝ) *
        (m ⟨(e' : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e'.property.1 δ.property.1)⟩ : ℝ) /
        (m ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩ : ℝ) := by
      dsimp [A, B]
      rw [heA, heB]
      have hr : (r : ℝ) = (δ : ℝ) * (q : ℝ) := by
        dsimp [δ]
        rw [div_eq_mul_inv, mul_assoc,
          inv_mul_cancel₀ (ne_of_gt (Set.mem_Ioi.mp q.property)), mul_one]
      rw [hr]
      exact ratio_cancel_real' _ _ _ _ _ (ne_of_gt q.property)
        (ne_of_gt (m ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩).property)
        (ne_of_gt (m (e n)).property)
    simpa only [δ, hcancel] using hstep
  exact ⟨ge_of_tendsto hAB (hbounds.mono fun n hn => hn.1),
    le_of_tendsto hAB (hbounds.mono fun n hn => hn.2)⟩

 






theorem exists_uniform_cluster_normalizer_compare
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (r c' : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c' : ℝ)) →
        K⁻¹ ≤ (c' : ℝ) / (c r : ℝ) ∧ (c' : ℝ) / (c r : ℝ) ≤ K := by
  obtain ⟨C, hC, hcmp⟩ :=
    real_ratio_compare_uniform_of_section4 hS ξ Q hQ m hm 1 one_pos
  have hΛpos : 0 < Λ := lt_trans one_pos hΛ
  set L : ℝ := Real.log 2 with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by norm_num)
  set p₁ : ℝ := (ξ : ℝ) * Q + 1
  set p₂ : ℝ := (ξ : ℝ) * Q - 1
  set E : ℝ := Real.exp (L * (|p₁| + |p₂| + |Λ|))
  have hE : 0 < E := Real.exp_pos _
  let K : ℝ := (C + C⁻¹) * Λ * E
  have hCC : 0 < C + C⁻¹ := by positivity
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro r c' ψ hψ hc'
  obtain ⟨q, hrq, hq2⟩ := exists_rat_btwn
    (show (r : ℝ) < 2 * (r : ℝ) by linarith [Set.mem_Ioi.mp r.property])
  have hq : (0 : ℚ) < q := by
    have : (0 : ℝ) < (q : ℝ) := lt_trans r.property hrq
    exact_mod_cast this
  let qq : Ioi (0 : ℝ) := ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hq)⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := Rat.cast_pos.mpr hq
  have hcq : Tendsto (fun n => (qq : ℝ) *
      (m ⟨(ε (ψ n) : ℝ) / (qq : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property qq.property)⟩ : ℝ) /
      (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c qq : ℝ)) :=
    (hc q hq).comp hψ.tendsto_atTop
  have hεψ : Tendsto (fun n => (ε (ψ n) : ℝ)) atTop (𝓝 0) :=
    hε.comp hψ.tendsto_atTop
  obtain ⟨hlow1, hupp1⟩ := hcmp (fun n => ε (ψ n)) hεψ r qq hrq c' (c qq) hc' hcq
  
  set d : ℝ := (r : ℝ) / (q : ℝ) with hd
  have hd1 : 1 / 2 < d := by
    rw [hd, lt_div_iff₀ hqpos]; linarith
  have hd2 : d < 1 := (div_lt_one hqpos).2 hrq
  have hd0 : 0 < d := lt_trans (by norm_num) hd1
  let δ : Ioo (0 : ℝ) 1 := ⟨d, hd0, hd2⟩
  have hVr := hV δ q hq
  have hrr : (⟨(δ : ℝ) * (q : ℝ), Set.mem_Ioi.mpr
      (mul_pos δ.property.1 (Rat.cast_pos.mpr hq))⟩ : Ioi (0 : ℝ)) = r := by
    apply Subtype.ext
    change (r : ℝ) / (q : ℝ) * (q : ℝ) = (r : ℝ)
    field_simp
  rw [hrr] at hVr
  change Λ⁻¹ * d ^ Λ ≤ (c r : ℝ) / (c qq : ℝ) ∧
      (c r : ℝ) / (c qq : ℝ) ≤ Λ * d ^ (-Λ) at hVr
  obtain ⟨hlow2, hupp2⟩ := hVr
  obtain ⟨hp1l, -⟩ := half_rpow_bounds d p₁ hd1 hd2
  obtain ⟨-, hp2u⟩ := half_rpow_bounds d p₂ hd1 hd2
  obtain ⟨hΛl, -⟩ := half_rpow_bounds d Λ hd1 hd2
  obtain ⟨-, hΛu⟩ := half_rpow_bounds d (-Λ) hd1 hd2
  rw [abs_neg] at hΛu
  have hcr : 0 < (c r : ℝ) := (c r).property
  have hcqv : 0 < (c qq : ℝ) := (c qq).property
  have hc'v : 0 < (c' : ℝ) := c'.property
  
  have hsplit : (c' : ℝ) / (c r : ℝ) =
      ((c' : ℝ) / (c qq : ℝ)) / ((c r : ℝ) / (c qq : ℝ)) := by
    field_simp
  set x : ℝ := (c' : ℝ) / (c qq : ℝ) with hx
  set y : ℝ := (c r : ℝ) / (c qq : ℝ) with hy
  have hy0 : 0 < y := div_pos hcr hcqv
  have hEa : Real.exp (L * |p₁|) * Real.exp (L * |Λ|) ≤ E := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg p₁, abs_nonneg p₂, abs_nonneg Λ]
  have hEb : Real.exp (L * |p₂|) * Real.exp (L * |Λ|) ≤ E := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg p₁, abs_nonneg p₂, abs_nonneg Λ]
  have hexp_inv (t : ℝ) : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  rw [hsplit]
  constructor
  · 
    have hxl : C⁻¹ * (Real.exp (L * |p₁|))⁻¹ ≤ x := by
      have := mul_le_mul_of_nonneg_left (hexp_inv (L * |p₁|) ▸ hp1l)
        (inv_pos.mpr hC).le
      exact this.trans hlow1
    have hyu : y ≤ Λ * Real.exp (L * |Λ|) :=
      hupp2.trans (mul_le_mul_of_nonneg_left hΛu hΛpos.le)
    have hden : 0 < Λ * Real.exp (L * |Λ|) := by positivity
    have hstep : (C⁻¹ * (Real.exp (L * |p₁|))⁻¹) / (Λ * Real.exp (L * |Λ|)) ≤
        x / y := by
      exact div_le_div₀ (div_pos hc'v hcqv).le hxl hy0 hyu
    refine le_trans ?_ hstep
    have hKbig : C * Λ * (Real.exp (L * |p₁|) * Real.exp (L * |Λ|)) ≤ K := by
      dsimp [K]
      have h1 : C ≤ C + C⁻¹ := by linarith [inv_pos.mpr hC]
      have h2 : 0 ≤ Real.exp (L * |p₁|) * Real.exp (L * |Λ|) := by positivity
      calc C * Λ * (Real.exp (L * |p₁|) * Real.exp (L * |Λ|))
          ≤ (C + C⁻¹) * Λ * (Real.exp (L * |p₁|) * Real.exp (L * |Λ|)) := by
            gcongr
        _ ≤ (C + C⁻¹) * Λ * E := by gcongr
    have hpos : 0 < C * Λ * (Real.exp (L * |p₁|) * Real.exp (L * |Λ|)) := by
      positivity
    have heq : (C⁻¹ * (Real.exp (L * |p₁|))⁻¹) / (Λ * Real.exp (L * |Λ|)) =
        (C * Λ * (Real.exp (L * |p₁|) * Real.exp (L * |Λ|)))⁻¹ := by
      field_simp
    rw [heq]
    exact (inv_le_inv₀ hK hpos).2 hKbig
  · 
    have hxu : x ≤ C * Real.exp (L * |p₂|) :=
      hupp1.trans (mul_le_mul_of_nonneg_left hp2u hC.le)
    have hyl : Λ⁻¹ * (Real.exp (L * |Λ|))⁻¹ ≤ y := by
      have := mul_le_mul_of_nonneg_left (hexp_inv (L * |Λ|) ▸ hΛl)
        (inv_pos.mpr hΛpos).le
      exact this.trans hlow2
    have hylpos : 0 < Λ⁻¹ * (Real.exp (L * |Λ|))⁻¹ := by positivity
    have hstep : x / y ≤ (C * Real.exp (L * |p₂|)) / (Λ⁻¹ * (Real.exp (L * |Λ|))⁻¹) := by
      apply div_le_div₀ (by positivity) hxu hylpos hyl
    refine hstep.trans ?_
    have heq : (C * Real.exp (L * |p₂|)) / (Λ⁻¹ * (Real.exp (L * |Λ|))⁻¹) =
        C * Λ * (Real.exp (L * |p₂|) * Real.exp (L * |Λ|)) := by
      field_simp
    rw [heq]
    dsimp [K]
    have h1 : C ≤ C + C⁻¹ := by linarith [inv_pos.mpr hC]
    calc C * Λ * (Real.exp (L * |p₂|) * Real.exp (L * |Λ|))
        ≤ (C + C⁻¹) * Λ * (Real.exp (L * |p₂|) * Real.exp (L * |Λ|)) := by
          gcongr
      _ ≤ (C + C⁻¹) * Λ * E := by gcongr

end SupercriticalLQGUniqueness.B2.PfeAxioms
