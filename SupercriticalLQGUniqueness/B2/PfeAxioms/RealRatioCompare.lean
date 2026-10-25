import SupercriticalLQGUniqueness.B2.PfeAxioms.RealRatioCluster

 



set_option autoImplicit false
noncomputable section

open Set Filter Topology
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private theorem ratio_cancel_real (δ q a b m : ℝ)
    (hq : q ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    (((δ * q) * a / m) / (q * b / m)) = δ * a / b := by
  field_simp

theorem real_ratio_cluster_compare_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (r q : Ioi (0 : ℝ)) (hrq : (r : ℝ) < (q : ℝ))
    (cr cq : Ioi (0 : ℝ))
    (hcr : Tendsto (fun n => (r : ℝ) *
      (m ⟨(ε n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
      (m (ε n) : ℝ)) atTop (𝓝 (cr : ℝ)))
    (hcq : Tendsto (fun n => (q : ℝ) *
      (m ⟨(ε n : ℝ) / (q : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property q.property)⟩ : ℝ) /
      (m (ε n) : ℝ)) atTop (𝓝 (cq : ℝ)))
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 < C ∧
      C⁻¹ * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q + ζ) ≤
        (cr : ℝ) / (cq : ℝ) ∧
      (cr : ℝ) / (cq : ℝ) ≤
        C * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q - ζ) := by
  obtain ⟨C, hC, hbound⟩ := (hS ξ Q hQ m hm).2.1 ζ hζ
  let δ : Ioo (0 : ℝ) 1 :=
    ⟨(r : ℝ) / (q : ℝ), div_pos r.property q.property,
      (div_lt_one q.property).2 hrq⟩
  let A : ℕ → ℝ := fun n => (r : ℝ) *
    (m ⟨(ε n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
    (m (ε n) : ℝ)
  let B : ℕ → ℝ := fun n => (q : ℝ) *
    (m ⟨(ε n : ℝ) / (q : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property q.property)⟩ : ℝ) /
    (m (ε n) : ℝ)
  have hAB : Tendsto (fun n => A n / B n) atTop
      (𝓝 ((cr : ℝ) / (cq : ℝ))) :=
    hcr.div hcq (ne_of_gt cq.property)
  have hev : ∀ᶠ n in atTop, (ε n : ℝ) < (r : ℝ) :=
    hε.eventually (Iio_mem_nhds r.property)
  have hbounds : ∀ᶠ n in atTop,
      C⁻¹ * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q + ζ) ≤
        A n / B n ∧
      A n / B n ≤ C * ((r : ℝ) / (q : ℝ)) ^ ((ξ : ℝ) * Q - ζ) := by
    filter_upwards [hev] with n hn
    let e : Ioo (0 : ℝ) (δ : ℝ) :=
      ⟨(ε n : ℝ) / (q : ℝ), div_pos (ε n).property q.property,
        by dsimp [δ]; exact (div_lt_div_of_pos_right hn q.property)⟩
    have hstep := hbound δ e
    have heA : (⟨(ε n : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : Ioi (0 : ℝ)) =
        ⟨(e : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e.property.1 δ.property.1)⟩ := by
      apply Subtype.ext
      dsimp [e, δ]
      field_simp [ne_of_gt (Set.mem_Ioi.mp r.property),
        ne_of_gt (Set.mem_Ioi.mp q.property)]
    have heB : (⟨(ε n : ℝ) / (q : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property q.property)⟩ : Ioi (0 : ℝ)) =
        ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩ := rfl
    have hcancel : A n / B n = (δ : ℝ) *
        (m ⟨(e : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e.property.1 δ.property.1)⟩ : ℝ) /
        (m ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩ : ℝ) := by
      dsimp [A, B]
      rw [heA, heB]
      have hr : (r : ℝ) = (δ : ℝ) * (q : ℝ) := by
        dsimp [δ]
        rw [div_eq_mul_inv, mul_assoc,
          inv_mul_cancel₀ (ne_of_gt (Set.mem_Ioi.mp q.property)), mul_one]
      rw [hr]
      exact ratio_cancel_real _ _ _ _ _ (ne_of_gt q.property)
        (ne_of_gt (m ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩).property)
        (ne_of_gt (m (ε n)).property)
    simpa only [δ, hcancel] using hstep
  exact ⟨C, hC,
    ge_of_tendsto hAB (hbounds.mono fun n hn => hn.1),
    le_of_tendsto hAB (hbounds.mono fun n hn => hn.2)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
