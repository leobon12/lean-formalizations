import SupercriticalLQGUniqueness.B2.PfeAxioms.PositiveRatioCluster

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_real_ratio_cluster_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (r : Ioi (0 : ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Ioi (0 : ℝ),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (φ n)).property r.property)⟩ : ℝ) /
          (m (ε (φ n)) : ℝ)) atTop (𝓝 (c : ℝ)) := by
  let R : ℕ → ℝ := fun n => (r : ℝ) *
    (m ⟨(ε n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
    (m (ε n) : ℝ)
  have hcompact : ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, R n ∈ Icc a b := by
    rcases lt_trichotomy (r : ℝ) 1 with hr | hr | hr
    · obtain ⟨C, hC, hbound⟩ := (hS ξ Q hQ m hm).2.1 1 one_pos
      let a : ℝ := C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + 1)
      let b : ℝ := C * (r : ℝ) ^ ((ξ : ℝ) * Q - 1)
      have ha : 0 < a := mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos r.property _)
      have hev : ∀ᶠ n in atTop, (ε n : ℝ) < (r : ℝ) :=
        hε.eventually (Iio_mem_nhds r.property)
      refine ⟨a, b, ha, ?_⟩
      filter_upwards [hev] with n hn
      exact hbound ⟨r, r.property, hr⟩
        ⟨(ε n : ℝ), (ε n).property, hn⟩
    · have hR : ∀ n, R n = 1 := by
        intro n
        dsimp [R]
        have hsub : (⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : Ioi (0 : ℝ)) =
            ε n := by
          apply Subtype.ext
          simp [hr]
        rw [hsub]
        rw [hr, one_mul, div_self (ne_of_gt (m (ε n)).property)]
      exact ⟨1, 1, one_pos, Filter.Eventually.of_forall
        (fun n => by simp [hR n])⟩
    · obtain ⟨C, hC, hbound⟩ := (hS ξ Q hQ m hm).2.2 1 one_pos
      let a : ℝ := C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q - 1)
      let b : ℝ := C * (r : ℝ) ^ ((ξ : ℝ) * Q + 1)
      have ha : 0 < a := mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos r.property _)
      have hev : ∀ᶠ n in atTop, (ε n : ℝ) < 1 :=
        hε.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      refine ⟨a, b, ha, ?_⟩
      filter_upwards [hev] with n hn
      exact hbound ⟨r, hr⟩ ⟨(ε n : ℝ), (ε n).property, hn⟩
  obtain ⟨a, b, ha, hab⟩ := hcompact
  obtain ⟨φ, hφ, c, hc⟩ :=
    exists_positive_subseq_limit_of_eventually_Icc R ha hab
  exact ⟨φ, hφ, c, hc⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
