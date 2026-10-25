import SupercriticalLQGUniqueness.B2.DG20Lim.RatioSubseq
import SupercriticalLQGUniqueness.B2.Iface.Statements

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

open SupercriticalLQGUniqueness.B2.Iface

private def ratioValue
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (n : ℕ) (r : Set.Ioi (0 : ℚ)) : ℝ :=
  (r : ℝ) *
    (m ⟨(ε n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr r.property))⟩ : ℝ) /
    (m (ε n) : ℝ)

private theorem ratioValue_pos
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (n : ℕ)
    (r : Set.Ioi (0 : ℚ)) : 0 < ratioValue m ε n r := by
  unfold ratioValue
  exact div_pos (mul_pos (Rat.cast_pos.mpr r.property) (m _).property) (m _).property

 

theorem exists_positive_ratio_subseq_of_section4
    (hS4 : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ c : Set.Ioi (0 : ℚ) → Set.Ioi (0 : ℝ),
        ∀ r, Tendsto (fun n => ratioValue m ε (ψ n) r) atTop
          (𝓝 (c r : ℝ)) := by
  have hsmall := (hS4 ξ Q hQ m hm).2.1
  have hlarge := (hS4 ξ Q hQ m hm).2.2
  apply exists_positive_ratio_subseq (ratioValue m ε) (ratioValue_pos m ε)
  intro r
  have hr : (0 : ℝ) < (r : ℝ) := Rat.cast_pos.mpr r.property
  rcases lt_trichotomy (r : ℝ) 1 with hlt | heq | hgt
  · let δ : Set.Ioo (0 : ℝ) 1 := ⟨(r : ℝ), hr, hlt⟩
    obtain ⟨C, hC, hbound⟩ := hsmall 1 one_pos
    let lo : ℝ := C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + 1)
    let hi : ℝ := C * (r : ℝ) ^ ((ξ : ℝ) * Q - 1)
    have hpos : 0 < lo := mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hr _)
    have hev : ∀ᶠ n in atTop, (ε n : ℝ) < (r : ℝ) :=
      (tendsto_order.1 hε).2 _ hr
    have hbounds : ∀ᶠ n in atTop, lo ≤ ratioValue m ε n r ∧
        ratioValue m ε n r ≤ hi := by
      filter_upwards [hev] with n hn
      let e : Set.Ioo (0 : ℝ) (r : ℝ) := ⟨(ε n : ℝ), (ε n).property, hn⟩
      simpa only [ratioValue, lo, hi] using (hbound δ e)
    obtain ⟨n, hn⟩ := hbounds.exists
    exact ⟨lo, hi, hpos, (hn.1.trans hn.2), hbounds⟩
  · have hr1 : (r : ℝ) = 1 := heq
    have hval : ∀ n, ratioValue m ε n r = 1 := by
      intro n
      unfold ratioValue
      have hs :
          (⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr r.property))⟩ :
              Set.Ioi (0 : ℝ)) = ε n := by
        apply Subtype.ext
        simp [hr1]
      rw [hs]
      have hposm : 0 < (m (ε n) : ℝ) := (m (ε n)).property
      simp [hr1, ne_of_gt hposm]
    exact ⟨1, 1, one_pos, le_rfl, Filter.Eventually.of_forall fun n => by
      simp only [hval n, le_refl, and_self]⟩
  · let R : Set.Ioi (1 : ℝ) := ⟨(r : ℝ), hgt⟩
    obtain ⟨C, hC, hbound⟩ := hlarge 1 one_pos
    let lo : ℝ := C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q - 1)
    let hi : ℝ := C * (r : ℝ) ^ ((ξ : ℝ) * Q + 1)
    have hpos : 0 < lo := mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hr _)
    have hev : ∀ᶠ n in atTop, (ε n : ℝ) < 1 :=
      (tendsto_order.1 hε).2 _ one_pos
    have hbounds : ∀ᶠ n in atTop, lo ≤ ratioValue m ε n r ∧
        ratioValue m ε n r ≤ hi := by
      filter_upwards [hev] with n hn
      let e : Set.Ioo (0 : ℝ) 1 := ⟨(ε n : ℝ), (ε n).property, hn⟩
      simpa only [ratioValue, lo, hi] using (hbound R e)
    obtain ⟨n, hn⟩ := hbounds.exists
    exact ⟨lo, hi, hpos, (hn.1.trans hn.2), hbounds⟩

 

theorem exists_scale_subseq_of_section4
    (hS4 : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        ∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)) := by
  obtain ⟨φ, hφ, cRat, hcRat⟩ :=
    exists_positive_ratio_subseq_of_section4 hS4 ξ Q hQ m hm ε hε
  let emb : Set.Ioi (0 : ℚ) → Set.Ioi (0 : ℝ) :=
    fun r => ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr r.property)⟩
  have hinj : Function.Injective emb := by
    intro r s h
    apply Subtype.ext
    exact Rat.cast_injective (congrArg Subtype.val h)
  let c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ) :=
    Function.extend emb cRat (fun _ => ⟨1, Set.mem_Ioi.mpr one_pos⟩)
  refine ⟨φ, hφ, c, ?_⟩
  intro r hr
  have hc : c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ =
      cRat ⟨r, hr⟩ := by
    exact hinj.extend_apply cRat (fun _ => ⟨1, Set.mem_Ioi.mpr one_pos⟩) ⟨r, hr⟩
  rw [hc]
  exact hcRat ⟨r, hr⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
