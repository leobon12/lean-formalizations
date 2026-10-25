import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Polar




 












set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
def toParams (T : Objects.CorrectedEvent.TubeData) : TubeParams where
  ρ := T.rho
  K := T.K
  α := T.alpha
  n := T.orientation
  ψu := T.psiU
  ψv := T.psiV
  sp := Objects.CorrectedEvent.sPrime T
  wp := T.lambda * T.A_endpt

section Bridge

variable (T : Objects.CorrectedEvent.TubeData)

theorem toParams_K : (toParams T).K = T.K := rfl

theorem ω_eq (k : Fin T.K) :
    (toParams T).ω (k : ℤ) = 2 * π * (k.val : ℝ) / (T.K : ℝ) := by
  simp only [TubeParams.ω, toParams, Int.cast_natCast]

theorem site_eq (k : Fin T.K) : Objects.CorrectedEvent.site T k = (toParams T).site T.r (k : ℤ) := by
  simp only [Objects.CorrectedEvent.site, TubeParams.site, polar_eq_pol, ω_eq]

theorem tangent_eq (k : Fin T.K) : Objects.CorrectedEvent.tangent T k = (toParams T).tangent (k : ℤ) := by
  simp only [Objects.CorrectedEvent.tangent, TubeParams.tangent, ex, ω_eq]

theorem twist_eq (k : Fin T.K) : Objects.CorrectedEvent.twistAngle T k = (toParams T).twist (k : ℤ) := by
  simp only [Objects.CorrectedEvent.twistAngle, TubeParams.twist, tangent_eq]
  rfl

theorem moduleMap_eq (k : Fin T.K) : Objects.CorrectedEvent.moduleMap T k = (toParams T).modMap T.r (k : ℤ) := by
  funext w
  simp only [Objects.CorrectedEvent.moduleMap, TubeParams.modMap, site_eq]
  rfl

theorem block_eq (k : Fin T.K) : Objects.CorrectedEvent.block T k = (toParams T).block T.r (k : ℤ) := by
  simp only [Objects.CorrectedEvent.block, TubeParams.block, moduleMap_eq]
  rfl

theorem innerCenter_eq (k : Fin T.K) : Objects.CorrectedEvent.innerCenter T k = (toParams T).uC T.r (k : ℤ) := by
  simp only [Objects.CorrectedEvent.innerCenter, TubeParams.uC, moduleMap_eq, Objects.CorrectedEvent.uNorm, polar_eq_pol]
  rfl

theorem outerCenter_eq (k : Fin T.K) : Objects.CorrectedEvent.outerCenter T k = (toParams T).vC T.r (k : ℤ) := by
  simp only [Objects.CorrectedEvent.outerCenter, TubeParams.vC, moduleMap_eq, Objects.CorrectedEvent.vNorm, polar_eq_pol]
  rfl

theorem s_eq (hρr : T.rho * T.r ≠ 0) : (toParams T).s T.r = T.blockRadius := by
  simp only [TubeParams.s, toParams, Objects.CorrectedEvent.sPrime]
  rw [mul_assoc]
  exact div_mul_cancel₀ _ hρr

theorem w_eq : (toParams T).w T.r = Objects.CorrectedEvent.tubeWidth T := by
  simp only [TubeParams.w, toParams, Objects.CorrectedEvent.tubeWidth]

 
theorem site_next (k : Fin T.K) :
    Objects.CorrectedEvent.site T (Objects.CorrectedEvent.nextSite T k) = (toParams T).site T.r ((k : ℤ) + 1) := by
  have hK : ((toParams T).K : ℝ) ≠ 0 := by
    simp only [toParams]; exact_mod_cast T.Kpos.ne'
  rcases Nat.lt_or_ge (k.val + 1) T.K with h | h
  · have hnext : (Objects.CorrectedEvent.nextSite T k).val = k.val + 1 := Nat.mod_eq_of_lt h
    rw [site_eq]
    congr 1
    rw [← Int.cast_natCast (n := (Objects.CorrectedEvent.nextSite T k).val)]
    simp only [hnext, Nat.cast_add, Nat.cast_one]
    rfl
  · have hK1 : k.val + 1 = T.K := le_antisymm (Nat.succ_le_of_lt k.isLt) h
    have hnext : (Objects.CorrectedEvent.nextSite T k).val = 0 := by
      simp only [Objects.CorrectedEvent.nextSite, hK1, Nat.mod_self]
    have h0 : Objects.CorrectedEvent.nextSite T k = ⟨0, T.Kpos⟩ := Fin.ext hnext
    rw [h0, site_eq]
    have hk : ((k : ℤ) + 1 : ℤ) = 0 + ((toParams T).K : ℤ) := by
      simp only [toParams, zero_add]
      have : ((k : ℕ) : ℤ) + 1 = ((k.val + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [show ((k : ℤ)) = ((k : ℕ) : ℤ) from rfl, this, hK1]
    rw [hk, TubeParams.site_add_K hK]
    rfl

theorem tangent_next (k : Fin T.K) :
    Objects.CorrectedEvent.tangent T (Objects.CorrectedEvent.nextSite T k) = (toParams T).tangent ((k : ℤ) + 1) := by
  have hK : ((toParams T).K : ℝ) ≠ 0 := by
    simp only [toParams]; exact_mod_cast T.Kpos.ne'
  rcases Nat.lt_or_ge (k.val + 1) T.K with h | h
  · have hnext : (Objects.CorrectedEvent.nextSite T k).val = k.val + 1 := Nat.mod_eq_of_lt h
    rw [tangent_eq]
    congr 1
    simp only [hnext]
    push_cast
    rfl
  · have hK1 : k.val + 1 = T.K := le_antisymm (Nat.succ_le_of_lt k.isLt) h
    have hnext : (Objects.CorrectedEvent.nextSite T k).val = 0 := by
      simp only [Objects.CorrectedEvent.nextSite, hK1, Nat.mod_self]
    have h0 : Objects.CorrectedEvent.nextSite T k = ⟨0, T.Kpos⟩ := Fin.ext hnext
    rw [h0, tangent_eq]
    have hk : ((k : ℤ) + 1 : ℤ) = 0 + ((toParams T).K : ℤ) := by
      simp only [toParams, zero_add]
      have : ((k : ℕ) : ℤ) + 1 = ((k.val + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [show ((k : ℤ)) = ((k : ℕ) : ℤ) from rfl, this, hK1]
    rw [hk, TubeParams.tangent_add_K hK]
    rfl

theorem twist_next (k : Fin T.K) :
    Objects.CorrectedEvent.twistAngle T (Objects.CorrectedEvent.nextSite T k) = (toParams T).twist ((k : ℤ) + 1) := by
  simp only [Objects.CorrectedEvent.twistAngle, TubeParams.twist, tangent_next]
  rfl

theorem moduleMap_next (k : Fin T.K) :
    Objects.CorrectedEvent.moduleMap T (Objects.CorrectedEvent.nextSite T k) = (toParams T).modMap T.r ((k : ℤ) + 1) := by
  funext w
  simp only [Objects.CorrectedEvent.moduleMap, TubeParams.modMap, site_next]
  rfl

theorem gatePlus_eq' (hn : ‖T.orientation‖ = 1) (k : Fin T.K) :
    Objects.CorrectedEvent.gatePlus T k = (toParams T).gatePlus T.r (k : ℤ) := by
  rw [TubeParams.gatePlus_eq (P := toParams T) hn, Objects.CorrectedEvent.gatePlus, site_eq, tangent_eq]
  simp only [toParams]

theorem gateMinus_next (hn : ‖T.orientation‖ = 1) (k : Fin T.K) :
    Objects.CorrectedEvent.gateMinus T (Objects.CorrectedEvent.nextSite T k) = (toParams T).gateMinus T.r ((k : ℤ) + 1) := by
  rw [TubeParams.gateMinus_eq (P := toParams T) hn, Objects.CorrectedEvent.gateMinus, site_next, tangent_next]
  simp only [toParams]

end Bridge

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
