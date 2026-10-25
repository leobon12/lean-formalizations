import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.UpperSourceV2




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
theorem last_open_visit_data (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (ha : P a ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    let o : ℝ := sSup E
    a ≤ o ∧ o ≤ b ∧
      (∀ u ∈ Icc a b, o < u → P u ∉ V) ∧
      (∀ δ : ℝ, 0 < δ → ∃ t ∈ Icc a b, P t ∈ V ∧ t ≤ o ∧ o - δ < t) := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  have hEne : E.Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
  have hEabove : BddAbove E := ⟨b, fun t ht => ht.1.2⟩
  have haO : a ≤ sSup E := le_csSup hEabove ⟨⟨le_rfl, hab⟩, ha⟩
  have hOb : sSup E ≤ b := csSup_le hEne (fun t ht => ht.1.2)
  refine ⟨haO, hOb, ?_, ?_⟩
  · intro u hu hou huv
    have := le_csSup hEabove ⟨hu, huv⟩
    exact (not_le_of_gt hou) this
  · intro δ hδ
    obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hEne (sub_lt_self (sSup E) hδ)
    exact ⟨t, ht.1, ht.2, le_csSup hEabove ht, hlt⟩

 
theorem last_open_visit_mem_closure (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (ha : P a ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    P (sSup E) ∈ closure V := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  have hEne : E.Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
  have hEabove : BddAbove E := ⟨b, fun t ht => ht.1.2⟩
  have hdata := last_open_visit_data P V hab ha
  dsimp only at hdata
  have hEo : sSup E ∈ closure E := csSup_mem_closure hEne hEabove
  have hcont : ContinuousWithinAt P E (sSup E) :=
    (hP (sSup E) ⟨hdata.1, hdata.2.1⟩).mono (fun t ht => ht.1)
  exact hcont.mem_closure hEo (fun t ht => ht.2)

 

theorem first_open_entry_charge_local
    (D D₀ : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D₀ p = weylScale ξ f D p)
    (P : ℝ → ℂ) {T a b : ℝ} (S V : Set ℂ) (charge C : ℝ)
    (hG : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (haS : P a ∈ S)
    (hf0 : ∀ v ∈ Icc a b, P v ∉ V → f (P v) = 0)
    (hfglobal : ∀ x, ξ * f x ≤ C)
    (hpa : P a ∉ V) (hpb : P b ∈ V)
    (hcharge : ENNReal.ofReal charge ≤ OptimalConstants.Ratios.setDist D₀ S V) :
    charge ≤ sInf {t ∈ Icc a b | P t ∈ V} - a := by
  set e := sInf {t ∈ Icc a b | P t ∈ V} with he
  have hdata := EndSaving.PathSurgery.first_open_entry_data P V hab hpa hpb
  dsimp only at hdata
  have heNonneg : 0 ≤ e - a := sub_nonneg.mpr hdata.1
  have hset : OptimalConstants.Ratios.setDist D₀ S V ≤ ENNReal.ofReal (e - a) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    let K : ℝ := Real.exp C
    have hK : 0 < K := Real.exp_pos C
    let δ : ℝ := (ε : ℝ) / (2 * K + 1)
    have hden : 0 < 2 * K + 1 := by positivity
    have hδ : 0 < δ := div_pos (by exact_mod_cast hε) hden
    have hδeq : (2 * K + 1) * δ = (ε : ℝ) := by
      dsimp [δ]
      exact mul_div_cancel₀ _ hden.ne'
    obtain ⟨t, ht, htV, he_t, htnear⟩ := hdata.2.2.2 δ hδ
    let u : ℝ := max a (e - δ)
    have ha_u : a ≤ u := le_max_left _ _
    have hu_e : u ≤ e := max_le hdata.1 (by linarith)
    have hu_t : u ≤ t := hu_e.trans he_t
    have huT : u ≤ T := hu_e.trans (hdata.2.1.trans hb)
    have hzero : ∀ v ∈ Icc a u, ξ * f (P v) ≤ 0 := by
      intro v hv
      have hvI : v ∈ Icc a b := ⟨hv.1, hv.2.trans (hu_e.trans hdata.2.1)⟩
      have hvE : P v ∉ V := by
        by_cases hvlt : v < e
        · exact hdata.2.2.1 v hvI hvlt
        · have hve : v = e := le_antisymm (hv.2.trans hu_e) (le_of_not_gt hvlt)
          have hae : a = e := by
            by_contra hne
            have halt : a < e := lt_of_le_of_ne hdata.1 hne
            have hmaxlt : u < e := max_lt halt (by linarith)
            linarith [hv.2, hve]
          simpa only [hve, ← hae] using hpa
      rw [hf0 v hvI hvE]
      simp only [mul_zero, le_refl]
    have hfirst := EndSaving.PathSurgery.weyl_subpath_le D D₀ ξ f hWeyl P hG hu ha ha_u huT hzero
    have hfirst' : D₀ (P a, P u) ≤ ENNReal.ofReal (u - a) := by
      simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using hfirst
    have hsecond := EndSaving.PathSurgery.weyl_subpath_le D D₀ ξ f hWeyl P hG hu
      (ha.trans ha_u) hu_t (ht.2.trans hb) (by
        intro v _
        exact hfglobal (P v))
    have hdist : OptimalConstants.Ratios.setDist D₀ S V ≤ D₀ (P a, P t) :=
      iInf₂_le_of_le (P a) haS (iInf₂_le (P t) htV)
    have htri := D₀.isExtMetric.2.2.2 (P a) (P u) (P t)
    have hraw : OptimalConstants.Ratios.setDist D₀ S V ≤
        ENNReal.ofReal (u - a) + ENNReal.ofReal K * ENNReal.ofReal (t - u) :=
      hdist.trans (htri.trans (add_le_add hfirst' hsecond))
    have htime1 : u - a ≤ e - a := by linarith
    have htime2 : t - u ≤ 2 * δ := by
      have : e - δ ≤ u := le_max_right _ _
      linarith
    have hKδ : K * (2 * δ) ≤ (ε : ℝ) := by nlinarith [hδeq, hδ]
    calc OptimalConstants.Ratios.setDist D₀ S V
        ≤ ENNReal.ofReal (u - a) + ENNReal.ofReal K * ENNReal.ofReal (t - u) := hraw
      _ ≤ ENNReal.ofReal (e - a) + ENNReal.ofReal K * ENNReal.ofReal (2 * δ) := by
          gcongr
      _ = ENNReal.ofReal (e - a) + ENNReal.ofReal (K * (2 * δ)) := by
          rw [ENNReal.ofReal_mul hK.le]
      _ ≤ ENNReal.ofReal (e - a) + ε := by
          gcongr
          rw [ENNReal.coe_nnreal_eq]
          exact ENNReal.ofReal_le_ofReal hKδ
  exact (ENNReal.ofReal_le_ofReal_iff heNonneg).mp (hcharge.trans hset)

 
theorem last_open_exit_charge_local
    (D D₀ : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D₀ p = weylScale ξ f D p)
    (P : ℝ → ℂ) {T a b : ℝ} (S V : Set ℂ) (charge C : ℝ)
    (hG : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hbS : P b ∈ S)
    (hf0 : ∀ v ∈ Icc a b, P v ∉ V → f (P v) = 0)
    (hfglobal : ∀ x, ξ * f x ≤ C)
    (hpa : P a ∈ V) (hpb : P b ∉ V)
    (hcharge : ENNReal.ofReal charge ≤ OptimalConstants.Ratios.setDist D₀ S V) :
    charge ≤ b - sSup {t ∈ Icc a b | P t ∈ V} := by
  set o := sSup {t ∈ Icc a b | P t ∈ V} with ho
  have hdata := last_open_visit_data P V hab hpa
  dsimp only at hdata
  have hoNonneg : 0 ≤ b - o := sub_nonneg.mpr hdata.2.1
  have hset : OptimalConstants.Ratios.setDist D₀ S V ≤ ENNReal.ofReal (b - o) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    let K : ℝ := Real.exp C
    have hK : 0 < K := Real.exp_pos C
    let δ : ℝ := (ε : ℝ) / (2 * K + 1)
    have hden : 0 < 2 * K + 1 := by positivity
    have hδ : 0 < δ := div_pos (by exact_mod_cast hε) hden
    have hδeq : (2 * K + 1) * δ = (ε : ℝ) := by
      dsimp [δ]
      exact mul_div_cancel₀ _ hden.ne'
    obtain ⟨t, ht, htV, ht_o, htnear⟩ := hdata.2.2.2 δ hδ
    let u : ℝ := min b (o + δ)
    have hu_b : u ≤ b := min_le_left _ _
    have ho_u : o ≤ u := le_min hdata.2.1 (by linarith)
    have ht_u : t ≤ u := ht_o.trans ho_u
    have hzero : ∀ v ∈ Icc u b, ξ * f (P v) ≤ 0 := by
      intro v hv
      have hvI : v ∈ Icc a b := ⟨(hdata.1.trans ho_u).trans hv.1, hv.2⟩
      have hvE : P v ∉ V := by
        by_cases hvlt : o < v
        · exact hdata.2.2.1 v hvI hvlt
        · have hve : v = o := le_antisymm (le_of_not_gt hvlt) (ho_u.trans hv.1)
          have hbo : b = o := by
            by_contra hne
            have hlt : o < b := lt_of_le_of_ne hdata.2.1 (Ne.symm hne)
            have hminlt : o < u := lt_min hlt (by linarith)
            linarith [hv.1, hve]
          simpa only [hve, ← hbo] using hpb
      rw [hf0 v hvI hvE]
      simp only [mul_zero, le_refl]
    have huT0 : 0 ≤ u := ha.trans (hdata.1.trans ho_u)
    have hlast := EndSaving.PathSurgery.weyl_subpath_le D D₀ ξ f hWeyl P hG hu huT0 hu_b hb hzero
    have hlast' : D₀ (P u, P b) ≤ ENNReal.ofReal (b - u) := by
      simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using hlast
    have hmid := EndSaving.PathSurgery.weyl_subpath_le D D₀ ξ f hWeyl P hG hu
      (ha.trans ht.1) ht_u (hu_b.trans hb) (by
        intro v _
        exact hfglobal (P v))
    have hdist : OptimalConstants.Ratios.setDist D₀ S V ≤ D₀ (P b, P t) :=
      iInf₂_le_of_le (P b) hbS (iInf₂_le (P t) htV)
    have hsymm : D₀ (P b, P t) = D₀ (P t, P b) := D₀.isExtMetric.2.2.1 _ _
    have htri := D₀.isExtMetric.2.2.2 (P t) (P u) (P b)
    have hraw : OptimalConstants.Ratios.setDist D₀ S V ≤
        ENNReal.ofReal K * ENNReal.ofReal (u - t) + ENNReal.ofReal (b - u) := by
      rw [hsymm] at hdist
      exact hdist.trans (htri.trans (add_le_add hmid hlast'))
    have htime1 : b - u ≤ b - o := by linarith
    have htime2 : u - t ≤ 2 * δ := by
      have : u ≤ o + δ := min_le_right _ _
      linarith
    have hKδ : K * (2 * δ) ≤ (ε : ℝ) := by nlinarith [hδeq, hδ]
    calc OptimalConstants.Ratios.setDist D₀ S V
        ≤ ENNReal.ofReal K * ENNReal.ofReal (u - t) + ENNReal.ofReal (b - u) := hraw
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * δ) + ENNReal.ofReal (b - o) := by
          gcongr
      _ = ENNReal.ofReal (K * (2 * δ)) + ENNReal.ofReal (b - o) := by
          rw [ENNReal.ofReal_mul hK.le]
      _ ≤ ε + ENNReal.ofReal (b - o) := by
          gcongr
          rw [ENNReal.coe_nnreal_eq]
          exact ENNReal.ofReal_le_ofReal hKδ
      _ = ENNReal.ofReal (b - o) + ε := add_comm _ _
  exact (ENNReal.ofReal_le_ofReal_iff hoNonneg).mp (hcharge.trans hset)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
