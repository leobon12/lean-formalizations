import SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.FiniteSplice
import SLUMetricAPI2
import LQGMetric.Metric.Geodesic




 





set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

 

theorem first_open_entry_data (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (_ha : P a ∉ V) (hb : P b ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    let e : ℝ := sInf E
    a ≤ e ∧ e ≤ b ∧
      (∀ u ∈ Icc a b, u < e → P u ∉ V) ∧
      (∀ δ : ℝ, 0 < δ →
        ∃ t ∈ Icc a b, P t ∈ V ∧ e ≤ t ∧ t < e + δ) := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  let e : ℝ := sInf E
  have hEne : E.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hEbelow : BddBelow E := ⟨a, by
    intro t ht
    exact ht.1.1⟩
  have haE : a ≤ e := le_csInf hEne (by
    intro t ht
    exact ht.1.1)
  have heB : e ≤ b := csInf_le hEbelow ⟨⟨hab, le_rfl⟩, hb⟩
  refine ⟨haE, heB, ?_, ?_⟩
  · intro u hu hue huv
    have heu : e ≤ u := csInf_le hEbelow ⟨hu, huv⟩
    exact (not_lt_of_ge heu) hue
  · intro δ hδ
    obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt hEne (lt_add_of_pos_right e hδ)
    exact ⟨t, ht.1, ht.2, csInf_le hEbelow ht, hlt⟩

 

theorem first_open_entry_mem_closure (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (ha : P a ∉ V) (hb : P b ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    P (sInf E) ∈ closure V := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  let e : ℝ := sInf E
  have hEne : E.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hEbelow : BddBelow E := ⟨a, by
    intro t ht
    exact ht.1.1⟩
  have hdata := first_open_entry_data P V hab ha hb
  dsimp only at hdata
  have hEe : e ∈ closure E := csInf_mem_closure hEne hEbelow
  have hcont : ContinuousWithinAt P E e :=
    (hP e ⟨hdata.1, hdata.2.1⟩).mono (by
      intro t ht
      exact ht.1)
  exact hcont.mem_closure hEe (by
    intro t ht
    exact ht.2)

 


theorem weyl_subpath_le (D D₀ : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D₀ p = weylScale ξ f D p)
    (P : ℝ → ℂ) {T a b c : ℝ}
    (hG : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hf : ∀ t ∈ Icc a b, ξ * f (P t) ≤ c) :
    D₀ (P a, P b) ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (b - a) := by
  let L : ℝ := b - a
  let Q : ℝ → ℂ := fun u => P (a + u)
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hTime : ∀ u ∈ Icc 0 L, a + u ∈ Icc 0 T := by
    intro u hu'
    constructor <;> dsimp only [L] at hu'
    · linarith [hu'.1]
    · linarith [hu'.2]
  have hOrdered : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, u ≤ v →
      edist ((D.pt ∘ Q) u) ((D.pt ∘ Q) v) = edist u v := by
    intro u hu' v hv' huv
    have h := hG.edist_eq_of_hasUnitSpeedOn hu
      (hTime u hu') (hTime v hv') (by linarith)
    change edist (D.pt (P (a + u))) (D.pt (P (a + v))) = _ at h
    change edist (D.pt (Q u)) (D.pt (Q v)) = _
    rw [h]
    have hsub : (a + v) - (a + u) = v - u := by ring
    rw [hsub, edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv)]
    congr 1
    ring
  have hQdist : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
      edist ((D.pt ∘ Q) u) ((D.pt ∘ Q) v) = edist u v := by
    intro u hu' v hv'
    rcases le_total u v with huv | hvu
    · exact hOrdered u hu' v hv' huv
    · rw [edist_comm, edist_comm u v]
      exact hOrdered v hv' u hu' hvu
  obtain ⟨hQgeo, hQspeed⟩ := isGeodesicCurve_of_edist_eq hL hQdist
  have hQcurve : D.IsCurve Q 0 L := ⟨hL, hQgeo.2.1⟩
  have hQ0 : Q 0 = P a := by simp only [Q, add_zero]
  have hQL : Q L = P b := by dsimp [Q, L]; congr 1; ring
  have hcost : weylScale ξ f D (P a, P b) ≤
      ∫⁻ u in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (Q u))) :=
    iInf_le_of_le Q <| iInf_le_of_le L <| iInf_le_of_le hQcurve <|
      iInf_le_of_le hQspeed <| iInf_le_of_le hQ0 <|
      iInf_le_of_le hQL le_rfl
  have hbound : (∫⁻ u in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (Q u)))) ≤
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal L := by
    calc
      (∫⁻ u in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (Q u))))
          ≤ ∫⁻ _u in Icc 0 L, ENNReal.ofReal (Real.exp c) :=
            setLIntegral_mono' measurableSet_Icc (fun u hu' =>
              ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
                (hf (a + u) (by
                  have huT := hTime u hu'
                  exact ⟨by linarith [hu'.1], by dsimp [L] at hu'; linarith [hu'.2]⟩))))
      _ = ENNReal.ofReal (Real.exp c) * ENNReal.ofReal L := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  rw [hWeyl]
  exact hcost.trans hbound

 
def setDistLSC (D : LSCMetric) (A B : Set ℂ) : ℝ≥0∞ :=
  ⨅ x ∈ A, ⨅ y ∈ B, D (x, y)

 


theorem first_open_entry_charge
    (D D₀ : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D₀ p = weylScale ξ f D p)
    (P : ℝ → ℂ) {T a b : ℝ} (z : ℂ) (r charge C : ℝ)
    (hG : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hPcont : ContinuousOn P (Icc a b))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (haSphere : P a ∈ sphere z (3 * r))
    (V : Set ℂ) (_hVopen : IsOpen V)
    (hfzero : ∀ x ∉ V, f x = 0)
    (hfglobal : ∀ x, ξ * f x ≤ C)
    (hpa : P a ∉ V) (hpb : P b ∈ V)
    (hcharge : ENNReal.ofReal charge ≤
      setDistLSC D₀ (sphere z (3 * r)) V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    let e : ℝ := sInf E
    P e ∈ closure V ∧ charge ≤ e - a := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  let e : ℝ := sInf E
  have hdata := first_open_entry_data P V hab hpa hpb
  dsimp only at hdata
  have hclose : P e ∈ closure V :=
    first_open_entry_mem_closure P V hab hPcont hpa hpb
  refine ⟨hclose, ?_⟩
  have heNonneg : 0 ≤ e - a := sub_nonneg.mpr hdata.1
  have hset : setDistLSC D₀ (sphere z (3 * r)) V ≤
      ENNReal.ofReal (e - a) := by
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
    have heδ_u : e - δ ≤ u := le_max_right _ _
    have hu_e : u ≤ e := max_le hdata.1 (by linarith)
    have hu_t : u ≤ t := hu_e.trans he_t
    have huT : u ≤ T := hu_e.trans (hdata.2.1.trans hb)
    have hzero : ∀ v ∈ Icc a u, ξ * f (P v) ≤ 0 := by
      intro v hv
      have hvE : P v ∉ V := by
        by_cases hvlt : v < e
        · exact hdata.2.2.1 v ⟨hv.1, hv.2.trans (hu_e.trans hdata.2.1)⟩ hvlt
        · have hve : v = e := le_antisymm (hv.2.trans hu_e) (le_of_not_gt hvlt)
          have hae : a = e := by
            by_contra hne
            have halt : a < e := lt_of_le_of_ne hdata.1 hne
            have hmaxlt : u < e := max_lt halt (by linarith)
            linarith [hv.2, hve]
          simpa only [hve, ← hae] using hpa
      rw [hfzero (P v) hvE]
      simp only [mul_zero, le_refl]
    have hfirst := weyl_subpath_le D D₀ ξ f hWeyl P hG hu
      ha ha_u huT hzero
    have hfirst' : D₀ (P a, P u) ≤ ENNReal.ofReal (u - a) := by
      simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using hfirst
    have hsecond := weyl_subpath_le D D₀ ξ f hWeyl P hG hu
      (ha.trans ha_u) hu_t (ht.2.trans hb) (by
        intro v _
        exact hfglobal (P v))
    have hdist : setDistLSC D₀ (sphere z (3 * r)) V ≤ D₀ (P a, P t) := by
      exact iInf_le_of_le (P a) <| iInf_le_of_le haSphere <|
        iInf_le_of_le (P t) <| iInf_le_of_le htV le_rfl
    have htri := D₀.isExtMetric.2.2.2 (P a) (P u) (P t)
    have hraw : setDistLSC D₀ (sphere z (3 * r)) V ≤
        ENNReal.ofReal (u - a) + ENNReal.ofReal K * ENNReal.ofReal (t - u) := by
      exact hdist.trans (htri.trans (add_le_add hfirst' hsecond))
    have htime1 : u - a ≤ e - a := by linarith
    have htime2 : t - u ≤ 2 * δ := by linarith
    have hKδ : K * (2 * δ) ≤ (ε : ℝ) := by
      nlinarith [hδeq, hδ]
    calc
      setDistLSC D₀ (sphere z (3 * r)) V
          ≤ ENNReal.ofReal (u - a) +
            ENNReal.ofReal K * ENNReal.ofReal (t - u) := hraw
      _ ≤ ENNReal.ofReal (e - a) +
            ENNReal.ofReal K * ENNReal.ofReal (2 * δ) := by gcongr
      _ = ENNReal.ofReal (e - a) + ENNReal.ofReal (K * (2 * δ)) := by
            rw [ENNReal.ofReal_mul hK.le]
      _ ≤ ENNReal.ofReal (e - a) + ε := by
            gcongr
            rw [ENNReal.coe_nnreal_eq]
            exact ENNReal.ofReal_le_ofReal hKδ
  exact (ENNReal.ofReal_le_ofReal_iff heNonneg).mp (hcharge.trans hset)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery
