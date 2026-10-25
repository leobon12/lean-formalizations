import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Exc




 













set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 

theorem image_reflect_Icc (c u v : ℝ) : (fun t : ℝ => c - t) '' Icc u v = Icc (c - v) (c - u) := by
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro hw
    exact ⟨c - w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, by ring⟩

theorem mapsTo_reflect_Icc (c u v : ℝ) :
    MapsTo (fun t : ℝ => c - t) (Icc u v) (Icc (c - v) (c - u)) := by
  intro t ht
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem antitoneOn_reflect (c : ℝ) (s : Set ℝ) : AntitoneOn (fun t : ℝ => c - t) s := by
  intro x _ y _ hxy
  dsimp only
  linarith

 
theorem isCurve_reflect {D : LSCMetric} {P : ℝ → ℂ} {c u v : ℝ} (hP : D.IsCurve P (c - v) (c - u)) :
    D.IsCurve (fun t => P (c - t)) u v := by
  have huv : u ≤ v := by linarith [hP.1]
  refine ⟨huv, ?_⟩
  have hφ : ContinuousOn (fun t : ℝ => c - t) (Icc u v) := by fun_prop
  exact hP.2.comp hφ (mapsTo_reflect_Icc c u v)

 
theorem len_reflect (D : LSCMetric) (P : ℝ → ℂ) (c u v : ℝ) :
    D.len (fun t => P (c - t)) u v = D.len P (c - v) (c - u) := by
  change eVariationOn ((D.pt ∘ P) ∘ (fun t : ℝ => c - t)) (Icc u v) =
    eVariationOn (D.pt ∘ P) (Icc (c - v) (c - u))
  rw [eVariationOn.comp_eq_of_antitoneOn (D.pt ∘ P) (fun t : ℝ => c - t)
    (antitoneOn_reflect c _), image_reflect_Icc]

theorem continuousOn_reflect {P : ℝ → ℂ} {c u v : ℝ} (hP : ContinuousOn P (Icc (c - v) (c - u))) :
    ContinuousOn (fun t => P (c - t)) (Icc u v) := by
  have hφ : ContinuousOn (fun t : ℝ => c - t) (Icc u v) := by fun_prop
  exact hP.comp hφ (mapsTo_reflect_Icc c u v)

 

 
theorem acr_le_curve_rev (D : LSCMetric) {P : ℝ → ℂ} {s t c d : ℝ} {v : ℂ}
    (hP : D.IsCurve P s t) (hcont : ContinuousOn P (Icc s t)) (hcd : c ≤ d)
    (hs : d ≤ dist (P s) v) (ht : dist (P t) v ≤ c) :
    Objects.CorrectedEvent.acr D v c d ≤ D.len P s t := by
  have hP' : D.IsCurve P ((s + t) - t) ((s + t) - s) := by
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using hP
  have hcont' : ContinuousOn P (Icc ((s + t) - t) ((s + t) - s)) := by
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using hcont
  have hQ := isCurve_reflect hP'
  have hQc := continuousOn_reflect hcont'
  have hlen := len_reflect D P (s + t) s t
  rw [add_sub_cancel_right, add_sub_cancel_left] at hlen
  rw [← hlen]
  refine Objects.Compare.acr_le_curve_of_endpoint_order D hQ hQc hcd ?_ ?_
  · simpa only [add_sub_cancel_left] using ht
  · simpa only [add_sub_cancel_right] using hs

 


theorem sum_acr_le_len (D : LSCMetric) (P : ℝ → ℂ) (v : ℂ) (a b : ℕ → ℝ)
    (hab : ∀ j, a j ≤ b j) (hmono : ∀ i j, i < j → b i ≤ a j) (J : Finset ℕ) :
    ∀ u s : ℝ, u ≤ s → D.IsCurve P u s → ContinuousOn P (Icc u s) →
      (∀ j ∈ J, b j ≤ dist (P u) v) → (∀ j ∈ J, dist (P s) v ≤ a j) →
      ∑ j ∈ J, Objects.CorrectedEvent.acr D v (a j) (b j) ≤ D.len P u s := by
  induction J using Finset.induction_on_max with
  | empty =>
    intro u s _ _ _ _ _
    simp only [Finset.sum_empty, zero_le]
  | insert m J hlt ih =>
    intro u s hus hP hcont hstart hend
    have hmJ : m ∉ J := fun h => lt_irrefl m (hlt m h)
    
    have hrad : ContinuousOn (fun t => dist (P t) v) (Icc u s) := by
      fun_prop (disch := assumption)
    obtain ⟨β, hβ, hβv⟩ : ∃ β ∈ Icc u s, dist (P β) v = a m := by
      have := intermediate_value_Icc' hus hrad
      exact this ⟨hend m (Finset.mem_insert_self m J),
        (hab m).trans (hstart m (Finset.mem_insert_self m J))⟩
    have hPuβ : D.IsCurve P u β := ⟨hβ.1, hP.2.mono (Icc_subset_Icc le_rfl hβ.2)⟩
    have hPβs : D.IsCurve P β s := ⟨hβ.2, hP.2.mono (Icc_subset_Icc hβ.1 le_rfl)⟩
    have hm : Objects.CorrectedEvent.acr D v (a m) (b m) ≤ D.len P u β :=
      acr_le_curve_rev D hPuβ (hcont.mono (Icc_subset_Icc le_rfl hβ.2)) (hab m)
        (hstart m (Finset.mem_insert_self m J)) hβv.le
    have hJ : ∑ j ∈ J, Objects.CorrectedEvent.acr D v (a j) (b j) ≤ D.len P β s :=
      ih β s hβ.2 hPβs (hcont.mono (Icc_subset_Icc hβ.1 le_rfl))
        (fun j hj => by rw [hβv]; exact hmono j m (hlt j hj))
        (fun j hj => hend j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hmJ, ← Objects.Producer.len_add D P hβ.1 hβ.2]
    exact add_le_add hm hJ

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
