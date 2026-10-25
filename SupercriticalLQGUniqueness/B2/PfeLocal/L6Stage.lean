import SupercriticalLQGUniqueness.B2.PfeLocal.L6Rel
import LQGMetric.Field.GFFLaw

 























set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.GM.Bilip PfeWeyl
open Uniqueness.Toolkit.CompactPathInfimum

 

theorem l6_obs_enlarge_mono (D : LSCMetric) (c : L5Code) :
    Monotone fun k => l5Obs D (l6Enlarge c k) := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with h | h
  · rw [h]
  obtain ⟨h1, h2, h3⟩ := l6_enlarge_margin c h
  have hpos : (0 : ℝ) < (l6δ m : ℝ) - l6δ m' := by
    have := l6δ_anti h; rw [sub_pos]; exact_mod_cast this
  unfold l5Obs compactPathInf
  refine iInf_mono fun P => iInf_mono fun a => iInf_mono fun b => iInf_mono fun _ =>
    iInf_mono' fun htr => ⟨fun t ht => h1 (self_subset_thickening hpos _ (htr t ht)),
      iInf_mono' fun hE => ⟨h2 (self_subset_thickening hpos _ hE),
        iInf_mono' fun hF => ⟨h3 (self_subset_thickening hpos _ hF), le_rfl⟩⟩⟩

theorem l6_obs_eq_iSup (D : LSCMetric) (c : L5Code) :
    l5Obs D c = ⨆ k, l5Obs D (l6Enlarge c k) :=
  tendsto_nhds_unique (l6_obs_enlarge_tendsto D c) (tendsto_atTop_iSup (l6_obs_enlarge_mono D c))

theorem l6_rect_enlarge_anti (c : L5Code) : Antitone fun k => l5Rect (l6Enlarge c k).1 := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with h | h
  · rw [h]
  obtain ⟨h1, -, -⟩ := l6_enlarge_margin c h
  have hpos : (0 : ℝ) < (l6δ m : ℝ) - l6δ m' := by
    have := l6δ_anti h; rw [sub_pos]; exact_mod_cast this
  exact (self_subset_thickening hpos _).trans h1

 
theorem l6_eventually_rect_subset {U : Set ℂ} (hU : IsOpen U) {c : L5Code}
    (hc : l5Rect c.1 ⊆ U) : ∃ k₀, ∀ k, k₀ ≤ k → l5Rect (l6Enlarge c k).1 ⊆ U := by
  obtain ⟨k₀, hk₀⟩ := exists_subset_nhds_of_isCompact' (V := fun k => l5Rect (l6Enlarge c k).1)
    (l6_rect_enlarge_anti c).directed_ge (fun k => l5Rect_isCompact _)
    (fun k => (l5Rect_isCompact _).isClosed)
    (by rw [l6_iInter_rect]; exact hU.mem_nhdsSet.2 hc)
  exact ⟨k₀, fun k hk => (l6_rect_enlarge_anti c hk).trans hk₀⟩

 

 
def l6GoodL {R : ℝ} (l : L6Lam R) : Prop :=
  ∀ c : L5Code, (Monotone (fun k => l.2.1 (l6Enlarge c k)) ∧ l.2.1 c = ⨆ k, l.2.1 (l6Enlarge c k)) ∧
    (Monotone (fun k => l.2.2.1 (l6Enlarge c k)) ∧ l.2.2.1 c = ⨆ k, l.2.2.1 (l6Enlarge c k))

theorem l6GoodL_Λ (S : L6Geo) (ξ : ℝ) (g₀ : L6S → DistC) {Ω' : Type} (h' : Ω' → DistC)
    (L : Ω' → LSCMetric) (ω : Ω') : l6GoodL (l6Λ S ξ g₀ h' L ω) := by
  intro c
  have hm := l6_obs_enlarge_mono (L ω) c
  refine ⟨⟨hm, l6_obs_eq_iSup (L ω) c⟩, ⟨fun a b hab => ?_, ?_⟩⟩
  · exact l6_mul_le_mul_left (hm hab)
  · change ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) * l5Obs (L ω) c =
      ⨆ k, ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) * l5Obs (L ω) (l6Enlarge c k)
    rw [← ENNReal.mul_iSup, ← l6_obs_eq_iSup]

theorem l6_measurableSet_imp {α : Type*} [MeasurableSpace α] {A B : α → Prop}
    (hA : MeasurableSet {p | A p}) (hB : MeasurableSet {p | B p}) :
    MeasurableSet {p | A p → B p} := by
  have : {p | A p → B p} = {p | A p}ᶜ ∪ {p | B p} := by
    ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [this]; exact hA.compl.union hB

theorem measurableSet_l6GoodL (R : ℝ) : MeasurableSet {l : L6Lam R | l6GoodL l} := by
  have hc1 : ∀ d : L5Code, Measurable fun l : L6Lam R => l.2.1 d := fun d =>
    (measurable_pi_apply d).comp (measurable_fst.comp measurable_snd)
  have hc2 : ∀ d : L5Code, Measurable fun l : L6Lam R => l.2.2.1 d := fun d =>
    (measurable_pi_apply d).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hmono : ∀ (f : L5Code → L6Lam R → ℝ≥0∞), (∀ d, Measurable (f d)) → ∀ c : L5Code,
      MeasurableSet {l : L6Lam R | Monotone fun k => f (l6Enlarge c k) l} := by
    intro f hf c
    simp only [Monotone, Set.ofPred_forall]
    exact MeasurableSet.iInter fun a : ℕ => MeasurableSet.iInter fun b : ℕ =>
      MeasurableSet.iInter fun _ => measurableSet_le (hf _) (hf _)
  have hsup : ∀ (f : L5Code → L6Lam R → ℝ≥0∞), (∀ d, Measurable (f d)) → ∀ c : L5Code,
      MeasurableSet {l : L6Lam R | f c l = ⨆ k, f (l6Enlarge c k) l} := fun f hf c =>
    measurableSet_eq_fun (hf c) (Measurable.iSup fun k : ℕ => hf (l6Enlarge c k))
  unfold l6GoodL
  simp only [Set.ofPred_forall, Set.ofPred_and]
  exact MeasurableSet.iInter fun c : L5Code =>
    ((hmono _ hc1 c).inter (hsup _ hc1 c)).inter ((hmono _ hc2 c).inter (hsup _ hc2 c))

 

 
theorem l6_fibA (S : L6Geo) {p p' : L6Lam S.R × L6Y} (hp : l6GoodA S p) (hpL : l6GoodL p.1)
    (hp' : l6GoodA S p') (hp'L : l6GoodL p'.1) (ha : p.2.2.1 = p'.2.2.1) {d : L5Code}
    (hd : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)) : p.1.2.2.1 d ≤ p'.1.2.2.1 d := by
  obtain ⟨k₀, hk₀⟩ := l6_eventually_rect_subset S.V₁.isOpen hd
  have hmono := (hpL d).2.1
  have hk : ∀ k, k₀ ≤ k → p.1.2.2.1 (l6Enlarge d k) ≤ p'.1.2.2.1 d := by
    intro k hk
    calc p.1.2.2.1 (l6Enlarge d k) ≤ p.2.2.1 (l6Enlarge d k) := hp.1 _ (hk₀ k hk)
      _ = p'.2.2.1 (l6Enlarge d k) := by rw [ha]
      _ ≤ p'.1.2.2.1 (l6Enlarge d (k + 1)) := hp'.2 d k (hk₀ k hk)
      _ ≤ p'.1.2.2.1 d := by
        rw [(hp'L d).2.2]; exact le_iSup (fun k => p'.1.2.2.1 (l6Enlarge d k)) (k + 1)
  rw [(hpL d).2.2]
  refine iSup_le fun k => ?_
  rcases le_total k₀ k with h | h
  · exact hk k h
  · exact (hmono h).trans (hk k₀ le_rfl)

 
theorem l6_fibB (S : L6Geo) {ξ : ℝ} {p p' : L6Lam S.R × L6Y}
    (hp : l6GoodB S ξ p) (hpL : l6GoodL p.1) (hp' : l6GoodB S ξ p') (hp'L : l6GoodL p'.1)
    (hb : p.2.2.2 = p'.2.2.2) (hu : p.1.2.2.2 = p'.1.2.2.2) {d : L5Code}
    (hd : l5Rect d.1 ⊆ (S.U₁ : Set ℂ)) : p.1.2.1 d ≤ p'.1.2.1 d := by
  obtain ⟨k₀, hk₀⟩ := l6_eventually_rect_subset S.U₁.isOpen hd
  have hmono := (hpL d).1.1
  have hk : ∀ k, k₀ ≤ k → p.1.2.1 (l6Enlarge d k) ≤ p'.1.2.1 d := by
    intro k hk
    
    have hq : ∀ i : ℕ, ∃ j, ‖l6Res S.R (l6W S.R j) - p.1.2.2.2‖ < ((1 / ((i : ℚ) + 1) : ℚ) : ℝ) :=
      fun i => l6_exists_weight S.R _ (by
        have : (0 : ℚ) < 1 / ((i : ℚ) + 1) := by positivity
        exact_mod_cast this)
    choose j hj using hq
    have hle : ∀ i : ℕ, p.1.2.1 (l6Enlarge d k) ≤
        ENNReal.ofReal (Real.exp (2 * ξ * ((1 / ((i : ℚ) + 1) : ℚ) : ℝ))) * p'.1.2.1 d := by
      intro i
      set q : ℚ := 1 / ((i : ℚ) + 1)
      have h1 := hp.1 (l6Enlarge d k) (j i) q (hk₀ k hk) (hj i)
      have h2 := hp'.2 d k (j i) q (hk₀ k hk) (by rw [← hu]; exact hj i)
      have h3 : p'.1.2.1 (l6Enlarge d (k + 1)) ≤ p'.1.2.1 d := by
        rw [(hp'L d).1.2]; exact le_iSup (fun k => p'.1.2.1 (l6Enlarge d k)) (k + 1)
      have h4 : ENNReal.ofReal (Real.exp (-(ξ * q))) * p.1.2.1 (l6Enlarge d k) ≤
          ENNReal.ofReal (Real.exp (ξ * q)) * p'.1.2.1 d := by
        calc _ ≤ p.2.2.2 (l6Enlarge d k, j i) := h1
          _ = p'.2.2.2 (l6Enlarge d k, j i) := by rw [hb]
          _ ≤ _ := h2.trans (l6_mul_le_mul_left h3)
      calc p.1.2.1 (l6Enlarge d k)
          = ENNReal.ofReal (Real.exp (ξ * q)) * (ENNReal.ofReal (Real.exp (-(ξ * q))) *
              p.1.2.1 (l6Enlarge d k)) := by
            rw [← mul_assoc, l6_ofReal_exp_mul, add_neg_cancel, Real.exp_zero,
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (ξ * q)) * (ENNReal.ofReal (Real.exp (ξ * q)) *
              p'.1.2.1 d) := l6_mul_le_mul_left h4
        _ = _ := by rw [← mul_assoc, l6_ofReal_exp_mul]; congr 3; ring
    
    set t : ℕ → ℝ := fun i => (((1 / ((i : ℚ) + 1) : ℚ) : ℝ)) with ht
    have h0 : Tendsto t atTop (𝓝 0) := by
      refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun i => ?_
      simp only [ht]; push_cast; ring
    have hcont : Continuous fun x : ℝ => ENNReal.ofReal (Real.exp (2 * ξ * x)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h1 : Tendsto (fun i => ENNReal.ofReal (Real.exp (2 * ξ * t i))) atTop (𝓝 1) :=
      (hcont.tendsto' 0 1 (by simp)).comp h0
    have hlim : Tendsto (fun i => ENNReal.ofReal (Real.exp (2 * ξ * t i)) * p'.1.2.1 d) atTop
        (𝓝 (p'.1.2.1 d)) := by
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    exact ge_of_tendsto' hlim hle
  rw [(hpL d).1.2]
  refine iSup_le fun k => ?_
  rcases le_total k₀ k with h | h
  · exact hk k h
  · exact (hmono h).trans (hk k₀ le_rfl)

 

theorem l6_comap_le_aeClosure_of_ae_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → β} (mβ : MeasurableSpace β) (hfg : f =ᵐ[μ] g) :
    MeasurableSpace.comap f mβ ≤ aeClosure μ (MeasurableSpace.comap g mβ) := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨g ⁻¹' t, ⟨t, ht, rfl⟩, ?_⟩
  filter_upwards [hfg] with x hx
  simp only [mem_preimage, hx]

theorem l6_comap_le_aeClosure_comap {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [mβ : MeasurableSpace β] {ι : α → β} (hι : Measurable ι)
    (m₂ : {m : MeasurableSpace β // m ≤ mβ}) (h : mβ ≤ aeClosure (μ.map ι) m₂.1) :
    MeasurableSpace.comap ι mβ ≤ aeClosure μ (MeasurableSpace.comap ι m₂.1) := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨t', ht', htt'⟩ := h t ht
  exact ⟨ι ⁻¹' t', ⟨t', ht', rfl⟩, ae_of_ae_map hι.aemeasurable htt'⟩

 
theorem l6_raw_recovery {μ : Measure DistC} [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWPGFF id μ) (S : L6Geo) :
    (MeasurableSpace.pi : MeasurableSpace L6S) ≤ aeClosure (μ.map (pairJ ⊤))
      (MeasurableSpace.comap (normField (pairJInv ⊤) S.z S.r) inferInstance) := by
  set N : L6S → DistC := normField (pairJInv ⊤) S.z S.r
  have hNm : Measurable N := isGFFPlusBddCont_normField_pairJInv_measurable S
  set raw : DistC → DistC := fun f => addConst f (-circleAvg f 1 0) with hraw
  have hrawm : Measurable raw := measurable_distOn_iff.2 fun ψ => by
    have : (fun f : DistC => raw f ψ) = fun f => f ψ + (∫ x, ψ x) * (-circleAvg f 1 0) := by
      funext f; exact GFFInv.addConst_apply _ _ _
    rw [this]
    exact (measurable_distOn_apply ψ).add ((measurable_circleAvg_left 1 0).neg.const_mul _)
  set F : L6S → L6S := fun x => pairJ ⊤ (raw (N x))
  have hFm : Measurable F := (measurable_pairJ ⊤).comp (hrawm.comp hNm)
  have hae : ∀ᵐ x ∂(μ.map (pairJ ⊤)), id x = F x := by
    refine (ae_map_iff (measurable_pairJ ⊤).aemeasurable
      (measurableSet_eq_fun measurable_id hFm)).2 ?_
    filter_upwards [hμ.2, CircleAvg.ae_circleAvg_addConst hμ.1 0 one_pos] with g hg hadd
    have hNX : N (pairJ ⊤ g) = S.ren g := normField_pairJInv_pairJ (h := (id : DistC → DistC))
      S.z S.r g
    have h1 : circleAvg (S.ren g) 1 0 = -S.cA g := by
      change circleAvg (addConst (id g) (-circleAvg (id g) S.r S.z)) 1 0 = _
      rw [hadd, show circleAvg (id g) 1 0 = 0 from hg, zero_add]; rfl
    have h2 : raw (S.ren g) = g := by
      simp only [hraw, h1, neg_neg]
      change addConst (addConst g (-S.cA g)) (S.cA g) = g
      rw [GFFLaw.addConst_addConst, neg_add_cancel, GFFLaw.addConst_zero']
    simp only [id, F, hNX, h2]
  have hle : MeasurableSpace.comap F (MeasurableSpace.pi : MeasurableSpace L6S) ≤
      MeasurableSpace.comap N inferInstance := by
    rw [show F = (fun f => pairJ ⊤ (raw f)) ∘ N from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((measurable_pairJ ⊤).comp hrawm).comap_le
  have h := l6_comap_le_aeClosure_of_ae_eq (MeasurableSpace.pi : MeasurableSpace L6S) hae
  rw [MeasurableSpace.comap_id] at h
  exact h.trans (aeClosure_mono hle)

theorem l6_comap_G_le (S : L6Geo) : (l6G S).comap (pairJ ⊤) ≤ l6Germ S :=
  (MeasurableSpace.comap_mono inf_le_left).trans MeasurableSpace.comap_map_le

end SupercriticalLQGUniqueness.B2.PfeLocal
