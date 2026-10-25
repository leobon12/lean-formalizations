import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadiusCompact
import SupercriticalLQGUniqueness.B2.LscTop.Limits

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

variable {α : Type*} [TopologicalSpace α]

 


theorem lscTendsto_restrict_of_eventually_eq {W : Set α} (hW : IsOpen W)
    {F : ℕ → α × α → EReal} {G : ℕ → W × W → EReal}
    {f : α × α → EReal} {g : W × W → EReal}
    (hF : LSCTendsto F f)
    (hEq : ∀ᶠ n in atTop, ∀ p : W × W, G n p = F n (p.1.1, p.2.1))
    (hlim : ∀ p : W × W, g p = f (p.1.1, p.2.1)) :
    LSCTendsto G g := by
  classical
  constructor
  · intro p q hp
    have hp' : Tendsto (fun n => ((p n).1.1, (p n).2.1)) atTop
        (𝓝 ((q.1.1, q.2.1) : α × α)) :=
      ((continuous_subtype_val.comp continuous_fst).tendsto q |>.comp hp).prodMk_nhds
        ((continuous_subtype_val.comp continuous_snd).tendsto q |>.comp hp)
    have hlow := hF.1 (fun n => ((p n).1.1, (p n).2.1)) (q.1.1, q.2.1) hp'
    have heq : (fun n => G n (p n)) =ᶠ[atTop]
        (fun n => F n ((p n).1.1, (p n).2.1)) := by
      filter_upwards [hEq] with n hn
      exact hn (p n)
    rw [hlim q, Filter.liminf_congr heq]
    exact hlow
  · intro q
    obtain ⟨p, hp, hval⟩ := hF.2 (q.1.1, q.2.1)
    have hmem : ∀ᶠ n in atTop, p n ∈ W ×ˢ W := by
      apply hp.eventually
      exact (hW.prod hW).mem_nhds ⟨q.1.2, q.2.2⟩
    let p' : ℕ → W × W := fun n =>
      if hn : p n ∈ W ×ˢ W then
        (⟨(p n).1, hn.1⟩, ⟨(p n).2, hn.2⟩)
      else q
    have hp'eq : (fun n => ((p' n).1.1, (p' n).2.1)) =ᶠ[atTop] p := by
      filter_upwards [hmem] with n hn
      simp only [p', dite_eq_left hn]
    have hp' : Tendsto p' atTop (𝓝 q) := by
      have h1 : Tendsto (fun n => (p' n).1) atTop (𝓝 q.1) := by
        apply tendsto_subtype_rng.mpr
        exact ((continuous_fst.tendsto _).comp hp).congr'
          (hp'eq.symm.mono fun n hn => congrArg Prod.fst hn)
      have h2 : Tendsto (fun n => (p' n).2) atTop (𝓝 q.2) := by
        apply tendsto_subtype_rng.mpr
        exact ((continuous_snd.tendsto _).comp hp).congr'
          (hp'eq.symm.mono fun n hn => congrArg Prod.snd hn)
      exact h1.prodMk_nhds h2
    refine ⟨p', hp', ?_⟩
    have hval' : Tendsto (fun n => F n ((p' n).1.1, (p' n).2.1)) atTop
        (𝓝 (f (q.1.1, q.2.1))) := hval.congr' (hp'eq.symm.mono fun n hn => congrArg (F n) hn)
    have hvalG : (fun n => G n (p' n)) =ᶠ[atTop]
        (fun n => F n ((p' n).1.1, (p' n).2.1)) := by
      filter_upwards [hEq] with n hn
      exact hn (p' n)
    rw [hlim q]
    exact hval'.congr' hvalG.symm

 



theorem internal_lscTendsto_of_common_metric_ball
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLenG : ∀ n, (G n).IsLengthSpace) (hLenD : D.IsLengthSpace)
    {Y W : Set ℂ} (hWopen : IsOpen W) (hWY : W ⊆ Y)
    {r : ℝ≥0∞} (hr : r < ∞)
    (hballG : ∀ᶠ n in atTop, ∀ u : W,
      Metric.eball ((G n).pt u.1) r ⊆ (G n).pt '' Y)
    (hsmallG : ∀ᶠ n in atTop, ∀ p : W × W,
      (G n) (p.1.1, p.2.1) < r)
    (hballD : ∀ u : W, Metric.eball (D.pt u.1) r ⊆ D.pt '' Y)
    (hsmallD : ∀ p : W × W, D (p.1.1, p.2.1) < r) :
    LSCTendsto
      (fun n (p : W × W) =>
        ((G n).internal Y
          (⟨p.1.1, hWY p.1.2⟩, ⟨p.2.1, hWY p.2.2⟩) : EReal))
      (fun p : W × W =>
        (D.internal Y
          (⟨p.1.1, hWY p.1.2⟩, ⟨p.2.1, hWY p.2.2⟩) : EReal)) := by
  have hF : LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1 := by
    have hF' : Tendsto (fun n => (G n).toLSCFun) atTop (𝓝 D.toLSCFun) :=
      LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff.mp hG
    exact LSCFun.lscTendsto_of_tendsto hF'
  apply lscTendsto_restrict_of_eventually_eq hWopen hF
  · filter_upwards [hballG, hsmallG] with n hb hs p
    exact congrArg (fun x : ℝ≥0∞ => (x : EReal))
      (internal_eq_of_metric_ball (G n) (hLenG n) hr (hb p.1) (hs p)
        (hWY p.1.2) (hWY p.2.2))
  · intro p
    exact congrArg (fun x : ℝ≥0∞ => (x : EReal))
      (internal_eq_of_metric_ball D hLenD hr (hballD p.1) (hsmallD p)
        (hWY p.1.2) (hWY p.2.2))

 



theorem internal_liminf_of_ambient_lsc
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {Y : Set ℂ} {p : ℕ → Y × Y} {q : Y × Y}
    (hp : Tendsto p atTop (𝓝 q))
    (heq : D.internal Y q = D (q.1.1, q.2.1)) :
    (D.internal Y q : EReal) ≤
      liminf (fun n => ((G n).internal Y (p n) : EReal)) atTop := by
  have hF : LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1 := by
    have hF' : Tendsto (fun n => (G n).toLSCFun) atTop (𝓝 D.toLSCFun) :=
      LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff.mp hG
    exact LSCFun.lscTendsto_of_tendsto hF'
  have hp' : Tendsto (fun n => ((p n).1.1, (p n).2.1)) atTop
      (𝓝 ((q.1.1, q.2.1) : ℂ × ℂ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto q |>.comp hp).prodMk_nhds
      ((continuous_subtype_val.comp continuous_snd).tendsto q |>.comp hp)
  have hlow := hF.1 (fun n => ((p n).1.1, (p n).2.1)) (q.1.1, q.2.1) hp'
  have hpoint : ∀ n,
      ((G n) ((p n).1.1, (p n).2.1) : EReal) ≤
        ((G n).internal Y (p n) : EReal) := by
    intro n
    exact_mod_cast (by
      rw [(G n).internal_eq_internalEDist, ← (G n).edist_pt]
      exact edist_le_internalEDist ((G n).pt '' Y) _ _)
  have hpointEv : ∀ᶠ n in atTop,
      ((G n) ((p n).1.1, (p n).2.1) : EReal) ≤
        ((G n).internal Y (p n) : EReal) :=
    Filter.Eventually.of_forall hpoint
  have hliminf := Filter.liminf_le_liminf hpointEv
  calc
    (D.internal Y q : EReal) = (D (q.1.1, q.2.1) : EReal) :=
      congrArg (fun a : ℝ≥0∞ => (a : EReal)) heq
    _ ≤ liminf (fun n => ((G n) ((p n).1.1, (p n).2.1) : EReal)) atTop := hlow
    _ ≤ liminf (fun n => ((G n).internal Y (p n) : EReal)) atTop := hliminf

end SupercriticalLQGUniqueness.B2.PfeAxioms
