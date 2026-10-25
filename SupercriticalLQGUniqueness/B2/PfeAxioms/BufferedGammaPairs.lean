import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSegment

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem recovery_pairs_in_open
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V : Set ℂ} (hV : IsOpen V) (x₀ y₀ : V) :
    ∃ x y : ℕ → V,
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      Tendsto (fun n => (G n) ((x n : ℂ), (y n : ℂ))) atTop
        (𝓝 (D ((x₀ : ℂ), (y₀ : ℂ)))) := by
  classical
  have hF : LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1 := by
    have hF' : Tendsto (fun n => (G n).toLSCFun) atTop (𝓝 D.toLSCFun) :=
      LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff.mp hG
    exact LSCFun.lscTendsto_of_tendsto hF'
  obtain ⟨p, hp, hval⟩ := hF.2 ((x₀ : ℂ), (y₀ : ℂ))
  have hmem : ∀ᶠ n in atTop, p n ∈ V ×ˢ V :=
    hp.eventually ((hV.prod hV).mem_nhds ⟨x₀.property, y₀.property⟩)
  let q : ℕ → V × V := fun n =>
    if hn : p n ∈ V ×ˢ V then
      (⟨(p n).1, hn.1⟩, ⟨(p n).2, hn.2⟩)
    else (x₀, y₀)
  have hqeq : (fun n => ((q n).1.1, (q n).2.1)) =ᶠ[atTop] p := by
    filter_upwards [hmem] with n hn
    simp only [q, dite_eq_left hn]
  have hq : Tendsto q atTop (𝓝 (x₀, y₀)) := by
    have h1 : Tendsto (fun n => (q n).1) atTop (𝓝 x₀) := by
      apply tendsto_subtype_rng.mpr
      exact ((continuous_fst.tendsto _).comp hp).congr'
        (hqeq.symm.mono fun n hn => congrArg Prod.fst hn)
    have h2 : Tendsto (fun n => (q n).2) atTop (𝓝 y₀) := by
      apply tendsto_subtype_rng.mpr
      exact ((continuous_snd.tendsto _).comp hp).congr'
        (hqeq.symm.mono fun n hn => congrArg Prod.snd hn)
    exact h1.prodMk_nhds h2
  refine ⟨fun n => (q n).1, fun n => (q n).2,
    (continuous_fst.tendsto _).comp hq,
    (continuous_snd.tendsto _).comp hq, ?_⟩
  apply EReal.tendsto_coe_ennreal.mp
  exact hval.congr' (hqeq.symm.mono fun n hn => congrArg (fun z => (G n z : EReal)) hn)

 


theorem short_segment_internal_recovery
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (x₀ y₀ : V) (hxK : (x₀ : ℂ) ∈ interior K)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrfin : r < ∞)
    (hdr : D ((x₀ : ℂ), (y₀ : ℂ)) < r) :
    ∃ x y : ℕ → V,
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      Tendsto (fun n => (G n).internal V (x n, y n)) atTop
        (𝓝 (D ((x₀ : ℂ), (y₀ : ℂ)))) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := recovery_pairs_in_open hG hV x₀ y₀
  have hxK' : ∀ᶠ n in atTop, (x n : ℂ) ∈ K := by
    have hxc : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (x₀ : ℂ)) :=
      (continuous_subtype_val.tendsto x₀).comp hx
    exact (hxc.eventually (isOpen_interior.mem_nhds hxK)).mono
      (fun _ hn => interior_subset hn)
  exact ⟨x, y, hx, hy,
    buffered_short_segment_recovery hG hLen hPath hV hK hfront x y
      hxK' hrR hR hrfin hxy hdr⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
