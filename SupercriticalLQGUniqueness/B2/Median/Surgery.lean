import SupercriticalLQGUniqueness.B2.Median.Height

 





set_option autoImplicit false
noncomputable section

open Set Metric Topology

namespace SupercriticalLQGUniqueness.B2.Median

 



theorem exists_strict_sub_crossing
    {f : ℝ → ℝ} {α β z w : ℝ} (hαβ : α ≤ β)
    (hf : ContinuousOn f (Icc α β)) (hzw : z < w)
    (hα : f α ≤ z) (hβ : w ≤ f β) :
    ∃ s t : ℝ, α ≤ s ∧ s < t ∧ t ≤ β ∧
      f s = z ∧ f t = w ∧
      ∀ u ∈ Ioo s t, z < f u ∧ f u < w := by
  let T : Set ℝ := Icc α β ∩ f ⁻¹' {w}
  have hTc : IsClosed T :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hαβ hf
      ⟨hα.trans hzw.le, hβ⟩
    exact ⟨v, hv, hfv⟩
  have hTb : BddBelow T := ⟨α, fun u hu => hu.1.1⟩
  let t := sInf T
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  have hαt : α ≤ t := htT.1.1
  have hbelow : ∀ u ∈ Ico α t, f u < w := by
    intro u hu
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.1
      (hf.mono (Icc_subset_Icc le_rfl (hu.2.le.trans htT.1.2)))
      ⟨hα.trans hzw.le, hcon⟩
    have hvt : t ≤ v := csInf_le hTb
      ⟨⟨hv.1, hv.2.trans (hu.2.le.trans htT.1.2)⟩, hfv⟩
    exact (not_le_of_gt (hv.2.trans_lt hu.2)) hvt
  have hft : f t = w := htT.2
  let S : Set ℝ := Icc α t ∩ f ⁻¹' {z}
  have hfαt : ContinuousOn f (Icc α t) :=
    hf.mono (Icc_subset_Icc le_rfl htT.1.2)
  have hSc : IsClosed S :=
    hfαt.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hαt hfαt
      ⟨hα, hft ▸ hzw.le⟩
    exact ⟨v, hv, hfv⟩
  have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  let s := sSup S
  have hsS : s ∈ S := hSc.csSup_mem hSne hSb
  have habove : ∀ u ∈ Ioc s t, z < f u := by
    intro u hu
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hu.2
      (hfαt.mono (Icc_subset_Icc (hsS.1.1.trans hu.1.le) le_rfl))
      ⟨hcon, hft ▸ hzw.le⟩
    have hvs : v ≤ s := le_csSup hSb
      ⟨⟨hsS.1.1.trans (hu.1.le.trans hv.1), hv.2⟩, hfv⟩
    exact (not_le_of_gt (hu.1.trans_le hv.1)) hvs
  have hst : s < t := by
    by_contra hnot
    have heq : s = t := le_antisymm hsS.1.2 (le_of_not_gt hnot)
    have : z = w := by rw [← hsS.2, ← hft, heq]
    exact hzw.ne this
  refine ⟨s, t, hsS.1.1, hst, htT.1.2, hsS.2, hft, ?_⟩
  intro u hu
  exact ⟨habove u ⟨hu.1, hu.2.le⟩,
    hbelow u ⟨hsS.1.1.trans hu.1.le, hu.2⟩⟩

 


theorem exists_normalized_square_crossing
    (d : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : d.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ unitSquare)
    (hA : P a ∈ LQGMetric.leftSide)
    (hB : P b ∈ LQGMetric.rightSide) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧
      d.IsCurve P s t ∧
      (∀ u ∈ Icc s t, P u ∈ unitSquare) ∧
      P s ∈ LQGMetric.leftSide ∧ P t ∈ LQGMetric.rightSide ∧
      (∀ u ∈ Ioo s t, 0 < (P u).re ∧ (P u).re < 1) ∧
      d.len P s t ≤ d.len P a b := by
  have hK : IsCompact unitSquare := by
    change IsCompact LQGMetric.Blueprint.closedUnitSquare
    exact LQGMetric.DFGPS.isCompact_closedUnitSquare
  have hcont : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace
      d P hP hK (fun z ⟨u, hu, huz⟩ => huz ▸ htrace u hu)
  have hRe : ContinuousOn (fun u => (P u).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn hcont
  obtain ⟨s, t, has, hst, htb, hs, ht, hbetween⟩ :=
    exists_strict_sub_crossing hP.1 hRe (by norm_num : (0 : ℝ) < 1)
      (by simpa only [hA.1] using le_refl (0 : ℝ))
      (by simpa only [hB.1] using le_refl (1 : ℝ))
  have hPs : P s ∈ unitSquare := htrace s ⟨has, hst.le.trans htb⟩
  have hPt : P t ∈ unitSquare := htrace t ⟨has.trans hst.le, htb⟩
  have hcurve : d.IsCurve P s t :=
    ⟨hst.le, hP.2.mono (Icc_subset_Icc has htb)⟩
  have hlen : d.len P s t ≤ d.len P a b := by
    exact LQGMetric.MetricGeometry.curveLength_mono (d.pt ∘ P) has htb
  exact ⟨s, t, has, hst, htb, hcurve,
    (fun u hu => htrace u ⟨has.trans hu.1, hu.2.trans htb⟩),
    ⟨hs, hPs.2.2.1, hPs.2.2.2⟩,
    ⟨ht, hPt.2.2.1, hPt.2.2.2⟩, hbetween, hlen⟩

 


theorem height_alternation_has_min_time
    {a b : ℝ} {P : ℝ → ℂ}
    (hP : ContinuousOn P (Icc a b)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        (P s).im ≤ 1 / 3 → 2 / 3 ≤ (P t).im →
        δ ≤ dist s t := by
  have him : ContinuousOn (fun s => (P s).im) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn hP
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous him
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC
    (1 / 3) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hslo hthi
  by_contra hnot
  have hst : dist s t < δ := lt_of_not_ge hnot
  have hsmall := hclose s hs t ht hst
  rw [Real.dist_eq] at hsmall
  have hle := le_abs_self ((P t).im - (P s).im)
  rw [abs_sub_comm] at hsmall
  linarith

end SupercriticalLQGUniqueness.B2.Median
