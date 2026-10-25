import SupercriticalLQGUniqueness.B2.LscTop.Dilate

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def translateMetric (z : ℂ) (D : LSCMetric) : LSCMetric :=
  ⟨fun p => D (p.1 + z, p.2 + z),
    ⟨fun x => D.isExtMetric.1 _,
      fun x y h => add_right_cancel (D.isExtMetric.2.1 _ _ h),
      fun x y => D.isExtMetric.2.2.1 _ _,
      fun x y w => D.isExtMetric.2.2.2 _ _ _⟩,
    D.lowerSemicontinuous.comp
      (show Continuous fun p : ℂ × ℂ => (p.1 + z, p.2 + z) by fun_prop)⟩

@[simp] theorem translateMetric_apply (z : ℂ) (D : LSCMetric) (p : ℂ × ℂ) :
    translateMetric z D p = D (p.1 + z, p.2 + z) := rfl

theorem tendsto_translateMetric {G : ℕ → LSCMetric} {D : LSCMetric}
    (z : ℂ) (hG : Tendsto G atTop (𝓝 D)) :
    Tendsto (fun n => translateMetric z (G n)) atTop
      (𝓝 (translateMetric z D)) := by
  rw [LSCMetric.tendsto_iff] at hG ⊢
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · exact hG.1 (fun n => ((p n).1 + z, (p n).2 + z))
      (q.1 + z, q.2 + z)
      (((continuous_fst.tendsto q).comp hp |>.add tendsto_const_nhds).prodMk_nhds
        ((continuous_snd.tendsto q).comp hp |>.add tendsto_const_nhds))
  · obtain ⟨p, hp, hGp⟩ := hG.2 (q.1 + z, q.2 + z)
    refine ⟨fun n => ((p n).1 - z, (p n).2 - z), ?_, ?_⟩
    · have h1 := ((continuous_fst.tendsto _).comp hp).sub
        (show Tendsto (fun _ : ℕ => z) atTop (𝓝 z) from tendsto_const_nhds)
      have h2 := ((continuous_snd.tendsto _).comp hp).sub
        (show Tendsto (fun _ : ℕ => z) atTop (𝓝 z) from tendsto_const_nhds)
      simpa only [Function.comp_apply, add_sub_cancel_right, Prod.mk.eta]
        using h1.prodMk_nhds h2
    · simpa only [translateMetric_apply, sub_add_cancel] using hGp

theorem continuous_translateMetric (z : ℂ) :
    Continuous (translateMetric z) := by
  rw [continuous_iff_seqContinuous]
  intro D G hG
  exact tendsto_translateMetric z hG

end SupercriticalLQGUniqueness.B2.PfeAxioms
