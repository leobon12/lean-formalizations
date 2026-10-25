import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Bridge




 










set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

theorem r15 : (1.5 : ℝ) = 3 / 2 := by norm_num
theorem r25 : (2.5 : ℝ) = 5 / 2 := by norm_num
theorem r35 : (3.5 : ℝ) = 7 / 2 := by norm_num

theorem neg_image_pol_spoke (a b ψ : ℝ) :
    (fun w : ℂ => -w) '' ((fun R => pol R ψ) '' Icc a b) = (fun R => pol R (ψ + π)) '' Icc a b := by
  rw [image_image]
  congr 1
  funext R
  rw [pol_add_pi]

theorem neg_image_pol_arc (R θ₀ θ₁ : ℝ) :
    (fun w : ℂ => -w) '' ((fun θ => pol R θ) '' uIcc θ₀ θ₁) =
      (fun θ => pol R θ) '' uIcc (θ₀ + π) (θ₁ + π) := by
  rw [image_image, ← image_add_const_uIcc, image_image]
  congr 1
  funext θ
  rw [pol_add_pi]

section Pieces

variable {sp ψu ψv α Δ : ℝ}

theorem o1_eq (hsp : sp ≤ 2 / 3) :
    {w : ℂ | ∃ t ∈ Icc (1 + 3 * sp / 4) (1.5 : ℝ), w = Objects.CorrectedEvent.polar t ψv} = range (o1 sp ψv) := by
  rw [radial76_eq, o1, range_spoke, uIcc_of_le (by linarith), r15]

theorem o2_eq : Objects.CorrectedEvent.arc 1.5 ψv 0 = range (o2 ψv) := by
  rw [arc76_eq, o2, range_arc, r15]

theorem o3_eq : Objects.CorrectedEvent.segment (1.5 : ℂ) (2.5 : ℂ) = range o3 := by
  rw [seg76_eq, o3, range_spoke, uIcc_of_le (by norm_num)]
  have h := segment_real_pos (a := 3 / 2) (b := 5 / 2) (by norm_num)
  have e1 : ((3 / 2 : ℝ) : ℂ) = (1.5 : ℂ) := by push_cast; norm_num
  have e2 : ((5 / 2 : ℝ) : ℂ) = (2.5 : ℂ) := by push_cast; norm_num
  rw [e1, e2] at h
  exact h

theorem t1_eq : Objects.CorrectedEvent.arc 2.5 0 (Δ / 2) = range (t1 Δ) := by
  rw [arc76_eq, t1, range_arc, r25]

theorem t2_eq : {w : ℂ | ∃ t ∈ Icc (2.5 : ℝ) 3.5, w = Objects.CorrectedEvent.polar t (Δ / 2)} = range (t2 Δ) := by
  rw [radial76_eq, t2, range_spoke, uIcc_of_le (by norm_num), r25, r35]

theorem t3_eq : Objects.CorrectedEvent.arc 3.5 (Δ / 2) Δ = range (t3 Δ) := by
  rw [arc76_eq, t3, range_arc, r35]

theorem t4_eq : {w : ℂ | ∃ t ∈ Icc (3.5 : ℝ) 4, w = Objects.CorrectedEvent.polar t Δ} = range (t4 Δ) := by
  rw [radial76_eq, t4, range_spoke, uIcc_of_le (by norm_num), r35]

theorem nt1_eq : (fun w : ℂ => -w) '' Objects.CorrectedEvent.arc 2.5 0 (Δ / 2) = range (nt1 Δ) := by
  rw [arc76_eq, neg_image_pol_arc, nt1, range_arc, r25, zero_add, uIcc_comm]

theorem nt2_eq : (fun w : ℂ => -w) '' {w : ℂ | ∃ t ∈ Icc (2.5 : ℝ) 3.5, w = Objects.CorrectedEvent.polar t (Δ / 2)} =
    range (nt2 Δ) := by
  rw [radial76_eq, neg_image_pol_spoke, nt2, range_spoke, uIcc_of_ge (by norm_num), r25, r35]

theorem nt3_eq : (fun w : ℂ => -w) '' Objects.CorrectedEvent.arc 3.5 (Δ / 2) Δ = range (nt3 Δ) := by
  rw [arc76_eq, neg_image_pol_arc, nt3, range_arc, r35, uIcc_comm]

theorem nt4_eq : (fun w : ℂ => -w) '' {w : ℂ | ∃ t ∈ Icc (3.5 : ℝ) 4, w = Objects.CorrectedEvent.polar t Δ} =
    range (nt4 Δ) := by
  rw [radial76_eq, neg_image_pol_spoke, nt4, range_spoke, uIcc_of_ge (by norm_num), r35]

theorem i2_eq : Objects.CorrectedEvent.segment (-(2.5 : ℂ)) 0 = range i2 := by
  rw [seg76_eq, i2, range_spoke, uIcc_of_ge (by norm_num)]
  have h := segment_neg_zero (c := 5 / 2) (by norm_num)
  have e : ((5 / 2 : ℝ) : ℂ) = (2.5 : ℂ) := by push_cast; norm_num
  rw [e] at h
  exact h

theorem i1_eq (hpos : 0 ≤ α - 3 * sp / 4) :
    Objects.CorrectedEvent.segment 0 (Objects.CorrectedEvent.polar (α - 3 * sp / 4) ψu) = range (i1 α sp ψu) := by
  rw [seg76_eq, range_i1, range_spoke, uIcc_of_le hpos, polar_eq_pol]
  exact segment_zero_pol hpos

end Pieces

variable (T : Objects.CorrectedEvent.TubeData)

theorem outTwist_eq (k : Fin T.K) :
    Objects.CorrectedEvent.outTwist T k = range (t1 (Objects.CorrectedEvent.twistAngle T k)) ∪ range (t2 (Objects.CorrectedEvent.twistAngle T k)) ∪
      range (t3 (Objects.CorrectedEvent.twistAngle T k)) ∪ range (t4 (Objects.CorrectedEvent.twistAngle T k)) := by
  simp only [Objects.CorrectedEvent.outTwist]
  rw [t1_eq, t2_eq, t3_eq, t4_eq]

 
theorem outSet_eq (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3) (k : Fin T.K) :
    Objects.CorrectedEvent.outStub T ∪ Objects.CorrectedEvent.outTwist T k =
      range (outPath (Objects.CorrectedEvent.sPrime T) T.psiV (Objects.CorrectedEvent.twistAngle T k)) := by
  rw [range_outPath, outTwist_eq]
  simp only [Objects.CorrectedEvent.outStub, outRest]
  rw [o1_eq hsp, o2_eq, o3_eq]
  ext x
  simp only [mem_union]
  tauto

 
theorem inSet_eq (hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) (k : Fin T.K) :
    (fun w : ℂ => -w) '' Objects.CorrectedEvent.outTwist T k ∪ Objects.CorrectedEvent.inStub T =
      range (inPath T.alpha (Objects.CorrectedEvent.sPrime T) T.psiU (Objects.CorrectedEvent.twistAngle T k)) := by
  rw [range_inPath]
  simp only [Objects.CorrectedEvent.outTwist, Objects.CorrectedEvent.inStub, inRest, image_union]
  rw [nt1_eq, nt2_eq, nt3_eq, nt4_eq, i2_eq, i1_eq hpos]
  ext x
  simp only [mem_union]
  tauto

 
theorem connector_eq (hn : ‖T.orientation‖ = 1) (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3)
    (hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) (k : Fin T.K) :
    Objects.CorrectedEvent.connector T k = (toParams T).conn T.r (k : ℤ) := by
  rw [TubeParams.conn_eq, TubeParams.range_outA, TubeParams.range_inA,
    TubeParams.range_corridor_eq]
  simp only [Objects.CorrectedEvent.connector]
  rw [outSet_eq T hsp k, inSet_eq T hpos (Objects.CorrectedEvent.nextSite T k), seg76_eq, gatePlus_eq' T hn,
    gateMinus_next T hn, moduleMap_eq, moduleMap_next, twist_eq, twist_next]
  rfl

 
theorem summand_eq (hn : ‖T.orientation‖ = 1) (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3)
    (hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) (hρr : T.rho * T.r ≠ 0) (k : Fin T.K) :
    Objects.CorrectedEvent.block T k ∪ ball (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ∪
        ball (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ∪
        {x | ∃ y ∈ Objects.CorrectedEvent.connector T k, dist x y < Objects.CorrectedEvent.tubeWidth T} =
      (toParams T).summand T.r (k : ℤ) := by
  simp only [TubeParams.summand]
  rw [block_eq, innerCenter_eq, outerCenter_eq, s_eq T hρr, w_eq, connector_eq T hn hsp hpos]
  congr 1
  ext x
  rw [mem_thickening_iff]
  rfl

 
theorem tubeSet_eq (hn : ‖T.orientation‖ = 1) (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3)
    (hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) (hρr : T.rho * T.r ≠ 0) :
    Objects.CorrectedEvent.tubeSet T = (toParams T).tube T.r := by
  have hK : ((toParams T).K : ℝ) ≠ 0 := by
    simp only [toParams]; exact_mod_cast T.Kpos.ne'
  have hKZ : (0 : ℤ) < T.K := by exact_mod_cast T.Kpos
  rw [TubeParams.tube_eq_iUnion_summand]
  simp only [Objects.CorrectedEvent.tubeSet]
  apply Subset.antisymm
  · intro x hx
    rw [mem_iUnion] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨(k : ℤ), (summand_eq T hn hsp hpos hρr k) ▸ hk⟩
  · intro x hx
    rw [mem_iUnion] at hx ⊢
    obtain ⟨j, hj⟩ := hx
    set j' := j % (T.K : ℤ) with hj'
    have h0 : 0 ≤ j' := Int.emod_nonneg _ (by omega)
    have h1 : j' < T.K := Int.emod_lt_of_pos _ hKZ
    have hd := Int.mul_ediv_add_emod j (T.K : ℤ)
    have hjj : j = j' + (toParams T).K * (j / T.K) := by
      simp only [toParams]; rw [hj']; linarith
    rw [hjj, TubeParams.summand_add_K_mul hK] at hj
    let k : Fin T.K := ⟨j'.toNat, by omega⟩
    have hk : ((k : ℕ) : ℤ) = j' := by simp only [k]; omega
    refine ⟨k, ?_⟩
    rw [summand_eq T hn hsp hpos hρr k]
    rw [hk]
    exact hj

 
theorem tubeV_eq (hn : ‖T.orientation‖ = 1) (hsp : Objects.CorrectedEvent.sPrime T ≤ 2 / 3)
    (hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4) (hρr : T.rho * T.r ≠ 0) (A : ℝ) :
    Objects.CorrectedEvent.tubeV T A = (toParams T).nbhd T.r A := by
  simp only [Objects.CorrectedEvent.tubeV, TubeParams.nbhd]
  rw [← tubeSet_eq T hn hsp hpos hρr]
  ext x
  rw [mem_thickening_iff]
  rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
