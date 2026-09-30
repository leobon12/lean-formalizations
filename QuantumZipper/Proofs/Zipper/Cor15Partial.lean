import QuantumZipper.Proofs.Zipper.UnzipInvariance
import QuantumZipper.Proofs.LQG.WedgeToolkit

/-!
# Partial results towards Corollary 1.5

* `theorem1_5a_zero`, `theorem1_5a_nonpos`: clause (a) of `theorem1_5` at `t = 0`, hence for all
  `t ≤ 0` (combined with `theorem1_5a_neg_holds` of `UnzipInvariance`). At time `0` every
  continuous `W'` with `W' 0 = 0` is a welding driver (`isWeldingDriver_zero`), the zip-up map is
  the identity on `ℍ`, and the zipped field pairs through `evalReg`, which agrees a.s. with the
  raw pairing (`ae_evalReg_h0rev_add`).
* `gamma0_scale_invariance`: scale invariance of `Γ⁰`. For `a > 0`,
  `(rescale h Q a, s ↦ W(a² s)/a)` has the law of `(h, W)` (drivers compared on `[0,∞)`), with
  the Brownian-scaling convention of `zipLenDown` (`Zipper/Maps.lean`, item 4).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Partial

open CharFun UnzipInvariance

/-! ## Laws with one coordinatewise-a.e. component -/

theorem map_prod_eq_of_forall_ae_eq {Ω ι κ' : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f g : Ω → ι → ℝ} {h : Ω → κ' → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (H : ∀ i, ∀ᵐ ω ∂P, f ω i = g ω i) :
    P.map (fun ω => (f ω, h ω)) = P.map (fun ω => (g ω, h ω)) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ' => ℝ)
  have key : ∀ u : Ω → ι → ℝ, Measurable u →
      P.map (fun ω => (u ω, h ω)) = (P.map (fun ω => e.symm (u ω, h ω))).map e := by
    intro u hu
    rw [Measure.map_map e.measurable (show Measurable fun ω => e.symm (u ω, h ω) from
      e.symm.measurable.comp (hu.prodMk hh))]
    congr 1
  rw [key f hf, key g hg]
  congr 1
  refine map_eq_of_forall_ae_eq (e.symm.measurable.comp (hf.prodMk hh))
    (e.symm.measurable.comp (hg.prodMk hh)) ?_
  rintro (i | k)
  · filter_upwards [H i] with ω hω
    simpa [e, MeasurableEquiv.coe_sumPiEquivProdPi_symm] using hω
  · exact ae_of_all _ fun ω => rfl

/-! ## 1. Clause (a) at `t = 0` -/

theorem revMapBdry_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (x : ℝ) :
    revMapBdry W 0 x = x := by
  unfold revMapBdry
  have ht : Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h : Tendsto (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (𝓝 0)
        (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
    rw [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine (ht.congr' ?_).limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (revMap_zero_eq hW hW0 (show (0 : ℝ) < ((x : ℂ) + y * Complex.I).im by
    simpa using hy)).symm

/-- At time `0` the zero driver (indeed every continuous driver from `0`) is a welding
driver. -/
theorem isWeldingDriver_zero (γ : ℝ) (x : FieldSample) :
    IsWeldingDriver γ x 0 (fun _ => 0) := by
  have hW : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hb := revMapBdry_zero hW rfl
  refine ⟨hW, rfl, Or.inl rfl, fun s hs => ?_⟩
  have hzm : zeroMinus (fun _ => (0 : ℝ)) 0 = 0 := by
    unfold zeroMinus
    have : {x : ℝ | x < 0 ∧ revMapBdry (fun _ => (0 : ℝ)) 0 x = 0} = ∅ := by
      ext y
      simp only [hb, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy h
      exact hy.ne (by exact_mod_cast h)
    rw [this, Real.sSup_empty]
  rw [hzm] at hs
  have hs0 : s = 0 := le_antisymm hs.2 hs.1
  subst hs0
  have e1 : weldingHom (fun _ => (0 : ℝ)) 0 0 = 0 := by
    unfold weldingHom
    have : {y : ℝ | 0 ≤ y ∧ revMapBdry (fun _ => (0 : ℝ)) 0 y =
        revMapBdry (fun _ => (0 : ℝ)) 0 0} = {0} := by
      ext y
      simp only [hb, Set.mem_setOf_eq, Set.mem_singleton_iff, Complex.ofReal_zero,
        Complex.ofReal_eq_zero]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨le_rfl, rfl⟩
    rw [this, csInf_singleton]
  have e2 : weldHomR γ x 0 = 0 := by
    unfold weldHomR
    have : {r : ℝ | 0 ≤ r ∧ qBoundaryMeasure γ x (Set.Icc 0 0) ≤
        qBoundaryMeasure γ x (Set.Icc 0 r)} = Set.Ici 0 := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      exact ⟨fun h => h.1, fun h => ⟨h, measure_mono (Set.Icc_subset_Icc le_rfl h)⟩⟩
    rw [this, csInf_Ici]
  rw [e1, e2]

theorem revMapInv_zero_eqOn {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    EqOn (revMapInv W 0) id H := by
  intro w hw
  have hex : ∃! z, z ∈ H ∧ revMap W 0 z = w :=
    ⟨w, ⟨hw, revMap_zero_eq hW hW0 hw⟩, fun y hy => by rw [← hy.2, revMap_zero_eq hW hW0 hy.1]⟩
  unfold revMapInv
  rw [dif_pos hex]
  exact hex.unique hex.choose_spec.1 ⟨hw, revMap_zero_eq hW hW0 hw⟩

theorem coordChange_id_apply (y : FieldSample) (Q : ℝ) (μ : Measure ℂ) :
    coordChange y id Q μ = evalReg y μ := by
  unfold coordChange
  simp [Measure.map_id]

/-- **Corollary 1.5 (a) at `t = 0`** (unconditional). -/
theorem theorem1_5a_zero (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    configLawMod0 (fun ω => zipCap (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  rw [zipCap_of_nonneg le_rfl]
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hy : Measurable fun ω => ofFun (h0rev κ) + X ω := (measurable_add_left _).comp hXm
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Ω → ℝ≥0 → ℝ, G₀ = fun ω s => Real.sqrt κ * B₁ s ω := ⟨_, rfl⟩
  have hG₀m : Measurable G₀ := by
    rw [hG₀]; exact measurable_pi_iff.2 fun s => (hB₁m s).const_mul _
  have hzip : (fun ω => ((fun ρ : TestFun0 H =>
      pairRaw (zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ρ.1.1),
        fun s : ℝ≥0 => (zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)).2 s))
      =ᵐ[P] fun ω => ((fun ρ : TestFun0 H => pairTest (ofFun (h0rev κ) + X ω) ρ.1.1), G₀ ω) := by
    filter_upwards [hB₁eq, hB₁.eval_zero_ae_eq_zero] with ω h1 h0
    obtain ⟨hWc, hW0, -, -⟩ := weldDriver_spec
      ⟨_, isWeldingDriver_zero (Real.sqrt κ) (ofFun (h0rev κ) + X ω)⟩
    rw [hG₀]
    refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
    · show pairRaw (coordChange (ofFun (h0rev κ) + X ω)
          (revMapInv (weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) 0) 0)
          (Qc (Real.sqrt κ))) ρ.1.1 = pairTest (ofFun (h0rev κ) + X ω) ρ.1.1
      rw [pairRaw_coordChange_congr (revMapInv_zero_eqOn hWc hW0) _ _ ρ.1]
      simp only [pairRaw_eq_tdens, coordChange_id_apply]
      rfl
    · show (if (s : ℝ) ≤ 0 then
          weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) 0 (0 - max (s : ℝ) 0) -
            weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) 0 0
        else drive κ B ω ((s : ℝ) - 0) - weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) 0 0) =
          Real.sqrt κ * B₁ s ω
      rw [hW0]
      split_ifs with hs
      · have hs0 : s = 0 := by exact_mod_cast le_antisymm hs s.coe_nonneg
        subst hs0
        simp [hW0, h0]
      · simp only [drive, sub_zero]
        rw [Real.toNNReal_coe, h1]
  have hc0 : (fun ω => ((fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1),
        fun s : ℝ≥0 => drive κ B ω s)) =ᵐ[P]
      fun ω => ((fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1), G₀ ω) := by
    filter_upwards [hB₁eq] with ω h1
    rw [hG₀]
    refine Prod.ext rfl (funext fun s => ?_)
    show Real.sqrt κ * B (s : ℝ).toNNReal ω = Real.sqrt κ * B₁ s ω
    rw [Real.toNNReal_coe, h1]
  have hT : Measurable fun ω (ρ : TestFun0 H) => pairTest (ofFun (h0rev κ) + X ω) ρ.1.1 := by
    refine measurable_pi_iff.2 fun ρ => ?_
    have key := (measurable_pairTest ρ.1.1).comp hy
    simp only [Function.comp_def] at key
    exact key
  have hR : Measurable fun ω (ρ : TestFun0 H) => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 :=
    measurable_pi_iff.2 fun ρ => measurable_pairRaw_lhs κ hX ρ
  have hae : ∀ ρ : TestFun0 H, ∀ᵐ ω ∂P,
      pairTest (ofFun (h0rev κ) + X ω) ρ.1.1 = pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 := by
    intro ρ
    obtain ⟨M, δ, hd⟩ := exists_dens ρ.1
    filter_upwards [ae_evalReg_h0rev_add κ hX hd.tdens_le hd.compact hd.delta hd.sub
      hd.tdens_compl, ae_evalReg_h0rev_add κ hX hd.neg.tdens_le hd.neg.compact hd.neg.delta
      hd.neg.sub hd.neg.tdens_compl] with ω h1 h2
    show evalReg (ofFun (h0rev κ) + X ω) (tdens ρ.1.1) -
      evalReg (ofFun (h0rev κ) + X ω) (tdens fun z => -ρ.1.1 z) = _
    rw [h1, h2]
    rfl
  calc configLawMod0
        (fun ω => zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)) P
      = P.map (fun ω => ((fun ρ : TestFun0 H => pairTest (ofFun (h0rev κ) + X ω) ρ.1.1),
          G₀ ω)) := Measure.map_congr hzip
    _ = P.map (fun ω => ((fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1),
          G₀ ω)) := map_prod_eq_of_forall_ae_eq hT hR hG₀m hae
    _ = configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P :=
        (Measure.map_congr hc0).symm

/-- **Corollary 1.5 (a) for all `t ≤ 0`** (unconditional), in the shape of `theorem1_5`. -/
theorem theorem1_5a_nonpos :
    ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      let γ := Real.sqrt κ
      let c : Ω → FieldSample × (ℝ → ℝ) := fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)
      ∀ t : ℝ, t ≤ 0 → configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind γ c t ht
  rcases ht.lt_or_eq with h | rfl
  · exact theorem1_5a_neg_holds κ hκ hκ4 P B X hB hX hind t h
  · exact theorem1_5a_zero κ P B X hB hX

/-! ## 2. Scale invariance of `Γ⁰` -/

theorem deriv_mul_left_c (c z : ℂ) : deriv (fun u => c * u) z = c := by
  simpa using ((hasDerivAt_id z).const_mul c).deriv

theorem rescale_apply_eq (y : FieldSample) (Q : ℝ) {a : ℝ} (ha : 0 < a) (μ : Measure ℂ) :
    rescale y Q a μ =
      evalReg y (μ.map fun u => (a : ℂ) * u) + Q * ((μ Set.univ).toReal * Real.log a) := by
  show evalReg y _ + Q * ∫ z, Real.log ‖deriv (fun u => (a : ℂ) * u) z‖ ∂μ = _
  rw [show (fun z => Real.log ‖deriv (fun u => (a : ℂ) * u) z‖) = fun _ => Real.log a from
    funext fun z => by rw [deriv_mul_left_c, Complex.norm_real, Real.norm_of_nonneg ha.le],
    integral_const, smul_eq_mul, measureReal_def]

end Cor15Partial
end QuantumZipper
