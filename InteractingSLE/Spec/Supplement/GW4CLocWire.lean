/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocSafe
import InteractingSLE.Spec.Supplement.GW4CLocTime
import InteractingSLE.Spec.Supplement.GW4SafeRMeanShared
import InteractingSLE.Spec.Supplement.GW4SafeRClipMean
import InteractingSLE.Spec.Supplement.GW4BarrierCond
import InteractingSLE.Spec.Supplement.GW4RelMatch
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# GW4: the component-locality half of `GW4ComponentLinesStatement`, proved

Packet PROVE-GW4-CLOC. **`gw4ComponentLocalityStatement`**: from Theorems 1.2–1.3 (R48: Theorem 1.4 only),
PROVE-GW4-SAFER's `GW4ComponentLocalityStatement` (`Spec/Supplement/GW4SafeRMeanShared`) holds, with the witnesses
`u₀ = safeWordHarmonic c₀` (the bounded harmonic extension of the component word), `ℋ = physFilt` (the physical
filtration) and `B = safeHull` (the relative hull at the line clock on the safe event, `ℍ` off it).

Route (Astra's follow-up 3, Q3 §§3.2, 3.5–3.6, L736–L1000, in the form of the landed kernels):

1. the original-space Gaussian union kernel of the walks and the counterflow (`exists_walkCfUnion_kernel`) is coarsened
   to countably generated marks and transferred to the regular conditional law `ν` given the walks, at all dyadic
   times and all tests (`exists_ae_condExpKernel_kernel`);
2. read in the component chart and the inverting chart, it is the Gaussian kernel of the inverted component field with
   the chart pre-image domain; the complement of that domain is history-marked local
   (`isHistoryAvoidanceLocal_chartSet`);
3. that set is the relative hull, which lies in the safe hull; the physical marks are a.s. events of the kernel's marks
   (`isHistoryAvoidanceLocal_safeHull_of_kernel`);
4. dyadic times extend to all times (`isHistoryAvoidanceLocal_of_dyadic`), by right-continuity of the safe hull on
   compact sets (`exists_gt_disjoint_safeHull`) and the Gaussian tail identity of Proposition 3.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField WalkLaw GW4Traverse GW4Rel Sec5.GlueCond Sec5.Cond44Ref Supp8.RelSafe
  Sec7.StripSysField Exist.StagedLaw

/-! ### The safe hull in time -/

section SafeTime

variable {F : Frame} (hF : F.IsOk) {Ω : Type*} {Wd : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
include hF hGT

theorem monotone_safeHull (ω : Ω) : Monotone fun t => safeHull F Wd GT R V t ω := by
  intro s t hst
  have hmono := Frame.monotone_min_physClockG hF hGT (V := V) ω hst
  by_cases ht : lineClock F Wd GT V t ω < V ω
  · have hs : lineClock F Wd GT V s ω < V ω := hmono.trans_lt ht
    simp only [safeHull, hs, ht, ↓reduceIte]
    refine inter_subset_inter_right _ ((QuantumZipper.fwdHull_mono (W := fun r : ℝ => R r.toNNReal ω)).1 ?_)
    exact NNReal.coe_le_coe.2 (ENNReal.toNNReal_mono (ht.trans_le le_top).ne hmono)
  · simp only [safeHull, ht, ↓reduceIte]
    exact safeHull_subset_H F Wd GT R V s ω

/-- **Right-continuity of the safe hull on compact sets.** -/
theorem exists_gt_disjoint_safeHull (hRc : ∀ ω, Continuous fun t => R t ω) (t : ℝ≥0) (ω : Ω)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ H) (hd : Disjoint (safeHull F Wd GT R V t ω) K) :
    ∃ t', t < t' ∧ Disjoint (safeHull F Wd GT R V t' ω) K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨t + 1, lt_add_one t, disjoint_empty _⟩
  obtain ⟨hlive, hdK⟩ := (disjoint_safeHull_iff F Wd GT R V t ω hKH hKne).1 hd.symm
  set ℓ := lineClock F Wd GT V t ω with hℓ
  set s : ℝ≥0 := ℓ.toNNReal with hs
  have hℓs : (s : ℝ≥0∞) = ℓ := ENNReal.coe_toNNReal (hlive.trans_le le_top).ne
  have hRc' : Continuous fun r : ℝ => R r.toNNReal ω := (hRc ω).comp continuous_real_toNNReal
  -- a uniform capacity margin on the compact set
  set O : ℕ → Set ℂ := fun n => H \ fwdHull (fun r : ℝ => R r.toNNReal ω) ((s : ℝ) + 1 / ((n : ℝ) + 1))
    with hO
  have hOo : ∀ n, IsOpen (O n) := fun n =>
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hRc' (by positivity)
  have hcover : K ⊆ ⋃ n, O n := by
    intro z hz
    have hzH := hKH hz
    have hzn : z ∉ fwdHull (fun r : ℝ => R r.toNNReal ω) (s : ℝ) := fun h => Set.disjoint_left.1 hdK hz h
    have hlt : ENNReal.ofReal (s : ℝ) < QuantumZipper.swallowTime (fun r : ℝ => R r.toNNReal ω) z := by
      by_contra hge
      exact hzn ⟨hzH, not_lt.1 hge⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal ((s : ℝ) + 1 / ((n : ℝ) + 1)) <
        QuantumZipper.swallowTime (fun r : ℝ => R r.toNNReal ω) z := by
      rcases eq_or_ne (QuantumZipper.swallowTime (fun r : ℝ => R r.toNNReal ω) z) ⊤ with htop | htop
      · exact ⟨0, htop ▸ ENNReal.ofReal_lt_top⟩
      · have hreal : (s : ℝ) < (QuantumZipper.swallowTime (fun r : ℝ => R r.toNNReal ω) z).toReal := by
          rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg, ENNReal.ofReal_toReal htop]
          exact hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hreal)
        refine ⟨n, ?_⟩
        rw [← ENNReal.ofReal_toReal htop]
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt s.coe_nonneg hreal)).2 (by linarith)
    exact mem_iUnion.2 ⟨n, hzH, fun h => (not_le.2 hn) h.2⟩
  have hdir : Directed (· ⊆ ·) O := by
    refine Monotone.directed_le fun m n hmn z ⟨hzH, hz⟩ => ⟨hzH, fun h => hz ?_⟩
    refine (QuantumZipper.fwdHull_mono (W := fun r : ℝ => R r.toNNReal ω)).1 ?_ h
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  obtain ⟨n, hn⟩ := hK.elim_directed_cover O hOo hcover hdir
  -- a later time with the line clock below the margin and still safe
  set a : ℝ≥0∞ := ENNReal.ofReal ((s : ℝ) + 1 / ((n : ℝ) + 1)) with ha
  have hℓa : ℓ < a := by
    rw [← hℓs, ha, ← ENNReal.ofReal_coe_nnreal]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  have hcont := Frame.continuous_min_physClockG hF hGT (V := V) ω
  have hev : ∀ᶠ t' in 𝓝[>] t, lineClock F Wd GT V t' ω < V ω ∧ lineClock F Wd GT V t' ω < a := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (hcont.tendsto t).eventually ((isOpen_Iio.inter isOpen_Iio).mem_nhds ⟨hlive, hℓa⟩)
  obtain ⟨t', ⟨h1, h2⟩, ht'⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨t', ht', ?_⟩
  refine ((disjoint_safeHull_iff F Wd GT R V t' ω hKH hKne).2 ⟨h1, ?_⟩).symm
  refine Set.disjoint_left.2 fun z hz hzh => (hn hz).2 ?_
  refine (QuantumZipper.fwdHull_mono (W := fun r : ℝ => R r.toNNReal ω)).1 ?_ hzh
  have hfin : lineClock F Wd GT V t' ω ≠ ⊤ := (h1.trans_le le_top).ne
  have := ENNReal.toReal_mono (by rw [ha]; exact ENNReal.ofReal_ne_top) h2.le
  rw [ha, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

end SafeTime

/-! ### The global statement -/

/-- **PROVE-GW4-SAFER's component-locality half of `GW4ComponentLinesStatement`, from Theorems 1.2–1.3.** -/
theorem gw4ComponentLocalityStatement (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    GW4ComponentLocalityStatement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨B, M, 𝓜, hJ, hcf𝓜, hBm, hMm, hBc, hBeq, hMh, hker⟩ :=
    exists_ae_condExpKernel_kernel h12p h13 hκ hκ4 hb hh hcf hζ' hE hreg hu₀
  have hpR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hpL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  have hjm : jointPast κ b jumps E ≤ ‹MeasurableSpace Ω› :=
    sup_le ((hE _ hpR).2.1 _) ((hE _ hpL).2.1 _)
  have hRw := GW4Reg.ae_ae_physSet_eq (hreg wR hpR) hjm le_sup_left
  have hLw := GW4Reg.ae_ae_physSet_eq (hreg wL hpL) hjm le_sup_right
  have hBeq' : ∀ᵐ ω₀ ∂P, ∀ p : ℕ × ℕ, ∀ᵐ ω ∂(condExpKernel P (jointPast κ b jumps E) ω₀),
      B (LawUnique.dyadicTime p) ω = relClosureH (walkUnionSet κ b jumps E ω ∪
        cfHullQ (LawUnique.dyadicTime p) (cfHistory W' ζ' ω)) :=
    ae_all_iff.2 fun p => KernelTower.ae_ae_condExpKernel_of_ae hjm (hBeq _)
  have hMh' : ∀ᵐ ω₀ ∂P, ∀ p : ℕ × ℕ, ∀ᵐ ω ∂(condExpKernel P (jointPast κ b jumps E) ω₀),
      IsHarmonicDistOn (M (LawUnique.dyadicTime p) ω) (H \ B (LawUnique.dyadicTime p) ω) :=
    ae_all_iff.2 fun p => KernelTower.ae_ae_condExpKernel_of_ae hjm (hMh _)
  have hζν := KernelTower.ae_ae_condExpKernel_of_ae hjm hζ'
  filter_upwards [hker, hRw, hLw, hBeq', hMh', hζν] with ω₀ hkerω hRω hLω hBω hMω hζω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hX : IsGFFWithBoundaryData ν (fun ω => invField κ (hC ω)) c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hXc := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX (safeWordHarmonic_spec c₀)
  obtain ⟨ω₁, hω₁⟩ := hGTae.exists
  have hCo : IsOpen C := hFC ▸ Frame.isOpen_C hF (hGT ω₁ hω₁)
  have hS : ∀ᵐ ω ∂ν, walkUnionSet κ b jumps E ω = (R ∪ L) ∩ H := by
    filter_upwards [hRω, hLω] with ω h1 h2
    show WalkLaw.walkSet κ b jumps wR (E wR) ω ∪ WalkLaw.walkSet κ b jumps wL (E wL) ω = (R ∪ L) ∩ H
    simp only [WalkLaw.walkSet]
    rw [h1, h2]
    exact (union_inter_distrib_right _ _ _).symm
  refine ⟨safeWordHarmonic c₀, physFilt Frame.measurable_gw4Rec hWm ν, safeHull F Wd GT Rv V,
    safeWordHarmonic_spec c₀, fun _ => le_rfl, (physFilt Frame.measurable_gw4Rec hWm ν).le,
    fun t => (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono
      ((physFilt Frame.measurable_gw4Rec hWm ν).le t) le_rfl,
    fun t ω => ⟨safeHull_subset_H F Wd GT Rv V t ω, Frame.isOpen_H_diff_safeHull hver t ω⟩, ?_,
    fun t => Eventually.of_forall fun ω hlt => H_diff_safeHull_of_lt F Wd GT Rv V t ω hlt⟩
  intro t
  refine isHistoryAvoidanceLocal_of_dyadic hXc (fun _ _ hst => (physFilt Frame.measurable_gw4Rec hWm ν).mono hst)
    (physFilt Frame.measurable_gw4Rec hWm ν).le
    (fun t => (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono
      ((physFilt Frame.measurable_gw4Rec hWm ν).le t) le_rfl)
    (fun t ω => ⟨safeHull_subset_H F Wd GT Rv V t ω, Frame.isOpen_H_diff_safeHull hver t ω⟩)
    (monotone_safeHull hF hGT)
    (fun t ω K hK hKH hd => exists_gt_disjoint_safeHull hF hGT hver.1.1.2.1 t ω K hK hKH hd) (fun p => ?_) t
  exact isHistoryAvoidanceLocal_safeHull_of_kernel (𝓜 (LawUnique.dyadicTime p)).2 hCm hch hCo hκ hh.1 htr
    (safeWordHarmonic_spec c₀).1 (hBm _) (hMm _) (hBc _) (hMω p) (hkerω p) (hcf𝓜 _) (hBω p) hS hF hFC hFc
    hGT hWm hGTm hGTae hVW hζω hver

/-- `GW4ComponentLinesStatement` from Theorems 1.2–1.3 and PROVE-GW4-SAFER's mean half alone. -/
theorem gw4ComponentLinesStatement_of_mean (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hM : GW4ComponentMeanStatement.{u}) :
    GW4ComponentLinesStatement.{u} :=
  gw4ComponentLinesStatement_of_locality_mean (gw4ComponentLocalityStatement h12 h13) hM

/-- GW4's path-rule safe law from Theorems 1.2–1.3, the barrier and word-bound inputs and the mean half alone. -/
theorem gw4RelSafeRStatement_of_mean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hM : GW4ComponentMeanStatement.{u}) : GW4RelSafeRStatement.{u} :=
  gw4RelSafeRStatement_of_componentLines h12 h13 hB hWB (gw4ComponentLinesStatement_of_mean h12 h13 hM)

end InteractingSLE.Theorem14.GW4Fix.CLoc
