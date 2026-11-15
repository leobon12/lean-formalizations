/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerLawLine

/-!
# Gluing per-box conditionings into one forward mark

Packet PROVE-T15-FCKER3 (R82). The per-cap kernels of the first continuation (`exists_fcBoxKernel_physical`)
condition on a σ-algebra that depends on the cap `m` (the marked capped union at the later line). They live on the
disjoint boxes `B m` of the physical line. Following `planning/handoffs/PROVE-T15-FCKER2.md` ("Glue the caps"), the
glued σ-algebra `glueSigma base big B` consists of the sets whose trace on each box `B m` is in `big m` and whose part
off the boxes is in `base`. It contains `base` (when every `big m` does), and its trace on `B m` is the trace of
`big m`, so conditional expectations given it agree with those given `big m` on `B m`
(`condExp_ae_eq_restrict_of_measurableSpace_eq_on`). No comparison of different caps is needed.

* `glueSigma`, `le_glueSigma`, `glueSigma_le`, **`ae_condExp_glueSigma_eq`**,
  **`setIntegral_eq_of_glueSigma`** (member identities glue);
* **`hasFCK2CapForwardKernel_of_boxLaw`**, **`hasFCK2CapForwardMembers_of_boxMembers`**: the two fields of
  `FCK2CapForwardInputsC` from per-box laws on the physical lines, with the safe events taken inside the live event
  (only `F ∩ lineSafe` has to be a physical event), and `hasFCK2CapForwardKernel_mono`,
  `hasFCK2CapForwardMembers_mono` (the protected set matters only up to null sets).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerC

open LQGMetric WangWu.ChartConst DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 Coupling LocalSets

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### The glued σ-algebra -/

section Glue

/-- **The glued σ-algebra**: traces in `big m` on the disjoint boxes `B m`, and in `base` off their union. -/
@[instance_reducible]
def glueSigma (base : MeasurableSpace Ω) (big : ℕ → MeasurableSpace Ω) (B : ℕ → Set Ω)
    (hB : ∀ m, MeasurableSet[big m] (B m)) (hU : MeasurableSet[base] (⋃ m, B m)) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[base] (A \ ⋃ m, B m) ∧ ∀ m, MeasurableSet[big m] (A ∩ B m)
  measurableSet_empty := by
    refine ⟨?_, fun m => ?_⟩
    · rw [empty_sdiff]
      exact @MeasurableSet.empty Ω base
    · rw [empty_inter]
      exact @MeasurableSet.empty Ω (big m)
  measurableSet_compl A hA := by
    refine ⟨?_, fun m => ?_⟩
    · have he : Aᶜ \ (⋃ m, B m) = (⋃ m, B m)ᶜ \ (A \ ⋃ m, B m) := by
        ext ω
        simp only [Set.mem_sdiff, mem_compl_iff]
        tauto
      rw [he]
      exact hU.compl.diff hA.1
    · have he : Aᶜ ∩ B m = B m \ (A ∩ B m) := by
        ext ω
        simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, not_and]
        tauto
      rw [he]
      exact (hB m).diff (hA.2 m)
  measurableSet_iUnion f hf := by
    refine ⟨?_, fun m => ?_⟩
    · rw [iUnion_sdiff]
      exact MeasurableSet.iUnion fun i => (hf i).1
    · rw [iUnion_inter]
      exact MeasurableSet.iUnion fun i => (hf i).2 m

variable {base : MeasurableSpace Ω} {big : ℕ → MeasurableSpace Ω} {B : ℕ → Set Ω}
  {hB : ∀ m, MeasurableSet[big m] (B m)} {hU : MeasurableSet[base] (⋃ m, B m)}

omit mΩ in
theorem measurableSet_glueSigma_iff {A : Set Ω} :
    MeasurableSet[glueSigma base big B hB hU] A ↔
      MeasurableSet[base] (A \ ⋃ m, B m) ∧ ∀ m, MeasurableSet[big m] (A ∩ B m) := Iff.rfl

omit mΩ in
theorem le_glueSigma (h : ∀ m, base ≤ big m) : base ≤ glueSigma base big B hB hU :=
  fun _ hA => ⟨hA.diff hU, fun m => (h m _ hA).inter (hB m)⟩

theorem glueSigma_le (hbase : base ≤ mΩ) (hbig : ∀ m, big m ≤ mΩ) : glueSigma base big B hB hU ≤ mΩ := by
  let _ : MeasurableSpace Ω := mΩ
  intro A hA
  have he : A = (A \ ⋃ m, B m) ∪ (⋃ m, (A ∩ B m)) := by
    ext ω
    simp only [mem_union, Set.mem_sdiff, mem_iUnion, mem_inter_iff]
    constructor
    · intro hω
      by_cases h : ∃ m, ω ∈ B m
      · obtain ⟨m, hm⟩ := h
        exact Or.inr ⟨m, hω, hm⟩
      · exact Or.inl ⟨hω, by simpa only [mem_iUnion] using h⟩
    · rintro (⟨hω, -⟩ | ⟨m, hω, -⟩) <;> exact hω
  rw [he]
  exact (hbase _ hA.1).union (MeasurableSet.iUnion fun m => hbig m _ (hA.2 m))

omit mΩ in
/-- The trace of the glued σ-algebra on a box is that of the box's σ-algebra. -/
theorem measurableSet_glueSigma_inter_iff (hdisj : Pairwise (Function.onFun Disjoint B)) (m : ℕ) (A : Set Ω) :
    MeasurableSet[glueSigma base big B hB hU] (B m ∩ A) ↔ MeasurableSet[big m] (B m ∩ A) := by
  constructor
  · intro h
    have he : B m ∩ A ∩ B m = B m ∩ A := by
      ext ω
      simp only [mem_inter_iff]
      tauto
    exact he ▸ h.2 m
  · intro h
    refine ⟨?_, fun k => ?_⟩
    · have he : (B m ∩ A) \ (⋃ k, B k) = ∅ := by
        ext ω
        simp only [Set.mem_sdiff, mem_inter_iff, mem_iUnion, mem_empty_iff_false, iff_false, not_and, not_exists]
        intro hm h'
        exact h' m hm.1
      rw [he]
      exact @MeasurableSet.empty Ω base
    · rcases eq_or_ne k m with rfl | hkm
      · have he : B k ∩ A ∩ B k = B k ∩ A := by
          ext ω
          simp only [mem_inter_iff]
          tauto
        rw [he]
        exact h
      · have he : B m ∩ A ∩ B k = ∅ := by
          ext ω
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro hm hk
          exact Set.disjoint_left.1 (hdisj hkm) hk hm.1
        rw [he]
        exact @MeasurableSet.empty Ω (big k)

/-- **Conditioning on the glued σ-algebra is conditioning on `big m` on the box `B m`.** -/
theorem ae_condExp_glueSigma_eq [IsFiniteMeasure P] (hbase : base ≤ mΩ) (hbig : ∀ m, big m ≤ mΩ)
    (hdisj : Pairwise (Function.onFun Disjoint B)) (X : Ω → ℂ) (m : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ B m → P[X | glueSigma base big B hB hU] ω = P[X | big m] ω := by
  let _ : MeasurableSpace Ω := mΩ
  have hle := glueSigma_le (mΩ := mΩ) (hB := hB) (hU := hU) hbase hbig
  have hBg : MeasurableSet[glueSigma base big B hB hU] (B m) := by
    have h := (measurableSet_glueSigma_inter_iff (hB := hB) (hU := hU) hdisj m univ).2
      (by rw [inter_univ]; exact hB m)
    rwa [inter_univ] at h
  have h := condExp_ae_eq_restrict_of_measurableSpace_eq_on (f := X) (μ := P) hle (hbig m) hBg
    (measurableSet_glueSigma_inter_iff hdisj m)
  have hBm : MeasurableSet (B m) := hbig m _ (hB m)
  exact (ae_restrict_iff' hBm).1 h

/-- **Member identities glue.** If the identity `∫_E X = c ∫_E Y` holds for the events of each `big m` inside a set
`A ∩ B m`, it holds for the events of the glued σ-algebra inside `A`, as soon as `A` is almost surely covered by the
boxes. -/
theorem setIntegral_eq_of_glueSigma (hbase : base ≤ mΩ) (hbig : ∀ m, big m ≤ mΩ)
    (hdisj : Pairwise (Function.onFun Disjoint B)) {X Y : Ω → ℂ} (hX : Integrable X P) (hY : Integrable Y P)
    {c : ℂ} {A : Set Ω} (hcov : ∀ᵐ ω ∂P, ω ∈ A → ∃ m, ω ∈ B m)
    (hbox : ∀ m E, MeasurableSet[big m] E → (∀ᵐ ω ∂P, ω ∈ E → ω ∈ A ∧ ω ∈ B m) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P)
    {E : Set Ω} (hE : MeasurableSet[glueSigma base big B hB hU] E) (hEA : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ A) :
    ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P := by
  let _ : MeasurableSpace Ω := mΩ
  have hEm : MeasurableSet E := glueSigma_le (mΩ := mΩ) (hB := hB) (hU := hU) hbase hbig _ hE
  have hpiece : ∀ m, MeasurableSet (E ∩ B m) := fun m => hbig m _ (hE.2 m)
  have hEU : E =ᵐ[P] ⋃ m, (E ∩ B m) := by
    filter_upwards [hcov, hEA] with ω hc ha
    refine propext ⟨fun hω => ?_, fun hω => ?_⟩
    · obtain ⟨m, hm⟩ := hc (ha hω)
      exact mem_iUnion.2 ⟨m, hω, hm⟩
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hω
      exact hm.1
  have hd : Pairwise (Function.onFun (AEDisjoint P) fun m => E ∩ B m) := fun k l hkl =>
    Disjoint.aedisjoint ((hdisj hkl).mono inter_subset_right inter_subset_right)
  have hsum : ∀ Z : Ω → ℂ, Integrable Z P →
      ∫ ω in E, Z ω ∂P = ∑' m, ∫ ω in E ∩ B m, Z ω ∂P := fun Z hZ => by
    rw [setIntegral_congr_set hEU]
    exact integral_iUnion_ae (fun m => (hpiece m).nullMeasurableSet) hd hZ.integrableOn
  rw [hsum X hX, hsum Y hY, ← tsum_mul_left]
  refine tsum_congr fun m => hbox m _ (hE.2 m) ?_
  filter_upwards [hEA] with ω hω hωE
  exact ⟨hω hωE.1, hωE.2⟩

end Glue

/-! ### The forward inputs from per-box laws -/

section Forward

/-- The protected set of a forward kernel matters only up to null sets. -/
theorem hasFCK2CapForwardKernel_mono {m : MeasurableSpace Ω} {S S' : Set Ω} {X G : Ω → ℂ}
    (hSS : ∀ᵐ ω ∂P, ω ∈ S → ω ∈ S') (h : HasFCK2CapForwardKernel (mΩ := mΩ) P m S' X G) :
    HasFCK2CapForwardKernel (mΩ := mΩ) P m S X G := by
  obtain ⟨𝓜, Av, K, τ, h𝓜, hτ, hb, hdet, hread, hlim⟩ := h
  refine ⟨𝓜, Av, K, τ, h𝓜, hτ, hb, hdet, fun D hD hs => hread D hD ?_, ?_⟩
  · filter_upwards [hs, hSS] with ω h1 h2 hωD using h2 (h1 hωD)
  · filter_upwards [hlim, hSS] with ω h1 h2 hωS using h1 (h2 hωS)

/-- The protected set of forward member data matters only up to null sets. -/
theorem hasFCK2CapForwardMembers_mono {m : MeasurableSpace Ω} {S S' : Set Ω} {X Y : Ω → ℂ} {c : ℂ}
    (hSS : ∀ᵐ ω ∂P, ω ∈ S → ω ∈ S') (h : HasFCK2CapForwardMembers (mΩ := mΩ) P m S' X Y c) :
    HasFCK2CapForwardMembers (mΩ := mΩ) P m S X Y c := by
  obtain ⟨𝓜, Av, τ, h𝓜, hτ, hline, hread, hev⟩ := h
  refine ⟨𝓜, Av, τ, h𝓜, hτ, hline, fun D hD hs => hread D hD ?_, ?_⟩
  · filter_upwards [hs, hSS] with ω h1 h2 hωD using h2 (h1 hωD)
  · filter_upwards [hev, hSS] with ω h1 h2 hωS using h1 (h2 hωS)

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **The Gaussian forward kernel from per-box laws on the physical lines.** As
`FCKerLaw.hasFCK2CapForwardKernel_of_lineLaw`, but the conditional law at the physical line `t` is asked only box by
box, given a σ-algebra `big t m ⊇ 𝓖 t` depending on the box, on disjoint physical boxes `B t m` covering the live
safe event; only `F ∩ lineSafe` has to be a physical event. The forward marks are the glued σ-algebras. -/
theorem hasFCK2CapForwardKernel_of_boxLaw [IsProbabilityMeasure P] {d : PairData Ω} (hd : d.IsMeasGood)
    (hm : ∀ r, Measurable (W r)) (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hmono : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    (hS : ∀ t, MeasurableSet[𝓖 t] (F ∩ lineSafe Qc W U (tsupport ψ) t))
    (hreach : ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < U ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR U ω)
    (B : ℝ≥0 → ℕ → Set Ω) (hdisj : ∀ t, Pairwise (Function.onFun Disjoint (B t)))
    (hBG : ∀ t m, MeasurableSet[𝓖 t] (B t m))
    (hcov : ∀ t, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ lineSafe Qc W U (tsupport ψ) t → ∃ m, ω ∈ B t m)
    (big : ℝ≥0 → ℕ → MeasurableSpace Ω) (hbig : ∀ t m, 𝓖 t ≤ big t m) (hbigm : ∀ t m, big t m ≤ mΩ)
    {X : Ω → ℂ}
    (hline : ∀ t, 0 < t → ∀ m, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ B t m → ω ∈ lineSafe Qc W U (tsupport ψ) t →
      P[X | big t m] ω = cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (Qc t) ω) :
    HasFCK2CapForwardKernel P (fcRetainedDriverFiltration P hd W hm q)
      {ω | ω ∈ F ∧ ω ∈ avoidSet W U ψ q} X (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q)) := by
  classical
  have hBb : ∀ t m, MeasurableSet[big t m] (B t m) := fun t m => hbig t m _ (hBG t m)
  have hUG : ∀ t, MeasurableSet[𝓖 t] (⋃ m, B t m) := fun t => MeasurableSet.iUnion (hBG t)
  let 𝓜 : ℝ≥0 → MeasurableSpace Ω := fun t => glueSigma (𝓖 t) (big t) (B t) (hBb t) (hUG t)
  have h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t := fun t => le_glueSigma (hbig t)
  have h𝓜 : ∀ t, 𝓜 t ≤ mΩ := fun t => glueSigma_le (mΩ := mΩ) (𝓖.le t) (hbigm t)
  set u := bheProc κ ρL ρR W VL VR with hu
  set Av : ℝ≥0 → Set Ω := fun t => {_ω | 0 < t} ∩ (F ∩ lineSafe Qc W U (tsupport ψ) t) with hAv_def
  set K : ℝ≥0 → Ω → ℂ := fun t ω =>
    if ‖cfAt κ W u ψ 1 (Qc t) ω‖ ≤ 1 then cfAt κ W u ψ 1 (Qc t) ω else 0 with hK_def
  have hQm : ∀ t, Measurable (Qc t) := fun t => (hQa t).mono (𝓖.le t) le_rfl
  have hτ := measurable_hitT hQm hc hmono q
  have hAv : ∀ t, MeasurableSet[𝓜 t] (Av t) := fun t =>
    h𝓖𝓜 t _ ((MeasurableSet.const (0 < t)).inter (hS t))
  have hb : ∀ t ω, ω ∈ Av t → ‖K t ω‖ ≤ 1 := fun t ω _ => by
    simp only [hK_def]
    split_ifs with h
    · exact h
    · rw [norm_zero]; exact zero_le_one
  have hKeq : ∀ t ω, ω ∈ Av t → IsForceReg W VL VR U ω → K t ω = cfAt κ W u ψ 1 (Qc t) ω :=
    fun t ω hω hp => by
      have hle := norm_cfAt_le_one_of_isForceReg (κ := κ) u ψ hp hω.2.2.1 hω.2.2.2
      simp only [hK_def, hle, ↓reduceIte]
  have hdet : ∀ t, ∀ᵐ ω ∂P, ω ∈ Av t → P[X | 𝓜 t] ω = K t ω := fun t => by
    rcases eq_or_ne t 0 with rfl | ht
    · exact ae_of_all P fun ω hω => absurd (show (0 : ℝ≥0) < 0 from hω.1) (lt_irrefl 0)
    have hglue : ∀ m, ∀ᵐ ω ∂P, ω ∈ B t m → P[X | 𝓜 t] ω = P[X | big t m] ω := fun m =>
      ae_condExp_glueSigma_eq (hB := hBb t) (hU := hUG t) (𝓖.le t) (hbigm t) (hdisj t) X m
    filter_upwards [hcov t, hreg, ae_all_iff.2 hglue, ae_all_iff.2 (hline t (pos_iff_ne_zero.2 ht))]
      with ω hcv hr hg hl hω
    obtain ⟨m, hmB⟩ := hcv hω.2.1 hω.2.2
    rw [hg m hmB, hl m hω.2.1 hmB hω.2.2, hKeq t ω hω (hr hω.2.1)]
  refine fcCapForwardKernel_of_observed_cuts hd W hm hQa hret hobs hτ
    (fun ω hr t => (le_Qc_iff (hc ω) (hmono ω) hr).symm) h𝓖𝓜 h𝓜 hAv hb hdet ?_ ?_
  · filter_upwards [hreach] with ω hω hS'
    exact hω hS'.1 hS'.2.1
  · filter_upwards [hreach, hreg] with ω hr hp hS'
    obtain ⟨hωF, hav⟩ := hS'
    have hp' := hp hωF
    have hrω := hr hωF hav.1
    have hQt := tendsto_Qc_dyF_hitT (hc ω) (hmono ω) (h0 ω) hrω
    have hsafe := eventually_mem_lineSafe ψ.hasCompactSupport.isCompact (tsupport_subset_H ψ) hp' hav.1 hav.2
      (fun n => dyF n (hitT Qc q ω)) hQt
    have hev : ∀ᶠ n in atTop, ω ∈ Av (dyF n (hitT Qc q ω)) := hsafe.mono fun n hn =>
      ⟨(zero_le (a := hitT Qc q ω)).trans_lt (lt_dyF n _), hωF, hn⟩
    refine ⟨hev, ?_⟩
    have hlim := (tendsto_cfAt_of_isForceReg (κ := κ) (ρL := ρL) (ρR := ρR) (u := u)
      (isBoundedHarmonicExtension_bheProc) ψ hp' hav.1 hav.2 hQt).2
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    exact (hKeq _ ω hn hp').symm

/-- **The corrected member field from per-box member identities on the physical lines** (glued as in
`hasFCK2CapForwardKernel_of_boxLaw`). -/
theorem hasFCK2CapForwardMembers_of_boxMembers [IsProbabilityMeasure P] {d : PairData Ω} (hd : d.IsMeasGood)
    (hm : ∀ r, Measurable (W r)) (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hmono : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (Fb : Finset (ℚ × ℚ × ℚ)) (hFb : ballsK Fb ⊆ QuantumZipper.H)
    (q : ℝ≥0) (hS : ∀ t, MeasurableSet[𝓖 t] (F ∩ lineSafe Qc W U (ballsK Fb) t))
    (hreach : ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < U ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR U ω)
    (B : ℝ≥0 → ℕ → Set Ω) (hdisj : ∀ t, Pairwise (Function.onFun Disjoint (B t)))
    (hBG : ∀ t m, MeasurableSet[𝓖 t] (B t m))
    (hcov : ∀ t, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ lineSafe Qc W U (ballsK Fb) t → ∃ m, ω ∈ B t m)
    (big : ℝ≥0 → ℕ → MeasurableSpace Ω) (hbig : ∀ t m, 𝓖 t ≤ big t m) (hbigm : ∀ t m, big t m ≤ mΩ)
    {X Y : Ω → ℂ} {c : ℂ} (hX : Integrable X P) (hY : Integrable Y P)
    (hline : ∀ t, 0 < t → ∀ m E, MeasurableSet[big t m] E →
      (∀ᵐ ω ∂P, ω ∈ E → (ω ∈ F ∧ ω ∈ lineSafe Qc W U (ballsK Fb) t) ∧ ω ∈ B t m) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P) :
    HasFCK2CapForwardMembers P (fcRetainedDriverFiltration P hd W hm q)
      {ω | ω ∈ F ∧ (q : ℝ≥0∞) < U ω ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)} X Y c := by
  classical
  have hBb : ∀ t m, MeasurableSet[big t m] (B t m) := fun t m => hbig t m _ (hBG t m)
  have hUG : ∀ t, MeasurableSet[𝓖 t] (⋃ m, B t m) := fun t => MeasurableSet.iUnion (hBG t)
  let 𝓜 : ℝ≥0 → MeasurableSpace Ω := fun t => glueSigma (𝓖 t) (big t) (B t) (hBb t) (hUG t)
  have h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t := fun t => le_glueSigma (hbig t)
  have h𝓜 : ∀ t, 𝓜 t ≤ mΩ := fun t => glueSigma_le (mΩ := mΩ) (𝓖.le t) (hbigm t)
  set Av : ℝ≥0 → Set Ω := fun t => {_ω | 0 < t} ∩ (F ∩ lineSafe Qc W U (ballsK Fb) t) with hAv_def
  have hQm : ∀ t, Measurable (Qc t) := fun t => (hQa t).mono (𝓖.le t) le_rfl
  have hτ := measurable_hitT hQm hc hmono q
  have hAv : ∀ t, MeasurableSet[𝓜 t] (Av t) := fun t =>
    h𝓖𝓜 t _ ((MeasurableSet.const (0 < t)).inter (hS t))
  have hline' : ∀ t E, MeasurableSet[𝓜 t] E → (∀ᵐ ω ∂P, ω ∈ E → ω ∈ Av t) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P := by
    intro t E hE hEA
    rcases eq_or_ne t 0 with rfl | ht
    · have hE0 : P E = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hEA] with ω hω hωE
        exact lt_irrefl 0 (show (0 : ℝ≥0) < 0 from (hω hωE).1)
      rw [setIntegral_measure_zero _ hE0, setIntegral_measure_zero _ hE0, mul_zero]
    · refine setIntegral_eq_of_glueSigma (hB := hBb t) (hU := hUG t) (𝓖.le t) (hbigm t) (hdisj t) hX hY
        (A := F ∩ lineSafe Qc W U (ballsK Fb) t) ?_ (fun m E' hE' hE'A =>
          hline t (pos_iff_ne_zero.2 ht) m E' hE' hE'A) hE (hEA.mono fun ω hω hωE => (hω hωE).2)
      filter_upwards [hcov t] with ω hω hA using hω hA.1 hA.2
  refine ⟨𝓜, Av, hitT Qc q, h𝓜, hτ, hline', ?_, ?_⟩
  · intro D hD hs n k
    refine fcCap_censored_versions_of_observed_cuts hd W hm hQa hret hobs
      (fun ω hr t => (le_Qc_iff (hc ω) (hmono ω) hr).symm) h𝓖𝓜 hAv hD ?_ n k
    filter_upwards [hs, hreach] with ω hsω hr hωD
    exact hr (hsω hωD).1 (hsω hωD).2.1
  · filter_upwards [hreach, hreg] with ω hr hp hS'
    obtain ⟨hωF, hqU, hdis⟩ := hS'
    have hQt := tendsto_Qc_dyF_hitT (hc ω) (hmono ω) (h0 ω) (hr hωF hqU)
    have hsafe := eventually_mem_lineSafe (isCompact_ballsK Fb) hFb (hp hωF) hqU hdis
      (fun n => dyF n (hitT Qc q ω)) hQt
    exact hsafe.mono fun n hn => ⟨(zero_le (a := hitT Qc q ω)).trans_lt (lt_dyF n _), hωF, hn⟩

end Forward

end InteractingSLE.Restart.FCPlumb.FCKerC
