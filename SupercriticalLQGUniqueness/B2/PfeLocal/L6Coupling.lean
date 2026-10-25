import SupercriticalLQGUniqueness.B2.PfeLocal.L6Weights
import LQGMetric.Papers.DFGPS.L2_17Core3J

 

















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric

 
abbrev L6S : Type := CoordJ → ℝ
 
abbrev L6T1 : Type := L5Code → ℝ≥0∞
 
abbrev L6T2 : Type := L5Code × ℕ → ℝ≥0∞
 

abbrev L6Lam (R : ℝ) : Type := L6S × (L6T1 × (L6T1 × C(L6K R, ℝ)))
 
abbrev L6Y : Type := L6S × (L6T1 × L6T2)

instance l6Lam_scT (R : ℝ) : SecondCountableTopology (L6Lam R) := inferInstance
instance l6Lam_cm (R : ℝ) : TopologicalSpace.IsCompletelyMetrizableSpace (L6Lam R) :=
  inferInstance
instance l6Lam_polish (R : ℝ) : PolishSpace (L6Lam R) := {}
instance l6Lam_borel (R : ℝ) : BorelSpace (L6Lam R) := Prod.borelSpace
instance l6Y_scT : SecondCountableTopology L6Y := inferInstance
instance l6Y_cm : TopologicalSpace.IsCompletelyMetrizableSpace L6Y := inferInstance
instance l6Y_polish : PolishSpace L6Y := {}
instance l6Y_borel : BorelSpace L6Y := Prod.borelSpace
instance l6Xi_scT (R : ℝ) : SecondCountableTopology (L6Lam R × L6Y) := inferInstance
instance l6Xi_cm (R : ℝ) : TopologicalSpace.IsCompletelyMetrizableSpace (L6Lam R × L6Y) :=
  inferInstance
instance l6Xi_polish (R : ℝ) : PolishSpace (L6Lam R × L6Y) := {}
instance l6Xi_borel (R : ℝ) : BorelSpace (L6Lam R × L6Y) := Prod.borelSpace

 
theorem l6_isTight_of_compactSpace {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [CompactSpace T] (S : Set (Measure T)) : IsTightMeasureSet S :=
  isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε _ =>
    ⟨univ, isCompact_univ, fun μ _ => by simp⟩

 
def l6Yn {Ω' : Type} (hN : ℕ → Ω' → DistC) (An : ℕ → DistC → L6T1) (Bn : ℕ → DistC → L6T2) (n : ℕ)
    (ω : Ω') : L6Y :=
  (pairJ ⊤ (hN n ω), (An n (hN n ω), Bn n (hN n ω)))

 
theorem l6_exists_coupling {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {μ : Measure DistC} [IsProbabilityMeasure μ] {R : ℝ}
    {Λ : Ω' → L6Lam R} (hΛ : Measurable Λ) {hN : ℕ → Ω' → DistC}
    (hNm : ∀ n, Measurable (hN n)) (hNlaw : ∀ n, P'.map (hN n) = μ)
    {An : ℕ → DistC → L6T1} {Bn : ℕ → DistC → L6T2} (hAn : ∀ n, Measurable (An n))
    (hBn : ∀ n, Measurable (Bn n)) (𝒢 ℋ : {m : MeasurableSpace L6S // m ≤ MeasurableSpace.pi})
    (hind : ∀ n, Indep (𝒢.1.comap (pairJ ⊤) ⊔ MeasurableSpace.comap (An n) inferInstance)
      (ℋ.1.comap (pairJ ⊤) ⊔ MeasurableSpace.comap (Bn n) inferInstance) μ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (μs : ℕ → ProbabilityMeasure (L6Lam R × L6Y))
      (ρ : ProbabilityMeasure (L6Lam R × L6Y)),
      (∀ n, (μs n : Measure (L6Lam R × L6Y)) =
        P'.map fun ω => (Λ ω, l6Yn hN An Bn (ψ n) ω)) ∧
      Tendsto μs atTop (𝓝 ρ) ∧
      (ρ : Measure (L6Lam R × L6Y)).map Prod.fst = P'.map Λ ∧
      Indep (𝒢.1.comap (fun p : L6Lam R × L6Y => p.2.1) ⊔
          MeasurableSpace.comap (fun p : L6Lam R × L6Y => p.2.2.1) inferInstance)
        (ℋ.1.comap (fun p : L6Lam R × L6Y => p.2.1) ⊔
          MeasurableSpace.comap (fun p : L6Lam R × L6Y => p.2.2.2) inferInstance)
        (ρ : Measure (L6Lam R × L6Y)) := by
  have hX : Measurable (pairJ ⊤ : DistC → L6S) := measurable_pairJ ⊤
  have hJ : ∀ n, Measurable fun g : DistC => (pairJ ⊤ g, (An n g, Bn n g)) := fun n =>
    hX.prodMk ((hAn n).prodMk (hBn n))
  have hYm : ∀ n, Measurable (l6Yn hN An Bn n) := fun n => (hJ n).comp (hNm n)
  have hlawY : ∀ n, P'.map (l6Yn hN An Bn n) =
      μ.map fun g : DistC => (pairJ ⊤ g, (An n g, Bn n g)) := fun n => by
    rw [← hNlaw n, Measure.map_map (hJ n) (hNm n)]; rfl
  
  have htight : IsTightMeasureSet (range fun n => P'.map (l6Yn hN An Bn n)) := by
    refine IsTightMeasureSet.prodMk ?_ ?_
    · refine (isTightMeasureSet_singleton (μ := μ.map (pairJ ⊤))).subset ?_
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine mem_singleton_iff.2 ?_
      show (P'.map (l6Yn hN An Bn n)).fst = _
      rw [hlawY n]
      exact Measure.fst_map_prodMk hX ((hAn n).prodMk (hBn n))
    · exact l6_isTight_of_compactSpace _
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ := DFGPS.L217.exists_limit_coupling hΛ hYm htight
  set μs : ℕ → ProbabilityMeasure (L6Lam R × L6Y) := fun n =>
    ⟨P'.map fun ω => (Λ ω, l6Yn hN An Bn (ψ n) ω),
      (Measure.isProbabilityMeasure_map_iff (hΛ.prodMk (hYm (ψ n))).aemeasurable).2
        inferInstance⟩ with hμsdef
  refine ⟨ψ, hψ, μs, ρ, fun n => rfl, hlim, hmarg, ?_⟩
  
  set ρ' : ProbabilityMeasure L6Y := ρ.map Prod.snd with hρ'
  have hlim' : Tendsto (fun n => (μs n).map Prod.snd) atTop (𝓝 ρ') :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_snd
  have hsnd : ∀ n, ((μs n).map Prod.snd : Measure L6Y) =
      μ.map fun g : DistC => (pairJ ⊤ g, (An (ψ n) g, Bn (ψ n) g)) := fun n => by
    rw [ProbabilityMeasure.toMeasure_map, ← hlawY (ψ n)]
    exact Measure.snd_map_prodMk hΛ (hYm _)
  have hlim'' : Tendsto (β := ProbabilityMeasure L6Y)
      (fun n => (⟨μ.map fun g : DistC => (pairJ ⊤ g, (An (ψ n) g, Bn (ψ n) g)),
        (Measure.isProbabilityMeasure_map_iff (hJ (ψ n)).aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure L6Y)) atTop (𝓝 ρ') :=
    hlim'.congr fun n => Subtype.ext (hsnd n)
  have hmarg' : (ρ' : Measure L6Y).map Prod.fst = μ.map (pairJ ⊤) := by
    have h1 : Tendsto (fun n => ((μs n).map Prod.snd).map Prod.fst) atTop
        (𝓝 (ρ'.map Prod.fst)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim' continuous_fst
    have hc : ∀ n, ((μs n).map Prod.snd).map Prod.fst =
        (⟨μ.map (pairJ ⊤), (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2
          inferInstance⟩ : ProbabilityMeasure L6S) := fun n => by
      refine Subtype.ext ?_
      change (((μs n).map Prod.snd : Measure L6Y)).map Prod.fst = μ.map (pairJ ⊤)
      rw [hsnd n]
      exact Measure.fst_map_prodMk hX ((hAn _).prodMk (hBn _))
    simp only [hc] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    rw [← ProbabilityMeasure.toMeasure_map, this]
    rfl
  have H := DFGPS.L217.indep_of_tendsto_coupling (P := μ) hX (An := fun n => An (ψ n))
    (Bn := fun n => Bn (ψ n)) (fun n => hAn _) (fun n => hBn _) hlim'' hmarg' 𝒢 ℋ
    (fun n => hind (ψ n))
  
  rw [Indep_iff] at H ⊢
  intro t₁ t₂ ht₁ ht₂
  have e₁ : MeasurableSet[(𝒢.1.comap (Prod.fst : L6Y → L6S) ⊔
      MeasurableSpace.comap (fun q : L6Y => q.2.1) inferInstance).comap Prod.snd] t₁ := by
    have : 𝒢.1.comap (fun p : L6Lam R × L6Y => p.2.1) ⊔
        MeasurableSpace.comap (fun p : L6Lam R × L6Y => p.2.2.1) inferInstance =
        (𝒢.1.comap (Prod.fst : L6Y → L6S) ⊔
          MeasurableSpace.comap (fun q : L6Y => q.2.1) inferInstance).comap Prod.snd := by
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
      rfl
    rw [← this]; exact ht₁
  have e₂ : MeasurableSet[(ℋ.1.comap (Prod.fst : L6Y → L6S) ⊔
      MeasurableSpace.comap (fun q : L6Y => q.2.2) inferInstance).comap Prod.snd] t₂ := by
    have : ℋ.1.comap (fun p : L6Lam R × L6Y => p.2.1) ⊔
        MeasurableSpace.comap (fun p : L6Lam R × L6Y => p.2.2.2) inferInstance =
        (ℋ.1.comap (Prod.fst : L6Y → L6S) ⊔
          MeasurableSpace.comap (fun q : L6Y => q.2.2) inferInstance).comap Prod.snd := by
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
      rfl
    rw [← this]; exact ht₂
  obtain ⟨s₁, hs₁, rfl⟩ := e₁
  obtain ⟨s₂, hs₂, rfl⟩ := e₂
  have hm₁ : MeasurableSet s₁ :=
    (sup_le ((MeasurableSpace.comap_mono 𝒢.2).trans measurable_fst.comap_le)
      (measurable_fst.comp measurable_snd).comap_le) s₁ hs₁
  have hm₂ : MeasurableSet s₂ :=
    (sup_le ((MeasurableSpace.comap_mono ℋ.2).trans measurable_fst.comap_le)
      (measurable_snd.comp measurable_snd).comap_le) s₂ hs₂
  have h := H s₁ s₂ hs₁ hs₂
  rw [hρ', ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_snd (hm₁.inter hm₂),
    Measure.map_apply measurable_snd hm₁, Measure.map_apply measurable_snd hm₂] at h
  exact h

end SupercriticalLQGUniqueness.B2.PfeLocal
