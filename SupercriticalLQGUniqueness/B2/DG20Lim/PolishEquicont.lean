import SupercriticalLQGUniqueness.B2.DG20Lim.PolishOrder
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed

 





















set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal Distributions CompactConvergenceCLM BoundedContinuousFunction
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
theorem exists_iotaK_eq (φ : TestC) :
    ∃ k, ∃ f : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ), iotaK ⊤ k f = φ := by
  obtain ⟨k, hk⟩ := exists_exhaustK_superset ⊤ φ.hasCompactSupport.isCompact
    φ.tsupport_subset
  exact ⟨k, mkT ⊤ φ hk, by ext; rfl⟩

section Bound

variable (T : ℕ → DistC)

 
def UniformOrderBound : Prop :=
  ∀ k, ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n (f : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ)),
    |T n (iotaK ⊤ k f)| ≤ B * ordSeminorm k N f

variable {T}

theorem UniformOrderBound.exists_bound (hT : UniformOrderBound T) (φ : TestC) :
    ∃ C : ℝ, ∀ n, ‖T n φ‖ ≤ C := by
  obtain ⟨k, f, rfl⟩ := exists_iotaK_eq φ
  obtain ⟨N, B, -, hB⟩ := hT k
  exact ⟨B * ordSeminorm k N f, fun n => by
    rw [Real.norm_eq_abs]
    exact hB n f⟩

 
def UniformOrderBound.seqBCF (hT : UniformOrderBound T) (φ : TestC) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => T n φ)
    (Classical.choose (hT.exists_bound φ)) (Classical.choose_spec (hT.exists_bound φ))

@[simp] theorem UniformOrderBound.seqBCF_apply (hT : UniformOrderBound T)
    (φ : TestC) (n : ℕ) : hT.seqBCF φ n = T n φ := rfl

 
def UniformOrderBound.seqLM (hT : UniformOrderBound T) : TestC →ₗ[ℝ] (ℕ →ᵇ ℝ) where
  toFun := hT.seqBCF
  map_add' φ ψ := by ext n; simp [map_add]
  map_smul' c φ := by ext n; simp [map_smul]

theorem UniformOrderBound.continuous_seqLM_comp_iotaK (hT : UniformOrderBound T)
    (k : ℕ) : Continuous (hT.seqLM ∘ iotaK ⊤ k) := by
  obtain ⟨N, B, hB0, hB⟩ := hT k
  let A : 𝓓^{⊤}_{exhaustK ⊤ k}(ℂ, ℝ) →L[ℝ] (ℕ →ᵇ ℝ) :=
    ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ (hT.seqLM ∘ iotaK ⊤ k)
      (fun f g => by simp [map_add]) (fun c f => by simp [map_smul])
      ⟨Finset.Iic N, B, hB0, fun f => by
        refine (BoundedContinuousFunction.norm_le
          (mul_nonneg hB0 (apply_nonneg _ _))).2 fun n => ?_
        rw [Real.norm_eq_abs]
        exact hB n f⟩
  exact A.continuous

theorem UniformOrderBound.continuous_seqLM (hT : UniformOrderBound T) :
    Continuous hT.seqLM := by
  rw [TestFunction.continuous_iff_continuous_comp (𝕜 := ℝ)]
  intro K hK
  obtain ⟨k, hk⟩ := exists_exhaustK_superset ⊤ K.isCompact (subset_univ _)
  have hEq : (hT.seqLM ∘ TestFunction.ofSupportedIn hK) =
      (hT.seqLM ∘ iotaK ⊤ k) ∘
        (ContDiffMapSupportedIn.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (K₁ := K)
          (K₂ := exhaustK ⊤ k)) := by
    funext f
    simp only [Function.comp_apply]
    congr 1
    ext x
    have hk' : K ≤ exhaustK ⊤ k := hk
    simp [iotaK, hk']
  rw [hEq]
  exact (hT.continuous_seqLM_comp_iotaK k).comp (ContinuousLinearMap.continuous _)

 
theorem equicontinuous_of_uniform_order_bound (hT : UniformOrderBound T) :
    Equicontinuous (fun n (φ : TestC) => T n φ) := by
  intro φ₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hc := hT.continuous_seqLM.continuousAt (x := φ₀)
  filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with φ hφ n
  calc dist (T n φ₀) (T n φ) = dist (hT.seqLM φ₀ n) (hT.seqLM φ n) := rfl
    _ ≤ dist (hT.seqLM φ₀) (hT.seqLM φ) :=
      BoundedContinuousFunction.dist_coe_le_dist n
    _ < ε := by rw [dist_comm]; exact hφ

end Bound

 

theorem tendsto_distC_of_equicontinuous {T : ℕ → DistC} {T₀ : DistC}
    (hEq : Equicontinuous (fun n (φ : TestC) => T n φ))
    (hgen : ∀ j, Tendsto (fun n => T n (distGen ⊤ j)) atTop
      (𝓝 (T₀ (distGen ⊤ j)))) :
    Tendsto T atTop (𝓝 T₀) := by
  have hClosed : IsClosed {φ : TestC | Tendsto (fun n => T n φ) atTop (𝓝 (T₀ φ))} :=
    hEq.isClosed_setOfPred_tendsto (map_continuous T₀)
  have hpt : ∀ φ : TestC, Tendsto (fun n => T n φ) atTop (𝓝 (T₀ φ)) := by
    intro φ
    obtain ⟨k, f, rfl⟩ := exists_iotaK_eq φ
    exact (denseRange_denseSeqK ⊤ k).induction_on f
      (hClosed.preimage (iotaK ⊤ k).continuous) fun j => hgen (k, j)
  rw [UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn]
  intro s hs
  have hs' : IsCompact s := hs
  have hU := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi'
    (𝔖 := {s}) (fun K hK => by rw [mem_singleton_iff.1 hK]; exact hs')
    (fun K _ => hEq.equicontinuousOn K) atTop (fun φ : TestC => T₀ φ)).2 (by
      rw [tendsto_pi_nhds]
      intro x
      exact (hpt x).comp tendsto_id)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hU
  exact hU s (mem_singleton s)

 


theorem exists_uniform_bound_of_tendsto (v : ℕ → ℕ → ℝ≥0∞)
    (hanti : ∀ n {N N' : ℕ}, N ≤ N' → v n N' ≤ v n N)
    (hfin : ∀ n, ∃ N, v n N < ⊤) {N₀ : ℕ} {ℓ : ℝ≥0∞} (hℓ : ℓ < ⊤)
    (hconv : Tendsto (fun n => v n N₀) atTop (𝓝 ℓ)) :
    ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, v n N ≤ ENNReal.ofReal B := by
  classical
  have hlt : ℓ < ℓ + 1 := ENNReal.lt_add_right hℓ.ne one_ne_zero
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds hlt))
  let N' : ℕ → ℕ := fun n => Classical.choose (hfin n)
  have hN' : ∀ n, v n (N' n) < ⊤ := fun n => Classical.choose_spec (hfin n)
  let N : ℕ := N₀ ⊔ (Finset.range n₀).sup N'
  let B' : ℝ≥0∞ := (ℓ + 1) ⊔ (Finset.range n₀).sup fun n => v n (N' n)
  have hB' : B' < ⊤ := by
    refine max_lt (ENNReal.add_lt_top.2 ⟨hℓ, ENNReal.one_lt_top⟩) ?_
    exact (Finset.sup_lt_iff (bot_lt_top : (⊥ : ℝ≥0∞) < ⊤)).2 fun n _ => hN' n
  refine ⟨N, B'.toReal, ENNReal.toReal_nonneg, fun n => ?_⟩
  rw [ENNReal.ofReal_toReal hB'.ne]
  by_cases hn : n₀ ≤ n
  · exact (hanti n le_sup_left).trans ((hn₀ n hn).le.trans le_sup_left)
  · have hmem : n ∈ Finset.range n₀ := Finset.mem_range.2 (lt_of_not_ge hn)
    refine (hanti n (le_sup_of_le_right (Finset.le_sup (f := N') hmem))).trans ?_
    exact (Finset.le_sup (f := fun n => v n (N' n)) hmem).trans le_sup_right

 

theorem tendsto_distC_of_ordCoords {T : ℕ → DistC} {T₀ : DistC}
    {u : ℕ → OrdCoords} {u₀ : OrdCoords}
    (hu : ∀ n, u n = ordCoords (pairJ ⊤ (T n)))
    (hconv : Tendsto u atTop (𝓝 u₀))
    (hfin : ∀ k, ∃ N, u₀ (k, N) < ⊤)
    (hcoord : Tendsto (fun n => pairJ ⊤ (T n)) atTop (𝓝 (pairJ ⊤ T₀))) :
    Tendsto T atTop (𝓝 T₀) := by
  have hBound : UniformOrderBound T := by
    intro k
    obtain ⟨N₀, hN₀⟩ := hfin k
    have hc : Tendsto (fun n => ordCoord k N₀ (pairJ ⊤ (T n))) atTop (𝓝 (u₀ (k, N₀))) := by
      have := (continuous_apply (k, N₀)).continuousAt.tendsto.comp hconv
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hu, ordCoords]
    obtain ⟨N, B, hB0, hB⟩ := exists_uniform_bound_of_tendsto
      (fun n N => ordCoord k N (pairJ ⊤ (T n)))
      (fun n _ _ h => ordCoord_anti k h _)
      (fun n => exists_ordCoord_lt_top (T n) k) hN₀ hc
    exact ⟨N, B, hB0, fun n f => abs_apply_le_of_ordCoord_le (T n) hB0 (hB n) f⟩
  refine tendsto_distC_of_equicontinuous (equicontinuous_of_uniform_order_bound hBound)
    fun j => ?_
  have := (continuous_apply (Finsupp.single j (1 : ℤ))).continuousAt.tendsto.comp hcoord
  simpa only [Function.comp_def, pairJ_single] using this

end SupercriticalLQGUniqueness.B2.DG20Lim
