import HigherDimLQGMetric.LogEnergy.DecayMoment
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

def decayKernelXFull {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (p : ℝ × Rd d × Rd d) : Rd d [×n]→L[ℝ] ℝ :=
  (iteratedFDeriv ℝ n (decayLocalKernel ha hb) p).compContinuousLinearMap
    (fun _ => ((LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).toContinuousLinearMap.comp
      (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap))

theorem decayKernelXFull_eq {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ) (x u : Rd d) :
    decayKernelXFull ha (ha.trans hab) n (ε,x,u) =
      decayKernelXDeriv ha (ha.trans hab) ε n (x,u) := by
  let g : Rd d →L[ℝ] (ℝ × Rd d × Rd d) :=
    (LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).toContinuousLinearMap.comp
      (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap
  have h := iteratedFDeriv_comp_affine_local (decayLocalKernel ha (ha.trans hab))
    g (ε, (0:Rd d),u) x n
    (by simpa [g] using decayLocalKernel_contDiffAt_small ha hab (ε,x,u) hε)
  change _ = iteratedFDeriv ℝ n
    (fun y : Rd d => decayLocalKernelSpatial ha (ha.trans hab) ε (y,u)) x
  simpa [decayKernelXFull, decayKernelXDeriv, decayLocalKernelSpatial, g] using h.symm

theorem decayKernelXFull_contDiffAt {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ)
    (p : ℝ × Rd d × Rd d) (hε : p.1 ∈ Set.Icc (0:ℝ) (a/(8*b))) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayKernelXFull ha (ha.trans hab) n) p := by
  let g : Rd d →L[ℝ] (ℝ × Rd d × Rd d) :=
    (LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).toContinuousLinearMap.comp
      (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap
  let T : ((ℝ × Rd d × Rd d) [×n]→L[ℝ] ℝ) →L[ℝ]
      (Rd d [×n]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => g)
  have hF := decayLocalKernel_contDiffAt_small ha hab p hε
  have hD : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (iteratedFDeriv ℝ n (decayLocalKernel ha (ha.trans hab))) p :=
    hF.iteratedFDeriv_right (by simp)
  exact (T.contDiff.contDiffAt.comp p hD)

theorem decayKernelXFull_zero {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ) (x u : Rd d) :
    decayKernelXFull ha (ha.trans hab) n (0,x,u) = 0 := by
  rw [decayKernelXFull_eq ha hab (show (0:ℝ) ∈ Set.Icc 0 (a/(8*b)) by
    exact ⟨le_rfl, (div_pos ha (mul_pos (by norm_num) (ha.trans hab))).le⟩)]
  simp [decayKernelXDeriv, decayLocalKernelSpatial_zero]

theorem decayKernelXDeriv_u_deriv_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ x u : Rd d, x ∈ annCl 0 (a/2) (2*b) →
        u ∈ Metric.closedBall 0 (2*b) →
        ‖iteratedFDeriv ℝ m
          (fun v : Rd d => decayKernelXDeriv ha (ha.trans hab) ε n (x,v)) u‖ ≤ C*ε := by
  let hb : 0 < b := ha.trans hab
  let ε₀ : ℝ := a/(8*b)
  let Kx : Set (Rd d) := annCl 0 (a/2) (2*b)
  let Ku : Set (Rd d) := Metric.closedBall 0 (2*b)
  let S : Set (Rd d × Rd d) := Kx ×ˢ Ku
  let slab : Set (ℝ × Rd d × Rd d) := Set.Icc 0 ε₀ ×ˢ S
  have hKx : IsCompact Kx := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Rd d) (2*b))
      (isClosed_annCl 0 (a/2) (2*b))
    intro x hx
    change a/2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 2*b at hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have hS : IsCompact S := hKx.prod (isCompact_closedBall 0 (2*b))
  have hslab : IsCompact slab := isCompact_Icc.prod hS
  have hsmooth : ∀ p ∈ slab,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (decayKernelXFull ha hb n) p := by
    intro p hp
    exact decayKernelXFull_contDiffAt ha hab n p (by simpa [slab, ε₀] using hp.1)
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_lipschitz
    (decayKernelXFull ha hb n) m slab hslab hsmooth
  refine ⟨C, hC, ?_⟩
  intro ε hε x u hx hu
  have hε₀ : 0 ≤ ε₀ := le_of_lt (div_pos ha (mul_pos (by norm_num) hb))
  have hseg : segment ℝ (0, (x,u)) (ε, (x,u)) ⊆ slab := by
    have hconv : Convex ℝ (Set.Icc (0:ℝ) ε₀ ×ˢ ({(x,u)} : Set (Rd d × Rd d))) :=
      Convex.prod (convex_Icc 0 ε₀) (convex_singleton (x,u))
    intro z hz
    have hz' := hconv.segment_subset
      (show (0, (x,u)) ∈ Set.Icc (0:ℝ) ε₀ ×ˢ ({(x,u)} : Set (Rd d × Rd d))
        from ⟨⟨le_rfl, hε₀⟩, rfl⟩)
      (show (ε, (x,u)) ∈ Set.Icc (0:ℝ) ε₀ ×ˢ ({(x,u)} : Set (Rd d × Rd d))
        from ⟨by simpa [ε₀] using hε, rfl⟩) hz
    exact ⟨hz'.1, hz'.2 ▸ ⟨hx,hu⟩⟩
  have hnorm : ‖(ε, (x,u)) - ((0:ℝ), (x,u))‖ = ε := by
    simp [Prod.norm_def, abs_of_nonneg hε.1, hε.1]
  have hfull := hbound (0, (x,u)) (ε, (x,u)) hseg
  rw [hnorm] at hfull
  let g : Rd d →ₗᵢ[ℝ] (ℝ × Rd d × Rd d) :=
    (LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).comp
      (LinearIsometry.inr ℝ (Rd d) (Rd d))
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) ε₀) :
      iteratedFDeriv ℝ m (fun v : Rd d => decayKernelXFull ha hb n (t,x,v)) u =
        (iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (t,x,u)).compContinuousLinearMap
          (fun _ => g.toContinuousLinearMap) := by
    have h := iteratedFDeriv_comp_affine_local (decayKernelXFull ha hb n)
      g.toContinuousLinearMap (t,x,(0:Rd d)) u m
      (by simpa [g, ε₀] using decayKernelXFull_contDiffAt ha hab n (t,x,u) ht)
    simpa [g] using h
  have hzero : iteratedFDeriv ℝ m
      (fun v : Rd d => decayKernelXFull ha hb n (0,x,v)) u = 0 := by
    have heq : (fun v : Rd d => decayKernelXFull ha hb n (0,x,v)) = 0 := by
      funext v
      exact decayKernelXFull_zero ha hab n x v
    rw [heq]
    exact congrFun (iteratedFDeriv_fun_zero (𝕜:=ℝ)
      (E:=Rd d) (F:=Rd d [×n]→L[ℝ] ℝ) (n:=m)) u
  have hsub :
      (iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (ε,x,u)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap) -
      (iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (0,x,u)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap) =
      (iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (ε,x,u) -
       iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (0,x,u)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap) := by
    ext v
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hfun : (fun v : Rd d => decayKernelXDeriv ha hb ε n (x,v)) =
      (fun v : Rd d => decayKernelXFull ha hb n (ε,x,v)) := by
    funext v
    exact (decayKernelXFull_eq ha hab hε n x v).symm
  rw [hfun]
  calc
    ‖iteratedFDeriv ℝ m (fun v : Rd d => decayKernelXFull ha hb n (ε,x,v)) u‖ =
      ‖iteratedFDeriv ℝ m (fun v : Rd d => decayKernelXFull ha hb n (ε,x,v)) u -
        iteratedFDeriv ℝ m (fun v : Rd d => decayKernelXFull ha hb n (0,x,v)) u‖ := by
          rw [hzero, sub_zero]
    _ = ‖(iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (ε,x,u) -
       iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (0,x,u)).compContinuousLinearMap
        (fun _ => g.toContinuousLinearMap)‖ := by
      rw [hg ε (by simpa [ε₀] using hε), hg 0 ⟨le_rfl,hε₀⟩, hsub]
    _ ≤ ‖iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (ε,x,u) -
       iteratedFDeriv ℝ m (decayKernelXFull ha hb n) (0,x,u)‖ := by
      exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => g)
    _ ≤ C*ε := hfull
end HigherDimLQGMetric
