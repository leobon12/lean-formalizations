import HigherDimLQGMetric.LogEnergy.DecayCutoff
import HigherDimLQGMetric.LogEnergy.QuantDeriv
set_option autoImplicit false
noncomputable section
open Filter Topology
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

def decayLocalKernel {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : ℝ × Rd d × Rd d) : ℝ :=
  decayAnnCutoff ha hb p.2.1 * decayOuterCutoff hb p.2.2 * logDiff p

theorem decayLocalKernel_contDiffAt {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (p : ℝ × Rd d × Rd d)
    (hx : p.2.1 ≠ 0) (hxu : p.2.1 - p.1 • p.2.2 ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayLocalKernel ha hb) p := by
  have hcx : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Rd d × Rd d => decayAnnCutoff ha hb q.2.1) p := by
    exact (decayAnnCutoff_contDiff ha hb).contDiffAt.comp p (by fun_prop)
  have hcu : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Rd d × Rd d => decayOuterCutoff hb q.2.2) p := by
    exact (decayOuterCutoff_contDiff hb).contDiffAt.comp p (by fun_prop)
  have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) logDiff p :=
    (logDiff_contDiffAt p hx hxu).of_le le_top
  exact (hcx.mul hcu).mul hlog

theorem decayLocalKernel_contDiffAt_outsideX {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (p : ℝ × Rd d × Rd d)
    (hx : p.2.1 ∉ tsupport (decayAnnCutoff ha hb)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayLocalKernel ha hb) p := by
  have hproj : ContinuousAt (fun q : ℝ × Rd d × Rd d => q.2.1) p := by fun_prop
  have hevent : ∀ᶠ q in 𝓝 p, q.2.1 ∉ tsupport (decayAnnCutoff ha hb) :=
    hproj.tendsto.eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds hx)
  have heq : (decayLocalKernel ha hb) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := by
    filter_upwards [hevent] with q hq
    simp [decayLocalKernel, image_eq_zero_of_notMem_tsupport hq]
  exact contDiffAt_const.congr_of_eventuallyEq heq

theorem decayLocalKernel_contDiffAt_outsideU {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (p : ℝ × Rd d × Rd d)
    (hu : p.2.2 ∉ tsupport (decayOuterCutoff hb)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayLocalKernel ha hb) p := by
  have hproj : ContinuousAt (fun q : ℝ × Rd d × Rd d => q.2.2) p := by fun_prop
  have hevent : ∀ᶠ q in 𝓝 p, q.2.2 ∉ tsupport (decayOuterCutoff hb) :=
    hproj.tendsto.eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds hu)
  have heq : (decayLocalKernel ha hb) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := by
    filter_upwards [hevent] with q hq
    simp [decayLocalKernel, image_eq_zero_of_notMem_tsupport hq]
  exact contDiffAt_const.congr_of_eventuallyEq heq

theorem decayLocalKernel_contDiffAt_small {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (p : ℝ × Rd d × Rd d)
    (hε : p.1 ∈ Set.Icc (0:ℝ) (a/(8*b))) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayLocalKernel ha (ha.trans hab)) p := by
  let hb : 0 < b := ha.trans hab
  by_cases hx : p.2.1 ∈ tsupport (decayAnnCutoff ha hb)
  swap
  · exact decayLocalKernel_contDiffAt_outsideX ha hb p hx
  by_cases hu : p.2.2 ∈ tsupport (decayOuterCutoff hb)
  swap
  · exact decayLocalKernel_contDiffAt_outsideU ha hb p hu
  have hKx := decayAnnCutoff_tsupport_subset ha hb hx
  have hKu := decayOuterCutoff_tsupport_subset hb hu
  have hxn : a/2 ≤ ‖p.2.1‖ := by simpa using hKx.1
  have hun : ‖p.2.2‖ ≤ 2*b := by
    simpa [Metric.mem_closedBall] using hKu
  have h0 : p.2.1 ≠ 0 := by
    intro heq
    simp [heq] at hxn
    linarith
  have hsep : p.2.1 - p.1 • p.2.2 ≠ 0 := by
    intro heq
    have heq' : p.2.1 = p.1 • p.2.2 := sub_eq_zero.mp heq
    rw [heq', norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.1] at hxn
    have hε0 : 0 ≤ a/(8*b) := le_of_lt (div_pos ha (by positivity))
    have hbound : p.1 * ‖p.2.2‖ ≤ a/4 := by
      calc
        _ ≤ (a/(8*b)) * (2*b) :=
          mul_le_mul hε.2 hun (norm_nonneg _) hε0
        _ = a/4 := by field_simp; ring
    linarith
  exact decayLocalKernel_contDiffAt ha hb p h0 hsep

def decayLocalKernelSpatial {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (z : Rd d × Rd d) : ℝ := decayLocalKernel ha hb (ε,z)

theorem decayLocalKernelSpatial_zero {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    decayLocalKernelSpatial (d:=d) ha hb 0 = 0 := by
  funext z
  simp [decayLocalKernelSpatial, decayLocalKernel, logDiff]

theorem decayLocalKernelSpatial_deriv_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x u : Rd d, x ∈ annCl 0 (a/2) (2*b) →
        u ∈ Metric.closedBall 0 (2*b) →
        ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
        ‖iteratedFDeriv ℝ n (decayLocalKernelSpatial ha (ha.trans hab) ε) (x,u)‖
          ≤ C * ε := by
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
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayLocalKernel ha hb) p := by
    intro p hp
    exact decayLocalKernel_contDiffAt_small ha hab p (by simpa [slab, ε₀] using hp.1)
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_lipschitz
    (decayLocalKernel ha hb) n slab hslab hsmooth
  refine ⟨C, hC, ?_⟩
  intro x u hx hu ε hε
  have hε₀ : 0 ≤ ε₀ := le_of_lt (div_pos ha (by positivity))
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
  let g : (Rd d × Rd d) →L[ℝ] (ℝ × Rd d × Rd d) :=
    (LinearIsometry.inr ℝ ℝ (Rd d × Rd d)).toContinuousLinearMap
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) ε₀) :
      iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb t) (x,u) =
        (iteratedFDeriv ℝ n (decayLocalKernel ha hb) (t,x,u)).compContinuousLinearMap
          (fun _ => g) := by
    have h := iteratedFDeriv_comp_affine_local (decayLocalKernel ha hb) g
      (t, (0 : Rd d × Rd d)) (x,u) n
      (by simpa [g, ε₀] using
        decayLocalKernel_contDiffAt_small ha hab (t,x,u) ht)
    change iteratedFDeriv ℝ n (fun y => decayLocalKernel ha hb (t,y)) (x,u) = _
    simpa [g] using h
  have hzero : iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb 0) (x,u) = 0 := by
    rw [decayLocalKernelSpatial_zero]
    exact congrFun (iteratedFDeriv_fun_zero (𝕜:=ℝ)
      (E:=Rd d × Rd d) (F:=ℝ) (n:=n)) (x,u)
  have hsub :
      (iteratedFDeriv ℝ n (decayLocalKernel ha hb) (ε,x,u)).compContinuousLinearMap
          (fun _ => g) -
      (iteratedFDeriv ℝ n (decayLocalKernel ha hb) (0,x,u)).compContinuousLinearMap
          (fun _ => g) =
      (iteratedFDeriv ℝ n (decayLocalKernel ha hb) (ε,x,u) -
       iteratedFDeriv ℝ n (decayLocalKernel ha hb) (0,x,u)).compContinuousLinearMap
          (fun _ => g) := by
    ext v
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hnormcomp := ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (iteratedFDeriv ℝ n (decayLocalKernel ha hb) (ε,x,u) -
      iteratedFDeriv ℝ n (decayLocalKernel ha hb) (0,x,u))
    (fun _ => LinearIsometry.inr ℝ ℝ (Rd d × Rd d))
  change ‖iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb ε) (x,u)‖ ≤ C * ε
  calc
    ‖iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb ε) (x,u)‖ =
        ‖iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb ε) (x,u) -
          iteratedFDeriv ℝ n (decayLocalKernelSpatial ha hb 0) (x,u)‖ := by
      rw [hzero, sub_zero]
    _ = ‖(iteratedFDeriv ℝ n (decayLocalKernel ha hb) (ε,x,u) -
       iteratedFDeriv ℝ n (decayLocalKernel ha hb) (0,x,u)).compContinuousLinearMap
          (fun _ => g)‖ := by
      rw [hg ε (by simpa [ε₀] using hε), hg 0 (by exact ⟨le_rfl, hε₀⟩), hsub]
    _ ≤ ‖iteratedFDeriv ℝ n (decayLocalKernel ha hb) (ε,x,u) -
       iteratedFDeriv ℝ n (decayLocalKernel ha hb) (0,x,u)‖ := by
      simpa [g] using hnormcomp
    _ ≤ C * ε := hfull

theorem decayLocalKernelSpatial_contDiff {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayLocalKernelSpatial (d:=d) ha (ha.trans hab) ε) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Rd d × Rd d => (ε,y)) z := by fun_prop
  exact (decayLocalKernel_contDiffAt_small ha hab (ε,z) hε).comp z hm

theorem decayLocalKernelSpatial_tsupport_subset {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) :
    tsupport (decayLocalKernelSpatial (d:=d) ha hb ε) ⊆
      annCl 0 (a/2) (2*b) ×ˢ Metric.closedBall 0 (2*b) := by
  let S : Set (Rd d × Rd d) :=
    annCl 0 (a/2) (2*b) ×ˢ Metric.closedBall 0 (2*b)
  have hsupp : Function.support (decayLocalKernelSpatial ha hb ε) ⊆ S := by
    intro z hz
    have hne : decayLocalKernelSpatial ha hb ε z ≠ 0 := hz
    constructor
    · by_contra hx
      have hx' : z.1 ∉ tsupport (decayAnnCutoff ha hb) :=
        fun hmem => hx (decayAnnCutoff_tsupport_subset ha hb hmem)
      have h0 := image_eq_zero_of_notMem_tsupport hx'
      exact hne (by simp [decayLocalKernelSpatial, decayLocalKernel, h0])
    · by_contra hu
      have hu' : z.2 ∉ tsupport (decayOuterCutoff hb) :=
        fun hmem => hu (decayOuterCutoff_tsupport_subset hb hmem)
      have h0 := image_eq_zero_of_notMem_tsupport hu'
      exact hne (by simp [decayLocalKernelSpatial, decayLocalKernel, h0])
  exact closure_minimal hsupp
    ((isClosed_annCl 0 (a/2) (2*b)).prod Metric.isClosed_closedBall)

theorem decayLocalKernelSpatial_global_deriv_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ z : Rd d × Rd d,
        ‖iteratedFDeriv ℝ n
          (decayLocalKernelSpatial ha (ha.trans hab) ε) z‖ ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ := decayLocalKernelSpatial_deriv_bound ha hab n
  refine ⟨C, hC, ?_⟩
  intro ε hε z
  let S : Set (Rd d × Rd d) :=
    annCl 0 (a/2) (2*b) ×ˢ Metric.closedBall 0 (2*b)
  by_cases hz : z ∈ S
  · exact hbound z.1 z.2 hz.1 hz.2 ε hε
  · have hts : z ∉ tsupport (decayLocalKernelSpatial ha (ha.trans hab) ε) :=
      fun hmem => hz (decayLocalKernelSpatial_tsupport_subset ha (ha.trans hab) ε hmem)
    have hzero : iteratedFDeriv ℝ n
        (decayLocalKernelSpatial ha (ha.trans hab) ε) z = 0 := by
      by_contra hne
      exact hts (support_iteratedFDeriv_subset n (by simpa [Function.mem_support] using hne))
    rw [hzero, norm_zero]
    exact mul_nonneg hC hε.1

end HigherDimLQGMetric
