import HigherDimLQGMetric.LogEnergy.DecaySlice
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

def decayKernelXDeriv {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (n : ℕ) (z : Rd d × Rd d) : Rd d [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun x : Rd d => decayLocalKernelSpatial ha hb ε (x,z.2)) z.1

theorem decayKernelXDeriv_eq_full {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ) (z : Rd d × Rd d) :
    decayKernelXDeriv ha (ha.trans hab) ε n z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ n (decayLocalKernelSpatial ha (ha.trans hab) ε) z)
        (fun _ => (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap) := by
  let g : Rd d →L[ℝ] (Rd d × Rd d) :=
    (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap
  have hsmooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayLocalKernelSpatial ha (ha.trans hab) ε) z :=
    (decayLocalKernelSpatial_contDiff (d:=d) ha hab hε).contDiffAt
  have h := iteratedFDeriv_comp_affine_local
    (decayLocalKernelSpatial ha (ha.trans hab) ε) g
    ((0 : Rd d), z.2) z.1 n (by simpa [g] using hsmooth)
  simpa [decayKernelXDeriv, g] using h

theorem decayKernelXDeriv_continuous {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (n : ℕ) :
    Continuous (decayKernelXDeriv (d:=d) ha (ha.trans hab) ε n) := by
  let g : Rd d →L[ℝ] (Rd d × Rd d) :=
    (LinearIsometry.inl ℝ (Rd d) (Rd d)).toContinuousLinearMap
  let T : ((Rd d × Rd d) [×n]→L[ℝ] ℝ) →L[ℝ]
      (Rd d [×n]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => g)
  have hfull : Continuous
      (iteratedFDeriv ℝ n (decayLocalKernelSpatial ha (ha.trans hab) ε)) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      (decayLocalKernelSpatial_contDiff (d:=d) ha hab hε)
  have heq : decayKernelXDeriv ha (ha.trans hab) ε n =
      T ∘ iteratedFDeriv ℝ n (decayLocalKernelSpatial ha (ha.trans hab) ε) := by
    funext z
    simpa [T, g] using decayKernelXDeriv_eq_full ha hab hε n z
  rw [heq]
  exact T.continuous.comp hfull

theorem decayKernelXDeriv_global_bound {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ z : Rd d × Rd d,
        ‖decayKernelXDeriv ha (ha.trans hab) ε n z‖ ≤ C*ε := by
  obtain ⟨C, hC, hbound⟩ := decayLocalKernelSpatial_global_deriv_bound (d:=d) ha hab n
  refine ⟨C, hC, ?_⟩
  intro ε hε z
  have hsmooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayLocalKernelSpatial ha (ha.trans hab) ε) z :=
    (decayLocalKernelSpatial_contDiff (d:=d) ha hab hε).contDiffAt
  exact (iteratedFDeriv_prod_slice_left_norm_le _ z.1 z.2 n hsmooth).trans
    (hbound ε hε z)

def decayKernelXDerivWeighted {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (ψ : TestRd d) (n : ℕ)
    (x u : Rd d) : Rd d [×n]→L[ℝ] ℝ :=
  (ψ u) • decayKernelXDeriv ha hb ε n (x,u)

theorem decayKernelXDerivWeighted_integrable {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (ψ : TestRd d) (n : ℕ) (x : Rd d) :
    Integrable (decayKernelXDerivWeighted ha (ha.trans hab) ε ψ n x) := by
  obtain ⟨C, hC, hbound⟩ := decayKernelXDeriv_global_bound (d:=d) ha hab n
  have hcont : Continuous (decayKernelXDerivWeighted ha (ha.trans hab) ε ψ n x) := by
    change Continuous (fun u : Rd d =>
      (ψ u) • decayKernelXDeriv ha (ha.trans hab) ε n (x,u))
    have hk := (decayKernelXDeriv_continuous (d:=d) ha hab hε n).comp
      (show Continuous (fun u : Rd d => (x,u)) by fun_prop)
    exact ψ.continuous.smul hk
  have hint : Integrable (fun u : Rd d => (C*ε) * |ψ u|) := by
    exact (integrable_testOn ψ).norm.const_mul _
  apply Integrable.mono' hint hcont.aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖(ψ u) • decayKernelXDeriv ha (ha.trans hab) ε n (x,u)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |ψ u| * ‖decayKernelXDeriv ha (ha.trans hab) ε n (x,u)‖ ≤
          |ψ u| * (C*ε) :=
        mul_le_mul_of_nonneg_left (hbound ε hε (x,u)) (abs_nonneg _)
      _ = C*ε*|ψ u| := by ring

theorem decayKernelXDerivWeighted_fderiv {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (ψ : TestRd d) (n : ℕ)
    (x u : Rd d) :
    fderiv ℝ (fun y : Rd d => decayKernelXDerivWeighted ha hb ε ψ n y u) x =
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => Rd d) ℝ)
          (decayKernelXDerivWeighted ha hb ε ψ (n+1) x u) := by
  let H : Rd d → ℝ := fun y => decayLocalKernelSpatial ha hb ε (y,u)
  change fderiv ℝ (fun y : Rd d => (ψ u) • iteratedFDeriv ℝ n H y) x = _
  rw [show (fun y : Rd d => (ψ u) • iteratedFDeriv ℝ n H y) =
      (ψ u) • (iteratedFDeriv ℝ n H) from rfl]
  rw [fderiv_const_smul_field, fderiv_iteratedFDeriv]
  simp only [Pi.smul_apply, Function.comp_apply]
  change (ψ u) •
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => Rd d) ℝ)
      (iteratedFDeriv ℝ (n+1) H x) = _
  change _ = (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (n+1) => Rd d) ℝ)
      ((ψ u) • iteratedFDeriv ℝ (n+1) H x)
  rw [map_smul]

def decayKernelMoment {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (ψ : TestRd d) (n : ℕ)
    (x : Rd d) : Rd d [×n]→L[ℝ] ℝ :=
  ∫ u : Rd d, decayKernelXDerivWeighted ha hb ε ψ n x u

theorem decayKernelMoment_hasFDerivAt {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (ψ : TestRd d) (n : ℕ)
    (x : Rd d) :
    HasFDerivAt (decayKernelMoment ha (ha.trans hab) ε ψ n)
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => Rd d) ℝ)
          (decayKernelMoment ha (ha.trans hab) ε ψ (n+1) x)) x := by
  let hb : 0 < b := ha.trans hab
  let F : Rd d → Rd d → (Rd d [×n]→L[ℝ] ℝ) :=
    decayKernelXDerivWeighted ha hb ε ψ n
  let F' : Rd d → Rd d → (Rd d →L[ℝ] (Rd d [×n]→L[ℝ] ℝ)) :=
    fun y u => fderiv ℝ (fun z => F z u) y
  obtain ⟨C, hC, hbound⟩ := decayKernelXDeriv_global_bound (d:=d) ha hab (n+1)
  let bound : Rd d → ℝ := fun u => (C*ε)*|ψ u|
  have hboundInt : Integrable bound := (integrable_testOn ψ).norm.const_mul _
  have hFint : ∀ y, Integrable (F y) := by
    intro y
    exact decayKernelXDerivWeighted_integrable ha hab hε ψ n y
  have hF'meas : AEStronglyMeasurable (F' x) volume := by
    let curry := continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n+1) => Rd d) ℝ
    have hnext : Integrable
        (decayKernelXDerivWeighted ha hb ε ψ (n+1) x) :=
      decayKernelXDerivWeighted_integrable ha hab hε ψ (n+1) x
    have h := curry.continuous.comp_aestronglyMeasurable hnext.aestronglyMeasurable
    have heq : F' x = fun u => curry (decayKernelXDerivWeighted ha hb ε ψ (n+1) x u) := by
      funext u
      exact decayKernelXDerivWeighted_fderiv ha hb ε ψ n x u
    rw [heq]
    exact h
  have hbound' : ∀ᵐ u : Rd d ∂volume, ∀ y ∈ (Set.univ : Set (Rd d)),
      ‖F' y u‖ ≤ bound u := ae_of_all _ fun u y _ => by
    change ‖fderiv ℝ (fun z => F z u) y‖ ≤ _
    rw [show fderiv ℝ (fun z => F z u) y =
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => Rd d) ℝ)
          (decayKernelXDerivWeighted ha hb ε ψ (n+1) y u) from
      decayKernelXDerivWeighted_fderiv ha hb ε ψ n y u]
    rw [LinearIsometryEquiv.norm_map]
    change ‖(ψ u) • decayKernelXDeriv ha hb ε (n+1) (y,u)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |ψ u| * ‖decayKernelXDeriv ha hb ε (n+1) (y,u)‖ ≤
          |ψ u| * (C*ε) :=
        mul_le_mul_of_nonneg_left (hbound ε hε (y,u)) (abs_nonneg _)
      _ = bound u := by dsimp [bound]; ring
  have hdiff : ∀ᵐ u : Rd d ∂volume,
      ∀ y ∈ (Set.univ : Set (Rd d)), HasFDerivAt (fun z => F z u) (F' y u) y :=
    ae_of_all _ fun u y _ => by
      have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Rd d => decayLocalKernelSpatial ha hb ε (z,u)) := by
        exact (decayLocalKernelSpatial_contDiff (d:=d) ha hab hε).comp (by fun_prop)
      have hdn : Differentiable ℝ
          (iteratedFDeriv ℝ n
            (fun z : Rd d => decayLocalKernelSpatial ha hb ε (z,u))) :=
        hH.differentiable_iteratedFDeriv
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
      exact (hdn.const_smul (ψ u)).differentiableAt.hasFDerivAt
  have hLip : ∀ᵐ u : Rd d ∂volume,
      LipschitzOnWith (Real.nnabs (bound u)) (fun y => F y u) Set.univ :=
    (hdiff.and hbound').mono fun u ⟨hDu, hBu⟩ => by
      refine (convex_univ : Convex ℝ (Set.univ : Set (Rd d)))
        |>.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
          (fun y _ => (hDu y (Set.mem_univ y)).hasFDerivWithinAt) ?_
      intro y _
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
      exact (hBu y (Set.mem_univ y)).trans (le_abs_self _)
  obtain ⟨hF'int, h⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    (F:=F) (F':=F' x) (bound:=bound) (s:=Set.univ)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hFint y).aestronglyMeasurable)
    (hFint x) hF'meas hLip hboundInt
    (hdiff.mono (fun u hu => hu x (Set.mem_univ x)))
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (n+1) => Rd d) ℝ
  have hnext : Integrable
      (decayKernelXDerivWeighted ha hb ε ψ (n+1) x) :=
    decayKernelXDerivWeighted_integrable ha hab hε ψ (n+1) x
  have heqFun : F' x = fun u => curry (decayKernelXDerivWeighted ha hb ε ψ (n+1) x u) := by
    funext u
    exact decayKernelXDerivWeighted_fderiv ha hb ε ψ n x u
  have heqDer : (∫ u, F' x u) =
      curry (∫ u, decayKernelXDerivWeighted ha hb ε ψ (n+1) x u) := by
    ext v w
    have hleftInt : Integrable (fun u => (F' x u) v) := by
      have hmeas : AEStronglyMeasurable (fun u => (F' x u) v) volume :=
        Continuous.comp_aestronglyMeasurable
          ((ContinuousLinearMap.apply ℝ (Rd d [×n]→L[ℝ] ℝ) v).continuous)
          hF'int.aestronglyMeasurable
      apply Integrable.mono' (hF'int.norm.const_mul ‖v‖) hmeas
      exact ae_of_all _ fun u => by
        change ‖(F' x u) v‖ ≤ ‖v‖ * ‖F' x u‖
        exact (F' x u).le_opNorm v |>.trans_eq (mul_comm _ _)
    rw [ContinuousLinearMap.integral_apply hF'int v,
      ContinuousMultilinearMap.integral_apply hleftInt w,
      continuousMultilinearCurryLeftEquiv_apply,
      ContinuousMultilinearMap.integral_apply hnext (Fin.cons v w)]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      change ((F' x u) v) w = _
      rw [show F' x u = curry (decayKernelXDerivWeighted ha hb ε ψ (n+1) x u)
        from congrFun heqFun u]
      rfl
  change HasFDerivAt (fun y => ∫ u, F y u)
    (curry (∫ u, decayKernelXDerivWeighted ha hb ε ψ (n+1) x u)) x
  rw [← heqDer]
  exact h
end HigherDimLQGMetric
