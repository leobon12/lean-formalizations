import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.BumpScale
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Shape
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ConsumerBridge




 

set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

def tubeDataOf (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ)
    (netRadius : ℝ) (netSites : Finset ℂ) : Objects.CorrectedEvent.TubeData where
  r := C.r
  rho := P.ρ
  alpha := P.α
  K := P.K
  Kpos := by exact_mod_cast hP.K_pos
  orientation := P.n
  psiU := P.ψu
  psiV := P.ψv
  blockRadius := P.s C.r
  lambda := C.lamConst
  A_endpt := C.A_endpt
  mollifier := scaledMollifierTest C.r C.rPos
    (Objects.Tube.TubeParams.quarter' ⟨C.A_sup, C.supPos⟩)
  bump := P.bumpTest C.r C.A_max ⟨C.A_sup, C.supPos⟩ hP C.rPos hSmall
  netRadius := netRadius
  netSites := netSites

theorem tubeDataOf_tubeSet_eq (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    Objects.CorrectedEvent.tubeSet (tubeDataOf C P hP hSmall netRadius netSites) = P.tube C.r := by
  exact tubeSet_eq _ P C.r rfl rfl rfl rfl rfl rfl rfl rfl hwp hP C.rPos

theorem tubeDataOf_tubeV_eq (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) (A : ℝ) :
    Objects.CorrectedEvent.tubeV (tubeDataOf C P hP hSmall netRadius netSites) A = P.nbhd C.r A := by
  exact tubeV_eq _ P C.r A rfl rfl rfl rfl rfl rfl rfl rfl hwp hP C.rPos

theorem tubeDataOf_tube_sub (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    Objects.CorrectedEvent.tubeSet (tubeDataOf C P hP hSmall netRadius netSites) ⊆
      (Objects.CentreZero.uZero P hP C.r C.A_sup C.rPos C.supPos hSmall : Set ℂ) := by
  exact tube_sub_uZero _ P C.r C.A_sup rfl rfl rfl rfl rfl rfl rfl rfl hwp
    hP C.rPos C.supPos hSmall

theorem tubeDataOf_tube_middle (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    Objects.CorrectedEvent.tubeSet (tubeDataOf C P hP hSmall netRadius netSites) ⊆ ball 0 (2.5 * C.r) := by
  exact tube_middle _ P C.r C.A_sup rfl rfl rfl rfl rfl rfl rfl rfl hwp
    hP C.rPos C.supPos hSmall

theorem tubeDataOf_bump_formula (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) (x : ℂ) :
    (tubeDataOf C P hP hSmall netRadius netSites).bump x =
      Objects.CorrectedEvent.bumpFormula (tubeDataOf C P hP hSmall netRadius netSites) C.A_max C.A_sup x := by
  rw [bumpFormula_eq_bump _ P C.r C.A_sup C.A_max C.supPos
    rfl rfl rfl rfl rfl rfl rfl rfl hwp hP C.rPos (by intro y; rfl) x]
  rfl

theorem fZero_eq_tubeDataOf_bump (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ) :
    Objects.CentreZero.fZero P hP C.r C.A_sup C.A_max C.rPos C.supPos hSmall =
      (tubeDataOf C P hP hSmall netRadius netSites).bump := by
  apply TestFunction.ext
  intro x
  change P.bumpAt C.r C.A_max ⟨C.A_sup, C.supPos⟩ 0 x =
    P.bump C.r C.A_max ⟨C.A_sup, C.supPos⟩ x
  simp only [Objects.Tube.TubeParams.bumpAt, sub_zero]

theorem tubeDataOf_mollifier_props (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ) :
    let T := tubeDataOf C P hP hSmall netRadius netSites
    (∀ x : ℂ, 0 ≤ T.mollifier x) ∧
    (∀ x : ℂ, C.A_sup * C.r / 4 ≤ dist x 0 → T.mollifier x = 0) ∧
    (∫ x : ℂ, T.mollifier x) = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact scaledMollifier_nonneg C.r (Objects.Tube.TubeParams.quarter' ⟨C.A_sup, C.supPos⟩) x
  · intro x hx
    apply scaledMollifier_eq_zero_of_dist C.r C.rPos
    change (C.A_sup / 4) * C.r ≤ dist x 0
    nlinarith
  · exact scaledMollifier_integral C.r C.rPos
      (Objects.Tube.TubeParams.quarter' ⟨C.A_sup, C.supPos⟩)

theorem tubeDataOf_bump_shape (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (netRadius : ℝ) (netSites : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    let T := tubeDataOf C P hP hSmall netRadius netSites
    (∀ x : ℂ, 0 ≤ T.bump x ∧ T.bump x ≤ C.A_max) ∧
    (∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), T.bump x = C.A_max) ∧
    (∀ x ∉ Objects.CorrectedEvent.tubeV T C.A_sup, T.bump x = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨Objects.Tube.TubeParams.bump_nonneg C.maxPos.le ⟨C.A_sup, C.supPos⟩ x,
      Objects.Tube.TubeParams.bump_le C.maxPos.le ⟨C.A_sup, C.supPos⟩ x⟩
  · intro x hx
    rw [tubeDataOf_tubeSet_eq C P hP hSmall netRadius netSites hwp] at hx
    exact Objects.Tube.TubeParams.bump_eq_of_mem_closure C.A_max ⟨C.A_sup, C.supPos⟩ hx
  · intro x hx
    rw [tubeDataOf_tubeV_eq C P hP hSmall netRadius netSites hwp] at hx
    exact Objects.Tube.TubeParams.bump_eq_zero C.rPos C.A_max ⟨C.A_sup, C.supPos⟩ hx


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
