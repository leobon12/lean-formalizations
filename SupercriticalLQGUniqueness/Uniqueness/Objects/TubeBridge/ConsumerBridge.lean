import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.TubeSetBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Shape
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Across
import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.NetworkBounds




 





set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

 
theorem uZero_eq_tubeSet (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (hAsup : 0 < Asup)
    (hSmall : 100 * Asup ≤ P.sp * P.ρ) :
    (Objects.CentreZero.uZero P hP r Asup hrpos hAsup hSmall : Set ℂ) = Objects.CorrectedEvent.tubeSet T := by
  rw [tubeSet_eq T P r hr hρ hK hn hα hψu hψv hs hwp hP hrpos]
  ext x
  change x ∈ P.tubeAt r 0 ↔ x ∈ P.tube r
  simp only [Objects.Tube.TubeParams.mem_tubeAt, sub_zero]

 
theorem vZero_eq_tubeV (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (hAsup : 0 < Asup)
    (hSmall : 100 * Asup ≤ P.sp * P.ρ) :
    (Objects.CentreZero.vZero P hP r Asup hrpos hAsup hSmall : Set ℂ) = Objects.CorrectedEvent.tubeV T Asup := by
  rw [tubeV_eq T P r Asup hr hρ hK hn hα hψu hψv hs hwp hP hrpos]
  ext x
  change x ∈ P.nbhdAt r Asup 0 ↔ x ∈ P.nbhd r Asup
  simp only [Objects.Tube.TubeParams.mem_nbhdAt, sub_zero]

 
theorem tube_sub_uZero (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (hAsup : 0 < Asup)
    (hSmall : 100 * Asup ≤ P.sp * P.ρ) :
    Objects.CorrectedEvent.tubeSet T ⊆
      (Objects.CentreZero.uZero P hP r Asup hrpos hAsup hSmall : Set ℂ) := by
  intro x hx
  have hx' : x ∈ P.tube r := by
    rw [← tubeSet_eq T P r hr hρ hK hn hα hψu hψv hs hwp hP hrpos]
    exact hx
  change x ∈ P.tubeAt r 0
  exact Objects.Tube.TubeParams.mem_tubeAt.mpr (by simpa only [sub_zero] using hx')

 
theorem tube_middle (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (hAsup : 0 < Asup)
    (hSmall : 100 * Asup ≤ P.sp * P.ρ) :
    Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * r) := by
  intro x hx
  have htu := tube_sub_uZero T P r Asup hr hρ hK hn hα hψu hψv hs hwp hP hrpos hAsup hSmall hx
  have hcl := Objects.CentreZero.closure_uZero_vZero P hP r Asup hrpos hAsup hSmall (subset_closure htu)
  have hmid := Objects.CentreZero.vZero_middle P hP r Asup hrpos hAsup hSmall hcl
  change 1.5 * r < dist x 0 ∧ dist x 0 < 2.5 * r at hmid
  simpa only [mem_ball, dist_comm] using hmid.2

 

theorem boundsAt_of_identified_tube
    {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hEvent : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (P : Objects.Tube.TubeParams) (hP : P.Good) (r : Set.Ioi (0 : ℝ))
    (hr : T.r = (r : ℝ)) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ)
    (hL : (D g).IsLengthSpace) (hForget : Continuous (BiLipschitz.Barrier.forget (D g)))
    (hInner : Objects.CorrectedEvent.ambientAcross (D g) 0 C.r (1.5 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 C.r (1.5 * C.r))
    (hOuter : Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * C.r) (3 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * C.r) (3 * C.r))
    (hEucl : ∀ (γ : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve γ a b → (D g).len γ a b < ∞ → ContinuousOn γ (Icc a b))
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    (hXi : C.ξ = (ξ : ℝ)) (hQ : C.Q = Q) (hR : C.r = (r : ℝ))
    (hAcross : par.Cacross = C.A_across) (hAround : par.Caround = C.A_around)
    (hCt : par.Ctube = C.A_internal) :
    Objects.Producer.BoundsAt D ξ Q par 0 r
      (Objects.CentreZero.uZero P hP r C.A_sup r.2 C.supPos hSmall)
      (Objects.CentreZero.vZero P hP r C.A_sup r.2 C.supPos hSmall) g := by
  have hTU := tube_sub_uZero T P r C.A_sup hr hρ hK hn hα hψu hψv hs hwp hP r.2 C.supPos hSmall
  have hU : Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * C.r) := by
    simpa only [hR] using
      tube_middle T P r C.A_sup hr hρ hK hn hα hψu hψv hs hwp hP r.2 C.supPos hSmall
  have hV := Objects.CentreZero.vZero_middle P hP r C.A_sup r.2 C.supPos hSmall
  intro c hc
  refine ⟨?_, ?_, ?_⟩
  · exact Objects.CentreZero.across_bound_of_corrected_event hEvent hL hForget hInner hOuter
      hXi hQ hR hAcross hV hc
  · exact Objects.CentreZero.around_bound_of_corrected_event hEvent hForget hXi hQ hR hAround hc
  · exact Objects.NetworkTour.event_hasTubeSeparator_bounds_field hEvent hU hEucl
      (Objects.CentreZero.uZero P hP r C.A_sup r.2 C.supPos hSmall) hTU hXi hQ hR hCt hc


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
