import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.FrameBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.TubeBridgeAtoms
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Core




 





set_option autoImplicit false
noncomputable section
open Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

 
theorem tangent_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams)
    (hK : T.K = P.K) (k : Fin T.K) :
    Objects.CorrectedEvent.tangent T k = P.tangent (k.val : ℤ) := by
  simp only [Objects.CorrectedEvent.tangent, Objects.Tube.TubeParams.tangent, Objects.Tube.TubeParams.ω,
    Objects.Tube.ex, hK]
  norm_cast

 
theorem twist_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams)
    (hK : T.K = P.K) (hn : T.orientation = P.n) (k : Fin T.K) :
    Objects.CorrectedEvent.twistAngle T k = P.twist (k.val : ℤ) := by
  unfold Objects.CorrectedEvent.twistAngle Objects.Tube.TubeParams.twist
  rw [tangent_eq T P hK k, hn]

 
theorem modMap_next_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hK : T.K = P.K) (k : Fin T.K) :
    P.modMap r ((Objects.CorrectedEvent.nextSite T k).val : ℤ) = P.modMap r ((k.val : ℤ) + 1) := by
  have hk : k.val < T.K := k.isLt
  have hKne : (P.K : ℝ) ≠ 0 := by
    have hpos : 0 < P.K := by omega
    exact Nat.cast_ne_zero.mpr (by omega)
  by_cases hlt : k.val + 1 < T.K
  · have hmod : (k.val + 1) % T.K = k.val + 1 := Nat.mod_eq_of_lt hlt
    simp only [Objects.CorrectedEvent.nextSite, hmod]
    norm_cast
  · have heq : k.val + 1 = T.K := by omega
    simp only [Objects.CorrectedEvent.nextSite, heq, Nat.mod_self]
    have hcast : ((k.val : ℤ) + 1) = (P.K : ℤ) := by exact_mod_cast heq.trans hK
    rw [hcast]
    funext ζ
    have hper := Objects.Tube.TubeParams.modMap_add_K (P := P) (r := r) hKne 0 ζ
    simpa using hper.symm

 
theorem twist_next_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams)
    (hK : T.K = P.K) (k : Fin T.K) :
    P.twist ((Objects.CorrectedEvent.nextSite T k).val : ℤ) = P.twist ((k.val : ℤ) + 1) := by
  have hk : k.val < T.K := k.isLt
  have hKne : (P.K : ℝ) ≠ 0 := by
    have hpos : 0 < P.K := by omega
    exact Nat.cast_ne_zero.mpr (by omega)
  by_cases hlt : k.val + 1 < T.K
  · have hmod : (k.val + 1) % T.K = k.val + 1 := Nat.mod_eq_of_lt hlt
    simp only [Objects.CorrectedEvent.nextSite, hmod]
    norm_cast
  · have heq : k.val + 1 = T.K := by omega
    simp only [Objects.CorrectedEvent.nextSite, heq, Nat.mod_self]
    have hcast : ((k.val : ℤ) + 1) = (P.K : ℤ) := by exact_mod_cast heq.trans hK
    rw [hcast]
    have hper := Objects.Tube.TubeParams.twist_add_K (P := P) hKne 0
    simpa using hper.symm

 
theorem sPrime_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hρ : T.rho = P.ρ) (hr : T.r = r) (hs : T.blockRadius = P.s r)
    (hρpos : 0 < P.ρ) (hrpos : 0 < r) : Objects.CorrectedEvent.sPrime T = P.sp := by
  unfold Objects.CorrectedEvent.sPrime
  rw [hs, hρ, hr]
  unfold Objects.Tube.TubeParams.s
  have hne : P.ρ * r ≠ 0 := (mul_pos hρpos hrpos).ne'
  field_simp

 
theorem gatePlus_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hnorm : ‖P.n‖ = 1) (k : Fin T.K) :
    Objects.CorrectedEvent.gatePlus T k = P.gatePlus r (k.val : ℤ) := by
  rw [Objects.Tube.TubeParams.gatePlus_eq hnorm]
  unfold Objects.CorrectedEvent.gatePlus
  rw [Objects.NetworkTour.site_eq T P r hr hK k, tangent_eq T P hK k, hρ, hr]

 
theorem gateMinus_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hnorm : ‖P.n‖ = 1) (k : Fin T.K) :
    Objects.CorrectedEvent.gateMinus T k = P.gateMinus r (k.val : ℤ) := by
  rw [Objects.Tube.TubeParams.gateMinus_eq hnorm]
  unfold Objects.CorrectedEvent.gateMinus
  rw [Objects.NetworkTour.site_eq T P r hr hK k, tangent_eq T P hK k, hρ, hr]

 
theorem gateMinus_next_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hnorm : ‖P.n‖ = 1) (k : Fin T.K) :
    Objects.CorrectedEvent.gateMinus T (Objects.CorrectedEvent.nextSite T k) = P.gateMinus r ((k.val : ℤ) + 1) := by
  rw [gateMinus_eq T P r hr hρ hK hnorm]
  unfold Objects.Tube.TubeParams.gateMinus
  rw [twist_next_eq T P hK k, modMap_next_eq T P r hK k]

 
theorem connector_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hP : P.Good) (hrpos : 0 < r)
    (k : Fin T.K) : Objects.CorrectedEvent.connector T k = P.conn r (k.val : ℤ) := by
  have hsp : Objects.CorrectedEvent.sPrime T = P.sp :=
    sPrime_eq T P r hρ hr hs hP.ρ_pos hrpos
  have hsp_le : Objects.CorrectedEvent.sPrime T ≤ 2 / 3 := by
    rw [hsp]
    have hα_lt := hP.α_lt
    have hα_gt := hP.α_gt
    have hsp_bd := hP.sp_le
    linarith
  have hM : Objects.CorrectedEvent.moduleMap T k = P.modMap r (k.val : ℤ) := by
    funext w
    exact Objects.NetworkTour.moduleMap_eq T P r hr hρ hK hn k w
  have hMn : Objects.CorrectedEvent.moduleMap T (Objects.CorrectedEvent.nextSite T k) = P.modMap r ((k.val : ℤ) + 1) := by
    funext w
    rw [Objects.NetworkTour.moduleMap_eq T P r hr hρ hK hn, modMap_next_eq T P r hK k]
  have ht : Objects.CorrectedEvent.twistAngle T k = P.twist (k.val : ℤ) := twist_eq T P hK hn k
  have htn : Objects.CorrectedEvent.twistAngle T (Objects.CorrectedEvent.nextSite T k) = P.twist ((k.val : ℤ) + 1) := by
    rw [twist_eq T P hK hn, twist_next_eq T P hK k]
  have hout : range (P.outA r (k.val : ℤ)) =
      Objects.CorrectedEvent.moduleMap T k '' (Objects.CorrectedEvent.outStub T ∪ Objects.CorrectedEvent.outTwist T k) := by
    rw [Objects.Tube.TubeParams.range_outA, ← hM, ← ht, ← hsp, ← hψv]
    rw [out_path_eq_literal T k hsp_le]
  have hin : range (P.inA r ((k.val : ℤ) + 1)) =
      Objects.CorrectedEvent.moduleMap T (Objects.CorrectedEvent.nextSite T k) ''
        ((fun w : ℂ => -w) '' Objects.CorrectedEvent.outTwist T (Objects.CorrectedEvent.nextSite T k) ∪ Objects.CorrectedEvent.inStub T) := by
    rw [Objects.Tube.TubeParams.range_inA, ← hMn, ← htn, ← hsp, ← hα, ← hψu]
    rw [in_path_eq_literal T (Objects.CorrectedEvent.nextSite T k)]
  have hcorr : range (P.corridor r (k.val : ℤ)) =
      Objects.CorrectedEvent.segment (Objects.CorrectedEvent.gatePlus T k) (Objects.CorrectedEvent.gateMinus T (Objects.CorrectedEvent.nextSite T k)) := by
    rw [Objects.Tube.TubeParams.range_corridor_eq, ← gatePlus_eq T P r hr hρ hK hP.n_norm k,
      ← gateMinus_next_eq T P r hr hρ hK hP.n_norm k, segment_eq_segment]
  rw [Objects.Tube.TubeParams.conn_eq]
  unfold Objects.CorrectedEvent.connector
  rw [hout, hin, hcorr]


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
