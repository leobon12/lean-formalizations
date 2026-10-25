import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ConnectorBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Family




 





set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

 
def tubeParamsOf (T : Objects.CorrectedEvent.TubeData) : Objects.Tube.TubeParams where
  ρ := T.rho
  K := T.K
  α := T.alpha
  n := T.orientation
  ψu := T.psiU
  ψv := T.psiV
  sp := Objects.CorrectedEvent.sPrime T
  wp := T.lambda * T.A_endpt

 
theorem testPoint_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hK : T.K = P.K) (k : Fin T.K) :
    Objects.CorrectedEvent.site T k = P.site r (k.val : ℤ) :=
  Objects.NetworkTour.site_eq T P r hr hK k

 
theorem blockCircles_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (k : Fin T.K) :
    sphere (Objects.CorrectedEvent.innerCenter T k) T.blockRadius =
        sphere (P.uC r (k.val : ℤ)) (P.s r) ∧
      sphere (Objects.CorrectedEvent.outerCenter T k) T.blockRadius =
        sphere (P.vC r (k.val : ℤ)) (P.s r) := by
  constructor
  · rw [Objects.NetworkTour.innerCenter_eq T P r hr hρ hK hn hα hψu k, hs]
  · rw [Objects.NetworkTour.outerCenter_eq T P r hr hρ hK hn hψv k, hs]

 
theorem tube_eq_fin_union (P : Objects.Tube.TubeParams) (r : ℝ) (hKpos : 0 < P.K) :
    P.tube r = ⋃ k : Fin P.K, P.summand r (k.val : ℤ) := by
  have hKne : (P.K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hKZ : (0 : ℤ) < P.K := by exact_mod_cast hKpos
  rw [Objects.Tube.TubeParams.tube_eq_iUnion_summand]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨k, hx⟩ := mem_iUnion.mp hx
    set q := k % (P.K : ℤ) with hq
    have hq0 : 0 ≤ q := by rw [hq]; exact Int.emod_nonneg _ (by omega)
    have hqK : q < P.K := by rw [hq]; exact Int.emod_lt_of_pos _ hKZ
    let j : Fin P.K := ⟨q.toNat, by omega⟩
    have hj : (j.val : ℤ) = q := by simp [j, Int.toNat_of_nonneg hq0]
    have hdiv := Int.mul_ediv_add_emod k (P.K : ℤ)
    have hk : k = q + P.K * (k / P.K) := by rw [hq]; linarith
    rw [hk, Objects.Tube.TubeParams.summand_add_K_mul hKne] at hx
    exact mem_iUnion.mpr ⟨j, by simpa only [hj] using hx⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨(j.val : ℤ), hj⟩

 
theorem tube_summand_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (k : Fin T.K) :
    (Objects.CorrectedEvent.block T k ∪ ball (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ∪
      ball (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ∪
      {x : ℂ | ∃ y ∈ Objects.CorrectedEvent.connector T k, dist x y < Objects.CorrectedEvent.tubeWidth T}) =
      P.summand r (k.val : ℤ) := by
  have hblock := Objects.NetworkTour.block_eq T P r hr hρ hK hn hα k
  have hinner := Objects.NetworkTour.innerCenter_eq T P r hr hρ hK hn hα hψu k
  have houter := Objects.NetworkTour.outerCenter_eq T P r hr hρ hK hn hψv k
  have hconn := connector_eq T P r hr hρ hK hn hα hψu hψv hs hP hrpos k
  have hwidth := Objects.NetworkTour.tubeWidth_eq T P r hr hρ hwp
  have hthick :
      {x : ℂ | ∃ y ∈ Objects.CorrectedEvent.connector T k, dist x y < Objects.CorrectedEvent.tubeWidth T} =
        thickening (P.w r) (P.conn r (k.val : ℤ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_thickening_iff, hconn, hwidth]
  rw [hblock, hinner, houter, hs, hthick]
  rfl

 
theorem tubeSet_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) : Objects.CorrectedEvent.tubeSet T = P.tube r := by
  have hKpos : 0 < P.K := by rw [← hK]; exact T.Kpos
  have hindex : (⋃ k : Fin T.K, P.summand r (k.val : ℤ)) =
      ⋃ k : Fin P.K, P.summand r (k.val : ℤ) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨Fin.cast hK k, by simpa using hk⟩
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨Fin.cast hK.symm k, by simpa using hk⟩
  have hfin : P.tube r = ⋃ k : Fin T.K, P.summand r (k.val : ℤ) := by
    rw [hindex]
    exact tube_eq_fin_union P r hKpos
  rw [hfin]
  unfold Objects.CorrectedEvent.tubeSet
  apply iUnion_congr
  intro k
  exact tube_summand_eq T P r hr hρ hK hn hα hψu hψv hs hwp hP hrpos k

 
theorem tubeV_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) : Objects.CorrectedEvent.tubeV T Asup = P.nbhd r Asup := by
  unfold Objects.CorrectedEvent.tubeV Objects.Tube.TubeParams.nbhd
  rw [tubeSet_eq T P r hr hρ hK hn hα hψu hψv hs hwp hP hrpos, hr]
  ext x
  simp only [Set.mem_ofPred_eq, mem_thickening_iff]

 
theorem tubeSet_eq_of_data (T : Objects.CorrectedEvent.TubeData)
    (hρ : 0 < T.rho) (hr : 0 < T.r)
    (hGood : (tubeParamsOf T).Good) :
    Objects.CorrectedEvent.tubeSet T = (tubeParamsOf T).tube T.r := by
  have hs : T.blockRadius = (tubeParamsOf T).s T.r := by
    unfold tubeParamsOf Objects.Tube.TubeParams.s Objects.CorrectedEvent.sPrime
    have hne : T.rho * T.r ≠ 0 := (mul_pos hρ hr).ne'
    field_simp
  exact tubeSet_eq T (tubeParamsOf T) T.r rfl rfl rfl rfl rfl rfl rfl hs rfl hGood hr

 
theorem tubeV_eq_of_data (T : Objects.CorrectedEvent.TubeData) (Asup : ℝ)
    (hρ : 0 < T.rho) (hr : 0 < T.r)
    (hGood : (tubeParamsOf T).Good) :
    Objects.CorrectedEvent.tubeV T Asup = (tubeParamsOf T).nbhd T.r Asup := by
  have hs : T.blockRadius = (tubeParamsOf T).s T.r := by
    unfold tubeParamsOf Objects.Tube.TubeParams.s Objects.CorrectedEvent.sPrime
    have hne : T.rho * T.r ≠ 0 := (mul_pos hρ hr).ne'
    field_simp
  exact tubeV_eq T (tubeParamsOf T) T.r Asup rfl rfl rfl rfl rfl rfl rfl hs rfl hGood hr


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
