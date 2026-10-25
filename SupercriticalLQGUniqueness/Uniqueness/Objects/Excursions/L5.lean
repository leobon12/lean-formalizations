import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Bridge2
import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.X4
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Params




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

section Params

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}

 
theorem dataMatch_basic (hData : Objects.CorrectedEvent.DataMatch C T) :
    T.r = C.r ∧ T.rho = C.ρ ∧ T.lambda = C.lamConst ∧ T.A_endpt = C.A_endpt ∧ T.alpha = C.K_ann ∧
    T.K = Nat.ceil (C.lamConst / (C.A_loc * C.ρ)) ∧ T.orientation ^ 4 = 1 ∧
    T.psiU ∈ Icc (-Real.pi / 2) (Real.pi / 2) ∧ T.psiV ∈ Icc (-Real.pi / 2) (Real.pi / 2) ∧
    C.A_endpt * C.ρ * C.r ≤ T.blockRadius ∧ T.blockRadius ≤ Real.sqrt C.A_endpt * C.ρ * C.r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := hData
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem sPrime_bounds (hData : Objects.CorrectedEvent.DataMatch C T) :
    C.A_endpt ≤ Objects.CorrectedEvent.sPrime T ∧ Objects.CorrectedEvent.sPrime T ≤ Real.sqrt C.A_endpt := by
  obtain ⟨hr, hρ, -, -, -, -, -, -, -, hlo, hhi⟩ := dataMatch_basic hData
  have hρr : 0 < T.rho * T.r := by rw [hρ, hr]; exact mul_pos C.rhoPos C.rPos
  unfold Objects.CorrectedEvent.sPrime
  rw [hρ, hr] at hρr ⊢
  constructor
  · rw [le_div_iff₀ hρr]; linarith
  · rw [div_le_iff₀ hρr]; linarith

 
theorem good_toParams (hData : Objects.CorrectedEvent.DataMatch C T) (hlam : C.lamConst < 1 / 10 ^ 100)
    (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2)) : (toParams T).Good := by
  obtain ⟨hr, hρ, hl, hE, hα, hK, hn4, hψu, hψv, -, -⟩ := dataMatch_basic hData
  obtain ⟨hs1, hs2⟩ := sPrime_bounds hData
  have hneg : -Real.pi / 2 = -(Real.pi / 2) := by ring
  refine TubeParams.good_of_DG (toParams T) (lam := C.lamConst) (Aloc := C.A_loc)
    (Aendpt := C.A_endpt) C.lamPos hlam hAloc ?_ ?_ C.endptPos ?_ hs1 hs2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [toParams]; rw [hα]; exact hKann
  · simp only [toParams]; rw [hα]; exact Objects.Producer.kann_lt_one C
  · simp only [toParams]; rw [hα]; exact hendpt
  · simp only [toParams]; rw [hl, hE]
  · simp only [toParams]; rw [hρ]; exact C.rhoPos
  · simp only [toParams]; rw [hρ]; exact hrho2
  · simp only [toParams]; rw [hK, hρ]
  · simp only [toParams]; exact Objects.Producer.norm_orientation hn4
  · simp only [toParams]; rw [← hneg]; exact hψu
  · simp only [toParams]; rw [← hneg]; exact hψv

end Params

 
theorem eevent_of_S4 {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} (hData : Objects.CorrectedEvent.DataMatch C T)
    {F : ℂ → Prop} (hS4 : Objects.CorrectedEvent.S4 C T F) : (toParams T).EEvent T.r C.A_sp F := by
  have hr : T.r = C.r := (dataMatch_basic hData).1
  intro θ₀ θ₁ h0 h2 hlen
  rw [hr] at hlen
  obtain ⟨k, ⟨θ, hθ, hsite⟩, hF⟩ := hS4 θ₀ θ₁ h0 h2 hlen
  refine ⟨(k : ℤ), by rw [← site_eq]; exact hF, θ, hθ, ?_⟩
  rw [← site_eq, hsite, hr]
  simp only [pol, ex]
  push_cast
  rfl

 
theorem modMap_add_K_mul (P : TubeParams) (r : ℝ) (hK : (P.K : ℝ) ≠ 0) (m k : ℤ) (ζ : ℂ) :
    P.modMap r (k + P.K * m) ζ = P.modMap r k ζ := by
  induction m using Int.induction_on generalizing k with
  | zero => simp
  | succ m ih =>
    rw [show k + (P.K : ℤ) * (m + 1) = (k + P.K * m) + P.K by ring, TubeParams.modMap_add_K hK, ih]
  | pred m ih =>
    have := TubeParams.modMap_add_K (r := r) hK (k + P.K * (-m - 1)) ζ
    rw [show k + (P.K : ℤ) * (-m - 1) + P.K = k + P.K * (-m) by ring, ih] at this
    exact this.symm

theorem site_add_K_mul (P : TubeParams) (r : ℝ) (hK : (P.K : ℝ) ≠ 0) (m k : ℤ) :
    P.site r (k + P.K * m) = P.site r k := by
  have h := modMap_add_K_mul P r hK m k 0
  simpa [TubeParams.modMap] using h

 
theorem exists_fin_of_int (T : Objects.CorrectedEvent.TubeData) (k : ℤ) :
    ∃ kf : Fin T.K, ∃ m : ℤ, k = (kf : ℤ) + (toParams T).K * m := by
  have hKZ : (0 : ℤ) < T.K := by exact_mod_cast T.Kpos
  have h0 : 0 ≤ k % (T.K : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : k % (T.K : ℤ) < T.K := Int.emod_lt_of_pos _ hKZ
  have hd := Int.mul_ediv_add_emod k (T.K : ℤ)
  generalize hx : k % (T.K : ℤ) = x at h0 h1 hd
  generalize hq : k / (T.K : ℤ) = q at hd
  have hxK : x.toNat < T.K := by omega
  refine ⟨⟨x.toNat, hxK⟩, q, ?_⟩
  simp only [toParams]
  have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg h0
  change k = ((x.toNat : ℕ) : ℤ) + (T.K : ℤ) * q
  rw [this]
  linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
