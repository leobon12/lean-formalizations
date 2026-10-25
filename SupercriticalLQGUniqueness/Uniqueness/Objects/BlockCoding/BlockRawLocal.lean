import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldFiniteTwoMetric
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockGeoLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.BlockF3Local
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldModConst




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

private theorem block_pair_eq_of_shields (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (D₁ E₁ D₂ E₂ : LSCMetric)
    (hR : 0 < T.rho * T.r) (W : Set ℂ)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ W)
    (hB₁ : BiLipschitz.Barrier.Barrier D₁ ∧ BiLipschitz.Barrier.Barrier E₁)
    (hB₂ : BiLipschitz.Barrier.Barrier D₂ ∧ BiLipschitz.Barrier.Barrier E₂)
    (hL₁ : D₁.IsLengthSpace ∧ E₁.IsLengthSpace)
    (hL₂ : D₂.IsLengthSpace ∧ E₂.IsLengthSpace)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hED₁ : ∀ p : ℂ × ℂ, E₁ p ≤ ENNReal.ofReal Cp * D₁ p)
    (hDE₁ : ∀ p : ℂ × ℂ, D₁ p ≤ ENNReal.ofReal Ci * E₁ p)
    (hED₂ : ∀ p : ℂ × ℂ, E₂ p ≤ ENNReal.ofReal Cp * D₂ p)
    (hDE₂ : ∀ p : ℂ × ℂ, D₂ p ≤ ENNReal.ofReal Ci * E₂ p)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (hS₁ : Objects.Excursions.shield C T Ksh D₁) (hS₂ : Objects.Excursions.shield C T Ksh D₂)
    (hDI : D₁.internal W = D₂.internal W)
    (hEI : E₁.internal W = E₂.internal W)
    (u v : ℂ)
    (hu : u ∈ closedBall (0 : ℂ) (3 * (T.rho * T.r)))
    (hv : v ∈ closedBall (0 : ℂ) (3 * (T.rho * T.r))) :
    D₁ (u,v) = D₂ (u,v) ∧ E₁ (u,v) = E₂ (u,v) := by
  obtain ⟨huW, hvW, hD₁, hE₁⟩ :=
    shield_finite_two_metric_all_pairs C T Ksh D₁ E₁ hR W hW
      hB₁.1 hB₁.2 hL₁.1 hL₁.2 Cp Ci hCp hCi hED₁ hDE₁ hLam hRatio hS₁ hu hv
  obtain ⟨huW', hvW', hD₂, hE₂⟩ :=
    shield_finite_two_metric_all_pairs C T Ksh D₂ E₂ hR W hW
      hB₂.1 hB₂.2 hL₂.1 hL₂.2 Cp Ci hCp hCi hED₂ hDE₂ hLam hRatio hS₂ hu hv
  constructor
  · calc
      D₁ (u,v) = D₁.internal W (⟨u, huW⟩, ⟨v, hvW⟩) := hD₁.symm
      _ = D₂.internal W (⟨u, huW⟩, ⟨v, hvW⟩) := by rw [hDI]
      _ = D₂ (u,v) := by simpa only using hD₂
  · calc
      E₁ (u,v) = E₁.internal W (⟨u, huW⟩, ⟨v, hvW⟩) := hE₁.symm
      _ = E₂.internal W (⟨u, huW⟩, ⟨v, hvW⟩) := by rw [hEI]
      _ = E₂ (u,v) := by simpa only using hE₂

 

theorem blockRaw_of_internal_eq (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D₁ E₁ D₂ E₂ : LSCMetric)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (W : Set ℂ)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ W)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ W)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ W)
    (hCU : closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ W)
    (hCV : closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ W)
    (hB₁ : BiLipschitz.Barrier.Barrier D₁ ∧ BiLipschitz.Barrier.Barrier E₁)
    (hB₂ : BiLipschitz.Barrier.Barrier D₂ ∧ BiLipschitz.Barrier.Barrier E₂)
    (hL₁ : D₁.IsLengthSpace ∧ E₁.IsLengthSpace)
    (hL₂ : D₂.IsLengthSpace ∧ E₂.IsLengthSpace)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hED₁ : ∀ p : ℂ × ℂ, E₁ p ≤ ENNReal.ofReal Cp * D₁ p)
    (hDE₁ : ∀ p : ℂ × ℂ, D₁ p ≤ ENNReal.ofReal Ci * E₁ p)
    (hED₂ : ∀ p : ℂ × ℂ, E₂ p ≤ ENNReal.ofReal Cp * D₂ p)
    (hDE₂ : ∀ p : ℂ × ℂ, D₂ p ≤ ENNReal.ofReal Ci * E₂ p)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (hDI : D₁.internal W = D₂.internal W)
    (hEI : E₁.internal W = E₂.internal W)
    (hRaw : Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D₁) (fun _ => E₁) (0 : LQGMetric.DistC)) :
    Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D₂) (fun _ => E₂)
      (0 : LQGMetric.DistC) := by
  let K : Set ℂ := closure (Objects.Excursions.blockShape T)
  have hK : IsCompact K := Objects.BlockWitness.blockShape_compact T hn hR
  have hKball : K ⊆ closedBall (0 : ℂ) (T.rho * T.r) :=
    closure_minimal (Objects.Excursions.blockShape_subset hn hR) isClosed_closedBall
  have hK3 : K ⊆ closedBall (0 : ℂ) (3 * (T.rho * T.r)) := by
    intro p hp
    have hp' := hKball hp
    rw [mem_closedBall] at hp' ⊢
    exact hp'.trans (by linarith)
  have hSiff : Objects.Excursions.shield C T Ksh D₁ ↔ Objects.Excursions.shield C T Ksh D₂ := by
    apply Objects.ShieldLocality.shield_iff_of_internal_eq C T Ksh D₁ D₂
      hB₁.1 hB₂.1 hL₁.1 hL₂.1 hR W
    · intro k hk
      have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) := by positivity
      exact (Objects.ShieldLocality.shieldClosed_subset_window _ ht).trans (hWin k hk)
    · intro k hk
      have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) := by positivity
      exact (Objects.ShieldLocality.shieldAnn_subset_window _ ht).trans (hWin k hk)
    · exact hDI
  rcases hRaw with ⟨⟨u, v, huNorm, huClose, hvNorm, hvClose,
    hratio, hfin, hgeo, hF3u, hF3v⟩, hS₁⟩
  have hS₂ := hSiff.mp hS₁
  obtain ⟨P, a, b, hP, hPa, hPb, htrace, hlen⟩ := hgeo
  have huK : u ∈ K := by
    have := htrace a ⟨le_rfl, hP.1⟩
    simpa only [hPa] using this
  have hvK : v ∈ K := by
    have := htrace b ⟨hP.1, le_rfl⟩
    simpa only [hPb] using this
  obtain ⟨hDxy, hExy⟩ := block_pair_eq_of_shields C T Ksh D₁ E₁ D₂ E₂
    hR W hW hB₁ hB₂ hL₁ hL₂ Cp Ci hCp hCi hED₁ hDE₁ hED₂ hDE₂
    hLam hRatio hS₁ hS₂ hDI hEI u v (hK3 huK) (hK3 hvK)
  have hgeo₂ : ∃ (Q : ℝ → ℂ) (c d : ℝ), E₂.IsCurve Q c d ∧
      Q c = u ∧ Q d = v ∧ (∀ s ∈ Icc c d, Q s ∈ K) ∧
      E₂.len Q c d = E₂ (u,v) := by
    have hconv := (compact_geodesic_congr_window E₁ E₂ K W hK hKW hEI
      ⟨u, huK⟩ ⟨v, hvK⟩ hExy).mp
      ⟨⟨P, a, b, hP, htrace, hPa, hPb, hlen⟩, hfin⟩
    obtain ⟨⟨Q, c, d, hQ, hQtrace, hQc, hQd, hQlen⟩, -⟩ := hconv
    exact ⟨Q, c, d, hQ, hQc, hQd, hQtrace, hQlen⟩
  refine ⟨⟨u, v, huNorm, huClose, hvNorm, hvClose, ?_, ?_, hgeo₂, ?_, ?_⟩, hS₂⟩
  · simpa only [← hDxy, ← hExy] using hratio
  · simpa only [← hExy] using hfin
  · obtain ⟨huBall, hcost⟩ := hF3u
    refine ⟨huBall, ?_⟩
    have hcircle := Objects.BlockWitness.circleOuter_bad_eq_of_window_internal_eq
      D₁ D₂ W (Objects.Excursions.cU T) u T.blockRadius
      (C.lamConst * (E₁ (u,v)).toReal) huBall hCU hDI
    rw [← hExy, ← hcircle]
    exact hcost
  · obtain ⟨hvBall, hcost⟩ := hF3v
    refine ⟨hvBall, ?_⟩
    have hcircle := Objects.BlockWitness.circleOuter_bad_eq_of_window_internal_eq
      D₁ D₂ W (Objects.Excursions.cV T) v T.blockRadius
      (C.lamConst * (E₁ (u,v)).toReal) hvBall hCV hDI
    rw [← hExy, ← hcircle]
    exact hcost

 


theorem blockRaw_iff_of_internal_eq (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D₁ E₁ D₂ E₂ : LSCMetric)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (W : Set ℂ)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ W)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ W)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ W)
    (hCU : closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ W)
    (hCV : closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ W)
    (hB₁ : BiLipschitz.Barrier.Barrier D₁ ∧ BiLipschitz.Barrier.Barrier E₁)
    (hB₂ : BiLipschitz.Barrier.Barrier D₂ ∧ BiLipschitz.Barrier.Barrier E₂)
    (hL₁ : D₁.IsLengthSpace ∧ E₁.IsLengthSpace)
    (hL₂ : D₂.IsLengthSpace ∧ E₂.IsLengthSpace)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hED₁ : ∀ p : ℂ × ℂ, E₁ p ≤ ENNReal.ofReal Cp * D₁ p)
    (hDE₁ : ∀ p : ℂ × ℂ, D₁ p ≤ ENNReal.ofReal Ci * E₁ p)
    (hED₂ : ∀ p : ℂ × ℂ, E₂ p ≤ ENNReal.ofReal Cp * D₂ p)
    (hDE₂ : ∀ p : ℂ × ℂ, D₂ p ≤ ENNReal.ofReal Ci * E₂ p)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (hDI : D₁.internal W = D₂.internal W)
    (hEI : E₁.internal W = E₂.internal W) :
    Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D₁) (fun _ => E₁)
      (0 : LQGMetric.DistC) ↔
    Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D₂) (fun _ => E₂)
      (0 : LQGMetric.DistC) := by
  constructor
  · exact blockRaw_of_internal_eq C T Ksh Cmid0 D₁ E₁ D₂ E₂ hR hn W
      hW hWin hKW hCU hCV hB₁ hB₂ hL₁ hL₂ Cp Ci hCp hCi
      hED₁ hDE₁ hED₂ hDE₂ hLam hRatio hDI hEI
  · exact blockRaw_of_internal_eq C T Ksh Cmid0 D₂ E₂ D₁ E₁ hR hn W
      hW hWin hKW hCU hCV hB₂ hB₁ hL₂ hL₁ Cp Ci hCp hCi
      hED₂ hDE₂ hED₁ hDE₁ hLam hRatio hDI.symm hEI.symm


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
