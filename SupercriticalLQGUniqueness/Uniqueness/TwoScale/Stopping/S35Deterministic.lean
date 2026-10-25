import LQGMetric.Papers.CONF.S3L36D
import LQGMetric.Papers.CONF.S3L35
import LQGMetric.Papers.GM.S3.AttainedCount




 






set_option autoImplicit false
noncomputable section

open Set Metric Finset
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping

 
theorem annulus_adapter {r : ℝ} (hr : 0 < r) (z x : ℂ)
    (hx : r / 2 ≤ dist x z ∧ dist x z ≤ 2 * r) :
    3 * r / 7 < dist x z ∧ dist x z < 3 * r * (3 / 4 : ℝ) := by
  constructor <;> linarith [hx.1, hx.2]

 
theorem annulus_adapter_ratio {r r' : ℝ} (hr : 0 ≤ r)
    (hnext : r' ≤ r / 8) : 3 * r' ≤ (3 * r) / 7 := by
  linarith

 
theorem fine_mesh_half_radius {ε b r : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hr : ε ^ 2 * b ≤ r) (x : ℂ) :
    dist x (LQGMetric.CONF.conf36Grid (ε ^ 2 * b / 100) x) < r / 2 := by
  have hm : 0 < ε ^ 2 * b / 100 := by positivity
  have hd := LQGMetric.CONF.conf36Grid_norm_lt hm x
  rw [dist_eq_norm]
  have h : 2 * (ε ^ 2 * b / 100) < r / 2 := by nlinarith
  exact hd.trans h

 

theorem fine_mesh_site_in_box {U : Set ℂ} {B ε b : ℝ}
    (hU : U ⊆ closedBall 0 B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b)
    {x : ℂ} (hx : x ∈ (fun u : ℂ => (b : ℂ) * u) '' U) :
    LQGMetric.CONF.conf36Grid (ε ^ 2 * b / 100) x ∈
      (fun k : ℤ × ℤ => (⟨k.1 * (ε ^ 2 * b / 100),
        k.2 * (ε ^ 2 * b / 100)⟩ : ℂ)) ''
      ↑(LQGMetric.CONF.gridBox (ε ^ 2 * b / 100) (b * (B + 1)) 0) := by
  obtain ⟨u, hu, rfl⟩ := hx
  let m := ε ^ 2 * b / 100
  have hm : 0 < m := by dsimp [m]; positivity
  have hnear := LQGMetric.CONF.conf36Grid_norm_lt hm ((b : ℂ) * u)
  have huB : ‖u‖ ≤ B := by simpa only [mem_closedBall, dist_zero_right] using hU hu
  have hscale : ‖(b : ℂ) * u‖ ≤ b * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
    exact mul_le_mul_of_nonneg_left huB hb.le
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have h2m : 2 * m < b := by
    dsimp [m]
    nlinarith
  have hball : LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) ∈ ball 0 (b * (B + 1)) := by
    rw [mem_ball, dist_zero_right]
    have htri := norm_add_le (LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) -
      (b : ℂ) * u) ((b : ℂ) * u)
    have hident : LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) -
      (b : ℂ) * u + (b : ℂ) * u =
        LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) := by ring
    rw [hident] at htri
    have hnear' : ‖LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) -
      (b : ℂ) * u‖ < 2 * m := by
      rw [norm_sub_rev]
      exact hnear
    nlinarith
  have hg : LQGMetric.CONF.conf36Grid m ((b : ℂ) * u) ∈
      LQGMetric.Blueprint.gridPts m := LQGMetric.CONF.conf36Grid_mem m _
  exact LQGMetric.CONF.grid_ball_subset hm 0 ⟨hg, hball⟩

 
theorem fine_mesh_box_count {ε b B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : 0 < b) (hB : 0 ≤ B) (z₀ : ℂ) :
    ((LQGMetric.CONF.gridBox (ε ^ 2 * b / 100) (b * (B + 1)) z₀).card : ℝ) * ε ^ 4
      ≤ (200 * (B + 1) + 3) ^ 2 := by
  rw [LQGMetric.CONF.gridBox_card]
  set N := ⌈b * (B + 1) / (ε ^ 2 * b / 100)⌉₊
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε2le : ε ^ 2 ≤ 1 := by nlinarith
  have harg : 0 ≤ b * (B + 1) / (ε ^ 2 * b / 100) := by positivity
  have hN : (N : ℝ) < b * (B + 1) / (ε ^ 2 * b / 100) + 1 :=
    Nat.ceil_lt_add_one harg
  have hdiv : b * (B + 1) / (ε ^ 2 * b / 100) = 100 * (B + 1) / ε ^ 2 := by
    field_simp
  rw [hdiv] at hN
  have hNε : (2 * (N : ℝ) + 1) * ε ^ 2 ≤ 200 * (B + 1) + 3 := by
    have hmul := mul_lt_mul_of_pos_right hN hε2
    have hcancel : (100 * (B + 1) / ε ^ 2 + 1) * ε ^ 2 =
        100 * (B + 1) + ε ^ 2 := by field_simp
    rw [hcancel] at hmul
    nlinarith
  have hleft : 0 ≤ (2 * (N : ℝ) + 1) * ε ^ 2 := by positivity
  have hright : 0 ≤ 200 * (B + 1) + 3 := by positivity
  push_cast
  calc
    (2 * (N : ℝ) + 1) ^ 2 * ε ^ 4 = ((2 * (N : ℝ) + 1) * ε ^ 2) ^ 2 := by ring
    _ ≤ (200 * (B + 1) + 3) ^ 2 := pow_le_pow_left₀ hleft hNε 2

 

theorem fine_mesh_union_budget {ε b B M : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (z₀ : ℂ)
    (p : ℤ × ℤ → ℝ)
    (hpt : ∀ k ∈ LQGMetric.CONF.gridBox (ε ^ 2 * b / 100) (b * (B + 1)) z₀,
      p k ≤ M * ε ^ 100) :
    ∑ k ∈ LQGMetric.CONF.gridBox (ε ^ 2 * b / 100) (b * (B + 1)) z₀, p k
      ≤ M * (200 * (B + 1) + 3) ^ 2 * ε ^ 96 := by
  let I := LQGMetric.CONF.gridBox (ε ^ 2 * b / 100) (b * (B + 1)) z₀
  have hcard := fine_mesh_box_count hε hε1 hb hB z₀
  have hpow : 0 ≤ M * ε ^ 96 := by positivity
  calc
    ∑ k ∈ I, p k ≤ ∑ _k ∈ I, M * ε ^ 100 :=
      Finset.sum_le_sum (fun k hk => hpt k hk)
    _ = (I.card : ℝ) * (M * ε ^ 100) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((I.card : ℝ) * ε ^ 4) * (M * ε ^ 96) := by ring
    _ ≤ (200 * (B + 1) + 3) ^ 2 * (M * ε ^ 96) :=
      mul_le_mul_of_nonneg_right hcard hpow
    _ = M * (200 * (B + 1) + 3) ^ 2 * ε ^ 96 := by ring

 

theorem bad_scale_eighth {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Good : ι → Prop) [DecidablePred Good] {L : ℝ} (hL : 8 ≤ L)
    (hcard : L - 1 ≤ (S.card : ℝ))
    (hgood : ((S.filter Good).card : ℝ) < 3 * L / 4) :
    L / 8 ≤ ((S.filter fun i => ¬ Good i).card : ℝ) := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := S) Good
  have hcast : ((S.filter Good).card : ℝ) +
      ((S.filter fun i => ¬ Good i).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hsum
  linarith

 
theorem bad_scale_eighth_of_grid {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (Good : ℕ → Prop) [DecidablePred Good]
    (hL : 8 ≤ Real.logb 8 ε⁻¹)
    (hgood : (LQGMetric.GM.scaleCount ε 1 Good : ℝ) <
      3 * Real.logb 8 ε⁻¹ / 4) :
    Real.logb 8 ε⁻¹ / 8 ≤
      (LQGMetric.GM.scaleCount ε 1 (fun i => ¬ Good i) : ℝ) := by
  classical
  have hcard := LQGMetric.GM.card_scaleSetK_ge hε hε1 (show (0 : ℝ) ≤ 1 by norm_num)
  have hpart := LQGMetric.GM.card_le_scaleCount_add (ν := 1) hε
    (Q₁ := Good) (Q₂ := fun i => ¬ Good i) (by intro k hk; exact em (Good k))
  have hpart' : ((LQGMetric.GM.scaleSetK ε 1).ncard : ℝ) ≤
      (LQGMetric.GM.scaleCount ε 1 Good : ℝ) +
      (LQGMetric.GM.scaleCount ε 1 (fun i => ¬ Good i) : ℝ) := by
    exact_mod_cast hpart
  nlinarith

 

theorem fraction_of_shortcut {K a s t : ℝ} (hK : 0 ≤ K)
    (hshortcut : s - a ≤ K * (t - s)) :
    s - a ≤ K / (K + 1) * (t - a) := by
  have hK1 : 0 < K + 1 := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hK1).mpr
  have h : (K + 1) * (s - a) ≤ K * (t - a) := by nlinarith
  nlinarith

 

theorem strict_telescope (J : ℕ) (t s : ℕ → ℝ)
    {C Cplus K C' T e : ℝ} (hK : 0 ≤ K) (hCC : C ≤ Cplus)
    (hA : 0 ≤ C + K / (K + 1) * (Cplus - C))
    (hgap : C + K / (K + 1) * (Cplus - C) < C')
    (hT : 0 < T) (ht0 : 0 ≤ t 0) (htJ : t J ≤ T)
    (horder : ∀ j < J, t j ≤ s j ∧ s j ≤ t (j + 1))
    (hshortcut : ∀ j < J, s j - t j ≤ K * (t (j + 1) - s j))
    (he : e ≤ ∑ j ∈ Finset.range J,
      (Cplus * (s j - t j) + C * (t (j + 1) - s j))) :
    e < C' * T := by
  let A := C + K / (K + 1) * (Cplus - C)
  have hstep : ∀ j < J,
      Cplus * (s j - t j) + C * (t (j + 1) - s j) ≤
        A * (t (j + 1) - t j) := by
    intro j hj
    obtain ⟨has, hst⟩ := horder j hj
    have hf := fraction_of_shortcut hK (hshortcut j hj)
    have hdiff : 0 ≤ Cplus - C := by linarith
    have hmul := mul_le_mul_of_nonneg_left hf hdiff
    dsimp [A]
    nlinarith
  have hsum := Finset.sum_le_sum (fun j hj => hstep j (Finset.mem_range.mp hj))
  have htel : ∑ j ∈ Finset.range J, (t (j + 1) - t j) = t J - t 0 := by
    exact Finset.sum_range_sub (fun j => t j) J
  calc
    e ≤ ∑ j ∈ Finset.range J,
        (Cplus * (s j - t j) + C * (t (j + 1) - s j)) := he
    _ ≤ ∑ j ∈ Finset.range J, A * (t (j + 1) - t j) := hsum
    _ = A * (t J - t 0) := by rw [← Finset.mul_sum, htel]
    _ ≤ A * T := by gcongr; linarith
    _ < C' * T := mul_lt_mul_of_pos_right hgap hT

 

 

theorem center_far_of_corridor {ε b r : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hr : r ≤ ε * b) {x c endpoint : ℂ}
    (hx : 4 * ε * b ≤ dist x endpoint)
    (hc : dist x c < r / 2) : 2 * r < dist c endpoint := by
  have htri := dist_triangle x c endpoint
  have h : dist x endpoint ≤ dist x c + dist c endpoint := htri
  nlinarith

 

theorem one_exit_step {P : ℝ → ℂ} {T a r α : ℝ} {c w : ℂ}
    (hP : ContinuousOn P (Icc 0 T)) (ha : 0 ≤ a) (haT : a < T)
    (hr : 0 < r) (hα : 1 / 2 < α) (hα1 : α < 1)
    (hstart : P a ∈ ball c (r / 2))
    (hwend : P T = w) (hw : 2 * r < dist c w) :
    ∃ s t : ℝ, a < s ∧ s < t ∧ t < T ∧
      P s ∈ sphere c (α * r) ∧ P t ∈ sphere c r ∧
      (∀ u ∈ Ico a t, P u ∈ ball c r) ∧
      (∀ u ∈ Icc s t, P u ∈ closedBall c r ∧ P u ∉ ball c (α * r)) ∧
      r / 2 ≤ dist (P t) (P a) := by
  have hPc : ContinuousOn P (Icc a T) := hP.mono (Icc_subset_Icc ha le_rfl)
  set E := Icc a T ∩ P ⁻¹' (ball c r)ᶜ with hEdef
  have hEc : IsClosed E :=
    hPc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_ball.isClosed_compl
  have hEne : E.Nonempty := by
    refine ⟨T, ⟨haT.le, le_rfl⟩, ?_⟩
    change P T ∉ ball c r
    rw [hwend, mem_ball]
    rw [dist_comm]
    exact not_lt.mpr (by linarith)
  have hEb : BddBelow E := ⟨a, fun u hu => hu.1.1⟩
  set t := sInf E with htdef
  have htE : t ∈ E := hEc.csInf_mem hEne hEb
  have hat : a < t := by
    rcases eq_or_lt_of_le htE.1.1 with h | h
    · exact absurd (h ▸ hstart : P t ∈ ball c (r / 2)) fun h' =>
        htE.2 (ball_subset_ball (by linarith) h')
    · exact h
  have hbefore : ∀ u ∈ Ico a t, P u ∈ ball c r := fun u hu => by
    by_contra hn
    exact absurd (csInf_le hEb ⟨⟨hu.1, by linarith [hu.2, htE.1.2]⟩, hn⟩)
      (not_le.2 hu.2)
  have hPt_cl : P t ∈ closedBall c r := by
    have hS : IsClosed (Icc a t ∩ P ⁻¹' closedBall c r) :=
      (hPc.mono (Icc_subset_Icc le_rfl htE.1.2)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_closedBall
    have hsub : Icc a t ⊆ Icc a t ∩ P ⁻¹' closedBall c r := by
      have h := closure_minimal (s := Ico a t)
        (t := Icc a t ∩ P ⁻¹' closedBall c r)
        (fun u hu => ⟨Ico_subset_Icc_self hu,
          ball_subset_closedBall (hbefore u hu)⟩) hS
      rwa [closure_Ico hat.ne] at h
    exact (hsub ⟨hat.le, le_rfl⟩).2
  have hPt : P t ∈ sphere c r :=
    mem_sphere.mpr (le_antisymm (mem_closedBall.mp hPt_cl)
      (not_lt.mp htE.2))
  have htT : t < T := by
    have hrad : dist (P t) c = r := mem_sphere.mp hPt
    by_contra h
    have heq : t = T := le_antisymm htE.1.2 (not_lt.mp h)
    rw [heq, hwend, dist_comm] at hrad
    linarith
  have hαr : α * r < r := by nlinarith
  have hr2 : r / 2 < α * r := by nlinarith
  set S := Icc a t ∩ P ⁻¹' closedBall c (α * r) with hSdef
  have hSc : IsClosed S :=
    (hPc.mono (Icc_subset_Icc le_rfl htE.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_closedBall
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hat.le⟩, ball_subset_closedBall
    (ball_subset_ball hr2.le hstart)⟩
  have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup S with hsdef
  have hsS : s ∈ S := hSc.csSup_mem hSne hSb
  have hst : s < t := by
    rcases eq_or_lt_of_le hsS.1.2 with h | h
    · have hrad := mem_closedBall.mp hsS.2
      rw [h, mem_sphere.mp hPt] at hrad
      linarith
    · exact h
  have has : a ≤ s := le_csSup hSb ⟨⟨le_rfl, hat.le⟩,
    ball_subset_closedBall (ball_subset_ball hr2.le hstart)⟩
  have haS : a < s := by
    rcases eq_or_lt_of_le has with heq | hlt
    · have hrad := mem_closedBall.mp (ball_subset_closedBall
        (ball_subset_ball hr2.le hstart))
      have hsrad : dist (P s) c = α * r := by
        have hafter : ∀ u ∈ Ioc s t, P u ∉ closedBall c (α * r) := fun u hu hn =>
          absurd (le_csSup hSb ⟨⟨by linarith [hu.1], hu.2⟩, hn⟩)
            (not_le.2 hu.1)
        have hS' : IsClosed (Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ) :=
          (hPc.mono (Icc_subset_Icc has htE.1.2)).preimage_isClosed_of_isClosed
            isClosed_Icc isOpen_ball.isClosed_compl
        have hsub : Icc s t ⊆ Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ := by
          have hh := closure_minimal (s := Ioc s t)
            (t := Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ)
            (fun u hu => ⟨Ioc_subset_Icc_self hu,
              fun h' => hafter u hu (ball_subset_closedBall h')⟩) hS'
          rwa [closure_Ioc hst.ne] at hh
        exact le_antisymm (mem_closedBall.mp hsS.2)
          (not_lt.mp ((hsub ⟨le_rfl, hst.le⟩).2))
      rw [← heq] at hsrad
      have hr0 := mem_ball.mp hstart
      linarith
    · exact hlt
  have hafter : ∀ u ∈ Ioc s t, P u ∉ closedBall c (α * r) := fun u hu hn =>
    absurd (le_csSup hSb ⟨⟨by linarith [hu.1], hu.2⟩, hn⟩)
      (not_le.2 hu.1)
  have hPs_out : P s ∉ ball c (α * r) := by
    have hS' : IsClosed (Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ) :=
      (hPc.mono (Icc_subset_Icc has htE.1.2)).preimage_isClosed_of_isClosed
        isClosed_Icc isOpen_ball.isClosed_compl
    have hsub : Icc s t ⊆ Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ := by
      have hh := closure_minimal (s := Ioc s t)
        (t := Icc s t ∩ P ⁻¹' (ball c (α * r))ᶜ)
        (fun u hu => ⟨Ioc_subset_Icc_self hu,
          fun h' => hafter u hu (ball_subset_closedBall h')⟩) hS'
      rwa [closure_Ioc hst.ne] at hh
    exact (hsub ⟨le_rfl, hst.le⟩).2
  have hPs : P s ∈ sphere c (α * r) :=
    mem_sphere.mpr (le_antisymm (mem_closedBall.mp hsS.2) (not_lt.mp hPs_out))
  have hann : ∀ u ∈ Icc s t, P u ∈ closedBall c r ∧ P u ∉ ball c (α * r) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with heq | hlt
    · rw [← heq]
      exact ⟨ball_subset_closedBall (hbefore s ⟨has, hst⟩), hPs_out⟩
    · refine ⟨?_, fun h' => hafter u ⟨hlt, hu.2⟩ (ball_subset_closedBall h')⟩
      rcases eq_or_lt_of_le hu.2 with heq | hlt'
      · rw [heq]; exact hPt_cl
      · exact ball_subset_closedBall (hbefore u ⟨by linarith, hlt'⟩)
  have hsep : r / 2 ≤ dist (P t) (P a) := by
    have h1 := mem_sphere.mp hPt
    have h2 := mem_ball.mp hstart
    have htri := dist_triangle (P t) (P a) c
    linarith
  exact ⟨s, t, haS, hst, htT, hPs, hPt, hbefore, hann, hsep⟩

 

theorem endpoint_corridor {P : ℝ → ℂ} {T ε b κ : ℝ} {z w : ℂ}
    (hP : ContinuousOn P (Icc 0 T)) (hT : 0 < T)
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b) (hεκ : ε ≤ κ / 32)
    (hzw : κ * b ≤ dist z w) :
    ∃ t₀ τ : ℝ, 0 < t₀ ∧ t₀ < τ ∧ τ < T ∧
      dist (P t₀) z = 4 * ε * b ∧
      P τ ∈ closedBall w (4 * ε * b) ∧
      (∀ u ∈ Ico t₀ τ,
        4 * ε * b ≤ dist (P u) z ∧ 4 * ε * b < dist (P u) w) := by
  let R := 4 * ε * b
  have hR : 0 < R := by dsimp [R]; positivity
  have hsep : 2 * R < dist z w := by
    dsimp [R]
    have hκ : 32 * ε ≤ κ := by linarith
    nlinarith
  have hF : ContinuousOn (fun u => dist (P u) w) (Icc 0 T) :=
    continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  have hqex : ∃ q ∈ Icc (0 : ℝ) T, dist (P q) w = R := by
    have h0 : R ≤ dist (P 0) w := by rw [hP0]; linarith
    have h1 : dist (P T) w ≤ R := by rw [hPT, dist_self]; exact hR.le
    obtain ⟨q, hq, hqe⟩ :=
      (intermediate_value_Icc' hT.le hF) ⟨h1, h0⟩
    exact ⟨q, hq, hqe⟩
  obtain ⟨q, hq, hqe⟩ := hqex
  have hqT : q < T := by
    rcases eq_or_lt_of_le hq.2 with heq | hlt
    · rw [heq, hPT, dist_self] at hqe
      linarith
    · exact hlt
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le hq.1 with heq | hlt
    · rw [← heq, hP0] at hqe
      linarith
    · exact hlt
  have hPq : ContinuousOn P (Icc 0 q) := hP.mono (Icc_subset_Icc le_rfl hq.2)
  set E := Icc 0 q ∩ P ⁻¹' closedBall w R with hEdef
  have hEc : IsClosed E :=
    hPq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have hEne : E.Nonempty := ⟨q, ⟨hq.1, le_rfl⟩, mem_closedBall.mpr hqe.le⟩
  have hEb : BddBelow E := ⟨0, fun u hu => hu.1.1⟩
  set τ := sInf E with hτdef
  have hτE : τ ∈ E := hEc.csInf_mem hEne hEb
  have hτ0 : 0 < τ := by
    rcases eq_or_lt_of_le hτE.1.1 with heq | hlt
    · have hz : dist z w ≤ R := by
        simpa only [← heq, hP0] using (mem_closedBall.mp hτE.2)
      linarith
    · exact hlt
  have hτT : τ < T := hτE.1.2.trans_lt hqT
  have hbefore_w : ∀ u ∈ Ico 0 τ, R < dist (P u) w := by
    intro u hu
    have hno : u ∉ E := by
      intro h
      exact (not_le.mpr hu.2) (csInf_le hEb h)
    have hball : P u ∉ closedBall w R := by
      intro h
      exact hno ⟨⟨hu.1, by linarith [hu.2, hτE.1.2]⟩, h⟩
    exact lt_of_not_ge (by simpa only [mem_closedBall] using hball)
  have hτz : R < dist (P τ) z := by
    have htri := dist_triangle z (P τ) w
    have hτw : dist (P τ) w ≤ R := mem_closedBall.mp hτE.2
    rw [dist_comm z (P τ)] at htri
    linarith
  have hPτ : ContinuousOn P (Icc 0 τ) := hP.mono (Icc_subset_Icc le_rfl hτT.le)
  set S := Icc 0 τ ∩ P ⁻¹' closedBall z R with hSdef
  have hSc : IsClosed S :=
    hPτ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, hτ0.le⟩, by
    change P 0 ∈ closedBall z R
    rw [hP0, mem_closedBall, dist_self]
    exact hR.le⟩
  have hSb : BddAbove S := ⟨τ, fun u hu => hu.1.2⟩
  set t₀ := sSup S with ht₀def
  have ht₀S : t₀ ∈ S := hSc.csSup_mem hSne hSb
  have ht₀τ : t₀ < τ := by
    rcases eq_or_lt_of_le ht₀S.1.2 with heq | hlt
    · have hz : dist (P τ) z ≤ R := by
        simpa only [heq] using (mem_closedBall.mp ht₀S.2)
      linarith
    · exact hlt
  have hafter_z : ∀ u ∈ Ioc t₀ τ, R < dist (P u) z := by
    intro u hu
    have hno : u ∉ S := by
      intro h
      exact (not_le.mpr hu.1) (le_csSup hSb h)
    have hball : P u ∉ closedBall z R := by
      intro h
      exact hno ⟨⟨by linarith [hu.1, ht₀S.1.1], hu.2⟩, h⟩
    exact lt_of_not_ge (by simpa only [mem_closedBall] using hball)
  have ht₀out : P t₀ ∉ ball z R := by
    have hS' : IsClosed (Icc t₀ τ ∩ P ⁻¹' (ball z R)ᶜ) :=
      (hP.mono (Icc_subset_Icc ht₀S.1.1 hτT.le)).preimage_isClosed_of_isClosed
        isClosed_Icc isOpen_ball.isClosed_compl
    have hsub : Icc t₀ τ ⊆ Icc t₀ τ ∩ P ⁻¹' (ball z R)ᶜ := by
      have hh := closure_minimal (s := Ioc t₀ τ)
        (t := Icc t₀ τ ∩ P ⁻¹' (ball z R)ᶜ)
        (fun u hu => ⟨Ioc_subset_Icc_self hu,
          fun h' => (not_lt.mpr (hafter_z u hu).le) (mem_ball.mp h')⟩) hS'
      rwa [closure_Ioc ht₀τ.ne] at hh
    exact (hsub ⟨le_rfl, ht₀τ.le⟩).2
  have ht₀sphere : dist (P t₀) z = R :=
    le_antisymm (mem_closedBall.mp ht₀S.2) (not_lt.mp ht₀out)
  have ht₀0 : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀S.1.1 with heq | hlt
    · rw [← heq, hP0, dist_self] at ht₀sphere
      linarith
    · exact hlt
  refine ⟨t₀, τ, ht₀0, ht₀τ, hτT, ht₀sphere, hτE.2, ?_⟩
  intro u hu
  constructor
  · rcases eq_or_lt_of_le hu.1 with heq | hlt
    · rw [← heq]; exact (by simpa only [R] using ht₀sphere.ge)
    · exact (hafter_z u ⟨hlt, hu.2.le⟩).le
  · exact hbefore_w u ⟨ht₀S.1.1.trans hu.1, hu.2⟩

 
structure CoveredStep (P : ℝ → ℂ) (Good : ℂ → ℝ → Prop)
    (ε b α : ℝ) (z w : ℂ) where
  a : ℝ
  s : ℝ
  t : ℝ
  center : ℂ
  radius : ℝ
  good : Good center radius
  radius_min : ε ^ 2 * b ≤ radius
  radius_max : radius ≤ ε * b
  start_half : P a ∈ ball center (radius / 2)
  z_far : 2 * radius < dist center z
  w_far : 2 * radius < dist center w
  a_lt_s : a < s
  s_lt_t : s < t
  inner_hit : P s ∈ sphere center (α * radius)
  outer_hit : P t ∈ sphere center radius
  before_exit : ∀ u ∈ Ico a t, P u ∈ ball center radius
  annulus_segment : ∀ u ∈ Icc s t,
    P u ∈ closedBall center radius ∧ P u ∉ ball center (α * radius)
  displacement : radius / 2 ≤ dist (P t) (P a)

 
def StepsFrom {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α : ℝ} {z w : ℂ} (a : ℝ) :
    List (CoveredStep P Good ε b α z w) → Prop
  | [] => True
  | st :: rest => st.a = a ∧ StepsFrom st.t rest

 
def StepsEnd {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α : ℝ} {z w : ℂ} (a : ℝ) :
    List (CoveredStep P Good ε b α z w) → ℝ
  | [] => a
  | st :: rest => StepsEnd st.t rest

 

theorem finite_stopping_in_corridor {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T t₀ τ : ℝ} {z w : ℂ}
    (hε : 0 < ε) (hb : 0 < b)
    (hα : 1 / 2 < α) (hα1 : α < 1)
    (hP : ContinuousOn P (Icc 0 T)) (hwend : P T = w)
    (ht₀ : 0 ≤ t₀) (hτ : t₀ < τ) (hτT : τ ≤ T)
    (hτw : P τ ∈ closedBall w (4 * ε * b))
    (hcorridor : ∀ a ∈ Ico t₀ τ,
      4 * ε * b ≤ dist (P a) z ∧ 4 * ε * b ≤ dist (P a) w)
    (hcover : ∀ a ∈ Ico t₀ τ, ∃ c r, Good c r ∧
      ε ^ 2 * b ≤ r ∧ r ≤ ε * b ∧ P a ∈ ball c (r / 2)) :
    ∃ steps : List (CoveredStep P Good ε b α z w),
      steps ≠ [] ∧ StepsFrom t₀ steps ∧ τ ≤ StepsEnd t₀ steps ∧
      (∀ st ∈ steps, st.t < T) ∧
      dist (P (StepsEnd t₀ steps)) w ≤ 6 * ε * b := by
  have hrmin : 0 < ε ^ 2 * b / 2 := by positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hP)
    (ε ^ 2 * b / 2) hrmin
  have hgo : ∀ n : ℕ, ∀ a ∈ Ico t₀ τ, τ - a ≤ n * δ →
      ∃ steps : List (CoveredStep P Good ε b α z w),
        steps ≠ [] ∧ StepsFrom a steps ∧ τ ≤ StepsEnd a steps ∧
        (∀ st ∈ steps, st.t < T) ∧
        dist (P (StepsEnd a steps)) w ≤ 6 * ε * b := by
    intro n
    induction n with
    | zero =>
        intro a ha hn
        simp only [Nat.cast_zero, zero_mul] at hn
        linarith [ha.2]
    | succ n ih =>
        intro a ha hn
        obtain ⟨c, r, hg, hrlo, hrhi, hstart⟩ := hcover a ha
        have hacorr := hcorridor a ha
        have hcz : 2 * r < dist c z :=
          center_far_of_corridor hε hb hrhi hacorr.1 (mem_ball.mp hstart)
        have hcw : 2 * r < dist c w :=
          center_far_of_corridor hε hb hrhi hacorr.2 (mem_ball.mp hstart)
        have haT : a < T := ha.2.trans_le hτT
        obtain ⟨s, t, has, hst, htT, hPs, hPt, hbefore, hann, hsep⟩ :=
          one_exit_step hP (ht₀.trans ha.1) haT (hrmin.trans_le (by linarith [hrlo]))
            hα hα1 hstart hwend hcw
        let hstep : CoveredStep P Good ε b α z w :=
          ⟨a, s, t, c, r, hg, hrlo, hrhi, hstart, hcz, hcw,
            has, hst, hPs, hPt, hbefore, hann, hsep⟩
        by_cases hterminal : τ ≤ t
        · refine ⟨[hstep], by simp, ?_, ?_, ?_, ?_⟩
          · exact ⟨rfl, trivial⟩
          · simpa only [StepsEnd] using hterminal
          · simpa only [List.mem_singleton] using fun st (hst' : st = hstep) => hst' ▸ htT
          · change dist (P t) w ≤ 6 * ε * b
            have hτc : P τ ∈ closedBall c r := by
              rcases eq_or_lt_of_le hterminal with heq | hlt
              · rw [heq]; exact (mem_sphere.mp hPt).le
              · exact ball_subset_closedBall (hbefore τ ⟨ha.2.le, hlt⟩)
            have htcr : dist (P t) c = r := mem_sphere.mp hPt
            have hτcr : dist c (P τ) ≤ r := by
              rw [dist_comm]
              exact mem_closedBall.mp hτc
            have hτwr : dist (P τ) w ≤ 4 * ε * b := mem_closedBall.mp hτw
            have htri₁ := dist_triangle (P t) c (P τ)
            have htri₂ := dist_triangle (P t) (P τ) w
            nlinarith
        · have htτ : t < τ := lt_of_not_ge hterminal
          have htmem : t ∈ Ico t₀ τ := ⟨ha.1.trans (has.trans hst).le, htτ⟩
          have hδstep : δ ≤ t - a := by
            by_contra hlt
            have hlt' : t - a < δ := lt_of_not_ge hlt
            have hdisttime : dist t a < δ := by
              rw [Real.dist_eq, abs_of_pos (by linarith)]
              exact hlt'
            have hcont := hmod t ⟨by linarith [ht₀, ha.1, has, hst], htT.le⟩
              a ⟨ht₀.trans ha.1, haT.le⟩ hdisttime
            have hcontr : dist (P t) (P a) < ε ^ 2 * b / 2 := hcont
            linarith
          have hn' : τ - t ≤ (n : ℝ) * δ := by
            push_cast at hn
            nlinarith
          obtain ⟨rest, hrestne, hfrom, hend, hlast, hbuffer⟩ := ih t htmem hn'
          refine ⟨hstep :: rest, by simp, ?_, ?_, ?_, ?_⟩
          · exact ⟨rfl, hfrom⟩
          · simpa only [StepsEnd] using hend
          · intro st hmem
            rcases List.mem_cons.mp hmem with heq | hin
            · exact heq ▸ htT
            · exact hlast st hin
          · simpa only [StepsEnd] using hbuffer
  obtain ⟨n, hn⟩ := exists_nat_ge ((τ - t₀) / δ)
  apply hgo n t₀ ⟨le_rfl, hτ⟩
  have hbound : τ - t₀ ≤ (n : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at hn
  exact hbound

 


theorem stopping_construction {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    (V : Set ℂ) {ε b κ α T : ℝ} {z w : ℂ}
    (hε : 0 < ε) (hb : 0 < b) (hεκ : ε ≤ κ / 32)
    (hα : 1 / 2 < α) (hα1 : α < 1)
    (hP : ContinuousOn P (Icc 0 T)) (hT : 0 < T)
    (hP0 : P 0 = z) (hPT : P T = w) (hzw : κ * b ≤ dist z w)
    (htrace : ∀ u ∈ Icc (0 : ℝ) T, P u ∈ V)
    (hcover : ∀ x ∈ V, ∃ c r, Good c r ∧
      ε ^ 2 * b ≤ r ∧ r ≤ ε * b ∧ x ∈ ball c (r / 2)) :
    ∃ t₀ τ : ℝ, ∃ steps : List (CoveredStep P Good ε b α z w),
      0 < t₀ ∧ t₀ < τ ∧ τ < T ∧
      steps ≠ [] ∧ StepsFrom t₀ steps ∧ τ ≤ StepsEnd t₀ steps ∧
      (∀ st ∈ steps, st.t < T) ∧
      P t₀ ∈ ball z (7 * ε * b) ∧
      P (StepsEnd t₀ steps) ∈ ball w (7 * ε * b) := by
  obtain ⟨t₀, τ, ht₀0, ht₀τ, hτT, ht₀sphere, hτw, hcorr⟩ :=
    endpoint_corridor hP hT hP0 hPT hε hb hεκ hzw
  have hcover' : ∀ a ∈ Ico t₀ τ, ∃ c r, Good c r ∧
      ε ^ 2 * b ≤ r ∧ r ≤ ε * b ∧ P a ∈ ball c (r / 2) := by
    intro a ha
    exact hcover (P a) (htrace a ⟨ht₀0.le.trans ha.1, ha.2.le.trans hτT.le⟩)
  have hcorr' : ∀ a ∈ Ico t₀ τ,
      4 * ε * b ≤ dist (P a) z ∧ 4 * ε * b ≤ dist (P a) w := by
    intro a ha
    exact ⟨(hcorr a ha).1, (hcorr a ha).2.le⟩
  obtain ⟨steps, hne, hfrom, hend, hlast, hbuffer⟩ :=
    finite_stopping_in_corridor hε hb hα hα1 hP hPT ht₀0.le ht₀τ hτT.le
      hτw hcorr' hcover'
  refine ⟨t₀, τ, steps, ht₀0, ht₀τ, hτT, hne, hfrom, hend, hlast, ?_, ?_⟩
  · rw [mem_ball]
    have hεb : 0 < ε * b := mul_pos hε hb
    linarith
  · rw [mem_ball]
    have hεb : 0 < ε * b := mul_pos hε hb
    linarith

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping

