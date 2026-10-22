import HigherDimLQGContinuity.MomentsW1.LocalChain

/-! The localized deterministic multiscale chain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox convex_obox mem_obox_self)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

/-- The scale sum in the localized chain. -/
def wnLocalChain_sum (d j n : ℕ) (c : ℕ → ℝ) (e : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico j n, (k:ℝ)^(2*d)*c k +
    (n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e

/-- Two points one mesh apart are joined by the localized multiscale chain. -/
theorem wnLocalChain_near (hd : 2 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w : Rd d) {O : ℕ → Set (Zd d)} {c : ℕ → ℝ}
    {j n : ℕ} (hj : 110 ≤ j) (hjn : j ≤ n) (hρ : 0 < ρ)
    (hδj : chainDelta j ≤ ρ/100)
    (hE : ∀ k, j ≤ k → k < n → SmallClusters (O k) (wnBadDiameter k))
    (hF : ∀ k, j ≤ k → k < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf ((k:ℤ)^2) x (2 • y) ∧
      FreeSite (O k) (2 • y) ∧ FreeSite (O (k-1)) y)
    (hc : ∀ k, j ≤ k → k < n → 0 ≤ c k)
    (hcost : ∀ k, j ≤ k → k < n → ∀ z ∈ O k,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e)
    {x y : Rd d} (hx : x ∈ obox w ρ) (hy : y ∈ obox w ρ)
    (hxy : ∀ i, |x i-y i| ≤ (2:ℝ)⁻¹ ^ j) :
    lfppDistOn ξ φ (obox w ρ) x y ≤
      (2*(2011:ℝ)^d+4004*Real.sqrt d) * wnLocalChain_sum d j n c e := by
  let A : ℝ := (2011:ℝ)^d
  let B : ℝ := 2002*Real.sqrt d
  let C : ℝ := 2*A+2*B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he0 : 0 ≤ e := by
    have := he x hx
    exact (Real.exp_pos _).le.trans this
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hS0 : 0 ≤ (n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e := by positivity
  rcases eq_or_lt_of_le hjn with heq | hlt
  · subst j
    have hseg := wnLocalChain_segment_box hφ w hx hy he
      (n := n) (L := 1) (fun i => by rw [abs_sub_comm, one_mul]; exact hxy i)
    have hsum : wnLocalChain_sum d n n c e = (n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e := by
      simp [wnLocalChain_sum]
    rw [hsum]
    have hsq : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hn1
    have hbase : Real.sqrt d*(2:ℝ)⁻¹ ^ n*e ≤
        Real.sqrt d*((n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e) := by
      have hq : (2:ℝ)⁻¹ ^ n*e ≤ (n:ℝ)^2*((2:ℝ)⁻¹ ^ n*e) := by
        exact le_mul_of_one_le_left (by positivity) hsq
      calc
        Real.sqrt d*(2:ℝ)⁻¹ ^ n*e = Real.sqrt d*((2:ℝ)⁻¹ ^ n*e) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
    have hcoef : Real.sqrt d ≤ 2*A+2*B := by
      dsimp [B]
      nlinarith [Real.sqrt_nonneg (d:ℝ), hA]
    have hcomp : Real.sqrt d*((n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e) ≤
        (2*A+2*B)*((n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e) :=
      mul_le_mul_of_nonneg_right hcoef hS0
    calc
      lfppDistOn ξ φ (obox w ρ) x y ≤
          Real.sqrt d*1*(2:ℝ)⁻¹ ^ n*e := hseg
      _ ≤ (2*A+2*B)*((n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e) := by
        simpa only [mul_one] using hbase.trans hcomp
      _ = (2*(2011:ℝ)^d+4004*Real.sqrt d)*
          ((n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e) := by dsimp [A, B]; ring
  · classical
    have hpts : ∀ z : Rd d, ∀ ℓ : ℕ, ∃ u : Zd d,
        z ∈ obox w ρ → j ≤ ℓ → ℓ < n →
          FreeSite (O ℓ) u ∧
          (∀ i, |latPt ((2:ℝ)⁻¹ ^ ℓ) u i -
            (w i+(1-chainDelta ℓ/ρ)*(z i-w i))| ≤
            (ℓ:ℝ)^2*(2:ℝ)⁻¹ ^ ℓ) ∧
          (ℓ+1<n → FreeSite (O (ℓ+1)) (2 • u)) := by
      intro z ℓ
      by_cases h : z ∈ obox w ρ ∧ j ≤ ℓ ∧ ℓ < n
      · obtain ⟨hz,h1,h2⟩ := h
        let v : Rd d := w+(1-chainDelta ℓ/ρ) • (z-w)
        obtain ⟨u,hu,hu2,hu3⟩ := wnLocalChain_point hd (by omega : 110 ≤ ℓ) h2
          (hE ℓ h1 h2)
          (fun h' p => by
            simpa only [Nat.add_sub_cancel] using hF (ℓ+1) (by omega) h' p) v
        refine ⟨u, fun _ _ _ => ⟨hu, fun i => ?_, hu3⟩⟩
        simpa only [v, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] using hu2 i
      · exact ⟨0, fun hz h1 h2 => absurd ⟨hz,h1,h2⟩ h⟩
    choose U hU using hpts
    have hδρ : chainDelta j ≤ ρ := by linarith
    have hX := wnLocalChain_half hφ w x hj hlt hρ hx hδj hE hc hcost he
      (U := U x)
      (fun ℓ h1 h2 => (hU x ℓ hx h1 h2).1)
      (fun ℓ h1 h2 => (hU x ℓ hx h1 h2).2.1)
      (fun ℓ h1 h2 => (hU x ℓ hx h1 (by omega)).2.2 h2)
    have hY := wnLocalChain_half hφ w y hj hlt hρ hy hδj hE hc hcost he
      (U := U y)
      (fun ℓ h1 h2 => (hU y ℓ hy h1 h2).1)
      (fun ℓ h1 h2 => (hU y ℓ hy h1 h2).2.1)
      (fun ℓ h1 h2 => (hU y ℓ hy h1 (by omega)).2.2 h2)
    obtain ⟨hux1,hux2,-⟩ := hU x j hx le_rfl hlt
    obtain ⟨huy1,huy2,-⟩ := hU y j hy le_rfl hlt
    let s : ℝ := (2:ℝ)⁻¹ ^ j
    have hs : 0 < s := by dsimp [s]; positivity
    have hj1 : (1:ℝ) ≤ (j:ℝ)^2 := by
      have : (1:ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
      nlinarith
    have hloc (z : Rd d) (u : Zd d) (hz : z ∈ obox w ρ)
        (hu : ∀ i, |latPt s u i -
          (w i+(1-chainDelta j/ρ)*(z i-w i))| ≤ (j:ℝ)^2*s) :
        ∀ i, |latPt s u i-w i| ≤ ρ-((j:ℝ)^2+3)*s := by
      intro i
      have h := wnLocalChain_point_margin hρ hz hδρ hu i
      have hpoly : (j:ℝ)^2+3 ≤ 999*(j:ℝ)^2 := by nlinarith
      have hprod := mul_le_mul_of_nonneg_right hpoly hs.le
      change |latPt s u i-w i| ≤ ρ-((j:ℝ)^2+3)*s
      dsimp [s] at h hprod ⊢
      linarith
    have hmid : lfppDistOn ξ φ (obox w ρ) (latPt s (U x j)) (latPt s (U y j)) ≤
        A*(j:ℝ)^(2*d)*c j := by
      have hcoef0 : 0 ≤ 1-chainDelta j/ρ := by
        rw [sub_nonneg, div_le_one hρ]
        exact hδρ
      have hcoef1 : 1-chainDelta j/ρ ≤ 1 := by
        have := div_nonneg (chainDelta_nonneg j) hρ.le
        linarith
      have hphysical : ∀ i, |latPt s (U x j) i-latPt s (U y j) i| ≤
          1003*(j:ℝ)^2*s := by
        intro i
        have e1 := hux2 i
        have e2 := huy2 i
        have hcon : |(w i+(1-chainDelta j/ρ)*(x i-w i))-
            (w i+(1-chainDelta j/ρ)*(y i-w i))| ≤ s := by
          have heq : (w i+(1-chainDelta j/ρ)*(x i-w i))-
              (w i+(1-chainDelta j/ρ)*(y i-w i)) =
              (1-chainDelta j/ρ)*(x i-y i) := by ring
          rw [heq, abs_mul, abs_of_nonneg hcoef0]
          exact (mul_le_mul_of_nonneg_right hcoef1 (abs_nonneg _)).trans
            (by simpa only [s, one_mul] using hxy i)
        have e4 := abs_sub_le (latPt s (U x j) i)
          (w i+(1-chainDelta j/ρ)*(x i-w i)) (latPt s (U y j) i)
        have e5 := abs_sub_le (w i+(1-chainDelta j/ρ)*(x i-w i))
          (w i+(1-chainDelta j/ρ)*(y i-w i)) (latPt s (U y j) i)
        have hpoly : 2*(j:ℝ)^2+1 ≤ 1003*(j:ℝ)^2 := by nlinarith
        have hprod := mul_le_mul_of_nonneg_right hpoly hs.le
        rw [abs_sub_comm (w i+(1-chainDelta j/ρ)*(y i-w i))] at e5
        dsimp [s] at e1 e2 hcon hprod e4 e5 ⊢
        linarith
      have h := wnLocalChain_link_cost hφ w hj (hc j le_rfl hlt)
        (hE j le_rfl hlt) hux1 huy1 hphysical
        (hloc x (U x j) hx hux2) (hloc y (U y j) hy huy2)
        (hcost j le_rfl hlt)
      simpa only [A, s, mul_assoc] using h
    have hXV : latPt s (U x j) ∈ obox w ρ := fun i => by
      have h := hloc x (U x j) hx hux2 i
      have hp : 0 < ((j:ℝ)^2+3)*s := by positivity
      linarith
    have hYV : latPt s (U y j) ∈ obox w ρ := fun i => by
      have h := hloc y (U y j) hy huy2 i
      have hp : 0 < ((j:ℝ)^2+3)*s := by positivity
      linarith
    have htri : lfppDistOn ξ φ (obox w ρ) x y ≤
        lfppDistOn ξ φ (obox w ρ) x (latPt s (U x j)) +
          (lfppDistOn ξ φ (obox w ρ) (latPt s (U x j)) (latPt s (U y j)) +
            lfppDistOn ξ φ (obox w ρ) y (latPt s (U y j))) := by
      have hcbox := convex_obox w ρ
      refine (lfppDistOn_triangle hφ (PcwJoined.of_convex hcbox hx hXV)
        (PcwJoined.of_convex hcbox hXV hy)).trans (add_le_add (le_refl _) ?_)
      rw [lfppDistOn_comm ξ φ _ y (latPt s (U y j))]
      exact lfppDistOn_triangle hφ (PcwJoined.of_convex hcbox hXV hYV)
        (PcwJoined.of_convex hcbox hYV hy)
    let F : ℝ := (j:ℝ)^(2*d)*c j
    let G : ℝ := ∑ k ∈ Finset.Ico (j+1) n, (k:ℝ)^(2*d)*c k
    let S : ℝ := (n:ℝ)^2*(2:ℝ)⁻¹ ^ n*e
    have hsum : wnLocalChain_sum d j n c e = F+G+S := by
      rw [wnLocalChain_sum, Finset.sum_eq_sum_Ico_succ_bot hlt]
    have hF0 : 0 ≤ F := mul_nonneg (by positivity) (hc j le_rfl hlt)
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun k hk => by
      rw [Finset.mem_Ico] at hk
      exact mul_nonneg (by positivity) (hc k (by omega) hk.2)
    have hS0' : 0 ≤ S := hS0
    have hmid' : lfppDistOn ξ φ (obox w ρ) (latPt s (U x j)) (latPt s (U y j)) ≤
        A*F := by simpa only [F, mul_assoc] using hmid
    have hCeq : 2*(2011:ℝ)^d+4004*Real.sqrt d = C := by
      dsimp [C, A, B]
      ring
    rw [hCeq]
    rw [hsum]
    have hX' : lfppDistOn ξ φ (obox w ρ) x (latPt s (U x j)) ≤ B*S+A*G := by
      simpa only [A, B, S, G, s, mul_assoc] using hX
    have hY' : lfppDistOn ξ φ (obox w ρ) y (latPt s (U y j)) ≤ B*S+A*G := by
      simpa only [A, B, S, G, s, mul_assoc] using hY
    have hA_F := mul_nonneg hA hF0
    have hA_G := mul_nonneg hA hG0
    have hA_S := mul_nonneg hA hS0'
    have hB_F := mul_nonneg hB hF0
    have hB_G := mul_nonneg hB hG0
    have hB_S := mul_nonneg hB hS0'
    dsimp [C]
    nlinarith

/-- Localized self-internal diameter from the near-pair chain and segment subdivision. -/
theorem wnLocalChain_diameter (hd : 2 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w : Rd d) {O : ℕ → Set (Zd d)} {c : ℕ → ℝ}
    {j n : ℕ} (hj : 110 ≤ j) (hjn : j ≤ n) (hρ : 0 < ρ)
    (hδj : chainDelta j ≤ ρ/100)
    (hE : ∀ k, j ≤ k → k < n → SmallClusters (O k) (wnBadDiameter k))
    (hF : ∀ k, j ≤ k → k < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf ((k:ℤ)^2) x (2 • y) ∧
      FreeSite (O k) (2 • y) ∧ FreeSite (O (k-1)) y)
    (hc : ∀ k, j ≤ k → k < n → 0 ≤ c k)
    (hcost : ∀ k, j ≤ k → k < n → ∀ z ∈ O k,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e) :
    selfDiam ξ φ w ρ ≤
      (2*ρ*(2:ℝ)^j+2) * (2*(2011:ℝ)^d+4004*Real.sqrt d) *
        wnLocalChain_sum d j n c e := by
  let T : ℝ := wnLocalChain_sum d j n c e
  let C : ℝ := 2*(2011:ℝ)^d+4004*Real.sqrt d
  have he0 : 0 ≤ e := by
    have := he w (mem_obox_self w hρ)
    exact (Real.exp_pos _).le.trans this
  have hT : 0 ≤ T := by
    dsimp [T, wnLocalChain_sum]
    apply add_nonneg
    · exact Finset.sum_nonneg fun k hk => by
        rw [Finset.mem_Ico] at hk
        exact mul_nonneg (by positivity) (hc k hk.1 hk.2)
    · positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let ε : ℝ := (2:ℝ)⁻¹ ^ j
  have hε : 0 < ε := by dsimp [ε]; positivity
  let N : ℕ := ⌈2*ρ/ε⌉₊+1
  have hN0 : (0:ℝ) < N := by dsimp [N]; positivity
  have hNmesh : 2*ρ ≤ (N:ℝ)*ε := by
    have hceil : 2*ρ/ε ≤ (N:ℝ) := by
      have := Nat.le_ceil (2*ρ/ε)
      dsimp [N]
      push_cast
      linarith
    exact (div_le_iff₀ hε).mp hceil
  have hpow : ε*(2:ℝ)^j=1 := by
    dsimp [ε]
    rw [← mul_pow]
    norm_num
  have hratio : 2*ρ/ε = 2*ρ*(2:ℝ)^j := by
    apply (div_eq_iff hε.ne').2
    linear_combination 2*ρ*hpow.symm
  have hNupper : (N:ℝ) ≤ 2*ρ*(2:ℝ)^j+2 := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg (by positivity : 0 ≤ 2*ρ) hε.le)
    dsimp [N]
    rw [hratio]
    push_cast
    rw [hratio] at hceil
    linarith
  refine selfDiam_le (by positivity) fun x hx y hy => ?_
  let v : ℕ → Rd d := fun t => x+((t:ℝ)/N) • (y-x)
  have hvV : ∀ t ≤ N, v t ∈ obox w ρ := by
    intro t ht
    exact (convex_obox w ρ).add_smul_sub_mem hx hy
      ⟨by positivity, by rw [div_le_one hN0]; exact_mod_cast ht⟩
  have hsum := lfppDistOn_le_sum (ζ := ξ) hφ v (fun _ => obox w ρ)
    (fun _ => subset_rfl) N (fun t ht =>
      PcwJoined.of_convex (convex_obox w ρ) (hvV t ht.le) (hvV (t+1) ht))
  have hv0 : v 0=x := by simp [v]
  have hvN : v N=y := by
    simp only [v]
    rw [div_self hN0.ne', one_smul, add_sub_cancel]
  rw [hv0,hvN] at hsum
  have hterm : ∀ t ∈ Finset.range N,
      lfppDistOn ξ φ (obox w ρ) (v t) (v (t+1)) ≤ C*T := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hxy : ∀ i, |v t i-v (t+1) i| ≤ ε := by
      intro i
      simp only [v, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have heq : x i+(t:ℝ)/N*(y i-x i)-
          (x i+((t+1:ℕ):ℝ)/N*(y i-x i)) = -(y i-x i)/N := by
        push_cast
        field_simp
        ring
      rw [heq, abs_div, abs_neg, abs_of_pos hN0, div_le_iff₀ hN0]
      have hxi : |x i-w i| < ρ := hx i
      have hyi : |y i-w i| < ρ := hy i
      have habs := abs_sub (y i-w i) (x i-w i)
      have heq' : (y i-w i)-(x i-w i)=y i-x i := by ring
      rw [heq'] at habs
      linarith
    simpa only [C, T, ε] using
      (wnLocalChain_near hd hφ w hj hjn hρ hδj hE hF hc hcost he
        (hvV t ht.le) (hvV (t+1) ht) hxy)
  calc
    lfppDistOn ξ φ (obox w ρ) x y ≤
        ∑ t ∈ Finset.range N, lfppDistOn ξ φ (obox w ρ) (v t) (v (t+1)) := hsum
    _ ≤ ∑ _t ∈ Finset.range N, C*T := Finset.sum_le_sum hterm
    _ = (N:ℝ)*C*T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ (2*ρ*(2:ℝ)^j+2)*C*T := by
      have hCT : 0 ≤ C*T := mul_nonneg hC hT
      nlinarith
    _ = (2*ρ*(2:ℝ)^j+2)*(2*(2011:ℝ)^d+4004*Real.sqrt d)*
        wnLocalChain_sum d j n c e := rfl

/-- The direct segment bound for every local box, including the terminal-scale case. -/
theorem wnLocalChain_diameter_segment {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w : Rd d) (hρ : 0 < ρ)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e) :
    selfDiam ξ φ w ρ ≤ 2*Real.sqrt (d:ℝ)*ρ*e := by
  have he0 : 0 ≤ e := by
    have := he w (mem_obox_self w hρ)
    exact (Real.exp_pos _).le.trans this
  refine selfDiam_le (by positivity) fun x hx y hy => ?_
  have hseg := lfppDistOn_le_of_segment hφ
    (mapsTo_segPath (convex_obox w ρ) hx hy)
    (fun u hu => he _ (segPath_mem_of_convex (convex_obox w ρ) hx hy hu))
  have hnorm := norm_sub_le_of_mem_cbox
    (HigherDimLFPP.DGZ.obox_subset_cbox w ρ hy)
    (HigherDimLFPP.DGZ.obox_subset_cbox w ρ hx)
  calc
    lfppDistOn ξ φ (obox w ρ) x y ≤ e*‖y-x‖ := hseg
    _ ≤ e*(Real.sqrt d*(2*ρ)) := mul_le_mul_of_nonneg_left hnorm he0
    _ = 2*Real.sqrt d*ρ*e := by ring

/-- Localized self-internal chaining with a contraction drift toward the box center. -/
theorem chain_selfInternal_loc (hd : 2 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ e ρ : ℝ} (w : Rd d) {O : ℕ → Set (Zd d)} {c : ℕ → ℝ}
    {k₀ j n : ℕ} (hk₀ : 110 ≤ k₀) (hk₀j : k₀ ≤ j) (hjn : j ≤ n)
    (hρ : 0 < ρ) (hδj : chainDelta j ≤ ρ/100)
    (hE : ∀ k, k₀ ≤ k → k < n → SmallClusters (O k) (wnBadDiameter k))
    (hF : ∀ k, k₀ ≤ k → k < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf ((k:ℤ)^2) x (2 • y) ∧
      FreeSite (O k) (2 • y) ∧ FreeSite (O (k-1)) y)
    (hc : ∀ k, k₀ ≤ k → k < n → 0 ≤ c k)
    (hcost : ∀ k, k₀ ≤ k → k < n → ∀ z ∈ O k,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k)
    (he : ∀ z ∈ obox w ρ, Real.exp (ξ * φ z) ≤ e) :
    (∀ x ∈ obox w ρ, ∀ y ∈ obox w ρ,
      (∀ i, |x i-y i| ≤ (2:ℝ)⁻¹ ^ j) →
      lfppDistOn ξ φ (obox w ρ) x y ≤
        (2*(2011:ℝ)^d+4004*Real.sqrt d)*wnLocalChain_sum d j n c e) ∧
    selfDiam ξ φ w ρ ≤
      (2*ρ*(2:ℝ)^j+2)*(2*(2011:ℝ)^d+4004*Real.sqrt d)*wnLocalChain_sum d j n c e ∧
    selfDiam ξ φ w ρ ≤ 2*Real.sqrt (d:ℝ)*ρ*e := by
  have hj : 110 ≤ j := hk₀.trans hk₀j
  have hE' : ∀ k, j ≤ k → k < n → SmallClusters (O k) (wnBadDiameter k) :=
    fun k h1 h2 => hE k (hk₀j.trans h1) h2
  have hF' : ∀ k, j ≤ k → k < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf ((k:ℤ)^2) x (2 • y) ∧
      FreeSite (O k) (2 • y) ∧ FreeSite (O (k-1)) y :=
    fun k h1 h2 => hF k (hk₀j.trans h1) h2
  have hc' : ∀ k, j ≤ k → k < n → 0 ≤ c k :=
    fun k h1 h2 => hc k (hk₀j.trans h1) h2
  have hcost' : ∀ k, j ≤ k → k < n → ∀ z ∈ O k,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ φ (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k :=
    fun k h1 h2 => hcost k (hk₀j.trans h1) h2
  refine ⟨?_, ?_, wnLocalChain_diameter_segment hφ w hρ he⟩
  · intro x hx y hy hxy
    exact wnLocalChain_near hd hφ w hj hjn hρ hδj hE' hF' hc' hcost' he hx hy hxy
  · exact wnLocalChain_diameter hd hφ w hj hjn hρ hδj hE' hF' hc' hcost' he

end HigherDimLQGContinuity
