import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb

/-- Derivative of `η ↦ (1+η²)^p`. -/
theorem bb_T1 (p η : ℝ) :
    HasDerivAt (fun η : ℝ => (1 + η ^ 2) ^ p) (2 * η * p * (1 + η ^ 2) ^ (p - 1)) η := by
  have h1 : HasDerivAt (fun η : ℝ => 1 + η ^ 2) (2 * η) η :=
    ((hasDerivAt_pow 2 η).const_add 1).congr_deriv (by norm_num)
  exact h1.rpow_const (Or.inl (by positivity))

/-- Derivative of `η ↦ 2 η p (1+η²)^(p-1)`. -/
theorem bb_F (p η : ℝ) :
    HasDerivAt (fun η : ℝ => 2 * η * p * (1 + η ^ 2) ^ (p - 1))
      (2 * p * (1 + η ^ 2) ^ (p - 1)
        + 2 * η * p * ((p - 1) * (2 * η) * (1 + η ^ 2) ^ (p - 1 - 1))) η := by
  have h1 : HasDerivAt (fun η : ℝ => 2 * η * p) (2 * p) η :=
    (((hasDerivAt_id' η).const_mul 2).mul_const p).congr_deriv (by ring)
  have h2 := h1.mul (bb_T1 (p - 1) η)
  exact h2.congr_deriv (by ring)

theorem bb_key_aux (ν V p b η s K : ℝ) (hν : 0 ≤ ν) (hb : |b| ≤ V)
    (hK : ν * (4 * |p * (p - 1)| + 2 * |p|) + V * |p| ≤ K) (hs0 : 0 < s)
    (hsu : s * (1 + η ^ 2) = 1) :
    ν * (2 * p * s + 2 * η * p * ((p - 1) * (2 * η) * (s * s))) + b * (2 * η * p * s) ≤ K := by
  have hs1 : s ≤ 1 := by nlinarith [mul_nonneg hs0.le (sq_nonneg η)]
  have h2q : |2 * (η * s)| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hs0.le (sq_nonneg (η + 1))]
    · nlinarith [mul_nonneg hs0.le (sq_nonneg (η - 1))]
  have hq2 : (η * s) ^ 2 ≤ 1 := by
    have h := abs_le.mp h2q
    nlinarith [mul_nonneg (by linarith [h.1] : (0:ℝ) ≤ 2 * (η * s) + 1)
      (by linarith [h.2] : (0:ℝ) ≤ 1 - 2 * (η * s))]
  have hA : ν * (4 * (p * (p - 1) * (η * s) ^ 2)) ≤ ν * (4 * |p * (p - 1)|) := by
    have h := le_abs_self (p * (p - 1) * (η * s) ^ 2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg (η * s))] at h
    have h' : p * (p - 1) * (η * s) ^ 2 ≤ |p * (p - 1)| := by
      nlinarith [mul_le_mul_of_nonneg_left hq2 (abs_nonneg (p * (p - 1)))]
    exact mul_le_mul_of_nonneg_left (by linarith) hν
  have hB : ν * (2 * p * s) ≤ ν * (2 * |p|) := by
    have h1 : p * s ≤ |p| := by
      calc p * s ≤ |p| * s := mul_le_mul_of_nonneg_right (le_abs_self p) hs0.le
        _ ≤ |p| * 1 := mul_le_mul_of_nonneg_left hs1 (abs_nonneg p)
        _ = |p| := mul_one _
    exact mul_le_mul_of_nonneg_left (by linarith) hν
  have hC : b * (2 * η * p * s) ≤ V * |p| := by
    calc b * (2 * η * p * s) = b * (p * (2 * (η * s))) := by ring
      _ ≤ |b * (p * (2 * (η * s)))| := le_abs_self _
      _ = |b| * (|p| * |2 * (η * s)|) := by rw [abs_mul, abs_mul]
      _ ≤ V * (|p| * 1) :=
          mul_le_mul hb (mul_le_mul_of_nonneg_left h2q (abs_nonneg p))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (le_trans (abs_nonneg b) hb)
      _ = V * |p| := by ring
  have eq : ν * (2 * p * s + 2 * η * p * ((p - 1) * (2 * η) * (s * s))) + b * (2 * η * p * s)
      = ν * (2 * p * s) + ν * (4 * (p * (p - 1) * (η * s) ^ 2)) + b * (2 * η * p * s) := by
    ring
  rw [eq]
  have hK' : ν * (4 * |p * (p - 1)|) + ν * (2 * |p|) + V * |p| ≤ K := by
    have : ν * (4 * |p * (p - 1)| + 2 * |p|) = ν * (4 * |p * (p - 1)|) + ν * (2 * |p|) := by
      ring
    linarith
  linarith [hA, hB, hC, hK']

/-- The barrier inequality for one power `(1+η²)^p`, with the constant `K` absorbing `ν` and
the drift bound `V`. -/
theorem bb_key (ν V p b η K : ℝ) (hν : 0 ≤ ν) (hb : |b| ≤ V)
    (hK : ν * (4 * |p * (p - 1)| + 2 * |p|) + V * |p| ≤ K) :
    ν * (2 * p * (1 + η ^ 2) ^ (p - 1)
        + 2 * η * p * ((p - 1) * (2 * η) * (1 + η ^ 2) ^ (p - 1 - 1)))
      + b * (2 * η * p * (1 + η ^ 2) ^ (p - 1)) ≤ K * (1 + η ^ 2) ^ p := by
  have hu : (1 + η ^ 2) ≠ 0 := by positivity
  have hP : 0 < (1 + η ^ 2) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hk := bb_key_aux ν V p b η (1 + η ^ 2)⁻¹ K hν hb hK (by positivity)
    (inv_mul_cancel₀ hu)
  have r1 : (1 + η ^ 2) ^ (p - 1) = (1 + η ^ 2) ^ p * (1 + η ^ 2)⁻¹ := by
    rw [Real.rpow_sub_one hu p, div_eq_mul_inv]
  have r2 : (1 + η ^ 2) ^ (p - 1 - 1) = (1 + η ^ 2) ^ p * (1 + η ^ 2)⁻¹ * (1 + η ^ 2)⁻¹ := by
    rw [Real.rpow_sub_one hu (p - 1), r1, div_eq_mul_inv]
  rw [r2, r1]
  linarith [mul_le_mul_of_nonneg_left hk hP.le]

/-- The derivative in `η` of a function of `x.2` alone. -/
theorem bb_pd0_snd (ψ ψ1 : ℝ → ℝ) (h1 : ∀ η, HasDerivAt ψ (ψ1 η) η) :
    B0579.pd 0 (fun y : B0579.Plane => ψ y.2) = fun _ => 0 := by
  funext y
  have hf : HasFDerivAt (fun y : B0579.Plane => ψ y.2)
      (ψ1 y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    (h1 y.2).comp_hasFDerivAt y hasFDerivAt_snd
  unfold B0579.pd
  rw [hf.fderiv]
  simp [B0579.dir]

theorem bb_pd1_snd (ψ ψ1 : ℝ → ℝ) (h1 : ∀ η, HasDerivAt ψ (ψ1 η) η) :
    B0579.pd 1 (fun y : B0579.Plane => ψ y.2) = fun y => ψ1 y.2 := by
  funext y
  have hf : HasFDerivAt (fun y : B0579.Plane => ψ y.2)
      (ψ1 y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    (h1 y.2).comp_hasFDerivAt y hasFDerivAt_snd
  unfold B0579.pd
  rw [hf.fderiv]
  simp [B0579.dir]

theorem bb_lap_snd (ψ ψ1 ψ2 : ℝ → ℝ) (h1 : ∀ η, HasDerivAt ψ (ψ1 η) η)
    (h2 : ∀ η, HasDerivAt ψ1 (ψ2 η) η) (x : B0579.Plane) :
    lapP (fun y : B0579.Plane => ψ y.2) x = ψ2 x.2 := by
  unfold lapP
  rw [bb_pd0_snd ψ ψ1 h1, bb_pd1_snd ψ ψ1 h1, bb_pd1_snd ψ1 ψ2 h2]
  simp [B0579.pd, B0579.dir]

/-- The barrier constant, depending only on `ν`, the drift bound `V` and the exponent `p`. -/
def bbK (ν V p : ℝ) : ℝ := ν * (4 * |p * (p - 1)| + 2 * |p|) + V * |p|

theorem bb_two_d1 (c1 c2 p1 p2 η : ℝ) :
    HasDerivAt (fun η : ℝ => c1 * (1 + η ^ 2) ^ p1 + c2 * (1 + η ^ 2) ^ p2)
      (c1 * (2 * η * p1 * (1 + η ^ 2) ^ (p1 - 1)) + c2 * (2 * η * p2 * (1 + η ^ 2) ^ (p2 - 1)))
      η :=
  ((bb_T1 p1 η).const_mul c1).add ((bb_T1 p2 η).const_mul c2)

theorem bb_two_d2 (c1 c2 p1 p2 η : ℝ) :
    HasDerivAt
      (fun η : ℝ => c1 * (2 * η * p1 * (1 + η ^ 2) ^ (p1 - 1))
        + c2 * (2 * η * p2 * (1 + η ^ 2) ^ (p2 - 1)))
      (c1 * (2 * p1 * (1 + η ^ 2) ^ (p1 - 1)
          + 2 * η * p1 * ((p1 - 1) * (2 * η) * (1 + η ^ 2) ^ (p1 - 1 - 1)))
        + c2 * (2 * p2 * (1 + η ^ 2) ^ (p2 - 1)
          + 2 * η * p2 * ((p2 - 1) * (2 * η) * (1 + η ^ 2) ^ (p2 - 1 - 1)))) η :=
  ((bb_F p1 η).const_mul c1).add ((bb_F p2 η).const_mul c2)

/-- **Leaf `/2`** (SP 2100-2105): the explicit barrier. -/
theorem bwdBarrier : BwdBarrier := by
  intro ν V N hν hV0
  refine ⟨bbK ν V (-N), bbK ν V (1 / 2), ?_⟩
  intro c s t b0 b1 hb A ε hA hε
  have hcont : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane =>
      A * Real.exp (bbK ν V (-N) * (t - z.1)) * (1 + z.2.2 ^ 2) ^ (-N) +
        ε * Real.exp (bbK ν V (1 / 2) * (t - z.1)) * (1 + z.2.2 ^ 2) ^ ((1 : ℝ) / 2)) := by
    have hq : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane => 1 + z.2.2 ^ 2) :=
      contDiff_const.add ((contDiff_snd.comp contDiff_snd).pow 2)
    have hqne : ∀ z : ℝ × B0579.Plane, 1 + z.2.2 ^ 2 ≠ 0 := fun z => by positivity
    have hg : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane => (1 + z.2.2 ^ 2) ^ (-N)) :=
      hq.rpow_const_of_ne hqne
    have hh : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane => (1 + z.2.2 ^ 2) ^ ((1 : ℝ) / 2)) :=
      hq.rpow_const_of_ne hqne
    have hE1 : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane =>
        Real.exp (bbK ν V (-N) * (t - z.1))) :=
      Real.contDiff_exp.comp (contDiff_const.mul (contDiff_const.sub contDiff_fst))
    have hE2 : ContDiff ℝ 2 (fun z : ℝ × B0579.Plane =>
        Real.exp (bbK ν V (1 / 2) * (t - z.1))) :=
      Real.contDiff_exp.comp (contDiff_const.mul (contDiff_const.sub contDiff_fst))
    exact ((contDiff_const.mul hE1).mul hg).add ((contDiff_const.mul hE2).mul hh)
  refine ⟨hcont.contDiffOn, fun r _ x => rfl, ?_⟩
  intro r hr x
  have hr' : r ∈ Icc s t := Ioo_subset_Icc_self hr
  have hbr := hb r hr' x
  have hE1pos : 0 < Real.exp (bbK ν V (-N) * (t - r)) := Real.exp_pos _
  have hE2pos : 0 < Real.exp (bbK ν V (1 / 2) * (t - r)) := Real.exp_pos _
  have hc1 : 0 ≤ A * Real.exp (bbK ν V (-N) * (t - r)) := mul_nonneg hA hE1pos.le
  have hc2 : 0 ≤ ε * Real.exp (bbK ν V (1 / 2) * (t - r)) := mul_nonneg hε hE2pos.le
  have e1 : HasDerivAt (fun r' : ℝ => Real.exp (bbK ν V (-N) * (t - r')))
      (Real.exp (bbK ν V (-N) * (t - r)) * (bbK ν V (-N) * -1)) r :=
    (((hasDerivAt_id' r).const_sub t).const_mul (bbK ν V (-N))).exp
  have e2 : HasDerivAt (fun r' : ℝ => Real.exp (bbK ν V (1 / 2) * (t - r')))
      (Real.exp (bbK ν V (1 / 2) * (t - r)) * (bbK ν V (1 / 2) * -1)) r :=
    (((hasDerivAt_id' r).const_sub t).const_mul (bbK ν V (1 / 2))).exp
  have hDeriv := ((e1.const_mul A).mul_const ((1 + x.2 ^ 2) ^ (-N))).add
    ((e2.const_mul ε).mul_const ((1 + x.2 ^ 2) ^ ((1 : ℝ) / 2)))
  refine ⟨_, hDeriv, ?_⟩
  -- the spatial part: W r x = ψ x.2 with ψ a two-term power sum
  have h1 := bb_two_d1 (A * Real.exp (bbK ν V (-N) * (t - r)))
    (ε * Real.exp (bbK ν V (1 / 2) * (t - r))) (-N) (1 / 2)
  have h2 := bb_two_d2 (A * Real.exp (bbK ν V (-N) * (t - r)))
    (ε * Real.exp (bbK ν V (1 / 2) * (t - r))) (-N) (1 / 2)
  have hz := bb_lap_snd _ _ _ (fun η => h1 η) (fun η => h2 η) x
  have hz0 := congrFun (bb_pd0_snd _ _ (fun η => h1 η)) x
  have hz1 := congrFun (bb_pd1_snd _ _ (fun η => h1 η)) x
  have k1 := bb_key ν V (-N) (b1 r x) x.2 (bbK ν V (-N)) hν.le hbr.2 (le_of_eq (by unfold bbK; rfl))
  have k2 := bb_key ν V (1 / 2) (b1 r x) x.2 (bbK ν V (1 / 2)) hν.le hbr.2 (le_of_eq (by unfold bbK; rfl))
  have m1 := mul_le_mul_of_nonneg_left k1 hc1
  have m2 := mul_le_mul_of_nonneg_left k2 hc2
  dsimp only at hz hz0 hz1 ⊢
  rw [hz, hz0, hz1]
  nlinarith [m1, m2]

end UnforcedLeray.Short.IIb
