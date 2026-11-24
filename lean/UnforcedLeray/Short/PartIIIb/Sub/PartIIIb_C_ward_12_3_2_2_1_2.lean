import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2` (decomposition): `RawResidualD2NearBound`

Source of record:
`the November 2 reference manuscript`,
lines 2548-2551 at `k = 2`, 1270-1304, 1305-1325: in the cylinder `0 < ϱ ≤ R₀`, the similarity
ring residual `F_R = rawResidualC p` agrees off the axis with the globally `C^∞` Cartesian
Navier-Stokes expression `Fc = L₀ p.ν U + advT U U + gradT Pw` (`IIb.RingLiftSmoothExt` and
`IIb.ringResidualCartesianNS_proof`), and its all-age heat expansion gives axial decay
`‖∂_j ∂_l (rawResidualC p)(τ, y)‖ ≤ C (1 + |y₃|)^{-2}`.

This file proves:
1. **Shell transfer (`RawNear2Sub.shell_near_of_far`)**: on any intermediate shell `R₁ < ϱ(y) ≤ R₀`
   with `0 < R₁`, the far-field envelope `ϱ^{-3} (1 + |y₃|/ϱ)^{-2}` is bounded by
   `(R₁^{-3} (max 1 R₀)^2) (1 + |y₃|)^{-2}`, reducing arbitrary `R₀ > 0` to a fixed radius `R₁`
   once `RawResidualD2FarDecay` holds (`RawNear2Sub.rawResidualD2NearBound_of_far_and_core`);
2. **Compact cylinder bound (`RawNear2Sub.compact_cyl_bound_of_smoothExt`)**: from
   `IIb.RingLiftSmoothExt` and `IIb.ringResidualCartesianNS_proof`, for any `R₀ > 0` and axial
   height `Z₀ ≥ 0`, compactness of `[0, P] × closedBall 0 (R₀ + Z₀)` bounds
   `‖∂_j ∂_l (rawResidualC p)(τ, y)‖` by `C (1 + |y₃|)^{-2}` on `{0 < ϱ(y) ≤ R₀, |y₃| ≤ Z₀}`;
3. **Complete reduction (`rawResidualD2NearBound_of`)**: combines `IIb.RingLiftSmoothExt`
   (task `PartII-b:R1/6`) on the compact core `|y₃| ≤ Z₀` with the large-`|y₃|` axial tail
   `RawResidualD2AxialTail` (task `PartIII-b:C/ward/12/3/2/2/1/2/1`) on
   `{0 < ϱ(y) ≤ R₀, Z₀ < |y₃|}`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params advT)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC isExactPlanarTrain_params
  isExactPlanarTrain_params_rpow)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Large-`|y₃|` axial tail of the order-2 raw ring residual in the near-axis cylinder**
(`the November 2 reference manuscript`, lines 1270-1304, 1310-1325, 2548-2551): for `0 < ϱ(y) ≤ R₀` and
`|y₃| > Z₀`, the all-age heat expansion of the residual profile gives
`‖∂_j ∂_l (rawResidualC p)(τ, y)‖ ≤ C (1 + |y₃|)^{-2}`. -/
def RawResidualD2AxialTail : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ (j l : Fin 3) (R0 : ℝ), 0 < R0 →
      ∃ C Z0 : ℝ, 0 ≤ Z0 ∧ ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
        UnforcedLeray.Axi.ϱ y ≠ 0 → Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 → Z0 < |y 2| →
        ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)

namespace RawNear2Sub

/-- Euclidean norm on `Space` is bounded by `ϱ(y) + |y₃|`. -/
theorem norm_space_le_ϱ_add_abs_two (y : UnforcedLeray.Space) :
    ‖y‖ ≤ UnforcedLeray.Axi.ϱ y + |y 2| := by
  have h0 : 0 ≤ UnforcedLeray.Axi.ϱ y + |y 2| :=
    add_nonneg (UnforcedLeray.Axi.ϱ_nonneg y) (abs_nonneg _)
  rw [← Real.sqrt_sq h0, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have h1 := UnforcedLeray.Axi.ϱ_sq y
  have h2 : 0 ≤ 2 * UnforcedLeray.Axi.ϱ y * |y 2| :=
    mul_nonneg (mul_nonneg (by norm_num) (UnforcedLeray.Axi.ϱ_nonneg y)) (abs_nonneg _)
  have h3 : |y 2| ^ 2 = y 2 ^ 2 := sq_abs (y 2)
  nlinarith

/-- On `0 < R₁ < ϱ(y) ≤ R₀`, the far-field weight `ϱ^{-3} (1 + |y₃|/ϱ)^{-2}` is bounded by
`(R₁^{-3} (max 1 R₀)^2) (1 + |y₃|)^{-2}`. -/
theorem shell_near_of_far {R1 R0 : ℝ} (hR1 : 0 < R1) {y : UnforcedLeray.Space}
    (hy1 : R1 < UnforcedLeray.Axi.ϱ y) (hy0 : UnforcedLeray.Axi.ϱ y ≤ R0) :
    UnforcedLeray.Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-2 : ℝ) ≤
      (R1 ^ (-3 : ℝ) * max 1 R0 ^ (2 : ℝ)) * (1 + |y 2|) ^ (-2 : ℝ) := by
  have hρ : 0 < UnforcedLeray.Axi.ϱ y := hR1.trans hy1
  have hrp1 : UnforcedLeray.Axi.ϱ y ^ (-3 : ℝ) ≤ R1 ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hR1 hy1.le (by norm_num)
  set M : ℝ := max 1 R0
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMR : UnforcedLeray.Axi.ϱ y ≤ M := hy0.trans (le_max_right _ _)
  have hdiv : (1 + |y 2|) / M ≤ 1 + |y 2| / UnforcedLeray.Axi.ϱ y := by
    rw [add_div]
    have h1 : 1 / M ≤ 1 := (div_le_one hM0).2 hM1
    have h2 : |y 2| / M ≤ |y 2| / UnforcedLeray.Axi.ϱ y :=
      div_le_div_of_nonneg_left (abs_nonneg _) hρ hMR
    linarith
  have hposL : 0 < (1 + |y 2|) / M := div_pos (by positivity) hM0
  have hrp2 : (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-2 : ℝ) ≤
      ((1 + |y 2|) / M) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hposL hdiv (by norm_num)
  have hdiv_rpow : ((1 + |y 2|) / M) ^ (-2 : ℝ) = M ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) := by
    rw [Real.div_rpow (by positivity) hM0.le, div_eq_iff (Real.rpow_pos_of_pos hM0 _).ne']
    have hM_mul : M ^ (2 : ℝ) * M ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_add hM0]
      norm_num
    calc (1 + |y 2|) ^ (-2 : ℝ)
        = (1 + |y 2|) ^ (-2 : ℝ) * (M ^ (2 : ℝ) * M ^ (-2 : ℝ)) := by rw [hM_mul, mul_one]
      _ = M ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) * M ^ (-2 : ℝ) := by ring
  rw [hdiv_rpow] at hrp2
  calc UnforcedLeray.Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-2 : ℝ)
      ≤ R1 ^ (-3 : ℝ) * (M ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ)) :=
        mul_le_mul hrp1 hrp2 (by positivity) (by positivity)
    _ = (R1 ^ (-3 : ℝ) * M ^ (2 : ℝ)) * (1 + |y 2|) ^ (-2 : ℝ) := by ring

/-- From `IIb.RingLiftSmoothExt` and `IIb.ringResidualCartesianNS_proof`, on any compact cylinder
`{τ ∈ (0, P], 0 < ϱ(y) ≤ R₀, |y₃| ≤ Z₀}` the second spatial derivatives of `rawResidualC p`
satisfy `‖∂_j ∂_l (rawResidualC p)(τ, y)‖ ≤ C (1 + |y₃|)^{-2}`. -/
theorem compact_cyl_bound_of_smoothExt (hExt : UnforcedLeray.Short.IIb.RingLiftSmoothExt) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → ∀ (j l : Fin 3) (R0 Z0 : ℝ), 0 < R0 → 0 ≤ Z0 →
        ∃ C : ℝ, ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
          UnforcedLeray.Axi.ϱ y ≠ 0 → Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 → |y 2| ≤ Z0 →
          ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ) := by
  obtain ⟨ν₀, hν₀, H⟩ := hExt
  refine ⟨ν₀, hν₀, fun p htr hν hc hR j l R0 Z0 hR0 hZ0 => ?_⟩
  obtain ⟨U, Pw, hU, hPw, -, -, hext⟩ :=
    H p.ν ⟨p.ν_pos, hν⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p htr hc) p.R hR
  let Fc : ℝ × UnforcedLeray.Space → CVec3 :=
    fun x => UnforcedLeray.B0411.L0 p.ν U x + advT U U x + gradT Pw x
  have hFc : ContDiff ℝ ∞ Fc := RawDeriv2EnvSub.contDiff_ns_rhs p.ν hU hPw
  have hoff : ∀ x : ℝ × UnforcedLeray.Space, UnforcedLeray.Axi.ϱ x.2 ≠ 0 →
      rawResidualC p x = Fc x := fun x hx =>
    UnforcedLeray.Short.IIb.ringResidualCartesianNS_proof p.ν p.c p.R
      (trainStream p) (trainPressure p) p.ν_pos p.c_pos hR
      (isExactPlanarTrain_params p htr) U Pw hU hPw hext x.1 x.2 hx
  let Fn : ℝ × UnforcedLeray.Space → CVec3 := dy j (dy l Fc)
  have hFn : ContDiff ℝ ∞ Fn :=
    UnforcedLeray.PhaseSpace.contDiff_dy (UnforcedLeray.PhaseSpace.contDiff_dy hFc l) j
  let K : Set (ℝ × UnforcedLeray.Space) :=
    Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) (R0 + Z0)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 (R0 + Z0))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hFn.continuous.norm.continuousOn
  refine ⟨max M 0 * (1 + Z0) ^ (2 : ℝ), fun τ hτ y hy0 hyR hyZ => ?_⟩
  have hd2 := RawDeriv2EnvSub.dy2_eq_off_axis hoff j l (x := (τ, y)) hy0
  rw [hd2]
  have hmemK : (τ, y) ∈ K := by
    refine ⟨⟨hτ.1.le, hτ.2⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_space_le_ϱ_add_abs_two y).trans (add_le_add hyR hyZ)
  have hFn_le : ‖Fn (τ, y)‖ ≤ max M 0 :=
    (hM (mem_image_of_mem (fun x => ‖Fn x‖) hmemK)).trans (le_max_left _ _)
  have h1y_pos : 0 < 1 + |y 2| := by positivity
  have h1Z_pos : 0 < 1 + Z0 := by linarith
  have hrp : (1 + Z0) ^ (-2 : ℝ) ≤ (1 + |y 2|) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h1y_pos (by linarith) (by norm_num)
  have h1_le : 1 ≤ (1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) := by
    have hmul : (1 + Z0) ^ (2 : ℝ) * (1 + Z0) ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_add h1Z_pos]
      norm_num
    calc (1 : ℝ) = (1 + Z0) ^ (2 : ℝ) * (1 + Z0) ^ (-2 : ℝ) := hmul.symm
      _ ≤ (1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hrp (by positivity)
  calc ‖Fn (τ, y)‖
      ≤ max M 0 * 1 := by linarith
    _ ≤ max M 0 * ((1 + Z0) ^ (2 : ℝ) * (1 + |y 2|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1_le (le_max_right _ _)
    _ = (max M 0 * (1 + Z0) ^ (2 : ℝ)) * (1 + |y 2|) ^ (-2 : ℝ) := by ring

/-- Via `RawResidualD2FarDecay`, the near-axis bound for arbitrary `R₀ > 0` reduces to the
near-axis bound at the far-field radius `R₁`. -/
theorem rawResidualD2NearBound_of_far_and_core (hFar : RawResidualD2FarDecay)
    (hCore : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train →
      p.ν < ν₀ → p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ (j l : Fin 3) (R1 : ℝ),
        0 < R1 → (∃ Cf : ℝ, ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
          R1 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
          ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤
            Cf * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
              (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ))) →
        ∃ C : ℝ, ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
          UnforcedLeray.Axi.ϱ y ≠ 0 → Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R1 →
          ‖dy j (dy l (rawResidualC p)) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)) :
    RawResidualD2NearBound := by
  obtain ⟨ν₁, hν₁, H1⟩ := hFar
  obtain ⟨ν₂, hν₂, H2⟩ := hCore
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p htr hν hc hR hP j l R0 hR0 => ?_⟩
  obtain ⟨Cf, R1, hR1, hfar⟩ :=
    H1 p htr (lt_of_lt_of_le hν (min_le_left _ _)) hc hR hP j l
  obtain ⟨Cc, hcore⟩ :=
    H2 p htr (lt_of_lt_of_le hν (min_le_right _ _)) hc hR hP j l R1 hR1 ⟨Cf, hfar⟩
  set Cs : ℝ := max Cf 0 * (R1 ^ (-3 : ℝ) * max 1 R0 ^ (2 : ℝ))
  refine ⟨max Cc Cs, fun τ hτ y hy0 hyR0 => ?_⟩
  have hpos : 0 ≤ (1 + |y 2|) ^ (-2 : ℝ) := by positivity
  by_cases hy1 : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R1
  · exact (hcore τ hτ y hy0 hy1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · have hy1' : R1 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := not_le.mp hy1
    have hf := hfar τ hτ y hy1'
    have hsh := shell_near_of_far hR1 hy1' hyR0
    have hCf : Cf ≤ max Cf 0 := le_max_left _ _
    have henv_pos : 0 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) := by
      have : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hR1.trans hy1'
      positivity
    calc ‖dy j (dy l (rawResidualC p)) (τ, y)‖
        ≤ max Cf 0 * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
            (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ)) :=
          hf.trans (mul_le_mul_of_nonneg_right hCf henv_pos)
      _ ≤ max Cf 0 * ((R1 ^ (-3 : ℝ) * max 1 R0 ^ (2 : ℝ)) * (1 + |y 2|) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsh (le_max_right _ _)
      _ = Cs * (1 + |y 2|) ^ (-2 : ℝ) := by ring
      _ ≤ max Cc Cs * (1 + |y 2|) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

end RawNear2Sub

/-- **`RawResidualD2NearBound` from `RingLiftSmoothExt` and `RawResidualD2AxialTail`**
(`the November 2 reference manuscript`, lines 1270-1325, 2548-2551). -/
theorem rawResidualD2NearBound_of (hExt : UnforcedLeray.Short.IIb.RingLiftSmoothExt)
    (hTail : RawResidualD2AxialTail) : RawResidualD2NearBound := by
  obtain ⟨ν₁, hν₁, H1⟩ := RawNear2Sub.compact_cyl_bound_of_smoothExt hExt
  obtain ⟨ν₂, hν₂, H2⟩ := hTail
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p htr hν hc hR hP j l R0 hR0 => ?_⟩
  obtain ⟨C_tail, Z0, hZ0, htail⟩ :=
    H2 p htr (lt_of_lt_of_le hν (min_le_right _ _)) hc hR hP j l R0 hR0
  obtain ⟨C_comp, hcomp⟩ :=
    H1 p htr (lt_of_lt_of_le hν (min_le_left _ _)) hc hR j l R0 Z0 hR0 hZ0
  refine ⟨max C_comp C_tail, fun τ hτ y hy0 hyR => ?_⟩
  have hpos : 0 ≤ (1 + |y 2|) ^ (-2 : ℝ) := by positivity
  by_cases hyZ : |y 2| ≤ Z0
  · exact (hcomp τ hτ y hy0 hyR hyZ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · exact (htail τ hτ y hy0 hyR (not_le.mp hyZ)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)

end UnforcedLeray.Short.PartIIIb.Concrete
