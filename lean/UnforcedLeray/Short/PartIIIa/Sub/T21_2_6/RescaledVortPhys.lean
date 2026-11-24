import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# `PartIII-a:T21/2/6/4`: the physical weighted vorticity bound (`RescaledVortPhys m`)

Source of record: `the November 2 reference manuscript` lines 2866-2873 and
3050-3054. Write `E = curl V_c^p + curl(v - V_c^p)` (`Ec tr r = Cyl.curl (tr.v r)`), split the
`j`-th derivative by `iteratedFDeriv_add_apply`, and bound the two pieces by `GaussVortMoving`
(Gaussian part) and `VortErrMoving` (error part) with the weight `jb^{(m+2)/2} ≤ jb^k` for
`k = ⌈(m+2)/2⌉₊` (`jb y = 1 + y₁² + y₂² ≥ 1`). The region `θ ≥ b ≥ 1` gives `a ≤ c²`, `c = ν⁻²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The curl of a smooth meridional field is smooth. -/
theorem curl_contDiff_vort {u : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl u) := by
  have h1 : ContDiff ℝ 1 u := hu.of_le (by first | exact le_top | simp)
  have hc : UnforcedLeray.Cyl.curl u = fun z =>
      fderiv ℝ (fun w => u w 1) z (1, 0) - fderiv ℝ (fun w => u w 0) z (0, 1) :=
    funext (fun z => UnforcedLeray.B0238.curl_eq_fderiv h1 z)
  rw [hc]
  have g1 : ContDiff ℝ ∞ (fun w => u w 1) := UnforcedLeray.B0238.contDiff_comp_apply hu 1
  have g0 : ContDiff ℝ ∞ (fun w => u w 0) := UnforcedLeray.B0238.contDiff_comp_apply hu 0
  have d1 : ContDiff ℝ ∞ (fderiv ℝ (fun w => u w 1)) := (contDiff_infty_iff_fderiv.1 g1).2
  have d0 : ContDiff ℝ ∞ (fderiv ℝ (fun w => u w 0)) := (contDiff_infty_iff_fderiv.1 g0).2
  exact (d1.clm_apply contDiff_const).sub (d0.clm_apply contDiff_const)

/-- Linearity of the curl for smooth meridional fields. -/
theorem curl_add_vort {u w : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) :
    UnforcedLeray.Cyl.curl (fun x => u x + w x) =
      fun z => UnforcedLeray.Cyl.curl u z + UnforcedLeray.Cyl.curl w z := by
  have h1 : ContDiff ℝ 1 u := hu.of_le (by first | exact le_top | simp)
  have h2 : ContDiff ℝ 1 w := hw.of_le (by first | exact le_top | simp)
  have h3 : ContDiff ℝ 1 (fun x => u x + w x) := h1.add h2
  funext z
  have d1u : DifferentiableAt ℝ (fun y => u y 1) z :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hu 1).differentiable (by simp)) z
  have d0u : DifferentiableAt ℝ (fun y => u y 0) z :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hu 0).differentiable (by simp)) z
  have d1w : DifferentiableAt ℝ (fun y => w y 1) z :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hw 1).differentiable (by simp)) z
  have d0w : DifferentiableAt ℝ (fun y => w y 0) z :=
    ((UnforcedLeray.B0238.contDiff_comp_apply hw 0).differentiable (by simp)) z
  rw [UnforcedLeray.B0238.curl_eq_fderiv h3 z, UnforcedLeray.B0238.curl_eq_fderiv h1 z,
    UnforcedLeray.B0238.curl_eq_fderiv h2 z]
  have e1 : fderiv ℝ (fun y => u y 1 + w y 1) z =
      fderiv ℝ (fun y => u y 1) z + fderiv ℝ (fun y => w y 1) z := fderiv_add d1u d1w
  have e0 : fderiv ℝ (fun y => u y 0 + w y 0) z =
      fderiv ℝ (fun y => u y 0) z + fderiv ℝ (fun y => w y 0) z := fderiv_add d0u d0w
  simp only [PiLp.add_apply]
  rw [e1, e0]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- **The physical weighted vorticity bound** (SP 2866-2873, 3050-3054). -/
theorem rescaledVortPhys_of (m : ℝ) (hG : GaussVortMoving) (hE : VortErrMoving) :
    RescaledVortPhys m := by
  set k : ℕ := Nat.ceil ((m + 2) / 2) with hk
  have hmk : (m + 2) / 2 ≤ (k : ℝ) := Nat.le_ceil _
  choose Gc hGc using fun j : ℕ => hG k j
  obtain ⟨b₀E, hbE⟩ := hE k
  refine ⟨max 1 b₀E, fun b hb => ?_⟩
  obtain ⟨CE, νE, hνE, hbE'⟩ := hbE b (le_trans (le_max_right _ _) hb)
  have hb1 : 1 ≤ b := le_trans (le_max_left _ _) hb
  refine ⟨(|Gc 0| + |CE|) + (|Gc 1| + |CE|) + (|Gc 2| + |CE|) + (|Gc 3| + |CE|),
    min 1 νE, lt_min one_pos hνE, fun ν hν tr hbuc r hr hθ j hj y hy => ?_⟩
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_left _ _)
  have hνE' : ν ≤ νE := le_trans hν.2 (min_le_right _ _)
  have hνpos : 0 < ν := hν.1
  have ha : 0 < clockA ν r := by
    unfold clockA
    nlinarith [mul_nonneg hνpos.le hr]
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hνpos _
  have hνa : ν * clockA ν r ≤ 1 := by
    have hθ' : b ≤ (ν * clockA ν r)⁻¹ := hθ
    have h1 : (1 : ℝ) ≤ (ν * clockA ν r)⁻¹ := le_trans hb1 hθ'
    have hpos : 0 < ν * clockA ν r := mul_pos hνpos ha
    have key : (ν * clockA ν r) * (ν * clockA ν r)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
  have hcsq : (ν ^ (-2 : ℝ)) ^ 2 = ((ν ^ 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hνpos.le, Real.rpow_two, inv_pow]
  have hac : clockA ν r ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hcsq, ← one_div, le_div_iff₀ (by positivity)]
    have h3 : ν ^ 3 ≤ 1 := pow_le_one₀ hνpos.le hν1
    nlinarith [mul_le_mul hνa h3 (by positivity) zero_le_one]
  have hX : 0 ≤ (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
    inv_nonneg.2 (mul_nonneg (pow_nonneg ha.le _) (pow_nonneg (Real.sqrt_nonneg _) _))
  -- smoothness and the splitting of the vorticity
  have hsmV : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hsmVc : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha
  have hv : tr.v r = fun x => UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x +
      (tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x) := by
    funext x
    simp
  have hW : ContDiff ℝ ∞ (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x) :=
    hsmV.sub hsmVc
  have hEc : UnforcedLeray.B0238.Ec tr r =
      UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) +
        UnforcedLeray.Cyl.curl (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x) := by
    show UnforcedLeray.Cyl.curl (tr.v r) = _
    conv_lhs => rw [hv]
    exact curl_add_vort hsmVc hW
  have hsA : ContDiffAt ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r))
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
    (curl_contDiff_vort hsmVc).contDiffAt.of_le (by first | exact le_top | simp)
  have hsB : ContDiffAt ℝ j (UnforcedLeray.Cyl.curl
      (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
    (curl_contDiff_vort hW).contDiffAt.of_le (by first | exact le_top | simp)
  -- the weight: `jb^{(m+2)/2} ≤ jb^k`
  have hjb1 : 1 ≤ UnforcedLeray.B0579.jb y := by
    unfold UnforcedLeray.B0579.jb
    nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have hwt : UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) ≤ UnforcedLeray.B0579.jb y ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hjb1 hmk
  have hwnn : 0 ≤ UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) := by
    apply Real.rpow_nonneg
    linarith
  have hG1 := hGc j ν (ν ^ (-2 : ℝ)) r hνpos hc hr hac y hy
  have hE1 := hbE' ν ⟨hνpos, hνE'⟩ tr hbuc r hr hθ j hj y hy
  have hsum : UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) *
      ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ≤
      (|Gc j| + |CE|) * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
    rw [hEc, iteratedFDeriv_add_apply hsA hsB]
    calc UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) +
            iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖
        ≤ UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) * (‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ +
            ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hwnn
      _ = UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ +
            UnforcedLeray.B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ := by ring
      _ ≤ UnforcedLeray.B0579.jb y ^ k * ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ +
            UnforcedLeray.B0579.jb y ^ k * ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
              (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
              (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hwt (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hwt (norm_nonneg _))
      _ ≤ Gc j * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ +
            CE * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ := add_le_add hG1 hE1
      _ ≤ |Gc j| * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ +
            |CE| * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hX)
            (mul_le_mul_of_nonneg_right (le_abs_self _) hX)
      _ = (|Gc j| + |CE|) * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ := by ring
  have a0 := abs_nonneg (Gc 0)
  have a1 := abs_nonneg (Gc 1)
  have a2 := abs_nonneg (Gc 2)
  have a3 := abs_nonneg (Gc 3)
  have aE := abs_nonneg CE
  interval_cases j
  · exact hsum.trans (mul_le_mul_of_nonneg_right (by linarith) hX)
  · exact hsum.trans (mul_le_mul_of_nonneg_right (by linarith) hX)
  · exact hsum.trans (mul_le_mul_of_nonneg_right (by linarith) hX)
  · exact hsum.trans (mul_le_mul_of_nonneg_right (by linarith) hX)

end UnforcedLeray.Short.IIIa
