import UnforcedLeray.Units.B0012
import UnforcedLeray.Infra.WeaklyNullCompact
import UnforcedLeray.Lib.PlanarSectors.Green

/-!
# The Gaussian space `X_G`, the bound `eq:st18-t00062` and the generator `L₀` (INF12 targets P4, P5)


§5, Level P: target **P4** (`norm_greenN_two_le_XG`, the pointwise Green bound
`eq:st18-t00062`) and target **P5** (`L0`, `isCompactOperator_kR`, `L0_eq_mul_add_compact`).

* `X_G = {f₂(r)e^{2iϑ} : ∫₀^∞ |f₂|² G⁻¹ r dr < ∞}`, `G = (4π)⁻¹e^{-r²/4}` (`paper/main.tex`
  lines 672–677, `eq:st18-t00005`, blueprint unit `B0010`; Lean `B0010.XG`, profiles only).
* `L₀f = -2iΩf + 2ikRf`, `R = Δ₂⁻¹` (lines 678–689, `eq:st18-t00006`/`t00007`, units `B0011`,
  `B0012`; Lean `B0012.L0`).
* `|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)` (lines 1417–1420, `eq:st18-t00062`): `norm_greenN_two_le_XG`.
  Proof: `Rf(r) = -¼⟨f, h_r⟩_{X_G}` with `h_r(s) = (min(r,s)/max(r,s))² G(s)`
  (`B0012.Psi_eq_pairing`), and `‖h_r‖² = ∫₀^∞ (min/max)⁴ G(s) s ds` is at most `(4π)⁻¹ J r²`
  (scaling `s = rt`) and at most `r⁻⁴ ∫₀^∞ s⁵ G` (since `(min/max)⁴ ≤ (s/r)⁴`).
* "The interaction `2ikR` is compact" (line 1425): `isCompactOperator_kR`, through weakly null
  sequences (`Infra/WeaklyNullCompact`): `Rf_j(r) = -¼⟨f_j, h_r⟩ → 0` for each `r`, and
  `|Rf_j(r)| ≤ ¼‖G‖‖f_j‖`, so `‖kRf_j‖² = ∫ |k|²|Rf_j|² → 0` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK)

/-! ### The kernel integrals -/

theorem continuous_minmax_pow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Continuous fun s : ℝ => (min r s / max r s) ^ k :=
  ((continuous_const.min continuous_id).div (continuous_const.max continuous_id)
    fun _ => (lt_max_of_lt_left hr).ne').pow k

theorem minmax_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : 0 ≤ min r s / max r s :=
  div_nonneg (le_min hr.le hs.le) (lt_max_of_lt_left hr).le

/-- `s ↦ (min(r,s)/max(r,s))⁴ s` is integrable on `(0, ∞)`. -/
theorem integrableOn_kernel4 {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (min r s / max r s) ^ 4 * s) (Ioi 0) := by
  have hc : Continuous (fun s : ℝ => (min r s / max r s) ^ 4 * s) :=
    (continuous_minmax_pow hr 4).mul continuous_id
  have h1 : IntegrableOn (fun s : ℝ => (min r s / max r s) ^ 4 * s) (Ioc 0 r) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun s : ℝ => (min r s / max r s) ^ 4 * s) (Ioi r) := by
    have h : IntegrableOn (fun s : ℝ => r ^ 4 * s ^ (-3 : ℝ)) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hr).const_mul (r ^ 4)
    refine IntegrableOn.congr_fun h (fun s hs => ?_) measurableSet_Ioi
    have hs' : r < s := hs
    have hs0 : 0 < s := hr.trans hs'
    rw [min_eq_left hs'.le, max_eq_right hs'.le, Real.rpow_neg hs0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hr.le] at this

/-- Scaling `s = rt`: `∫₀^∞ (min(r,s)/max(r,s))⁴ s ds = r² ∫₀^∞ (min(1,t)/max(1,t))⁴ t dt`. -/
theorem integral_kernel4_eq {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioi (0 : ℝ), (min r s / max r s) ^ 4 * s =
      r ^ 2 * ∫ t in Ioi (0 : ℝ), (min 1 t / max 1 t) ^ 4 * t := by
  have h := integral_comp_mul_left_Ioi (fun s : ℝ => (min r s / max r s) ^ 4 * s) 0 hr
  rw [mul_zero] at h
  have hg : ∀ t ∈ Ioi (0 : ℝ), (min r (r * t) / max r (r * t)) ^ 4 * (r * t) =
      r * ((min 1 t / max 1 t) ^ 4 * t) := by
    intro t _
    have e : min r (r * t) / max r (r * t) = min 1 t / max 1 t := by
      rw [show min r (r * t) = r * min 1 t by rw [mul_min_of_nonneg _ _ hr.le, mul_one],
        show max r (r * t) = r * max 1 t by rw [mul_max_of_nonneg _ _ hr.le, mul_one],
        mul_div_mul_left _ _ hr.ne']
    rw [e]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hg, integral_const_mul, smul_eq_mul,
    eq_inv_mul_iff_mul_eq₀ hr.ne'] at h
  rw [← h]
  ring

theorem radialGaussianWeight_le (s : ℝ) : B0010.radialGaussianWeight s ≤ (4 * π)⁻¹ := by
  unfold B0010.radialGaussianWeight
  exact mul_le_of_le_one_right (by positivity) (B0012.radialOmega_le_one s)

theorem integrableOn_kernel4_gauss {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (min r s / max r s) ^ 4 * B0010.radialGaussianWeight s * s)
      (Ioi 0) := by
  refine ((integrableOn_kernel4 hr).const_mul (4 * π)⁻¹).mono' ?_ ?_
  · exact (((continuous_minmax_pow hr 4).mul
      B0012.continuous_radialGaussianWeight).mul continuous_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hG := B0010.radialGaussianWeight_pos s
    have hk := pow_nonneg (minmax_nonneg hr hs') 4
    rw [Real.norm_of_nonneg (by positivity)]
    calc (min r s / max r s) ^ 4 * B0010.radialGaussianWeight s * s
        = B0010.radialGaussianWeight s * ((min r s / max r s) ^ 4 * s) := by ring
      _ ≤ (4 * π)⁻¹ * ((min r s / max r s) ^ 4 * s) := by
          gcongr
          exact radialGaussianWeight_le s

theorem integrableOn_pow_five_mul_radialGaussianWeight :
    IntegrableOn (fun s : ℝ => s ^ 5 * B0010.radialGaussianWeight s) (Ioi 0) :=
  B0011.integrableOn_pow_five_mul_gaussG

/-- `‖h_r‖²_{X_G} = ∫₀^∞ (min(r,s)/max(r,s))⁴ G(s) s ds`. -/
theorem norm_sq_rep {r : ℝ} (hr : 0 < r) :
    ‖(B0012.memLp_rep hr).toLp (B0012.rep r)‖ ^ 2 =
      ∫ s in Ioi (0 : ℝ), (min r s / max r s) ^ 4 * B0010.radialGaussianWeight s * s := by
  rw [B0010.norm_sq_toLp]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hG := (B0010.radialGaussianWeight_pos s).ne'
  rw [B0012.rep, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

/-- Near bound: `‖h_r‖² ≤ (4π)⁻¹ J r²`. -/
theorem norm_sq_rep_le_near {r : ℝ} (hr : 0 < r) :
    ‖(B0012.memLp_rep hr).toLp (B0012.rep r)‖ ^ 2 ≤
      (4 * π)⁻¹ * (∫ t in Ioi (0 : ℝ), (min 1 t / max 1 t) ^ 4 * t) * r ^ 2 := by
  rw [norm_sq_rep hr]
  have e : (4 * π)⁻¹ * (∫ t in Ioi (0 : ℝ), (min 1 t / max 1 t) ^ 4 * t) * r ^ 2 =
      ∫ s in Ioi (0 : ℝ), (4 * π)⁻¹ * ((min r s / max r s) ^ 4 * s) := by
    rw [integral_const_mul, integral_kernel4_eq hr]
    ring
  rw [e]
  refine setIntegral_mono_on (integrableOn_kernel4_gauss hr)
    ((integrableOn_kernel4 hr).const_mul _) measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  have hk := pow_nonneg (minmax_nonneg hr hs') 4
  calc (min r s / max r s) ^ 4 * B0010.radialGaussianWeight s * s
      = B0010.radialGaussianWeight s * ((min r s / max r s) ^ 4 * s) := by ring
    _ ≤ (4 * π)⁻¹ * ((min r s / max r s) ^ 4 * s) := by
        gcongr
        exact radialGaussianWeight_le s

theorem minmax_le_div {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : min r s / max r s ≤ s / r := by
  rcases le_total s r with h | h
  · rw [min_eq_right h, max_eq_left h]
  · rw [min_eq_left h, max_eq_right h]
    calc r / s ≤ 1 := div_le_one_of_le₀ h hs.le
      _ ≤ s / r := (one_le_div hr).2 h

/-- Far bound: `‖h_r‖² ≤ r⁻⁴ ∫₀^∞ s⁵ G(s) ds`. -/
theorem norm_sq_rep_le_far {r : ℝ} (hr : 0 < r) :
    ‖(B0012.memLp_rep hr).toLp (B0012.rep r)‖ ^ 2 ≤
      (∫ s in Ioi (0 : ℝ), s ^ 5 * B0010.radialGaussianWeight s) * ((r ^ 2)⁻¹) ^ 2 := by
  rw [norm_sq_rep hr, mul_comm, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_kernel4_gauss hr)
    (integrableOn_pow_five_mul_radialGaussianWeight.const_mul _) measurableSet_Ioi
    fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  have hG := B0010.radialGaussianWeight_pos s
  have h4 : (min r s / max r s) ^ 4 ≤ (s / r) ^ 4 :=
    pow_le_pow_left₀ (minmax_nonneg hr hs') (minmax_le_div hr hs') 4
  calc (min r s / max r s) ^ 4 * B0010.radialGaussianWeight s * s
      ≤ (s / r) ^ 4 * B0010.radialGaussianWeight s * s := by gcongr
    _ = ((r ^ 2)⁻¹) ^ 2 * (s ^ 5 * B0010.radialGaussianWeight s) := by
        field_simp

/-! ### `eq:st18-t00062` -/

/-- **`eq:st18-t00062`** (`paper/main.tex` lines 1417–1420): there is `C` with
`|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)` for every `f ∈ X_G` and `r > 0`; here `R f = greenN 2 f`
(`greenN_two_eq_R`). -/
theorem norm_greenN_two_le_XG : ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : B0010.XG) (r : ℝ), 0 < r →
    ‖greenN 2 f r‖ ≤ C * ‖f‖ * min r ((r ^ 2)⁻¹) := by
  set J : ℝ := ∫ t in Ioi (0 : ℝ), (min 1 t / max 1 t) ^ 4 * t with hJdef
  set K : ℝ := ∫ s in Ioi (0 : ℝ), s ^ 5 * B0010.radialGaussianWeight s with hKdef
  have hJ : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have := pow_nonneg (minmax_nonneg one_pos ht') 4
    positivity
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun s hs => by
    have hs' : (0 : ℝ) < s := hs
    have := B0010.radialGaussianWeight_pos s
    positivity
  set A : ℝ := √((4 * π)⁻¹ * J) + √K with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / 4 * A, by positivity, fun f r hr => ?_⟩
  have hw := B0012.wprof_coe f
  set v := (B0012.memLp_rep hr).toLp (B0012.rep r) with hv
  have h1 : ‖greenN 2 f r‖ ≤ 1 / 4 * (‖v‖ * ‖f‖) := by
    rw [greenN_two_eq_R hw hr, B0011.R_eq_Psi hw hr, B0012.Psi_eq_pairing f hr,
      B0010.pairing_eq_inner, norm_mul]
    have hn : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [hn]
    gcongr
    exact norm_inner_le_norm _ _
  have h2 : ‖v‖ ≤ A * min r ((r ^ 2)⁻¹) := by
    rcases le_total r 1 with h | h
    · have hmin : min r ((r ^ 2)⁻¹) = r := by
        refine min_eq_left (h.trans ?_)
        exact (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hr.le h)
      rw [hmin]
      have hle : ‖v‖ ≤ √((4 * π)⁻¹ * J) * r := by
        have e : √((4 * π)⁻¹ * J) * r = √((4 * π)⁻¹ * J * r ^ 2) := by
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (4 * π)⁻¹ * J) (r ^ 2),
            Real.sqrt_sq hr.le]
        rw [e]
        exact Real.le_sqrt_of_sq_le (norm_sq_rep_le_near hr)
      calc ‖v‖ ≤ √((4 * π)⁻¹ * J) * r := hle
        _ ≤ A * r := by
          gcongr
          rw [hA]
          exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    · have hmin : min r ((r ^ 2)⁻¹) = (r ^ 2)⁻¹ := by
        refine min_eq_right (le_trans ?_ h)
        exact inv_le_one_of_one_le₀ (one_le_pow₀ h)
      rw [hmin]
      have hle : ‖v‖ ≤ √K * (r ^ 2)⁻¹ := by
        have e : √K * (r ^ 2)⁻¹ = √(K * ((r ^ 2)⁻¹) ^ 2) := by
          rw [Real.sqrt_mul hK (((r ^ 2)⁻¹) ^ 2), Real.sqrt_sq (by positivity)]
        rw [e]
        exact Real.le_sqrt_of_sq_le (norm_sq_rep_le_far hr)
      calc ‖v‖ ≤ √K * (r ^ 2)⁻¹ := hle
        _ ≤ A * (r ^ 2)⁻¹ := by
          gcongr
          rw [hA]
          exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  calc ‖greenN 2 f r‖ ≤ 1 / 4 * (‖v‖ * ‖f‖) := h1
    _ ≤ 1 / 4 * (A * min r ((r ^ 2)⁻¹) * ‖f‖) := by gcongr
    _ = 1 / 4 * A * ‖f‖ * min r ((r ^ 2)⁻¹) := by ring

/-! ### P5: the generator `L₀` and compactness of `kR` -/

/-- **`isCompactOperator_kR`** (`paper/main.tex` line 1425, "The interaction `2ikR` is
compact"): `f ↦ k R f` is a compact operator on `X_G`. -/
theorem isCompactOperator_kR : IsCompactOperator B0012.kROp := by
  refine Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull_of_norm_le_one _
    fun x hx hw => ?_
  set C : ℝ := 1 / 4 * ‖B0012.gaussLp‖ with hC
  set F : ℕ → ℝ → ℝ := fun n r => ‖(radialK r : ℂ)‖ ^ 2 * ‖B0011.R (x n) r‖ ^ 2 with hF
  have hsq : ∀ n, ‖B0012.kROp (x n)‖ ^ 2 = ∫ r, F n r ∂B0010.xGMeasure := by
    intro n
    rw [norm_sq_Lp_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [B0012.coeFn_kROp (x n)] with r hr
    rw [hr, norm_mul, mul_pow]
  have hk2 : Integrable (fun r => ‖(radialK r : ℂ)‖ ^ 2) B0010.xGMeasure :=
    (memLp_two_iff_integrable_sq_norm B0012.memLp_k.1).1 B0012.memLp_k
  have hlim : Tendsto (fun n => ∫ r, F n r ∂B0010.xGMeasure) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := B0010.xGMeasure) (F := F)
      (f := fun _ => (0 : ℝ)) (fun r => ‖(radialK r : ℂ)‖ ^ 2 * C ^ 2) ?_ (hk2.mul_const _) ?_ ?_
    · simpa using h
    · intro n
      exact ((Complex.continuous_ofReal.comp B0012.continuous_radialK).norm.pow 2
        ).aestronglyMeasurable.mul ((B0012.aesm_R (x n)).norm.pow 2)
    · intro n
      filter_upwards [B0012.ae_xG_pos] with r hr
      have hR : ‖B0011.R (x n) r‖ ≤ C := by
        have := B0012.norm_R_coe_le (x n) hr
        calc ‖B0011.R (x n) r‖ ≤ 1 / 4 * ‖B0012.gaussLp‖ * ‖x n‖ := this
          _ ≤ 1 / 4 * ‖B0012.gaussLp‖ * 1 := by gcongr; exact hx n
          _ = C := by rw [hC, mul_one]
      have hnn : 0 ≤ F n r := by
        simp only [hF]
        positivity
      rw [Real.norm_of_nonneg hnn]
      simp only [hF]
      gcongr
    · filter_upwards [B0012.ae_xG_pos] with r hr
      have hRn : ∀ n, B0011.R (x n) r =
          -(1 / 4 : ℂ) * ⟪(B0012.memLp_rep hr).toLp (B0012.rep r), x n⟫_ℂ := by
        intro n
        rw [B0011.R_eq_Psi (B0012.wprof_coe (x n)) hr, B0012.Psi_eq_pairing (x n) hr,
          B0010.pairing_eq_inner]
      have h0 : Tendsto (fun n => B0011.R (x n) r) atTop (𝓝 0) := by
        have := (hw ((B0012.memLp_rep hr).toLp (B0012.rep r))).const_mul (-(1 / 4 : ℂ))
        rw [mul_zero] at this
        exact this.congr fun n => (hRn n).symm
      have h1 := ((h0.norm.pow 2).const_mul (‖(radialK r : ℂ)‖ ^ 2))
      simpa [hF] using h1
  have h2 : Tendsto (fun n => ‖B0012.kROp (x n)‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]
    exact hlim
  have h3 := ((Real.continuous_sqrt.tendsto 0).comp h2)
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h3
  exact h3

/-- The angular-two generator `L₀ = -2iΩ + 2ikR` on `X_G` (`paper/main.tex` lines 678–682,
`eq:st18-t00006`; the bounded operator of the drafted unit `B0012`). -/
def L0 : B0010.XG →L[ℂ] B0010.XG := B0012.L0

/-- `L₀f(r) = -2iΩ(r) f(r) + 2ik(r) R f(r)` a.e., with `R f = greenN 2 f`. -/
theorem coeFn_L0 (f : B0010.XG) :
    ⇑(L0 f) =ᵐ[B0010.xGMeasure] fun r => -2 * Complex.I * (radialOmega r : ℂ) * f r +
      2 * Complex.I * (radialK r : ℂ) * greenN 2 f r := by
  filter_upwards [B0012.coeFn_L0 f, B0012.ae_xG_pos] with r h1 hr
  rw [L0, h1, B0012.L0Fun, greenN_two_eq_R (B0012.wprof_coe f) hr]

/-- `L₀` is multiplication by `-2iΩ` plus the compact operator `2ikR` (`paper/main.tex`
lines 1424–1425). -/
theorem L0_eq_mul_add_compact :
    L0 = (-2 * Complex.I) • B0012.omegaOp + (2 * Complex.I) • B0012.kROp := rfl

theorem isCompactOperator_L0_sub_mul :
    IsCompactOperator (L0 - (-2 * Complex.I) • B0012.omegaOp) := by
  rw [L0_eq_mul_add_compact, add_sub_cancel_left]
  exact isCompactOperator_kR.smul (2 * Complex.I)

end UnforcedLeray.Planar
