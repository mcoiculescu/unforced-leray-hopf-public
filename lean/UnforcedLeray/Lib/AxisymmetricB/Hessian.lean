import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity

/-!
# AX07 (Hessian): second derivatives of `ρ g e_r + h e_z` near the axis


§5 Layer 3, target AX07, item `hessian_bound_axis`, and bypass BP6 (§4): "if `u_r = ρ g(ρ, z)`
and `u_z = h(ρ, z)` with `∂_ρ h = 0` at `ρ = 0`, then `‖D²u‖_∞ ≤ C(‖g‖_{C²} + ‖h‖_{C²})`; the
proof uses `|∂_ρ g/ρ| ≤ sup|∂²_ρ g|`". Blueprint units served: B0204 (`eq:st18-t00203`,
tex 3058–3078: `‖U_R‖_{W^{2,∞}} ≤ P`; "near the axis the cylindrical term
`∂_{r_y}(U_R)_r/r_y − (U_R)_r/r_y²` cancels on the linear radial term") and B0282
(`background:eq:2.15`, tex 5197–5205: `‖U_raw‖_{W^{2,∞}} ≤ P`).

The field is `radialField g h = g(ϱ, z)(y₀, y₁, 0) + h(ϱ, z) e_z`, which off the axis is the lift
`ρ g e_r + h e_z` (`radialField_eq_liftMer`). Off the axis,
`D²u(y)[u, v] = (D²(g∘mer)[u,v]) hor y + D(g∘mer)[u] hor v + D(g∘mer)[v] hor u
+ (D²(h∘mer)[u,v]) e_z` (`second_radialField`), and `hessian_bound_axis` gives
`‖D²u(y)[u, v]‖ ≤ (10A + 6B)‖u‖‖v‖` when on `{ρ > 0}`
* `|∂g| ≤ A` and `ρ|∂²g| ≤ A` (each first and second partial of `g`),
* `|∂_ρ h| ≤ Bρ` and `|∂²h| ≤ B` (each second partial of `h`).
The hypothesis `|∂_ρ h| ≤ Bρ` is the manuscript's cancellation: it follows from `∂_ρ h → 0` at
the axis and `|∂²_ρ h| ≤ B` (`abs_dρ_le_of_tendsto`, the mean value theorem).

Deviation from the scoping signature (recorded): the bound is stated with `ρ|∂²g|` rather than
`|∂²g|`, because `∂²(ρ g) = 2∂g + ρ∂²g` has the factor `ρ`; on `ρ ≤ 1` (the region near the
axis where the estimate is used) `ρ|∂²g| ≤ |∂²g| ≤ ‖g‖_{C²}`, which recovers the scoping form.
The condition `∂_ρ g = 0` at `ρ = 0` is not needed for the bound (it is needed for `C²`
regularity through the axis, which `contDiff_of_parity` covers in the parity form). All
hypotheses are on the open half-plane, so no one-sided derivatives at `ρ = 0` enter.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Axi

/-- The field `g(ϱ, z)(y₀, y₁, 0) + h(ϱ, z) e_z`, i.e. `ρ g e_r + h e_z`. -/
def radialField (g h : ℝ × ℝ → ℝ) (y : Space) : Space := g (mer y) • hor y + h (mer y) • e3

theorem ϱ_smul_eR (y : Space) : ϱ y • eR y = hor y := by
  by_cases hy : y ∈ axis
  · have h0 := (mem_axis_iff y).1 hy
    obtain ⟨hy0, hy1⟩ := hy
    rw [h0, zero_smul]
    ext i
    fin_cases i <;> simp [hor, hy0, hy1]
  · exact (hor_eq_smul_eR hy).symm

theorem radialField_eq_liftMer (g h : ℝ × ℝ → ℝ) (y : Space) :
    radialField g h y = liftMer (fun p => (p.1 * g p) • m0 + h p • m1) y := by
  rw [liftMer_eq_frameL, map_add, map_smul, map_smul, frameL_m0, frameL_m1, radialField,
    mul_comm, ← smul_smul]
  have : (mer y).1 = ϱ y := rfl
  rw [this, ϱ_smul_eR]

/-! ### Elementary bounds -/

theorem norm_sq_coords (u : Space) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem abs_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b :=
  (pow_le_pow_iff_left₀ (abs_nonneg a) hb two_ne_zero).1 (by rw [sq_abs]; exact h)

theorem abs_linH_le (u v : Space) : |linH u v| ≤ ‖u‖ * ‖v‖ := by
  refine abs_le_of_sq_le (by positivity) ?_
  rw [linH_apply, mul_pow, norm_sq_coords, norm_sq_coords]
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0), sq_nonneg (u 2), sq_nonneg (v 2),
    mul_nonneg (sq_nonneg (u 2)) (sq_nonneg (v 0)), mul_nonneg (sq_nonneg (u 2)) (sq_nonneg (v 1)),
    mul_nonneg (sq_nonneg (u 2)) (sq_nonneg (v 2)), mul_nonneg (sq_nonneg (u 0)) (sq_nonneg (v 2)),
    mul_nonneg (sq_nonneg (u 1)) (sq_nonneg (v 2))]

theorem abs_linH_self_le (u y : Space) : |linH u y| ≤ ‖u‖ * ϱ y := by
  refine abs_le_of_sq_le (mul_nonneg (norm_nonneg _) (ϱ_nonneg y)) ?_
  rw [linH_apply, mul_pow, norm_sq_coords, ϱ_sq]
  nlinarith [sq_nonneg (u 0 * y 1 - u 1 * y 0), mul_nonneg (sq_nonneg (u 2)) (sq_nonneg (y 0)),
    mul_nonneg (sq_nonneg (u 2)) (sq_nonneg (y 1))]

theorem abs_coord_le (u : Space) (i : Fin 3) : |u i| ≤ ‖u‖ := by
  have := PiLp.norm_apply_le u i
  rwa [Real.norm_eq_abs] at this

theorem norm_hor_le (u : Space) : ‖hor u‖ ≤ ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_coords, norm_sq_coords]
  simp only [hor_apply_zero, hor_apply_one, hor_apply_two]
  nlinarith [sq_nonneg (u 2)]

theorem norm_hor_self (y : Space) : ‖hor y‖ = ϱ y := by
  rw [← ϱ_smul_eR, norm_smul, Real.norm_of_nonneg (ϱ_nonneg y)]
  by_cases hy : y ∈ axis
  · rw [(mem_axis_iff y).1 hy, zero_mul]
  · rw [norm_eR hy, mul_one]

theorem norm_e3 : ‖e3‖ = 1 := by
  simp [e3, coordinateVector]

/-- The six-term bound used for both components. -/
theorem abs_six_le {L a b u2 v2 X0 X1 X2 X3 X4 U V A : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : 0 ≤ A) (hL : |L| ≤ U * V) (ha : |a| ≤ U) (hb : |b| ≤ V) (hu2 : |u2| ≤ U)
    (hv2 : |v2| ≤ V) (h0 : |X0| ≤ A) (h1 : |X1| ≤ A) (h2 : |X2| ≤ A) (h3 : |X3| ≤ A)
    (h4 : |X4| ≤ A) :
    |L * X0 + (-(a * b)) * X0 + a * (b * X1 + v2 * X2) + u2 * (b * X3 + v2 * X4)| ≤
      6 * A * (U * V) := by
  have t1 : |L * X0| ≤ U * V * A := by
    rw [abs_mul]; exact mul_le_mul hL h0 (abs_nonneg _) (by positivity)
  have t2 : |(-(a * b)) * X0| ≤ U * V * A := by
    rw [abs_mul, abs_neg, abs_mul]
    exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hU) h0 (abs_nonneg _) (by positivity)
  have t3 : |a * (b * X1 + v2 * X2)| ≤ U * (V * A + V * A) := by
    rw [abs_mul]
    refine mul_le_mul ha ((abs_add_le _ _).trans ?_) (abs_nonneg _) hU
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hb h1 (abs_nonneg _) hV) (mul_le_mul hv2 h2 (abs_nonneg _) hV)
  have t4 : |u2 * (b * X3 + v2 * X4)| ≤ U * (V * A + V * A) := by
    rw [abs_mul]
    refine mul_le_mul hu2 ((abs_add_le _ _).trans ?_) (abs_nonneg _) hU
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hb h3 (abs_nonneg _) hV) (mul_le_mul hv2 h4 (abs_nonneg _) hV)
  calc _ ≤ |L * X0 + (-(a * b)) * X0 + a * (b * X1 + v2 * X2)| + |u2 * (b * X3 + v2 * X4)| :=
        abs_add_le _ _
    _ ≤ |L * X0 + (-(a * b)) * X0| + |a * (b * X1 + v2 * X2)| + |u2 * (b * X3 + v2 * X4)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ |L * X0| + |(-(a * b)) * X0| + |a * (b * X1 + v2 * X2)| + |u2 * (b * X3 + v2 * X4)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ U * V * A + U * V * A + U * (V * A + V * A) + U * (V * A + V * A) := by gcongr
    _ = 6 * A * (U * V) := by ring

/-! ### First and second derivatives off the axis -/

theorem hasFDerivAt_hor (x : Space) : HasFDerivAt hor horL x := by
  have h : hor = fun x => horL x := funext fun x => (horL_apply x).symm
  rw [h]
  exact horL.hasFDerivAt

theorem contDiffOn_comp_mer {g : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ 2 (fun y => g (mer y)) axisᶜ :=
  hg.comp contDiffOn_mer mapsTo_mer

theorem differentiableAt_comp_mer {g : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ))
    {x : Space} (hx : x ∉ axis) : DifferentiableAt ℝ (fun y => g (mer y)) x :=
  differentiableAt_of_contDiffOn (contDiffOn_comp_mer hg) two_ne_zero hx

theorem fderiv_radialField_apply {g h : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ))
    (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {x : Space} (hx : x ∉ axis) (u : Space) :
    fderiv ℝ (radialField g h) x u =
      fderiv ℝ (fun y => g (mer y)) x u • hor x + g (mer x) • hor u +
        fderiv ℝ (fun y => h (mer y)) x u • e3 := by
  have hG := (differentiableAt_comp_mer hg hx).hasFDerivAt
  have hH := (differentiableAt_comp_mer hh hx).hasFDerivAt
  have hT := (hG.fun_smul (hasFDerivAt_hor x)).fun_add (hH.smul_const e3)
  have e : radialField g h = fun y => g (mer y) • hor y + h (mer y) • e3 := rfl
  rw [e, hT.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, horL_apply]
  abel

/-- **Second derivative of `ρ g e_r + h e_z` off the axis.** -/
theorem second_radialField {g h : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ))
    (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {y : Space} (hy : y ∉ axis) (u v : Space) :
    fderiv ℝ (fun x => fderiv ℝ (radialField g h) x u) y v =
      fderiv ℝ (fun x => fderiv ℝ (fun y => g (mer y)) x u) y v • hor y +
        fderiv ℝ (fun y => g (mer y)) y u • hor v + fderiv ℝ (fun y => g (mer y)) y v • hor u +
        fderiv ℝ (fun x => fderiv ℝ (fun y => h (mer y)) x u) y v • e3 := by
  have hev : (fun x => fderiv ℝ (radialField g h) x u) =ᶠ[𝓝 y]
      (fun x => fderiv ℝ (fun y => g (mer y)) x u • hor x + g (mer x) • hor u +
        fderiv ℝ (fun y => h (mer y)) x u • e3) := by
    filter_upwards [mem_nhds_compl_axis hy] with x hx
    exact fderiv_radialField_apply hg hh hx u
  have ha := (differentiableAt_fderiv_apply (contDiffOn_comp_mer hg) hy u).hasFDerivAt
  have hb := (differentiableAt_fderiv_apply (contDiffOn_comp_mer hh) hy u).hasFDerivAt
  have hG := (differentiableAt_comp_mer hg hy).hasFDerivAt
  have hT := ((ha.fun_smul (hasFDerivAt_hor y)).fun_add (hG.smul_const (hor u))).fun_add
    (hb.smul_const e3)
  rw [hev.fderiv_eq, hT.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, horL_apply]
  abel

/-- **AX07 `hessian_bound_axis`** (bypass BP6; B0204, tex 3058–3078; B0282, tex 5197–5205).
Off the axis, the second derivatives of `u = ρ g e_r + h e_z` satisfy
`‖D²u(y)[u, v]‖ ≤ (10A + 6B)‖u‖‖v‖`, uniformly up to the axis, when on `{ρ > 0}` the first
partials of `g` are bounded by `A`, `ρ` times its second partials by `A`, the second partials of
`h` by `B`, and `|∂_ρ h| ≤ Bρ`. -/
theorem hessian_bound_axis {g h : ℝ × ℝ → ℝ} {A B : ℝ}
    (hg : ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ)) (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ))
    (hgA : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), |dρ g p| ≤ A ∧ |dz g p| ≤ A ∧
      p.1 * |dρ (dρ g) p| ≤ A ∧ p.1 * |dz (dρ g) p| ≤ A ∧ p.1 * |dρ (dz g) p| ≤ A ∧
      p.1 * |dz (dz g) p| ≤ A)
    (hhB : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), |dρ h p| ≤ B * p.1 ∧ |dρ (dρ h) p| ≤ B ∧
      |dz (dρ h) p| ≤ B ∧ |dρ (dz h) p| ≤ B ∧ |dz (dz h) p| ≤ B)
    {y : Space} (hy : y ∉ axis) (u v : Space) :
    ‖fderiv ℝ (fun x => fderiv ℝ (radialField g h) x u) y v‖ ≤ (10 * A + 6 * B) * (‖u‖ * ‖v‖) := by
  have hpm : mer y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := mapsTo_mer hy
  have hρ : 0 < ϱ y := ϱ_pos hy
  have hρ' : (mer y).1 = ϱ y := rfl
  obtain ⟨gA1, gA2, gA3, gA4, gA5, gA6⟩ := hgA _ hpm
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hhB _ hpm
  rw [hρ'] at gA3 gA4 gA5 gA6 hB1
  have hA0 : 0 ≤ A := (abs_nonneg _).trans gA1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB2
  have hU := norm_nonneg u
  have hV := norm_nonneg v
  set ι := ιr y with hι
  have hιρ : ι * ϱ y = 1 := by rw [hι, ιr, inv_mul_cancel₀ hρ.ne']
  have hι0 : 0 ≤ ι := by rw [hι, ιr]; exact inv_nonneg.2 hρ.le
  -- the normalized horizontal products
  set a := linH u y * ι with ha_def
  set b := linH v y * ι with hb_def
  have ha : |a| ≤ ‖u‖ := by
    rw [ha_def, abs_mul, abs_of_nonneg hι0]
    calc |linH u y| * ι ≤ ‖u‖ * ϱ y * ι := by gcongr; exact abs_linH_self_le u y
      _ = ‖u‖ := by rw [mul_assoc, mul_comm (ϱ y), hιρ, mul_one]
  have hb : |b| ≤ ‖v‖ := by
    rw [hb_def, abs_mul, abs_of_nonneg hι0]
    calc |linH v y| * ι ≤ ‖v‖ * ϱ y * ι := by gcongr; exact abs_linH_self_le v y
      _ = ‖v‖ := by rw [mul_assoc, mul_comm (ϱ y), hιρ, mul_one]
  have hsymm : linH y v = linH v y := by rw [linH_apply, linH_apply]; ring
  have hsymm' : linH v u = linH u v := by rw [linH_apply, linH_apply]; ring
  rw [second_radialField hg hh hy u v, second_comp_mer hg hy u v, second_comp_mer hh hy u v,
    fderiv_comp_mer_eq hg hy u, fderiv_comp_mer_eq hg hy v]
  set α := linH u v * ι * dρ g (mer y) + linH u y * (-(ι ^ 3) * linH y v) * dρ g (mer y) +
    linH u y * ι * (linH v y * ι * dρ (dρ g) (mer y) + v 2 * dz (dρ g) (mer y)) +
    u 2 * (linH v y * ι * dρ (dz g) (mer y) + v 2 * dz (dz g) (mer y)) with hα
  set δ := linH u v * ι * dρ h (mer y) + linH u y * (-(ι ^ 3) * linH y v) * dρ h (mer y) +
    linH u y * ι * (linH v y * ι * dρ (dρ h) (mer y) + v 2 * dz (dρ h) (mer y)) +
    u 2 * (linH v y * ι * dρ (dz h) (mer y) + v 2 * dz (dz h) (mer y)) with hδ
  set β := linH u y * ι * dρ g (mer y) + u 2 * dz g (mer y) with hβ
  set γ := linH v y * ι * dρ g (mer y) + v 2 * dz g (mer y) with hγ
  -- the radial (g) part
  have hαρ : α * ϱ y = linH u v * dρ g (mer y) + (-(a * b)) * dρ g (mer y) +
      a * (b * (ϱ y * dρ (dρ g) (mer y)) + v 2 * (ϱ y * dz (dρ g) (mer y))) +
      u 2 * (b * (ϱ y * dρ (dz g) (mer y)) + v 2 * (ϱ y * dz (dz g) (mer y))) := by
    rw [hα, ha_def, hb_def, hsymm, hι, ιr]
    field_simp
  have hαb : |α| * ϱ y ≤ 6 * A * (‖u‖ * ‖v‖) := by
    have e : |α| * ϱ y = |α * ϱ y| := by rw [abs_mul, abs_of_pos hρ]
    rw [e, hαρ]
    refine abs_six_le hU hV hA0 (abs_linH_le u v) ha hb (abs_coord_le u 2) (abs_coord_le v 2)
      gA1 ?_ ?_ ?_ ?_
    · rw [abs_mul, abs_of_pos hρ]; exact gA3
    · rw [abs_mul, abs_of_pos hρ]; exact gA4
    · rw [abs_mul, abs_of_pos hρ]; exact gA5
    · rw [abs_mul, abs_of_pos hρ]; exact gA6
  -- the axial (h) part: `|ι ∂_ρ h| ≤ B` is the cancellation at the axis
  have hιh : |ι * dρ h (mer y)| ≤ B := by
    rw [abs_mul, abs_of_nonneg hι0]
    calc ι * |dρ h (mer y)| ≤ ι * (B * ϱ y) := by gcongr
      _ = B := by rw [mul_comm B, ← mul_assoc, hιρ, one_mul]
  have hδe : δ = linH u v * (ι * dρ h (mer y)) + (-(a * b)) * (ι * dρ h (mer y)) +
      a * (b * dρ (dρ h) (mer y) + v 2 * dz (dρ h) (mer y)) +
      u 2 * (b * dρ (dz h) (mer y) + v 2 * dz (dz h) (mer y)) := by
    rw [hδ, ha_def, hb_def, hsymm]
    ring
  have hδb : |δ| ≤ 6 * B * (‖u‖ * ‖v‖) := by
    rw [hδe]
    exact abs_six_le hU hV hB0 (abs_linH_le u v) ha hb (abs_coord_le u 2) (abs_coord_le v 2)
      hιh hB2 hB3 hB4 hB5
  -- first-order terms
  have hβb : |β| ≤ 2 * A * ‖u‖ := by
    rw [hβ]
    calc |linH u y * ι * dρ g (mer y) + u 2 * dz g (mer y)|
        ≤ |a * dρ g (mer y)| + |u 2 * dz g (mer y)| := abs_add_le _ _
      _ ≤ ‖u‖ * A + ‖u‖ * A := by
          rw [abs_mul a, abs_mul (u 2)]
          exact add_le_add (mul_le_mul ha gA1 (abs_nonneg _) hU)
            (mul_le_mul (abs_coord_le u 2) gA2 (abs_nonneg _) hU)
      _ = 2 * A * ‖u‖ := by ring
  have hγb : |γ| ≤ 2 * A * ‖v‖ := by
    rw [hγ]
    calc |linH v y * ι * dρ g (mer y) + v 2 * dz g (mer y)|
        ≤ |b * dρ g (mer y)| + |v 2 * dz g (mer y)| := abs_add_le _ _
      _ ≤ ‖v‖ * A + ‖v‖ * A := by
          rw [abs_mul b, abs_mul (v 2)]
          exact add_le_add (mul_le_mul hb gA1 (abs_nonneg _) hV)
            (mul_le_mul (abs_coord_le v 2) gA2 (abs_nonneg _) hV)
      _ = 2 * A * ‖v‖ := by ring
  calc ‖α • hor y + β • hor v + γ • hor u + δ • e3‖
      ≤ ‖α • hor y‖ + ‖β • hor v‖ + ‖γ • hor u‖ + ‖δ • e3‖ := norm_add₄_le
    _ ≤ |α| * ϱ y + |β| * ‖v‖ + |γ| * ‖u‖ + |δ| := by
        rw [norm_smul, norm_smul, norm_smul, norm_smul, norm_hor_self, norm_e3, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        · exact norm_hor_le v
        · exact norm_hor_le u
    _ ≤ 6 * A * (‖u‖ * ‖v‖) + 2 * A * ‖u‖ * ‖v‖ + 2 * A * ‖v‖ * ‖u‖ + 6 * B * (‖u‖ * ‖v‖) := by
        gcongr
    _ = (10 * A + 6 * B) * (‖u‖ * ‖v‖) := by ring

/-- **The axis cancellation** (tex 3070–3074). If `∂_ρ h(ρ, z) → 0` as `ρ → 0⁺` and
`|∂²_ρ h| ≤ B` on `{ρ > 0}`, then `|∂_ρ h(ρ, z)| ≤ Bρ` (mean value theorem). -/
theorem abs_dρ_le_of_tendsto {h : ℝ × ℝ → ℝ} {B : ℝ} (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ))
    (hB : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), |dρ (dρ h) p| ≤ B)
    (h0 : ∀ z, Tendsto (fun r => dρ h (r, z)) (𝓝[>] 0) (𝓝 0)) {p : ℝ × ℝ} (hp : 0 < p.1) :
    |dρ h p| ≤ B * p.1 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB p ⟨hp, trivial⟩)
  set f : ℝ → ℝ := fun r => dρ h (r, p.2) with hf
  have hder : ∀ r, 0 < r → HasDerivAt f (dρ (dρ h) (r, p.2)) r := by
    intro r hr
    have hm : (r, p.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, trivial⟩
    have hd : DifferentiableAt ℝ (dρ h) (r, p.2) :=
      ((contDiffOn_dρ hh).contDiffAt (isOpen_halfPlane.mem_nhds hm)).differentiableAt
        one_ne_zero
    exact hasDerivAt_line_fst (p := (r, p.2)) hd
  have hlip : ∀ ε, 0 < ε → ε ≤ p.1 → |f p.1| ≤ |f ε| + B * p.1 := by
    intro ε hε hεp
    have hmvt := (convex_Icc ε p.1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := fun r => dρ (dρ h) (r, p.2)) (C := B)
      (fun r hr => (hder r (hε.trans_le hr.1)).hasDerivWithinAt)
      (fun r hr => by
        rw [Real.norm_eq_abs]; exact hB _ ⟨hε.trans_le hr.1, trivial⟩)
      (left_mem_Icc.2 hεp) (right_mem_Icc.2 hεp)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    have e : |p.1 - ε| = p.1 - ε := abs_of_nonneg (by linarith)
    rw [e] at hmvt
    have := abs_sub_abs_le_abs_sub (f p.1) (f ε)
    have := mul_nonneg hB0 hε.le
    nlinarith
  have hlim : Tendsto (fun ε => |f ε| + B * p.1) (𝓝[>] 0) (𝓝 (0 + B * p.1)) := by
    have := (h0 p.2).abs
    rw [abs_zero] at this
    exact this.add_const _
  rw [zero_add] at hlim
  have hf1 : f p.1 = dρ h p := rfl
  rw [← hf1]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hp] with ε hε
  exact hlip ε hε.1 hε.2.le

end UnforcedLeray.Axi
