import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2

/-!
# Euler form of the homogeneity `K_{s²t}(sx) = s^{-3}K_t(x)` (`HeatLerayKEuler`, source 3800-3807)

From `HeatLerayScale` (`K_t(x) = t^{-3/2}K_1(x/√t)`, source 3598-3610) with `r = t^{-1/2}`:
`∂_kK_t(x) = r⁴ (∂_kK_1)(r x)`; differentiate in `t` (`r' = -r³/2`) and in `x`, and use `t r² = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `r(s) = s^{-1/2}`. -/
def eulR (s : ℝ) : ℝ := (Real.sqrt s)⁻¹

lemma eulR_pos {s : ℝ} (hs : 0 < s) : 0 < eulR s := inv_pos.mpr (Real.sqrt_pos.mpr hs)

lemma eulR_sq {s : ℝ} (hs : 0 < s) : s * eulR s ^ 2 = 1 := by
  unfold eulR
  have h : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have h0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  field_simp
  exact h.symm

lemma eulR_hasDerivAt {s : ℝ} (hs : 0 < s) : HasDerivAt eulR (-(1 / 2) * eulR s ^ 3) s := by
  have h := (Real.hasDerivAt_sqrt hs.ne').inv (Real.sqrt_pos.mpr hs).ne'
  have h0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  refine h.congr_deriv ?_
  unfold eulR
  field_simp

lemma eulR_cube {s : ℝ} (hs : 0 < s) : s ^ (-(3 / 2 : ℝ)) = eulR s ^ 3 := by
  unfold eulR
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hs.le]
  norm_num

lemma heatLerayK_fun_scale (s : ℝ) (hs : 0 < s) (i j : Fin 3) :
    (fun x : Space => IIIa.heatLerayK s i j x) =
      fun x => eulR s ^ 3 * IIIa.heatLerayK 1 i j (eulR s • x) := by
  funext x
  rw [heatLerayScale_of heatGTailScale s hs i j x, eulR_cube hs]
  rfl

lemma heatLerayK_grad_scale (s : ℝ) (hs : 0 < s) (i j k : Fin 3) (x : Space) :
    fderiv ℝ (fun x' : Space => IIIa.heatLerayK s i j x') x (UnforcedLeray.coordinateVector k) =
      eulR s ^ 4 * fderiv ℝ (fun y : Space => IIIa.heatLerayK 1 i j y) (eulR s • x)
        (UnforcedLeray.coordinateVector k) := by
  have hF : Differentiable ℝ (fun y : Space => IIIa.heatLerayK 1 i j y) :=
    (heatLerayKSmooth 1 one_pos i j).differentiable (by norm_num)
  rw [heatLerayK_fun_scale s hs i j]
  have h := ((hF (eulR s • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul (eulR s))).const_mul
    (eulR s ^ 3)
  have h' : HasFDerivAt (fun x : Space => eulR s ^ 3 * IIIa.heatLerayK 1 i j (eulR s • x)) _ x := h
  rw [h'.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul,
    ContinuousLinearMap.id_apply]
  ring

theorem heatLerayK_euler : UnforcedLeray.Short.PartIIIb.Concrete.HeatLerayKEuler := by
  intro t ht i j k x
  set F : Space → ℝ := fun y => IIIa.heatLerayK 1 i j y with hFdef
  set ek : Space := UnforcedLeray.coordinateVector k with hek
  have hF3 : ContDiff ℝ 3 F := heatLerayKSmooth 1 one_pos i j
  set Fk : Space → ℝ := fun y => fderiv ℝ F y ek with hFk
  have hFk2 : ContDiff ℝ 2 Fk := (hF3.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hFkd : Differentiable ℝ Fk := hFk2.differentiable (by norm_num)
  set r := eulR t with hr
  have hrpos : 0 < r := eulR_pos ht
  -- spatial part
  have hx : (fun x' : Space => fderiv ℝ (fun x'' => IIIa.heatLerayK t i j x'') x' ek) =
      fun x' => r ^ 4 * Fk (r • x') := by
    funext x'; exact heatLerayK_grad_scale t ht i j k x'
  -- time part
  have ht' : (fun s : ℝ => fderiv ℝ (fun x' => IIIa.heatLerayK s i j x') x ek) =ᶠ[nhds t]
      fun s => eulR s ^ 4 * Fk (eulR s • x) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact heatLerayK_grad_scale s hs i j k x
  have hsm : HasDerivAt (fun s => eulR s • x) ((-(1 / 2) * r ^ 3) • x) t :=
    (eulR_hasDerivAt ht).smul_const x
  have hcomp := (hFkd (r • x)).hasFDerivAt.comp_hasDerivAt t hsm
  have hT : HasDerivAt (fun s => eulR s ^ 4 * Fk (eulR s • x))
      (4 * r ^ 3 * (-(1 / 2) * r ^ 3) * Fk (r • x) +
        r ^ 4 * fderiv ℝ Fk (r • x) ((-(1 / 2) * r ^ 3) • x)) t := by
    have := ((eulR_hasDerivAt ht).pow 4).mul hcomp
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, Pi.pow_apply]
    norm_num [hr]
  rw [ht'.deriv_eq, hT.deriv]
  have hS : HasFDerivAt (fun x' : Space => r ^ 4 * Fk (r • x'))
      (r ^ 4 • ((fderiv ℝ Fk (r • x)).comp (r • ContinuousLinearMap.id ℝ Space))) x :=
    ((hFkd (r • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)).const_mul (r ^ 4)
  rw [hx, hS.fderiv, heatLerayK_grad_scale t ht i j k x]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul,
    smul_eq_mul, ContinuousLinearMap.id_apply]
  have h1 := eulR_sq ht
  rw [← hr] at h1
  linear_combination (-(4 * r ^ 4 * Fk (r • x) + r ^ 5 * fderiv ℝ Fk (r • x) x)) * h1

end UnforcedLeray.Short.PartIIIb.Concrete
