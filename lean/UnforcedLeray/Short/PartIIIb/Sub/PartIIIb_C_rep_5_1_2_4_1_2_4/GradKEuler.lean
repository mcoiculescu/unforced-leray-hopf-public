import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# Parabolic homogeneity of the contracted kernel gradient (`PartIII-b:C/rep/5/1/2/4/1/2/4`, `GradKEuler`)

Source `the November 2 reference manuscript` 3600-3610: `K_t(x) = t^{-3/2} K_1(x/√t)`.
With `F_t(x) = gradKCon t x M`, `F_t(x) = t^{-2} F_1(t^{-1/2} x)`, and differentiating in `x` and in `t`
gives `x·∇F_t = (-2t) ∂_t F_t - 4 F_t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma gradK_scale_coeff (t : ℝ) (ht : 0 < t) :
    t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹ = (t ^ 2)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_add ht,
    show (-(3 / 2 : ℝ) + -(1 / 2 : ℝ)) = -(2 : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_two]

lemma fderiv_scale_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (c : ℝ) (x : E) :
    fderiv ℝ (fun y => f (c • y)) x = c • fderiv ℝ f (c • x) :=
  fderiv_comp_smul (f := f) (x := x) c

lemma fderiv_smul_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : E → ℝ) (x v : E) :
    fderiv ℝ (fun y => c • f y) x v = c • fderiv ℝ f x v := by
  have := fderiv_const_smul_field (𝕜 := ℝ) (f := f) c
  exact congrArg (fun L => L v) (congrFun this x)

lemma fderiv_smul_apply_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : E → Space) (x v : E) :
    fderiv ℝ (fun y => c • f y) x v = c • fderiv ℝ f x v := by
  have := fderiv_const_smul_field (𝕜 := ℝ) (f := f) c
  exact congrArg (fun L => L v) (congrFun this x)

lemma kd_scale (t : ℝ) (ht : 0 < t) (i j k : Fin 3) (x : Space) :
    fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x (coordinateVector k)
      = (t ^ 2)⁻¹ * fderiv ℝ (fun x' => IIIa.heatLerayK 1 i j x') ((Real.sqrt t)⁻¹ • x) (coordinateVector k) := by
  have e1 : (fun x' => IIIa.heatLerayK t i j x')
      = fun y => t ^ (-(3 / 2 : ℝ)) • IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • y) := by
    funext x'
    rw [heatLerayScale_of heatGTailScale t ht i j x']
    rfl
  have key : ∀ v : Space, fderiv ℝ (fun y => IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • y)) x v
      = (Real.sqrt t)⁻¹ • fderiv ℝ (fun z => IIIa.heatLerayK 1 i j z) ((Real.sqrt t)⁻¹ • x) v := by
    intro v
    rw [fderiv_scale_comp (IIIa.heatLerayK 1 i j) _ x]
    simp [smul_eq_mul]
  rw [e1, fderiv_smul_apply', key, smul_eq_mul, smul_eq_mul, ← gradK_scale_coeff t ht]
  ring

lemma scale_gradK (t : ℝ) (ht : 0 < t) (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    gradKCon t x M = (t ^ 2)⁻¹ • gradKCon 1 ((Real.sqrt t)⁻¹ • x) M := by
  unfold gradKCon
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kd_scale t ht i j k x]
  ring

lemma gradK1_contDiff (M : Matrix (Fin 3) (Fin 3) ℝ) : ContDiff ℝ 2 (fun y => gradKCon 1 y M) := by
  have hK : ∀ i j : Fin 3, ContDiff ℝ 3 (fun x => IIIa.heatLerayK 1 i j x) :=
    fun i j => heatLerayKSmooth 1 one_pos i j
  unfold gradKCon
  refine PiLp.contDiff_toLp.comp ?_
  refine contDiff_pi.2 fun i => ?_
  refine ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_
  exact (((hK i j).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).mul contDiff_const

/-- **Parabolic homogeneity of the contracted kernel gradient** (source 3600-3610,
`K_t(x) = t^{-3/2}K_1(x/√t)`): `x·∇_x F + 2t ∂_tF = -4F` for `F = ∇K_t : M`, `t > 0`. -/
theorem gradKEuler : GradKEuler := by
  intro t ht x M
  have ht0 : t ≠ 0 := ht.ne'
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hF1d : ∀ p : Space, DifferentiableAt ℝ (fun y => gradKCon 1 y M) p :=
    fun p => ((gradK1_contDiff M).differentiable (by norm_num)) p
  -- x-derivative of the scaled field
  have hX : fderiv ℝ (fun y => gradKCon t y M) x x
      = (t ^ 2)⁻¹ • fderiv ℝ (fun z => gradKCon 1 z M) ((Real.sqrt t)⁻¹ • x) ((Real.sqrt t)⁻¹ • x) := by
    have e : (fun y => gradKCon t y M) = fun y => (t ^ 2)⁻¹ • gradKCon 1 ((Real.sqrt t)⁻¹ • y) M :=
      funext fun y => scale_gradK t ht y M
    have key : ∀ v : Space, fderiv ℝ (fun y => gradKCon 1 ((Real.sqrt t)⁻¹ • y) M) x v
        = (Real.sqrt t)⁻¹ • fderiv ℝ (fun z => gradKCon 1 z M) ((Real.sqrt t)⁻¹ • x) v := by
      intro v
      rw [fderiv_scale_comp (fun z => gradKCon 1 z M) _ x]
      simp [smul_eq_mul]
    rw [e, fderiv_smul_apply_space, key, map_smul (fderiv ℝ (fun z => gradKCon 1 z M) ((Real.sqrt t)⁻¹ • x)) ((Real.sqrt t)⁻¹) x]
  -- time derivative of the scaled field
  have hu : HasDerivAt (fun t' : ℝ => (t' ^ 2)⁻¹) (-(2 * t) / (t ^ 2) ^ 2) t := by
    have := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht0)
    refine this.congr_deriv ?_
    norm_num
  have hs : HasDerivAt (fun t' : ℝ => (Real.sqrt t')⁻¹)
      (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) t :=
    (Real.hasDerivAt_sqrt ht0).inv hs0
  have hsx : HasDerivAt (fun t' : ℝ => (Real.sqrt t')⁻¹ • x)
      ((-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) • x) t :=
    hs.smul_const x
  have hF1g : HasFDerivAt (fun z => gradKCon 1 z M)
      (fderiv ℝ (fun z => gradKCon 1 z M) ((Real.sqrt t)⁻¹ • x)) ((Real.sqrt t)⁻¹ • x) :=
    (hF1d _).hasFDerivAt
  have hG := HasFDerivAt.comp_hasDerivAt t hF1g hsx
  have hD := hu.smul hG
  have hev : (fun t' => gradKCon t' x M) =ᶠ[𝓝 t]
      fun t' => (t' ^ 2)⁻¹ • gradKCon 1 ((Real.sqrt t')⁻¹ • x) M := by
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    exact scale_gradK t' ht' x M
  have hT := hD.congr_of_eventuallyEq hev
  rw [hT.deriv]
  have hinv : t⁻¹ = (Real.sqrt t)⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt ht.le]
  have hsc : (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) • x
      = (-(1 / 2 : ℝ) * t⁻¹) • ((Real.sqrt t)⁻¹ • x) := by
    rw [smul_smul]
    congr 1
    rw [hinv]
    field_simp <;> ring
  simp only [Function.comp_apply]
  rw [hX, hsc, map_smul (fderiv ℝ (fun z => gradKCon 1 z M) ((Real.sqrt t)⁻¹ • x)) (-(1 / 2 : ℝ) * t⁻¹) ((Real.sqrt t)⁻¹ • x), scale_gradK t ht x M]
  generalize (Real.sqrt t)⁻¹ • x = y
  have ha : (-2 * t) * ((t ^ 2)⁻¹ * (-(1 / 2 : ℝ) * t⁻¹)) = (t ^ 2)⁻¹ := by
    field_simp <;> ring
  have hb : (-2 * t) * (-(2 * t) / (t ^ 2) ^ 2) - 4 * (t ^ 2)⁻¹ = 0 := by
    field_simp <;> ring
  have e2 : (-2 * t) • ((t ^ 2)⁻¹ • ((-(1 / 2 : ℝ) * t⁻¹) • fderiv ℝ (fun z => gradKCon 1 z M) y y)
        + (-(2 * t) / (t ^ 2) ^ 2) • gradKCon 1 y M) - (4 : ℝ) • ((t ^ 2)⁻¹ • gradKCon 1 y M)
      = ((-2 * t) * ((t ^ 2)⁻¹ * (-(1 / 2 : ℝ) * t⁻¹))) • fderiv ℝ (fun z => gradKCon 1 z M) y y
        + ((-2 * t) * (-(2 * t) / (t ^ 2) ^ 2) - 4 * (t ^ 2)⁻¹) • gradKCon 1 y M := by
    module
  rw [e2, ha, hb, zero_smul, add_zero]


end UnforcedLeray.Short.PartIIIb.Concrete
