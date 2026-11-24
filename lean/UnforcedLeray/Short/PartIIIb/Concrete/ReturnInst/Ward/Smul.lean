import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs

/-!
# `WardSmul`: homogeneity of the Ward fields (source 4171, 4140-4141, 3621-3629)

Proves `WardSmul` (`Ward/Defs.lean`) with no hypotheses.  Every step is unconditional:
`∫ r • f = r • ∫ f` (`integral_const_mul`), `fderiv (r • f) = r • fderiv f` and
`deriv (r • f) = r • deriv f` over `ℝ` (`fderiv_const_smul_field`, `deriv_fun_const_smul_field`),
and the entrywise linearity of the Cartesian lift `nsSym` / `cartLift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Matrix layer -/

theorem wsm_nsSym_smul (k : ℝ) (T : Ten3) :
    NearInst.nsSym (k • T) = k • NearInst.nsSym T := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem wsm_cartLift_smul (R c r : ℝ) (g : Chart → Ten3) :
    NearInst.cartLift R c (r • g) = fun τ z => r • NearInst.cartLift R c g τ z := by
  funext τ z
  unfold NearInst.cartLift
  simp only [Pi.smul_apply, wsm_nsSym_smul]
  rw [smul_comm, Matrix.mul_smul, Matrix.smul_mul]

theorem wsm_oldPhys_smul (R c r : ℝ) (g : Chart → Ten3) :
    oldPhys R c (r • g) = fun τ z => r • oldPhys R c g τ z := by
  unfold oldPhys
  exact wsm_cartLift_smul R c r g

/-! ## 2. The separated kernel and the outward primitive -/

theorem wsm_sepW_smul (ν : ℝ) (μ : ℂ) (r : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Space) (τ : ℝ) (i : Fin 3) :
    IIIa.sepW ν μ (fun τ z => r • T τ z) y τ i = (r : ℂ) * IIIa.sepW ν μ T y τ i := by
  unfold IIIa.sepW
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, ← Finset.mul_sum,
    mul_left_comm _ (r : ℂ), integral_const_mul]

theorem wsm_outPrim_smul (Z : ℝ → Space → Space) (r τ ρ z : ℝ) :
    outPrim (fun τ z => r • Z τ z) τ ρ z = r * outPrim Z τ ρ z := by
  have h : ∫ ρ' in Ioi ρ, ρ' * (r • Z τ !₂[ρ', 0, z]) 2 =
      r * ∫ ρ' in Ioi ρ, ρ' * Z τ !₂[ρ', 0, z] 2 := by
    rw [← integral_const_mul]
    congr 1
    funext ρ'
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  unfold outPrim
  rw [h]
  ring

theorem wsm_wardStreamCut_smul (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) (Z : ℝ → Space → Space)
    (τ : ℝ) (y : Space) :
    wardStreamCut ν R χy (fun τ z => r • Z τ z) τ y = r • wardStreamCut ν R χy Z τ y := by
  unfold wardStreamCut
  simp only [wsm_outPrim_smul]
  module

/-! ## 3. The Ward displacement -/

theorem wsm_wardX0_smul (ν μ R c r : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    wardX0 ν μ R c (r • g) τ y = r • wardX0 ν μ R c g τ y := by
  unfold wardX0
  rw [wsm_oldPhys_smul]
  ext i
  simp only [wsm_sepW_smul, PiLp.smul_apply, smul_eq_mul]
  rw [← mul_sub, Complex.re_ofReal_mul]

theorem wsm_wardX_smul (ν μ R c : ℝ) (χy : ℝ → ℝ) (r : ℝ) (g : Chart → Ten3) :
    wardX ν μ R c χy (r • g) = fun τ y => r • wardX ν μ R c χy g τ y := by
  unfold wardX
  have h0 : wardX0 ν μ R c (r • g) = fun τ y => r • wardX0 ν μ R c g τ y :=
    funext fun τ => funext fun y => wsm_wardX0_smul ν μ R c r g τ y
  rw [h0]
  funext τ y
  exact wsm_wardStreamCut_smul ν R χy r (wardX0 ν μ R c g) τ y

/-! ## 4. Pointwise calculus without differentiability -/

theorem wsm_fderiv (r : ℝ) (f : Space → Space) (y : Space) :
    fderiv ℝ (fun y' => r • f y') y = r • fderiv ℝ f y := by
  rw [show (fun y' => r • f y') = r • f from rfl, fderiv_const_smul_field]
  rfl

theorem wsm_fderiv' (r : ℝ) (f : Space → Space) (y : Space) :
    fderiv ℝ (r • f) y = r • fderiv ℝ f y := by
  rw [fderiv_const_smul_field]
  rfl

theorem wsm_physPd (r : ℝ) (f : Space → Space) (j : Fin 3) (y : Space) :
    physPd (fun y' => r • f y') j y = r • physPd f j y := by
  unfold physPd
  rw [wsm_fderiv, ContinuousLinearMap.smul_apply]

theorem wsm_physPd2 (r : ℝ) (f : Space → Space) (j l : Fin 3) (y : Space) :
    physPd2 (fun y' => r • f y') j l y = r • physPd2 f j l y := by
  have h : (fun y' => physPd (fun y'' => r • f y'') l y') = fun y' => r • physPd f l y' :=
    funext fun y' => wsm_physPd r f l y'
  unfold physPd2
  rw [h]
  exact wsm_physPd r (fun y' => physPd f l y') j y

theorem wsm_physLap (r : ℝ) (f : Space → Space) (y : Space) :
    physLap (fun y' => r • f y') y = r • physLap f y := by
  unfold physLap
  simp only [wsm_physPd2, Finset.smul_sum]

theorem wsm_physDmu (ν μ r : ℝ) (X : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    physDmu ν μ (fun t y' => r • X t y') τ y = r • physDmu ν μ X τ y := by
  have hd : deriv (fun t => r • X t y) τ = r • deriv (fun t => X t y) τ :=
    deriv_fun_const_smul_field r (fun t => X t y)
  unfold physDmu
  dsimp only
  rw [hd, wsm_fderiv, wsm_physLap]
  simp only [ContinuousLinearMap.smul_apply]
  module

theorem wsm_physCdiff (U X : Space → Space) (r : ℝ) (y : Space) :
    physCdiff U (fun y' => r • X y') y = r • physCdiff U X y := by
  unfold physCdiff
  simp only [wsm_physPd, wsm_physPd2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  module

theorem wsm_physUUD2 (U X : Space → Space) (r : ℝ) (y : Space) :
    physUUD2 U (fun y' => r • X y') y = r • physUUD2 U X y := by
  unfold physUUD2
  simp only [wsm_physPd2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  module

theorem wsm_physDXp (X : Space → Space) (q : Space → ℝ) (r : ℝ) (y : Space) :
    physDXp (fun y' => r • X y') q y = r • physDXp X q y := by
  unfold physDXp
  ext i
  simp only [wsm_physPd, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## 5. The three fields -/

theorem wsm_wardY (ν μ R c : ℝ) (χy : ℝ → ℝ) (r : ℝ) (g : Chart → Ten3) :
    wardY ν μ R c χy (r • g) = r • wardY ν μ R c χy g := by
  unfold wardY
  rw [wsm_wardX_smul]
  funext τ y
  exact wsm_physDmu ν (μ + 1) r (wardX ν μ R c χy g) τ y

theorem wsm_wardH (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (r : ℝ)
    (g : Chart → Ten3) :
    wardH ν μ R c χy U (r • g) = r • wardH ν μ R c χy U g := by
  unfold wardH
  rw [wsm_wardX_smul]
  funext τ y
  simp only [Pi.smul_apply, wsm_fderiv, ContinuousLinearMap.smul_apply, map_smul, smul_sub]

theorem wsm_wardE (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (r : ℝ) (g : Chart → Ten3) :
    wardE ν μ R c χy U p (r • g) = r • wardE ν μ R c χy U p g := by
  unfold wardE
  rw [wsm_wardY, wsm_wardX_smul]
  funext τ y
  simp only [Pi.smul_apply, wsm_fderiv', wsm_physCdiff, wsm_physUUD2, wsm_physDXp,
    ContinuousLinearMap.smul_apply]
  module

/-- **`WardSmul`** (source 4171, 4271-4280): the three Ward fields are homogeneous, with no
hypotheses on `g`, `U` or `p`. -/
theorem wardSmul_proved : WardSmul := by
  intro ν μ R c χy U p r g
  exact ⟨wsm_wardY ν μ R c χy r g, wsm_wardH ν μ R c χy U r g, wsm_wardE ν μ R c χy U p r g⟩

end UnforcedLeray.Short.PartIIIb.Concrete
