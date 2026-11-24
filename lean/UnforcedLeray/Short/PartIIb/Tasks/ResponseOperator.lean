import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator.BodySol
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys

/-!
# Part II-b, task `PartII-b:P2`: the physical response operator `Θ : RowSpace p.c →L[ℝ] p.Z`

Source of record: `the November 2 reference manuscript`, lines 2490-2498.

For `Ke, Ce` satisfying `IsKop p Ke` and `IsCop p Ce` (`p.period ≤ 1`), we construct the bounded
linear response operator `Θ : RowSpace p.c →L[ℝ] p.Z` (`thetaMap p hp1 hK`) mapping `y = (f, α)`
to `(w, νΔw, T₀w, R^{2/p} α)` where `w = solD p hp1 f` is the unique solenoidal solution in `D` of
`L₀ w = 𝔓 (N_v (toProf p.c f))`:
* `‖Θ‖ ≤ C (π R²)^{1/p}` with a universal constant `C > 0` (`norm_thetaMap_le`),
* `p.coord (Θ y) = y.ofLp.2.ofLp` and `cA p.period (Θ y : Amb p.period) = p.R ^ (2 / bgp) • y.ofLp.2`,
* for every profile `b` with `IsResponse p.ν p.c p.ε 0 bgp (toProf p.c y.ofLp.1) b`,
  `rep (p.wOf (Θ y)) =ᵃᵉ NvC p.R b` and `HasRep (p.wOf (Θ y)) (NvC p.R b)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp UnforcedLeray.Short.PartIIa
  UnforcedLeray.Short.IIb.RespOp

namespace RespOp

/-- Ambient tuple `(w, νΔw, T₀w, R^{2/p} α)` for `y = (f, α) : RowSpace p.c`. -/
def ambOf (p : Params) (hp1 : p.period ≤ 1) (y : RowSpace p.c) : Amb p.period :=
  WithLp.toLp 1 ((solD p hp1 y.ofLp.1 : Yq p.period q0E),
    WithLp.toLp 1 (nuLapD (solD p hp1 y.ofLp.1),
      WithLp.toLp 1 (T0D (solD p hp1 y.ofLp.1), p.R ^ (2 / bgp) • y.ofLp.2)))

@[simp]
theorem cw_ambOf (p : Params) (hp1 : p.period ≤ 1) (y : RowSpace p.c) :
    cw p.period (ambOf p hp1 y) = (solD p hp1 y.ofLp.1 : Yq p.period q0E) := rfl

@[simp]
theorem cΔ_ambOf (p : Params) (hp1 : p.period ≤ 1) (y : RowSpace p.c) :
    cΔ p.period (ambOf p hp1 y) = nuLapD (solD p hp1 y.ofLp.1) := rfl

@[simp]
theorem cT_ambOf (p : Params) (hp1 : p.period ≤ 1) (y : RowSpace p.c) :
    cT p.period (ambOf p hp1 y) = T0D (solD p hp1 y.ofLp.1) := rfl

@[simp]
theorem cA_ambOf (p : Params) (hp1 : p.period ≤ 1) (y : RowSpace p.c) :
    cA p.period (ambOf p hp1 y) = p.R ^ (2 / bgp) • y.ofLp.2 := rfl

theorem ambOf_mem_graphSpace (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) :
    ambOf p hp1 y ∈ graphSpace p.period p.ν := by
  rw [mem_graphSpace]
  have hwX : (solD p hp1 y.ofLp.1 : Yq p.period q0E) ∈ X p.period p.ν q0E :=
    ⟨⟨(solD p hp1 y.ofLp.1).2, solD_mem_Ysigma p hp1 y.ofLp.1⟩,
      solD_mem_Osym_of_isKop p hp1 hK y.ofLp.1⟩
  refine ⟨mem_XGraph_iff.2 ⟨hwX, rfl, rfl⟩, solD_mem_realSub p hp1 y.ofLp.1⟩

/-- The underlying `ℝ`-linear map `RowSpace p.c →ₗ[ℝ] p.Z`. -/
def thetaLin (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) : RowSpace p.c →ₗ[ℝ] p.Z where
  toFun y := ⟨ambOf p hp1 y, ambOf_mem_graphSpace p hp1 hK y⟩
  map_add' y₁ y₂ := by
    apply Subtype.ext
    change ambOf p hp1 (y₁ + y₂) = ambOf p hp1 y₁ + ambOf p hp1 y₂
    unfold ambOf
    have hf : (y₁ + y₂).ofLp.1 = y₁.ofLp.1 + y₂.ofLp.1 := rfl
    have hα : (y₁ + y₂).ofLp.2 = y₁.ofLp.2 + y₂.ofLp.2 := rfl
    have hs := solD_add p hp1 y₁.ofLp.1 y₂.ofLp.1
    have hL : nuLapD (solD p hp1 y₁.ofLp.1 + solD p hp1 y₂.ofLp.1) =
        nuLapD (solD p hp1 y₁.ofLp.1) + nuLapD (solD p hp1 y₂.ofLp.1) :=
      map_add nuLapL _ _
    have hT : T0D (solD p hp1 y₁.ofLp.1 + solD p hp1 y₂.ofLp.1) =
        T0D (solD p hp1 y₁.ofLp.1) + T0D (solD p hp1 y₂.ofLp.1) :=
      map_add T0L _ _
    rw [hf, hα, hs, Submodule.coe_add, hL, hT, smul_add]
    rfl
  map_smul' a y := by
    apply Subtype.ext
    change ambOf p hp1 (a • y) = a • ambOf p hp1 y
    unfold ambOf
    have hf : (a • y).ofLp.1 = a • y.ofLp.1 := rfl
    have hα : (a • y).ofLp.2 = a • y.ofLp.2 := rfl
    have hs := solD_smul p hp1 a y.ofLp.1
    have hL : nuLapD (a • solD p hp1 y.ofLp.1) = a • nuLapD (solD p hp1 y.ofLp.1) :=
      map_smul nuLapL (a : ℂ) (solD p hp1 y.ofLp.1)
    have hT : T0D (a • solD p hp1 y.ofLp.1) = a • T0D (solD p hp1 y.ofLp.1) :=
      map_smul T0L (a : ℂ) (solD p hp1 y.ofLp.1)
    rw [hf, hα, hs, hL, hT, smul_comm]
    rfl

theorem rpow_two_div_bgp_le (p : Params) :
    p.R ^ (2 / bgp) ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
  have hR : 0 ≤ p.R := p.R_pos.le
  have h1 : p.R ^ (2 / bgp) = (p.R ^ 2) ^ (1 / bgp) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hR, show (2 : ℝ) * (1 / bgp) = 2 / bgp by ring]
  have hpi : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
  have h2 : p.R ^ 2 ≤ Real.pi * p.R ^ 2 := by
    calc p.R ^ 2 = 1 * p.R ^ 2 := (one_mul _).symm
      _ ≤ Real.pi * p.R ^ 2 := mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
  have h3 : (p.R ^ 2) ^ (1 / bgp) ≤ (Real.pi * p.R ^ 2) ^ (1 / bgp) :=
    Real.rpow_le_rpow (sq_nonneg _) h2 (by norm_num [bgp])
  have hCb : 1 ≤ C_body := by
    unfold C_body
    have : 0 ≤ C_graph * 23 * ‖lerayC q0E one_lt_q0E q0E_ne_top‖ :=
      mul_nonneg (mul_nonneg C_graph_nonneg (by norm_num)) (norm_nonneg _)
    linarith
  have hK : 0 ≤ (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
    have : 0 < p.R := p.R_pos
    positivity
  calc p.R ^ (2 / bgp) = (p.R ^ 2) ^ (1 / bgp) := h1
    _ ≤ 1 * (Real.pi * p.R ^ 2) ^ (1 / bgp) := by rw [one_mul]; exact h3
    _ ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) := mul_le_mul_of_nonneg_right hCb hK

theorem norm_thetaLin_le (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) :
    ‖thetaLin p hp1 hK y‖ ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖y‖ := by
  have hnorm : ‖thetaLin p hp1 hK y‖ =
      graphNormD (solD p hp1 y.ofLp.1) + ‖p.R ^ (2 / bgp) • y.ofLp.2‖ := by
    change ‖ambOf p hp1 y‖ = _
    rw [norm_amb, cw_ambOf, cΔ_ambOf, cT_ambOf, cA_ambOf]
    rfl
  have hR_nonneg : 0 ≤ p.R ^ (2 / bgp) := Real.rpow_nonneg p.R_pos.le _
  have hA : ‖p.R ^ (2 / bgp) • y.ofLp.2‖ ≤
      C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖y.ofLp.2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hR_nonneg]
    exact mul_le_mul_of_nonneg_right (rpow_two_div_bgp_le p) (norm_nonneg _)
  have hD := graphNormD_solD_le p hp1 y.ofLp.1
  have hy : ‖y‖ = ‖y.ofLp.1‖ + ‖y.ofLp.2‖ := WithLp.prod_norm_eq_of_L1 y
  rw [hnorm, hy]
  linarith

/-- The bounded linear response operator `Θ : RowSpace p.c →L[ℝ] p.Z`. -/
def thetaMap (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) : RowSpace p.c →L[ℝ] p.Z :=
  LinearMap.mkContinuous (thetaLin p hp1 hK) (C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp))
    (norm_thetaLin_le p hp1 hK)

theorem norm_thetaMap_le (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) :
    ‖thetaMap p hp1 hK‖ ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
  have hK0 : 0 ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
    have : 0 < C_body := C_body_pos
    have : 0 < p.R := p.R_pos
    positivity
  exact LinearMap.mkContinuous_norm_le (thetaLin p hp1 hK) hK0 (norm_thetaLin_le p hp1 hK)

@[simp]
theorem thetaMap_wOf (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) :
    p.wOf (thetaMap p hp1 hK y) = (solD p hp1 y.ofLp.1 : Yq p.period q0E) := rfl

@[simp]
theorem thetaMap_cA (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) :
    cA p.period (thetaMap p hp1 hK y : Amb p.period) = p.R ^ (2 / bgp) • y.ofLp.2 := rfl

theorem thetaMap_coord_apply (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) (i : Fin 2) :
    p.coord (thetaMap p hp1 hK y) i = y.ofLp.2 i := by
  unfold Params.coord
  rw [thetaMap_cA]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hexp : (2 / bgp : ℝ) = 8 / 11 := by norm_num [bgp]
  have hR : p.R = p.ε⁻¹ := rfl
  have hε_ne : p.ε ^ (8 / 11 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos p.ε_pos _).ne'
  rw [hexp, hR, Real.inv_rpow p.ε_pos.le, ← mul_assoc, mul_inv_cancel₀ hε_ne, one_mul]

theorem thetaMap_coord (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) :
    p.coord (thetaMap p hp1 hK y) = y.ofLp.2.ofLp :=
  funext (thetaMap_coord_apply p hp1 hK y)

theorem thetaMap_hasRep (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (y : RowSpace p.c) (b : CProf)
    (hb : IsResponse p.ν p.c p.ε 0 bgp (toProf p.c y.ofLp.1) b) :
    (∀ᵐ x : ℝ × Space, rep (p.wOf (thetaMap p hp1 hK y)) x.1 x.2 = NvC p.R b x) ∧
      HasRep (p.wOf (thetaMap p hp1 hK y)) (NvC p.R b) :=
  solD_hasRep_of_isResponse p hp1 y.ofLp.1 b hb

end RespOp

/-- **Statement of `PartII-b:P2`** (SP 2490-2498): for `Ke, Ce` with `IsKop p Ke` and `IsCop p Ce`,
there is a bounded linear response operator `Θ : RowSpace p.c →L[ℝ] p.Z` mapping `(f, α)` to
`(N_v T_ε f, R^{2/p} α)` with `‖Θ‖ ≤ C (π R²)^{1/p}`. -/
def ResponseOperator : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ C : ℝ, 0 < C ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.period ≤ 1 →
      ∀ (Ke : HpR p.c →L[ℝ] HpR p.c) (Ce : E2 →L[ℝ] HpR p.c), IsKop p Ke → IsCop p Ce →
        ∃ Θ : RowSpace p.c →L[ℝ] p.Z,
          ‖Θ‖ ≤ C * (Real.pi * p.R ^ 2) ^ (1 / bgp) ∧
          (∀ y : RowSpace p.c, p.coord (Θ y) = y.ofLp.2.ofLp) ∧
          (∀ y : RowSpace p.c, cA p.period (Θ y : Amb p.period) = p.R ^ (2 / bgp) • y.ofLp.2) ∧
          ∀ (y : RowSpace p.c) (b : CProf),
            IsResponse p.ν p.c p.ε 0 bgp (toProf p.c y.ofLp.1) b →
              (∀ᵐ x : ℝ × Space, rep (p.wOf (Θ y)) x.1 x.2 = NvC p.R b x) ∧
                HasRep (p.wOf (Θ y)) (NvC p.R b)

/-- **`PartII-b:P2`** (`responseTheta`, SP 2490-2498). -/
theorem responseTheta : ResponseOperator := by
  intro dm dp _
  refine ⟨C_body, C_body_pos, ?_⟩
  intro p d _ hp1 Ke Ce hK _
  exact ⟨thetaMap p hp1 hK, norm_thetaMap_le p hp1 hK, thetaMap_coord p hp1 hK,
    thetaMap_cA p hp1 hK, thetaMap_hasRep p hp1 hK⟩

end UnforcedLeray.Short.IIb

end
