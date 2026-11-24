import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Ball
import UnforcedLeray.Short.PartIIb.ExactSplit
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# Three background facts at the levels of the regime (source 2031, 2505-2562, 2706-2777,
3877-3878, 4144-4145, 5007-5008, 5094)

Source of record: `the November 2 reference manuscript` (73 pages).

Part of `ORG:return-concrete/instance-3/background-facts`.  The three per-level hypotheses of
`raBoundExists_of` (`Concrete/ReturnInst/AffineSource/RABound.lean`), stated at the levels of the
regime (`IIb.BgRegime`, `ν ≤ ν₀`, slow age `Σ`, growing eigenpair `q`) over `Params`, each proved
from the Part II / near-layer fact it comes from:

* `SplitMultLevels` (source 2706, 2758-2762, 2775-2777, 3877-3878): for every exact split
  (`IIb.ExactSplitII` with `ρ_b = rhoB p m₀ C₀ k₀`) the split multiplier
  `M_U b = (v⊗b + b⊗v, v_b⊗b + b⊗v_b) : H → Z` exists.  `splitMultLevels_of` from the coefficient
  bounds `NearInst.SplitMultBound` (`PartIII-b:C/near/4`) and the multiplier construction
  `NearInst.CoeffMultExists` (accepted `PartIII-b:C/near/1`, `coeffMultExists`); this is the
  split-multiplier part of the near layer `NearOpsExistC` (`PartIII-b:C/near/5`).
* `BgAxiLevels` (source 121-124, 2031, 2522-2523, 4144-4145): `U = V + r_b` is axisymmetric
  without swirl, pointwise (`AxiNoSwirlPt`).  `bgAxiLevels_of` from `IIb.StrongRegularity`
  (`short-bg:strong`, 2525-2562: `U` is jointly smooth and axisymmetric without swirl) and
  `axiNoSwirlPt_of_ae`.
* `BgW1Levels` (source 2538-2541 `short-bg:strong`, 5007-5008, 5094 "`δ_U ≤ P_νρ` from the
  background bounds"): `δ_U = ‖U - U_raw‖_{W^{1,∞}} ≤ C ν^{-k} e^{m/ν} ε^{3/11}`.
  `bgW1Levels_of` from `IIb.StrongRegularity` (the `W^{1,∞}` bounds of `w` and `E_εα`) and
  `IIb.InletContDiff` (accepted `PartII-b:G4/5/1`, `inletContDiff`: `E_i` is smooth, source
  2347-2369, 2385-2387).

The last two are stated for the contraction-ball background (`IsBallSplit`, `Ball.lean`):
`IIb.StrongRegularity` is a statement about the solutions of the projected equation in the
contraction ball (2507-2512), and `IIb.ExactSplitII` alone does not place the state there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-! ## 1. The split multiplier (source 2706, 2758-2762, 2775-2777, 3877-3878) -/

/-- **The split multiplier exists at the levels of the regime** (source 2706, 2758-2762,
3877-3878, with the coefficient bounds 2716, 2775-2777): for `m_Z > 3/2`, `0 < m₀ ≤ 3d₋/11`,
`C₀ > 0`, the slow age `Σ > 0` and the growing eigenpair `(λ, q)`, there is `ν₀ > 0` such that at
every level of the regime with `ν ≤ ν₀`, `Σ = p.ageCut`, `q = p.mode`, and every exact split
`U = V + r_b` with `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`, a bounded `M_U : H → Z` with
`M_U b = (v⊗b + b⊗v, v_b⊗b + b⊗v_b)`, `v = s^{-1/2}V`, `v_b = s^{-1/2}r_b` (`IsSplitMult`)
exists. -/
def SplitMultLevels : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < m0 → m0 ≤ 3 * dm / 11 → 0 < C0 →
    ∀ mZ : ℝ, 3 / 2 < mZ →
    ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
      UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V
          rb →
        ∃ M : Hsp p.c →L[ℝ] Zsp p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
          NearInst.IsSplitMult M p.R V rb

/-- `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11} > 0` for `C₀ > 0`. -/
theorem bg_rhoB_pos (p : Params) {m0 C0 : ℝ} (k0 : ℕ) (hC0 : 0 < C0) :
    0 < UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 :=
  mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos p.ν_pos _))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos p.ε_pos _)

/-- **`SplitMultLevels`** from the coefficient bounds `SplitMultBound` (`PartIII-b:C/near/4`) and
the multiplier construction `CoeffMultExists` (`PartIII-b:C/near/1`). -/
theorem splitMultLevels_of (hC : NearInst.CoeffMultExists) (hS : NearInst.SplitMultBound) :
    SplitMultLevels := by
  intro dm dp hdm m0 C0 k0 hm0 hm0d hC0 mZ hmZ Sig lam q hSig hq
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hS dm dp hdm m0 C0 k0 hm0 hm0d hC0 mZ hmZ Sig lam q hSig hq
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hSig' hq' S_in V rb hsplit
  obtain ⟨hmV, hmr, hbV, hbr⟩ := h p d hreg hν hSig' hq' S_in V rb hsplit
  exact hC p.c mZ _ _ _ _ _ p.c_pos (bg_rhoB_pos p k0 hC0) hmV hmr hbV hbr

/-- `SplitMultLevels` from the coefficient bounds alone (`coeffMultExists` is accepted). -/
theorem splitMultLevels_of' (hS : NearInst.SplitMultBound) : SplitMultLevels :=
  splitMultLevels_of NearInst.coeffMultExists hS

/-! ## 2. Axisymmetry without swirl (source 121-124, 2031, 2522-2523, 2525-2562, 4144-4145) -/

/-- **`U = V + r_b` is axisymmetric without swirl at the levels of the regime** (source 121-124,
2031, 2522-2523 "reality, no-swirl symmetry, and periodicity are preserved at each iteration",
4144-4145 "the prescribed orthogonal symmetry"): for the slow age `Σ > 0`, the growing eigenpair
`(λ, q)`, `0 < m` with `2m < 3d₋/11` and the ball constants `C₁ > 0, k₁`, there is `ν₀ > 0` such
that at every level of the regime with `ν ≤ ν₀`, `Σ = p.ageCut`, `q = p.mode`, every split which
is the contraction-ball background of radius `C₁ν^{-k₁}e^{m/ν}ε^{3/11}` (`IsBallSplit`) has
`g(U(τ, g⁻¹y)) = U(τ, y)` for every isometry `g` fixing `e₃` (`AxiNoSwirlPt`). -/
def BgAxiLevels : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ V rb : ℝ → UnforcedLeray.SpatialField,
        IsBallSplit p (UnforcedLeray.Short.IIb.rhoB p m C₁ k₁) V rb →
        ∀ τ : ℝ, AxiNoSwirlPt (fun y => V τ y + rb τ y)

/-- **`BgAxiLevels`** from `short-bg:strong` (`IIb.StrongRegularity`, source 2525-2562: on the
contraction ball `U = U_raw + E_εα + w` is jointly smooth and axisymmetric without swirl) and
`axiNoSwirlPt_of_ae` (a continuous field invariant a.e. is invariant pointwise). -/
theorem bgAxiLevels_of (hSR : UnforcedLeray.Short.IIb.StrongRegularity) : BgAxiLevels := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C₂, k₂, ν₀, hC₂, hν₀, h⟩ := hSR Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, ?_⟩
  rintro p d hreg hν hSig' hq' V rb ⟨z, hz, hV, hrb, hball⟩ τ
  obtain ⟨hsm, -, -, haxi, -⟩ := h p d hreg hν hSig' hq' z hz hball
  rw [isBallSplit_bgField hV hrb τ]
  have hc : Continuous (UnforcedLeray.Short.IIb.bgField p z τ) := by
    have h1 := hsm.continuous.comp (Continuous.prodMk_right (Y := Space) τ)
    exact h1
  exact axiNoSwirlPt_of_ae hc (haxi τ)

/-! ## 3. The `W^{1,∞}` bound of `U - U_raw` (source 2538-2541, 5007-5008, 5094) -/

/-- **`δ_U = ‖U - U_raw‖_{W^{1,∞}} ≤ P_ν e^{m/ν}ε^{3/11}` at the levels of the regime** (source
2538-2541 `short-bg:strong`, 5007-5008, 5094 "`δ_U ≤ P_νρ` from the background bounds"): with the
data of `BgAxiLevels` there are `C > 0, k, ν₀ > 0` such that at every level of the regime with
`ν ≤ ν₀`, `Σ = p.ageCut`, `q = p.mode`, every contraction-ball split has
`|U - U_raw| ≤ Cν^{-k}e^{m/ν}ε^{3/11}` and `‖∇_y(U - U_raw)‖ ≤ Cν^{-k}e^{m/ν}ε^{3/11}` at every
phase and point (`U - U_raw = E_εα + w`). -/
def BgW1Levels : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ V rb : ℝ → UnforcedLeray.SpatialField,
        IsBallSplit p (UnforcedLeray.Short.IIb.rhoB p m C₁ k₁) V rb →
        ∀ (τ : ℝ) (y : Space),
          ‖V τ y + rb τ y - p.raw τ y‖ ≤ UnforcedLeray.Short.IIb.rhoB p m C k ∧
            ‖fderiv ℝ (fun y' => V τ y' + rb τ y' - p.raw τ y') y‖ ≤
              UnforcedLeray.Short.IIb.rhoB p m C k

/-- **`BgW1Levels`** from `short-bg:strong` (`IIb.StrongRegularity`: `‖w‖_{W^{1,∞}}` and
`‖E_εα‖_{W^{1,∞}}` are `≤ P_ν e^{m/ν}ε^{3/11}`, source 2538-2541) and the smoothness of the inlet
columns (`IIb.InletContDiff`, source 2347-2369, 2385-2387), which makes the derivative of the sum
`E_εα + w` the sum of the derivatives. -/
theorem bgW1Levels_of (hSR : UnforcedLeray.Short.IIb.StrongRegularity)
    (hI : UnforcedLeray.Short.IIb.InletContDiff) : BgW1Levels := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C₂, k₂, ν₀, hC₂, hν₀, h⟩ := hSR Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hI'⟩ := hI Sig lam q hSig hq dm dp hdm
  refine ⟨2 * C₂, k₂, min ν₀ ν₁, by positivity, lt_min hν₀ hν₁, ?_⟩
  rintro p d hreg hν hSig' hq' V rb ⟨z, hz, hV, hrb, hball⟩ τ y
  obtain ⟨-, -, -, -, hcorr, -, hinl⟩ :=
    h p d hreg (hν.trans (min_le_left _ _)) hSig' hq' z hz hball
  have hsm := hI' p d hreg (hν.trans (min_le_right _ _)) hSig' hq'
  have hB0 : 0 ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₂.le (inv_nonneg.2 (pow_nonneg p.ν_pos.le _)))
      (Real.exp_pos _).le) (Real.rpow_nonneg p.ε_pos.le _)
  have hB2 : UnforcedLeray.Short.IIb.rhoB p m (2 * C₂) k₂ =
      C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) +
        C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
    unfold UnforcedLeray.Short.IIb.rhoB
    ring
  have hF : (fun y' => V τ y' + rb τ y' - p.raw τ y') =
      fun y' => (∑ i : Fin 2, p.coord z i • p.inlet i τ y') + p.corr z τ y' := by
    funext y'
    rw [hV, hrb]
    abel
  have hd0 : Differentiable ℝ (p.inlet 0 τ) := (hsm 0 τ).differentiable (by simp)
  have hd1 : Differentiable ℝ (p.inlet 1 τ) := (hsm 1 τ).differentiable (by simp)
  have hSd : DifferentiableAt ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y := by
    have e0 : DifferentiableAt ℝ (fun y' => p.coord z 0 • p.inlet 0 τ y') y :=
      (hd0 y).fun_const_smul (p.coord z 0)
    have e1 : DifferentiableAt ℝ (fun y' => p.coord z 1 • p.inlet 1 τ y') y :=
      (hd1 y).fun_const_smul (p.coord z 1)
    simp only [Fin.sum_univ_two]
    exact e0.fun_add e1
  have hval : V τ y + rb τ y - p.raw τ y =
      (∑ i : Fin 2, p.coord z i • p.inlet i τ y) + p.corr z τ y := congrFun hF y
  rw [hF, hval, hB2]
  refine ⟨(norm_add_le _ _).trans (add_le_add (hinl τ y).1 (hcorr τ y).1), ?_⟩
  by_cases hc : DifferentiableAt ℝ (p.corr z τ) y
  · rw [fderiv_fun_add hSd hc]
    exact (norm_add_le _ _).trans (add_le_add (hinl τ y).2 (hcorr τ y).2)
  · have hnd : ¬ DifferentiableAt ℝ
        (fun y' => (∑ i : Fin 2, p.coord z i • p.inlet i τ y') + p.corr z τ y') y := by
      intro hd
      have h2 : DifferentiableAt ℝ (fun y' => ((∑ i : Fin 2, p.coord z i • p.inlet i τ y') +
          p.corr z τ y') - ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y := hd.fun_sub hSd
      simp only [add_sub_cancel_left] at h2
      exact hc h2
    rw [fderiv_zero_of_not_differentiableAt hnd, norm_zero]
    linarith

/-- `BgW1Levels` from `short-bg:strong` alone (`inletContDiff` is accepted). -/
theorem bgW1Levels_of' (hSR : UnforcedLeray.Short.IIb.StrongRegularity) : BgW1Levels :=
  bgW1Levels_of hSR UnforcedLeray.Short.IIb.inletContDiff

end UnforcedLeray.Short.PartIIIb.Concrete
