import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.GaussCore
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound.PlanarDualMain

/-!
# Part III-a, task `PartIII-a:T21/c5/2/2/2`: unnormalised moving Euler residual bound (`MovLam0EulerSubBound`, SP 2866-2889, 2905-2918, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2889,
2905-2918, and 2991-2995 (`eq:short-causal-ampl-moving`).

The moving residual `movLam0DualEulerSub κ lam tr r k` splits (SP 2866-2872) into the rescaled
BUC train comparison defect and the pure Gaussian-cylinder residual `movLam0EulerGaussSub`
(`EulerSubTrain.movLam0DualEulerSub_eq_trainDiff_add_gauss`). The train defect is
`O(ν³/θ)` in `X_{-m,d}` (`EulerSubTrain.memLp_and_xNorm_movEulerAdj_trainDiff`), and the
Gaussian-cylinder residual is `O(d⁻²) = O(ν³/θ)` once the planar seed duality holds
(`EulerSubCore.gaussSub_bound`: image expansion of the paired kernel, paired translates of the
dual rows, Gaussian columns; SP 2876-2897). These are the proved helpers of
`ComplCoupling/EulerSubBound/` (zero `sorry`).

* `SeedPlanarDualEigen κ` (`SubBound/PlanarDual.lean`): the planar seed duality
  `v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` (SP 593-610, 2891-2918) for the seed triple
  `(lam, h, ℓ)` realizing `κ`, with the eigenvalue `lam` of that triple; proved for every `κ` in
  `SubBound/PlanarDualMain.lean` (`PlanarDualSub.seedPlanarDualEigen`): `λ₀ = c G(|y|)e^{-2iϑ}`,
  `kG = h` from `L₀h = lam h`, `K_∞^T(λ₀∇ω₀) = -c y·(K q̃)` with `q̃ = h(|y|)e^{-2iϑ}`, the
  sector identity `y·(K q̃) = 2i Δ₂⁻¹h(|y|)e^{-2iϑ}` (`SubBound/SectorLimit.lean`: Part I's
  `K q = ∇^⊥Ψ` for truncated profiles plus dominated convergence), and `v₀·∇λ₀ = -2iΩλ₀`.
* `movLam0EulerSubBound_of_planarDual`: `MovLam0EulerSubBound κ` from `SeedPlanarDualEigen κ`.
* `movLam0EulerSubBound`: the target.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DirectEulerSub

/-- **Conditional assembly of `MovLam0EulerSubBound`** (SP 2866-2889, 2905-2918, 2991-2995):
train comparison (`EulerSubTrain.memLp_and_xNorm_movEulerAdj_trainDiff`) plus the
Gaussian-cylinder residual (`EulerSubCore.gaussSub_bound`) under the planar seed duality,
with `1/d(r)² = ν³/θ(r)` (`ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta`). -/
theorem movLam0EulerSubBound_of_planarDual (κ : PlanarFrameKernels)
    (hdual : SeedPlanarDualEigen κ) : MovLam0EulerSubBound κ := by
  intro hκ lam h hh ℓ hIS he0 he1 hpair m hm
  obtain ⟨C_tr, ν_tr, hCtr, hνtr, htr⟩ :=
    EulerSubTrain.memLp_and_xNorm_movEulerAdj_trainDiff κ (seedLamGradPerSum κ) hκ hm
  obtain ⟨C_G, hCG, hG⟩ :=
    EulerSubCore.gaussSub_bound hκ (hdual hκ lam h hh ℓ hIS he0 he1 hpair) (m := m)
      (by linarith)
  refine ⟨C_tr + C_G, 1, by positivity, le_rfl, fun b hb => ?_⟩
  refine ⟨min ν_tr (1 / 4), lt_min hνtr (by norm_num), fun ν hν tr hbuc r hr hbr k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_tr : ν ∈ Ioc 0 ν_tr := ⟨hν_pos, hν.2.trans (min_le_left _ _)⟩
  have hν4 : ν ≤ 1 / ((1 : ℝ) + 1) ^ 2 := by
    have := hν.2.trans (min_le_right _ _)
    norm_num at this ⊢
    linarith
  have hθ : 1 ≤ clockTheta ν r := hb.trans hbr
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  have hd1 : (1 : ℝ) ≤ d := cellLen_ge zero_le_one hν_pos hν4 hb hr hbr
  have h1 := htr ν hν_tr tr hbuc r hr hθ k
  have h2_raw := hG d hd1 k
  have h2_norm : xNorm d (-m) (EulerSubTrain.movLam0EulerGaussSub κ lam d k) ≤
      ENNReal.ofReal (C_G * ν ^ 3 / clockTheta ν r) := by
    refine h2_raw.2.trans (le_of_eq ?_)
    congr 1
    have hd2_inv : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
      ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta hν_pos hr
    calc C_G / d ^ 2 = C_G * (1 / d ^ 2) := by ring
      _ = C_G * (ν ^ 3 / clockTheta ν r) := by rw [hd2_inv]
      _ = C_G * ν ^ 3 / clockTheta ν r := by ring
  have hdecomp : UnforcedLeray.Short.IIIa.movLam0DualEulerSub κ lam tr r k =
      fun y =>
        (ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
            (perLam0 κ d k) y -
          EulerSubTrain.movEulerAdjGauss d (perLam0 κ d k) y) +
        EulerSubTrain.movLam0EulerGaussSub κ lam d k y :=
    funext fun y =>
      EulerSubTrain.movLam0DualEulerSub_eq_trainDiff_add_gauss κ lam tr hν_pos hr k y
  rw [hdecomp]
  obtain ⟨hm12, hx12⟩ := ComplCouplingHeat.memLp_and_xNorm_add_le (by positivity)
    (by positivity) h1.1 h2_raw.1 h1.2 h2_norm
  refine ⟨hm12, hx12.trans (le_of_eq ?_)⟩
  congr 1
  ring

end DirectEulerSub

/-- **`MovLam0EulerSubBound κ`** (`PartIII-a:T21/c5/2/2/2`, SP 2866-2889, 2905-2918,
2991-2995). -/
theorem movLam0EulerSubBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLam0EulerSubBound κ :=
  DirectEulerSub.movLam0EulerSubBound_of_planarDual κ (PlanarDualSub.seedPlanarDualEigen κ)

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.movLam0EulerSubBound
