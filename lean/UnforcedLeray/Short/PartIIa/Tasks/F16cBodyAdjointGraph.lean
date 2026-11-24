import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Short.PartIIa.Tasks.F16cBodyAdjointGraph.Glue
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint
import UnforcedLeray.Short.PartIIa.Sub.F06
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness
import UnforcedLeray.Short.PartIIa.Tasks.F08cLerayYResolventComm
import UnforcedLeray.Units.B0414
import UnforcedLeray.Units.B0428.Slice
import UnforcedLeray.Lib.SobolevC.FourierBridge

/-!
# Part II-a, task `PartII-a:F16/c`: the adjoint diffusion graph bound `‖A R_μ^* v‖_{Y_2} ≤ M ‖v‖_{Y_2}`

Source `shorter-proof-2026-11-02.tex` lines 1556-1557, 1595-1598, 1359-1361, 1426-1442.
Proves the two leaves `AdjointSolvesPhaseEq` and `NuLapFibrewise` of
`Tasks/F16cBodyAdjointGraph/Glue.lean` and combines them with `commonBodyAdjoint` (`F09Adjoint`)
via `bodyAdjointGraph_of` to obtain `bodyAdjointGraph : BodyAdjointGraph`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology SchwartzMap TemperedDistribution LineDeriv
open scoped ENNReal NNReal Laplacian ContDiff SchwartzMap

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp UnforcedLeray.FreeStress

/-! ### Leaf A: `R_μ^* v` solves the adjoint equation with Leray-projected data -/

/-- `R_μ` on `Y_2` equals `𝐏 ∘ Rm` where `Rm` is the Laplace transform of the phase semigroup. -/
private theorem bodyInverse_eq_lerayY_comp_laplace (P : ℝ) [Fact (0 < P)] (ν : ℝ) (hν : 0 < ν)
    (μ : ℂ) (hμ : 0 < μ.re + 1 / 4) (R : Yq P 2 →L[ℂ] Yq P 2) (hR : IsBodyInverse P ν μ R) :
    let S : UnforcedLeray.Infra.ExpSemigroup (Yq P 2) :=
      UnforcedLeray.B0421.phaseSemigroup (P := P) (q := 2) ENNReal.ofNat_ne_top hν.le 1 zero_le_one
        (fun r _ => by rw [one_mul]; exact UnforcedLeray.B0421.norm_freeC_two_le ν r)
    ∀ x : Yq P 2,
      R x = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (S.laplace μ x) := by
  intro S x
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  have hωval : S.ω = -(1 / 4 : ℝ) := by
    show -UnforcedLeray.B0418.gammaExp 2 = -(1 / 4 : ℝ)
    rw [UnforcedLeray.B0419.gammaExp_two]
  have hω : S.ω < μ.re := by rw [hωval]; linarith
  set Rm := S.laplace μ
  have hRm : ∀ f : Yq P 2, Rm f = ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-(μ * t)) • B0421.phaseT ENNReal.ofNat_ne_top ν t f :=
    fun f => S.laplace_apply hω f
  obtain ⟨w, hwR, hbw⟩ := hR x
  have hwL : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P 2)
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x) := by
    have h := hasPhaseOp_body_of_D (μ := μ) w
    rwa [hbw] at h
  have hz := bodyResolvent_solves 2 h1 h3 P ν hν μ hμ' Rm hRm
    (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x)
  have hx : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ)
      ((w : Yq P 2) - Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x)) (0 : Yq P 2) := by
    have h2 := hwL.add (hz.smul (-1))
    have e1 : (w : Yq P 2) + (-1 : ℂ) • Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x) =
        (w : Yq P 2) - Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x) := by
      simp [sub_eq_add_neg]
    have e2 : lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x +
        (-1 : ℂ) • lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x = (0 : Yq P 2) := by
      simp
    rw [e1, e2] at h2
    exact h2
  have hzero := bodyOp_uniqueness 2 h1 h3 P ν hν μ hμ' _ hx
  have hwz : (w : Yq P 2) = Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x) :=
    sub_eq_zero.mp hzero
  have hcomm := lerayYResolventComm_proof 2 h1 h3 P ν hν μ hμ' Rm hRm x
  rw [← hwR, hwz, ← hcomm]

/-- **Leaf A**: for `R` a body inverse on `Y_2`, `R^* v` solves `(μ̄ + L^*) (R^* v) = 𝐏 v`. -/
theorem adjointSolvesPhaseEq : AdjointSolvesPhaseEq := by
  intro P _ ν hν μ hμ R hR v
  let S : UnforcedLeray.Infra.ExpSemigroup (Yq P 2) :=
    UnforcedLeray.B0421.phaseSemigroup (P := P) (q := 2) ENNReal.ofNat_ne_top hν.le 1 zero_le_one
      (fun r _ => by rw [one_mul]; exact UnforcedLeray.B0421.norm_freeC_two_le ν r)
  have hωval : S.ω = -(1 / 4 : ℝ) := by
    show -UnforcedLeray.B0418.gammaExp 2 = -(1 / 4 : ℝ)
    rw [UnforcedLeray.B0419.gammaExp_two]
  have hω : S.ω < μ.re := by rw [hωval]; linarith
  have hω' : S.adjoint.ω < (starRingEnd ℂ μ).re := by
    rw [S.adjoint_ω, Complex.conj_re]; exact hω
  have hR_eq : ∀ x : Yq P 2,
      R x = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (S.laplace μ x) :=
    bodyInverse_eq_lerayY_comp_laplace P ν hν μ hμ R hR
  have hadj_eq : (ContinuousLinearMap.adjoint R) v =
      S.adjoint.laplace (starRingEnd ℂ μ)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v) := by
    rw [← S.adjoint_laplace hω]
    refine ext_inner_left ℂ fun x => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, hR_eq x,
      UnforcedLeray.B0414.inner_lerayY_two_left_eq_right,
      ContinuousLinearMap.adjoint_inner_right]
  rw [hadj_eq]
  exact adjResolventEquation P ν hν μ hμ (S.adjoint.laplace (starRingEnd ℂ μ))
    (fun f => S.adjoint.laplace_apply hω' f)
    (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v)

/-! ### Leaf B: `HasPhaseOp (nuLapT ν) u a` implies `νΔ (u τ) = a τ` in `𝓢'` for a.e. `τ` -/

/-- Decay bound for derivatives of a real Schwartz function against `(1 + ‖y‖) ^ (-m)`. -/
private theorem norm_iteratedFDeriv_schwartz_le_weight (ψ : 𝓢(Space, ℝ)) (m n : ℕ) (hn : n ≤ 2) :
    let S : ℝ := 2 ^ m * (Finset.Iic (m, 2)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ψ
    ∀ y : Space, ‖iteratedFDeriv ℝ n ψ y‖ ≤ S * (1 + ‖y‖) ^ (-(m : ℝ)) := by
  intro S y
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hpow : 0 < (1 + ‖y‖) ^ m := pow_pos hpos m
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 2)) le_rfl hn ψ y
  have h2 : ‖iteratedFDeriv ℝ n ψ y‖ ≤ S * ((1 + ‖y‖) ^ m)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀' hpow]
    exact h1
  rwa [← Real.rpow_natCast (1 + ‖y‖) m, ← Real.rpow_neg hpos.le] at h2

/-- A spatial weak-Laplacian pair in `L²(ℝ³; ℂ³)` satisfies the identity against any real
Schwartz test. -/
private theorem isWeakLaplacian_schwartz_real
    {U Λ : Lp CVec3 2 (volume : Measure Space)}
    (hWL : UnforcedLeray.Heat.IsWeakLaplacian (U : Space → CVec3) (Λ : Space → CVec3))
    (ψ : 𝓢(Space, ℝ)) :
    ∫ x, UnforcedLeray.Heat.laplacian ψ x • (U : Space → CVec3) x =
      ∫ x, ψ x • (Λ : Space → CVec3) x := by
  obtain ⟨hwm, mw, hmw⟩ := UnforcedLeray.B0428.heatAdmissible U
  obtain ⟨hLm, mL, hmL⟩ := UnforcedLeray.B0428.heatAdmissible Λ
  set m : ℕ := max mw mL
  have hw' := UnforcedLeray.Heat.integrable_weight_mono hwm (le_max_left mw mL) hmw
  have hL' := UnforcedLeray.Heat.integrable_weight_mono hLm (le_max_right mw mL) hmL
  set S : ℝ := 2 ^ m * (Finset.Iic (m, 2)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ψ
  have hS0 : 0 ≤ S := by
    refine mul_nonneg (by positivity) ?_
    exact apply_nonneg _ _
  have hw_pos : ∀ y : Space, 0 ≤ (1 + ‖y‖) ^ (-(m : ℝ)) := fun y => by positivity
  have hb0 : ∀ y : Space, |ψ y| ≤ (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) := by
    intro y
    have h0 := norm_iteratedFDeriv_schwartz_le_weight ψ m 0 (by omega) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    calc |ψ y| ≤ S * (1 + ‖y‖) ^ (-(m : ℝ)) := h0
      _ ≤ (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (hw_pos y)
  have hb1 : ∀ (j : Fin 3) (y : Space), |sd j ψ y| ≤ (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) := by
    intro j y
    have h1 := norm_iteratedFDeriv_schwartz_le_weight ψ m 1 (by omega) y
    calc |sd j ψ y| ≤ ‖iteratedFDeriv ℝ 1 ψ y‖ := UnforcedLeray.Heat.abs_sd_le ψ j y
      _ ≤ S * (1 + ‖y‖) ^ (-(m : ℝ)) := h1
      _ ≤ (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (hw_pos y)
  have hb2 : ∀ y : Space,
      |UnforcedLeray.Heat.laplacian ψ y| ≤ (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) := by
    intro y
    have h2 := norm_iteratedFDeriv_schwartz_le_weight ψ m 2 le_rfl y
    calc |UnforcedLeray.Heat.laplacian ψ y|
        ≤ 3 * ‖iteratedFDeriv ℝ 2 ψ y‖ := UnforcedLeray.Heat.abs_laplacian_le (ψ.smooth 2) y
      _ ≤ 3 * (S * (1 + ‖y‖) ^ (-(m : ℝ))) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (3 * S) * (1 + ‖y‖) ^ (-(m : ℝ)) := by ring
  exact hWL.extend hwm hLm hw' hL' (ψ.smooth ⊤) hb0 hb1 hb2

/-- Real-linear postcomposition of a complex Schwartz test commutes with `sd j`. -/
private theorem sd_postcompCLM (L : ℂ →L[ℝ] ℝ) (h : 𝓢(Space, ℂ)) (j : Fin 3) :
    sd j (h.postcompCLM L) = (∂_{coordinateVector j} h).postcompCLM L := by
  funext x
  have hd : HasFDerivAt (fun y => L (h y)) (L.comp (fderiv ℝ h x)) x :=
    L.hasFDerivAt.comp x h.differentiableAt.hasFDerivAt
  change fderiv ℝ (fun y => L (h y)) x (coordinateVector j) =
    L ((∂_{coordinateVector j} h) x)
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- `Heat.laplacian` of a real-linear postcomposition of `g : 𝓢(Space, ℂ)` is `L (Δ g x)`. -/
private theorem heat_laplacian_postcompCLM (L : ℂ →L[ℝ] ℝ) (g : 𝓢(Space, ℂ)) (x : Space) :
    UnforcedLeray.Heat.laplacian (g.postcompCLM L) x = L ((Δ g) x) := by
  rw [UnforcedLeray.Heat.laplacian_eq_sum_sd]
  have h1 : ∀ j : Fin 3, sd j (sd j (g.postcompCLM L)) x =
      L ((∂_{coordinateVector j} (∂_{coordinateVector j} g)) x) := by
    intro j
    rw [sd_postcompCLM L g j, sd_postcompCLM L (∂_{coordinateVector j} g) j]
    rfl
  simp_rw [h1, ← map_sum]
  congr 1
  have hb := SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ) g
  have hbv : ∀ j : Fin 3, (EuclideanSpace.basisFun (Fin 3) ℝ) j = coordinateVector j := by
    intro j
    simp [EuclideanSpace.basisFun_apply, coordinateVector]
  simp_rw [hbv] at hb
  exact (congrFun (congrArg DFunLike.coe hb) x).symm

/-- Integral decomposition into real and imaginary parts for a complex Schwartz test and an `L²`
vector field. -/
private theorem integral_schwartz_smul_decomp (f : 𝓢(Space, ℂ))
    (W : Lp CVec3 2 (volume : Measure Space)) :
    ∫ x, f x • (W : Space → CVec3) x =
      (∫ x, (f.postcompCLM Complex.reCLM) x • (W : Space → CVec3) x) +
        Complex.I • ∫ x, (f.postcompCLM Complex.imCLM) x • (W : Space → CVec3) x := by
  have hW : MemLp (W : Space → CVec3) 2 volume := Lp.memLp W
  have hIW : MemLp (fun x => Complex.I • (W : Space → CVec3) x) 2 volume :=
    hW.const_smul Complex.I
  have hr : MemLp (f.postcompCLM Complex.reCLM : Space → ℝ) 2 volume :=
    (f.postcompCLM Complex.reCLM).memLp 2 volume
  have hi : MemLp (f.postcompCLM Complex.imCLM : Space → ℝ) 2 volume :=
    (f.postcompCLM Complex.imCLM).memLp 2 volume
  have ir : Integrable (fun x => (f.postcompCLM Complex.reCLM) x • (W : Space → CVec3) x) volume :=
    UnforcedLeray.Sob.integrable_smul_of_memLp_two hr hW
  have ii : Integrable
      (fun x => (f.postcompCLM Complex.imCLM) x • (Complex.I • (W : Space → CVec3) x)) volume :=
    UnforcedLeray.Sob.integrable_smul_of_memLp_two hi hIW
  have hpt : ∀ x, f x • (W : Space → CVec3) x =
      (f.postcompCLM Complex.reCLM) x • (W : Space → CVec3) x +
        (f.postcompCLM Complex.imCLM) x • (Complex.I • (W : Space → CVec3) x) :=
    fun x => UnforcedLeray.Sob.complex_smul_eq (f x) ((W : Space → CVec3) x)
  simp_rw [hpt]
  rw [integral_add ir ii]
  congr 1
  have hcomm : ∀ x, (f.postcompCLM Complex.imCLM) x • (Complex.I • (W : Space → CVec3) x) =
      Complex.I • ((f.postcompCLM Complex.imCLM) x • (W : Space → CVec3) x) :=
    fun x => smul_comm _ _ _
  simp_rw [hcomm]
  exact integral_smul Complex.I _

/-- A spatial weak-Laplacian pair in `L²(ℝ³; ℂ³)` satisfies `Δ U = Λ` in `𝓢'(ℝ³; ℂ³)`. -/
private theorem laplacian_toTemperedDistribution_of_isWeakLaplacian
    {U Λ : Lp CVec3 2 (volume : Measure Space)}
    (hWL : UnforcedLeray.Heat.IsWeakLaplacian (U : Space → CVec3) (Λ : Space → CVec3)) :
    Δ (U : 𝓢'(Space, CVec3)) = (Λ : 𝓢'(Space, CVec3)) := by
  ext g
  rw [TemperedDistribution.laplacian_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply, integral_schwartz_smul_decomp (Δ g) U,
    integral_schwartz_smul_decomp g Λ]
  have hr : ∀ x, ((Δ g).postcompCLM Complex.reCLM) x =
      UnforcedLeray.Heat.laplacian (g.postcompCLM Complex.reCLM) x :=
    fun x => (heat_laplacian_postcompCLM Complex.reCLM g x).symm
  have hi : ∀ x, ((Δ g).postcompCLM Complex.imCLM) x =
      UnforcedLeray.Heat.laplacian (g.postcompCLM Complex.imCLM) x :=
    fun x => (heat_laplacian_postcompCLM Complex.imCLM g x).symm
  simp_rw [hr, hi]
  rw [isWeakLaplacian_schwartz_real hWL (g.postcompCLM Complex.reCLM),
    isWeakLaplacian_schwartz_real hWL (g.postcompCLM Complex.imCLM)]

/-- **Leaf B**: if `HasPhaseOp (nuLapT ν) u a` on `Y_2`, then for a.e. phase `τ`,
`ν Δ (u τ) = a τ` in `𝓢'(ℝ³; ℂ³)`. -/
theorem nuLapFibrewise : NuLapFibrewise := by
  intro P _ ν u a h
  have hLap : HasPhaseOp lapT ((ν : ℂ) • u) a := by
    intro Φ hΦ
    rw [phasePair, map_smul, smul_eq_mul, ← phasePair, ← phasePair_real_smul hΦ.lapT]
    exact h Φ hΦ
  filter_upwards [UnforcedLeray.B0428.ae_isWeakLaplacian ENNReal.one_lt_two hLap,
    Lp.coeFn_smul (ν : ℂ) u] with τ hτ hsmul
  have hD := laplacian_toTemperedDistribution_of_isWeakLaplacian hτ
  rw [hsmul, Pi.smul_apply] at hD
  have hlin : ((((ν : ℂ) • u τ : Lp CVec3 2 (volume : Measure Space))) : 𝓢'(Space, CVec3)) =
      (ν : ℂ) • ((u τ : Lp CVec3 2 (volume : Measure Space)) : 𝓢'(Space, CVec3)) :=
    map_smul (Lp.toTemperedDistributionCLM CVec3 (volume : Measure Space) 2) (ν : ℂ) (u τ)
  have hlap_smul : ∀ (c : ℂ) (T : 𝓢'(Space, CVec3)), Δ (c • T) = c • Δ T := fun _ _ => by
    ext g i
    simp only [TemperedDistribution.laplacian_apply_apply, smul_apply]
  rw [hlin, hlap_smul] at hD
  exact hD

/-! ### Main theorem (`PartII-a:F16/c`) -/

/-- **`PartII-a:F16/c`**: the adjoint diffusion graph bound `‖A R_μ^* v‖_{Y_2} ≤ M ‖v‖_{Y_2}`,
in the fibrewise distributional form consumed by `free_stress_28_Y2'`. -/
theorem bodyAdjointGraph : BodyAdjointGraph :=
  bodyAdjointGraph_of commonBodyAdjoint adjointSolvesPhaseEq nuLapFibrewise

end UnforcedLeray.Short.PartIIa
