import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Units.B0005.Consistency
import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Lib.Axisymmetric.Measure
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc

/-!
# Part II-b, task `PartII-b:R1` leaf: the smooth residual weak form (integration by parts)

Target: `UnforcedLeray.Short.IIb.SmoothResidualWeakForm` (`Sub/R1.lean`, the Prop
`SmoothResidualWeakForm`; source of record `the November 2 reference manuscript`,
SP 2042-2046, `paper/main.tex` line 5200).

Statement: for `U` smooth, `P`-periodic, divergence free, `Pw` smooth, `U' = U` and
`Fc = L₀U + (U·∇)U + ∇Pw` off the axis, and every solenoidal phase test `Φ`,
`⟪L₀ᵗΦ, U'⟫ - ⟪(U'·∇)Φ, U'⟫ = ⟪Φ, Fc⟫`.

Proof, integrating over the slab `(0,P] × ℝ³` (`srwfSlab P`):
* `lagrange_L0` (B0411): `L₀ᵗΦ·U - Φ·L₀U = srwf_lagRHS`, a `τ`-derivative and `y`-derivatives;
  the `τ`-derivative integrates to zero (`B0005.integral_slab_dτ`), each `y`-derivative by
  `srwf_slab_dy` (smooth, bounded support in `y`, no periodicity needed).
* Advection identity `∑ₖ ∂ₖ(Uₖ Φ·U) = (U·∇)Φ·U + Φ·(U·∇)U` (`srwf_div_identity`, uses `div U = 0`).
* `Φ·∇Pw = ∑ⱼ ∂ⱼ(Φⱼ Pw)` (`srwf_grad_identity`, uses `div Φ = 0`).
The axis is a null set (`Axi.ae_not_mem_axis`), so the off-axis agreement of `U'`, `Fc` changes
no phase pairing (`srwf_phaseInt_congr`).

Status: this leaf only; no other unit is claimed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

/-! ## The slab and the phase-integral bridge -/

/-- The phase slab `(0,P] × ℝ³` over which the phase pairings are integrated. -/
abbrev srwfSlab (P : ℝ) : Measure (ℝ × Space) :=
  (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)

/-- `phaseInt` congruence: pointwise agreement off a null set of `y` for each `t`. -/
theorem srwf_phaseInt_congr {P : ℝ} {f g : ℝ × Space → ℂ}
    (h : ∀ t : ℝ, ∀ᵐ y : Space ∂(volume : Measure Space), f (t, y) = g (t, y)) :
    phaseInt P f = phaseInt P g := by
  unfold phaseInt
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => integral_congr_ae (h t))

/-- For an integrable integrand on the slab, the phase pairing is the slab integral. -/
theorem srwf_phaseInt_eq {P : ℝ} {f : ℝ × Space → ℂ}
    (hf : Integrable f (srwfSlab P)) :
    phaseInt P f = P⁻¹ • ∫ z, f z ∂(srwfSlab P) := by
  unfold phaseInt
  rw [integral_prod f hf]

/-! ## Pointwise calculus -/

theorem srwf_coord_contDiff {U : ℝ × Space → CVec3} (hU : ContDiff ℝ ∞ U) (k : Fin 3) :
    ContDiff ℝ ∞ (fun w => U w k) :=
  ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hU

theorem srwf_dy_mul {f g : ℝ × Space → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) (z : ℝ × Space) :
    dy j (fun w => f w * g w) z = dy j f z * g z + f z * dy j g z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    (hf z).hasFDerivAt.mul (hg z).hasFDerivAt
  simp only [dy, h.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem srwf_dy_coord {U : ℝ × Space → CVec3} (hU : Differentiable ℝ U) (k j : Fin 3)
    (z : ℝ × Space) : dy j (fun w => U w k) z = dy j U z k := by
  let L : CVec3 →L[ℝ] ℂ := (EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ
  have h : HasFDerivAt (fun w => L (U w)) (L.comp (fderiv ℝ U z)) z :=
    L.hasFDerivAt.comp z (hU z).hasFDerivAt
  have e : (fun w => U w k) = fun w => L (U w) := rfl
  simp only [dy]
  rw [e, h.fderiv]
  rfl

/-- A smooth function vanishing for `‖y‖ > R` has `y`-derivatives vanishing there too. -/
theorem srwf_dy_bdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : ℝ × Space → F} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → K (τ, y) = 0) (j : Fin 3) :
    ∀ τ y, R < ‖y‖ → dy j K (τ, y) = 0 := by
  intro τ y hy
  have hopen : IsOpen {p : ℝ × Space | R < ‖p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : K =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds (show R < ‖((τ, y) : ℝ × Space).2‖ from hy)] with p hp
    exact hR p.1 p.2 hp
  simp [dy, hev.fderiv_eq]

/-- **Slab integral of a `y`-derivative.** For a smooth `K` vanishing for `‖y‖ > R`, the
`y_j`-derivative is integrable on `(0,P] × ℝ³` with zero integral. (Periodicity in `τ` is not
needed: the `y`-integral is taken slice by slice; this follows `B0005.integral_slab_dy`.) -/
theorem srwf_slab_dy {P : ℝ} {K : ℝ × Space → ℂ} (hK : ContDiff ℝ ∞ K) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → K (τ, y) = 0) (j : Fin 3) :
    Integrable (fun z => dy j K z) (srwfSlab P) ∧
      ∫ z, dy j K z ∂(srwfSlab P) = 0 := by
  have hcont : Continuous (fun z => dy j K z) := by
    simp only [dy]
    exact (hK.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable (fun z => dy j K z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hcont (srwf_dy_bdd hR j)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show ∫ y, dy j K (t, y) = 0
  have hd : Differentiable ℝ K := hK.differentiable (by simp)
  have hsl : ContDiff ℝ ∞ (fun y => K (t, y)) := hK.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y => K (t, y)) :=
    UnforcedLeray.B0005.hasCompactSupport_of_bound (R := R) fun y hy => hR t y hy
  have hpt : ∀ y, dy j K (t, y) = fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) := by
    intro y
    simp only [dy, UnforcedLeray.B0005.fderiv_slice_space (hd (t, y)),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  simp only [hpt]
  have hcd : HasCompactSupport fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    hc.fderiv_apply (𝕜 := ℝ) _
  have hcont' : Continuous fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    (hsl.continuous_fderiv (by simp)).clm_apply continuous_const
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℂ)) (g := fun x => K (t, x)) (v := coordinateVector j)
    (by simp) (by simpa using hcont'.integrable_of_hasCompactSupport hcd)
    (by simpa using hsl.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hsl.differentiable (by simp)) x)
  simpa using this

/-! ## Test-function calculus -/

set_option maxHeartbeats 1000000 in
theorem srwf_dotFn_contDiff {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (dotFn A B) := by
  have h := UnforcedLeray.B0005.dotR.isBoundedBilinearMap.contDiff.comp (hA.prodMk hB)
  exact h

theorem srwf_dotFn_isPhaseTest {P : ℝ} {Φ U : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hU : ContDiff ℝ ∞ U) (hper : ∀ x : ℝ × Space, U (x.1 + P, x.2) = U x) :
    IsPhaseTest P (dotFn Φ U) where
  smooth := srwf_dotFn_contDiff hΦ.smooth hU
  periodic τ y := by
    have h2 : U (τ + P, y) = U (τ, y) := hper (τ, y)
    show dotL (Φ (τ + P, y)) (U (τ + P, y)) = dotL (Φ (τ, y)) (U (τ, y))
    rw [hΦ.periodic τ y, h2]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [dotFn, hR τ y hy]⟩

theorem srwf_L0T_isPhaseTest {P ν : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (L0T ν Φ) :=
  (hΦ.driftT.sub (hΦ.lapT.const_smul ν)).sub (hΦ.const_smul (1 / 2 : ℝ))

/-- The advection identity: `∑ₖ ∂ₖ(Uₖ (Φ·U)) = (U·∇)Φ·U + Φ·(U·∇)U` for `div U = 0`. -/
theorem srwf_div_identity {Φ U : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (hU : ContDiff ℝ ∞ U) (hdiv : ∀ x : ℝ × Space, ∑ j : Fin 3, dy j U x j = 0)
    (z : ℝ × Space) :
    ∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ U w) z =
      dotL (advT U Φ z) (U z) + dotL (Φ z) (advT U U z) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hk : ∀ k : Fin 3, dy k (fun w => U w k * dotFn Φ U w) z =
      dy k U z k * dotFn Φ U z + U z k * (dotL (dy k Φ z) (U z) + dotL (Φ z) (dy k U z)) := by
    intro k
    rw [srwf_dy_mul ((srwf_coord_contDiff hU k).differentiable (by simp))
      (differentiable_dotFn hΦd hUd) k z, srwf_dy_coord hUd k k z, dy_dotFn hΦd hUd k z]
  simp only [hk]
  have hd := hdiv z
  simp only [Fin.sum_univ_three] at hd
  simp only [Fin.sum_univ_three, advT, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, dotL_apply, PiLp.add_apply, PiLp.smul_apply]
  linear_combination (dotFn Φ U z) * hd

/-- `Φ·∇Pw = ∑ⱼ ∂ⱼ(Φⱼ Pw)` for `div Φ = 0`. -/
theorem srwf_grad_identity {Φ : ℝ × Space → CVec3} {Pw : ℝ × Space → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hPw : ContDiff ℝ ∞ Pw)
    (hdiv : ∀ x : ℝ × Space, ∑ j : Fin 3, dy j Φ x j = 0) (z : ℝ × Space) :
    dotL (Φ z) (gradT Pw z) = ∑ j : Fin 3, dy j (fun w => Φ w j * Pw w) z := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hPwd : Differentiable ℝ Pw := hPw.differentiable (by simp)
  have hj : ∀ j : Fin 3, dy j (fun w => Φ w j * Pw w) z =
      dy j Φ z j * Pw z + Φ z j * dy j Pw z := by
    intro j
    rw [srwf_dy_mul ((srwf_coord_contDiff hΦ j).differentiable (by simp)) hPwd j z,
      srwf_dy_coord hΦd j j z]
  simp only [hj]
  have hd := hdiv z
  simp only [Fin.sum_univ_three] at hd
  simp [gradT, dotL_apply, Fin.sum_univ_three, EuclideanSpace.single_apply]
  linear_combination (-(Pw z)) * hd

/-- The right side of `lagrange_L0` (B0411) for the pair `(Φ, U)`, in the form of that lemma. -/
def srwf_lagRHS (ν : ℝ) (Φ U : ℝ × Space → CVec3) (p : ℝ × Space) : ℂ :=
  -dτ (dotFn Φ U) p + (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) p -
    (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) p

/-! ## The weak identity -/

/-- **`SmoothResidualWeakForm`**: integration by parts for the smooth residual. -/
theorem smoothResidualWeakForm_proof : UnforcedLeray.Short.IIb.SmoothResidualWeakForm := by
  intro P ν hP U Pw hU hPw hper hdiv U' Fc hagree Φ hΦ
  haveI : Fact (0 < P) := ⟨hP⟩
  unfold IsSolTest at hΦ
  obtain ⟨hΦs, hΦdiv⟩ := hΦ
  obtain ⟨R, hR⟩ := hΦs.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦs.smooth
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  -- the pairing `Φ·U` and its `τ`-derivative
  have hD : ContDiff ℝ ∞ (dotFn Φ U) := srwf_dotFn_contDiff hΦc hU
  have hH : IsPhaseTest P (dotFn Φ U) := srwf_dotFn_isPhaseTest hΦs hU hper
  obtain ⟨R₂, hR₂⟩ := hH.dτ.bounded_support
  have hτint : Integrable (fun z => dτ (dotFn Φ U) z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hH.dτ.continuous (R := R₂) hR₂
  have hτzero : ∫ z, dτ (dotFn Φ U) z ∂(srwfSlab P) = 0 :=
    UnforcedLeray.B0005.integral_slab_dτ hH
  -- the `y`-derivative terms of `lagrange_L0`
  have hY : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) ∧
        ∫ z, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) :=
      (Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd)).mul hD
    exact srwf_slab_dy (R := R) hK (fun τ y hy => by simp [dotFn, hR τ y hy]) j
  have hN : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z)
        (srwfSlab P) ∧
        ∫ z, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) :=
      (srwf_dotFn_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hΦc j) hU).sub
        (srwf_dotFn_contDiff hΦc (UnforcedLeray.PhaseSpace.contDiff_dy hU j))
    exact srwf_slab_dy (R := R) hK
      (fun τ y hy => by simp [dotFn, hR τ y hy, srwf_dy_bdd hR j τ y hy]) j
  -- the right side of the Lagrange identity is integrable with zero integral
  have hlag : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z) (U z) - dotL (Φ z) (L0 ν U z) = srwf_lagRHS ν Φ U z :=
    fun z => lagrange_L0 ν hΦc hU z
  have hRHSint : Integrable (srwf_lagRHS ν Φ U) (srwfSlab P) := by
    have i1 : Integrable (fun z => -dτ (dotFn Φ U) z) (srwfSlab P) := hτint.neg
    have i2 : Integrable (fun z => (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) :=
      (integrable_finset_sum _ fun j _ => (hY j).1).const_mul _
    have i3 : Integrable (fun z => (ν : ℂ) *
        ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z)
        (srwfSlab P) :=
      (integrable_finset_sum _ fun j _ => (hN j).1).const_mul _
    exact (i1.add i2).sub i3
  have hRHSzero : ∫ z, srwf_lagRHS ν Φ U z ∂(srwfSlab P) = 0 := by
    have i1 : Integrable (fun z => -dτ (dotFn Φ U) z) (srwfSlab P) := hτint.neg
    have i2 : Integrable (fun z => (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) :=
      (integrable_finset_sum _ fun j _ => (hY j).1).const_mul _
    have i3 : Integrable (fun z => (ν : ℂ) *
        ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z)
        (srwfSlab P) :=
      (integrable_finset_sum _ fun j _ => (hN j).1).const_mul _
    have i12 : Integrable (fun z => -dτ (dotFn Φ U) z + (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) :=
      i1.add i2
    have e : (fun z => srwf_lagRHS ν Φ U z) = fun z =>
        (-dτ (dotFn Φ U) z + (1 / 2 : ℂ) *
          ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z :=
      rfl
    rw [e, integral_sub i12 i3, integral_add i1 i2, integral_neg,
      integral_const_mul, integral_const_mul,
      integral_finset_sum _ fun j _ => (hY j).1,
      integral_finset_sum _ fun j _ => (hN j).1,
      Finset.sum_eq_zero fun j _ => (hY j).2, Finset.sum_eq_zero fun j _ => (hN j).2, hτzero]
    simp
  -- integrability of the four pairings
  have hAc : Continuous (fun z => dotL (L0T ν Φ z) (U z)) :=
    (dotL.continuous.comp (srwf_L0T_isPhaseTest (ν := ν) hΦs).continuous).clm_apply
      hU.continuous
  have hA_int : Integrable (fun z => dotL (L0T ν Φ z) (U z)) (srwfSlab P) := by
    obtain ⟨RL, hRL⟩ := (srwf_L0T_isPhaseTest (ν := ν) hΦs).bounded_support
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P) hAc (R := RL)
      (fun t y hy => by simp [hRL t y hy])
  have hAdvc : Continuous (advT U Φ) := by
    unfold advT
    exact continuous_finset_sum _ fun k _ =>
      (srwf_coord_contDiff hU k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hΦc k).continuous
  have hB_int : Integrable (fun z => dotL (advT U Φ z) (U z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hAdvc).clm_apply hU.continuous) (R := R)
      (fun t y hy => by
        have h0 : advT U Φ (t, y) = 0 := by
          unfold advT
          exact Finset.sum_eq_zero fun k _ => by rw [srwf_dy_bdd hR k t y hy, smul_zero]
        simp [h0])
  have hC_int : Integrable (fun z => dotL (Φ z) (L0 ν U z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (L0 ν U z)) =
        fun z => dotL (L0T ν Φ z) (U z) - srwf_lagRHS ν Φ U z := by
      funext z
      rw [← hlag z]
      ring
    rw [e]
    exact hA_int.sub hRHSint
  have hK'p : ∀ k : Fin 3,
      Integrable (fun z => dy k (fun w => U w k * dotFn Φ U w) z) (srwfSlab P) ∧
        ∫ z, dy k (fun w => U w k * dotFn Φ U w) z ∂(srwfSlab P) = 0 := by
    intro k
    exact srwf_slab_dy (R := R) ((srwf_coord_contDiff hU k).mul hD)
      (fun τ y hy => by simp [dotFn, hR τ y hy]) k
  have hDd_int : Integrable (fun z => dotL (Φ z) (advT U U z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (advT U U z)) =
        fun z => (∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ U w) z) -
          dotL (advT U Φ z) (U z) := by
      funext z
      rw [srwf_div_identity hΦc hU hdiv z]
      ring
    rw [e]
    exact (integrable_finset_sum _ fun k _ => (hK'p k).1).sub hB_int
  have hEj : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun w => Φ w j * Pw w) z) (srwfSlab P) ∧
        ∫ z, dy j (fun w => Φ w j * Pw w) z ∂(srwfSlab P) = 0 := fun j =>
    srwf_slab_dy (R := R) ((srwf_coord_contDiff hΦc j).mul hPw)
      (fun τ y hy => by simp [hR τ y hy]) j
  have hE_eq : ∀ z : ℝ × Space,
      dotL (Φ z) (gradT Pw z) = ∑ j : Fin 3, dy j (fun w => Φ w j * Pw w) z :=
    fun z => srwf_grad_identity hΦc hPw hΦdiv z
  have hE_int : Integrable (fun z => dotL (Φ z) (gradT Pw z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (gradT Pw z)) =
        fun z => ∑ j : Fin 3, dy j (fun w => Φ w j * Pw w) z := funext hE_eq
    rw [e]
    exact integrable_finset_sum _ fun j _ => (hEj j).1
  have hE0 : ∫ z, dotL (Φ z) (gradT Pw z) ∂(srwfSlab P) = 0 := by
    have e : (fun z => dotL (Φ z) (gradT Pw z)) =
        fun z => ∑ j : Fin 3, dy j (fun w => Φ w j * Pw w) z := funext hE_eq
    rw [e, integral_finset_sum _ fun j _ => (hEj j).1,
      Finset.sum_eq_zero fun j _ => (hEj j).2]
  -- the advection pairing: `∫ (B + Dd) = 0`
  have hBD : ∫ z, dotL (advT U Φ z) (U z) ∂(srwfSlab P) +
      ∫ z, dotL (Φ z) (advT U U z) ∂(srwfSlab P) = 0 := by
    rw [← integral_add hB_int hDd_int]
    have e : (fun z => dotL (advT U Φ z) (U z) + dotL (Φ z) (advT U U z)) =
        fun z => ∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ U w) z :=
      funext fun z => (srwf_div_identity hΦc hU hdiv z).symm
    rw [e, integral_finset_sum _ fun k _ => (hK'p k).1,
      Finset.sum_eq_zero fun k _ => (hK'p k).2]
  have hG_int : Integrable (fun z => dotL (Φ z) (L0 ν U z + advT U U z + gradT Pw z))
      (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (L0 ν U z + advT U U z + gradT Pw z)) =
        fun z => (dotL (Φ z) (L0 ν U z) + dotL (Φ z) (advT U U z)) + dotL (Φ z) (gradT Pw z) :=
      funext fun z => by simp [map_add]
    rw [e]
    exact (hC_int.add hDd_int).add hE_int
  have hG_eq : ∫ z, dotL (Φ z) (L0 ν U z + advT U U z + gradT Pw z) ∂(srwfSlab P) =
      ∫ z, dotL (Φ z) (L0 ν U z) ∂(srwfSlab P) +
        ∫ z, dotL (Φ z) (advT U U z) ∂(srwfSlab P) +
        ∫ z, dotL (Φ z) (gradT Pw z) ∂(srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (L0 ν U z + advT U U z + gradT Pw z)) =
        fun z => (dotL (Φ z) (L0 ν U z) + dotL (Φ z) (advT U U z)) + dotL (Φ z) (gradT Pw z) :=
      funext fun z => by simp [map_add]
    have hCD : Integrable (fun z => dotL (Φ z) (L0 ν U z) + dotL (Φ z) (advT U U z))
        (srwfSlab P) := hC_int.add hDd_int
    rw [e, integral_add hCD hE_int, integral_add hC_int hDd_int]
  -- the integral of the first pairing equals that of `Φ·L₀U`
  have hAC : ∫ z, dotL (L0T ν Φ z) (U z) ∂(srwfSlab P) =
      ∫ z, dotL (Φ z) (L0 ν U z) ∂(srwfSlab P) := by
    have e : (fun z => dotL (L0T ν Φ z) (U z)) =
        fun z => dotL (Φ z) (L0 ν U z) + srwf_lagRHS ν Φ U z :=
      funext fun z => by rw [← hlag z]; ring
    rw [e, integral_add hC_int hRHSint, hRHSzero, add_zero]
  have hB' : ∫ z, dotL (advT U Φ z) (U z) ∂(srwfSlab P) =
      -∫ z, dotL (Φ z) (advT U U z) ∂(srwfSlab P) := by
    linear_combination hBD
  -- off-axis agreement: the axis is a null set
  have e1 : pairF P (L0T ν Φ) U' = pairF P (L0T ν Φ) U := by
    unfold pairF
    apply srwf_phaseInt_congr
    intro t
    filter_upwards [UnforcedLeray.Axi.ae_not_mem_axis] with y hy
    simp only [(hagree (t, y) (UnforcedLeray.Axi.ϱ_ne_zero hy)).1]
  have e2 : pairF P (advT U' Φ) U' = pairF P (advT U Φ) U := by
    unfold pairF
    apply srwf_phaseInt_congr
    intro t
    filter_upwards [UnforcedLeray.Axi.ae_not_mem_axis] with y hy
    have h1 := (hagree (t, y) (UnforcedLeray.Axi.ϱ_ne_zero hy)).1
    simp only [h1, advT]
  have e3 : pairF P Φ Fc = pairF P Φ (fun x => L0 ν U x + advT U U x + gradT Pw x) := by
    unfold pairF
    apply srwf_phaseInt_congr
    intro t
    filter_upwards [UnforcedLeray.Axi.ae_not_mem_axis] with y hy
    simp only [(hagree (t, y) (UnforcedLeray.Axi.ϱ_ne_zero hy)).2]
  rw [e1, e2, e3]
  unfold pairF
  rw [srwf_phaseInt_eq hA_int, srwf_phaseInt_eq hB_int, srwf_phaseInt_eq hG_int, hAC, hG_eq,
    hE0, add_zero, hB', smul_neg, sub_neg_eq_add, smul_add]

end UnforcedLeray.Short.IIb
