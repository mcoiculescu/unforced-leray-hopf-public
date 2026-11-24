import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# Part II-b, task `PartII-b:G4/3/1/3` (`AbsPhaseIBP`)

Source of record: `the November 2 reference manuscript`, lines 2370-2382.

Proof.  (1) *Core* (`absIBP_core`): for a globally smooth `V` and a smooth periodic `E` with
`div V = 0` wherever `E ≠ 0`, the identity is the proof of `smoothResidualWeakForm_proof` with the
Lagrange identity for `L₀` (`E` in the role of the field) and the divergence identity
`∑ₖ ∂ₖ(Vₖ Φ·E) = (V·∇Φ)·E + Φ·(V·∇E) + (div V) Φ·E`; the term `(∇V)ᵀΦ·E = Φ·(E·∇)V` is pointwise.
(2) *Cutoff*: replace `V` by `χ(ϱ) V`, `χ = 1` on `ϱ ≥ δ/2`, `χ = 0` on `ϱ ≤ δ/4`: it is globally
smooth, `div(χV) = 0` on `ϱ ≥ δ ` (where `E` lives), and every term of both sides of the identity
sees `V` only through `V` and its first derivatives at points with `E ≠ 0` or with `ϱ ≥ δ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412
  UnforcedLeray.Cons.C03.Concrete

/-- Real vectors in `ℂ³`, as a real-linear map. -/
def absRealCL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => realC x
      map_add' := fun x y => by ext i; simp [realC_apply]
      map_smul' := fun c x => by ext i; simp [realC_apply, Complex.real_smul] }

theorem absRealCL_apply (x : Space) : absRealCL x = realC x := rfl

theorem contDiff_realC_abs : ContDiff ℝ ∞ (fun x : Space => realC x) := absRealCL.contDiff

/-- The `y`-derivative of the complexified real field. -/
theorem dy_realC_comp {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (k i : Fin 3) (x : ℝ × Space) :
    dy k (fun w : ℝ × Space => realC (V w.1 w.2)) x i =
      ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (fun w : ℝ × Space => V w.1 w.2) x :=
    (hV.differentiable (by simp)) x
  have h : HasFDerivAt (fun w : ℝ × Space => absRealCL (V w.1 w.2))
      (absRealCL.comp (fderiv ℝ (fun w : ℝ × Space => V w.1 w.2) x)) x :=
    absRealCL.hasFDerivAt.comp x hd.hasFDerivAt
  have e : (fun w : ℝ × Space => realC (V w.1 w.2)) =
      fun w : ℝ × Space => absRealCL (V w.1 w.2) := rfl
  have hs : fderiv ℝ (V x.1) x.2 =
      (fderiv ℝ (fun w : ℝ × Space => V w.1 w.2) x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space hd
  simp only [dy]
  rw [e, h.fderiv, hs]
  simp [absRealCL_apply, realC_apply, coordinateVector]

theorem contDiff_realC_field {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) :
    ContDiff ℝ ∞ (fun w : ℝ × Space => realC (V w.1 w.2)) :=
  contDiff_realC_abs.comp hV

/-- The divergence identity with three different fields:
`∑ₖ ∂ₖ(Vₖ Φ·E) = (V·∇Φ)·E + Φ·(V·∇E) + (div V) Φ·E`. -/
theorem abs_div_identity {Φ E Vc : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (hE : ContDiff ℝ ∞ E) (hV : ContDiff ℝ ∞ Vc) (z : ℝ × Space) :
    ∑ k : Fin 3, dy k (fun w => Vc w k * dotFn Φ E w) z =
      dotL (advT Vc Φ z) (E z) + dotL (Φ z) (advT Vc E z) +
        (∑ j : Fin 3, dy j Vc z j) * dotFn Φ E z := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hEd : Differentiable ℝ E := hE.differentiable (by simp)
  have hk : ∀ k : Fin 3, dy k (fun w => Vc w k * dotFn Φ E w) z =
      dy k Vc z k * dotFn Φ E z + Vc z k * (dotL (dy k Φ z) (E z) + dotL (Φ z) (dy k E z)) := by
    intro k
    rw [srwf_dy_mul ((srwf_coord_contDiff hV k).differentiable (by simp))
      (differentiable_dotFn hΦd hEd) k z, srwf_dy_coord (hV.differentiable (by simp)) k k z,
      dy_dotFn hΦd hEd k z]
  simp only [hk]
  simp only [Fin.sum_univ_three, advT, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, dotL_apply, PiLp.add_apply, PiLp.smul_apply,
    dotFn]
  ring

/-- The `L₀` part: `∫ L₀ᵗΦ·E = ∫ Φ·L₀E` on the slab, both integrable. -/
theorem abs_L0_slab {P ν : ℝ} (hP : 0 < P) {Φ E : ℝ × Space → CVec3} (hΦs : IsPhaseTest P Φ)
    (hU : ContDiff ℝ ∞ E) (hper : ∀ x : ℝ × Space, E (x.1 + P, x.2) = E x) :
    Integrable (fun z => dotL (L0T ν Φ z) (E z)) (srwfSlab P) ∧
      Integrable (fun z => dotL (Φ z) (L0 ν E z)) (srwfSlab P) ∧
      ∫ z, dotL (L0T ν Φ z) (E z) ∂(srwfSlab P) = ∫ z, dotL (Φ z) (L0 ν E z) ∂(srwfSlab P) := by
  haveI : Fact (0 < P) := ⟨hP⟩
  obtain ⟨R, hR⟩ := hΦs.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦs.smooth
  have hD : ContDiff ℝ ∞ (dotFn Φ E) := srwf_dotFn_contDiff hΦc hU
  have hH : IsPhaseTest P (dotFn Φ E) := srwf_dotFn_isPhaseTest hΦs hU hper
  obtain ⟨R₂, hR₂⟩ := hH.dτ.bounded_support
  have hτint : Integrable (fun z => dτ (dotFn Φ E) z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hH.dτ.continuous (R := R₂) hR₂
  have hτzero : ∫ z, dτ (dotFn Φ E) z ∂(srwfSlab P) = 0 :=
    UnforcedLeray.B0005.integral_slab_dτ hH
  have hY : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) z) (srwfSlab P) ∧
        ∫ z, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) :=
      (Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd)).mul hD
    exact srwf_slab_dy (R := R) hK (fun τ y hy => by simp [dotFn, hR τ y hy]) j
  have hN : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => dotFn (dy j Φ) E p - dotFn Φ (dy j E) p) z)
        (srwfSlab P) ∧
        ∫ z, dy j (fun p => dotFn (dy j Φ) E p - dotFn Φ (dy j E) p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => dotFn (dy j Φ) E p - dotFn Φ (dy j E) p) :=
      (srwf_dotFn_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hΦc j) hU).sub
        (srwf_dotFn_contDiff hΦc (UnforcedLeray.PhaseSpace.contDiff_dy hU j))
    exact srwf_slab_dy (R := R) hK
      (fun τ y hy => by simp [dotFn, hR τ y hy, srwf_dy_bdd hR j τ y hy]) j
  have hlag : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z) (E z) - dotL (Φ z) (L0 ν E z) = srwf_lagRHS ν Φ E z :=
    fun z => lagrange_L0 ν hΦc hU z
  have i1 : Integrable (fun z => -dτ (dotFn Φ E) z) (srwfSlab P) := hτint.neg
  have i2 : Integrable (fun z => (1 / 2 : ℂ) *
      ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) z) (srwfSlab P) :=
    (integrable_finset_sum _ fun j _ => (hY j).1).const_mul _
  have i3 : Integrable (fun z => (ν : ℂ) *
      ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) E p - dotFn Φ (dy j E) p) z)
      (srwfSlab P) :=
    (integrable_finset_sum _ fun j _ => (hN j).1).const_mul _
  have hRHSint : Integrable (srwf_lagRHS ν Φ E) (srwfSlab P) := (i1.add i2).sub i3
  have hRHSzero : ∫ z, srwf_lagRHS ν Φ E z ∂(srwfSlab P) = 0 := by
    have i12 : Integrable (fun z => -dτ (dotFn Φ E) z + (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) z) (srwfSlab P) :=
      i1.add i2
    have e : (fun z => srwf_lagRHS ν Φ E z) = fun z =>
        (-dτ (dotFn Φ E) z + (1 / 2 : ℂ) *
          ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ E p) z) -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) E p - dotFn Φ (dy j E) p) z :=
      rfl
    rw [e, integral_sub i12 i3, integral_add i1 i2, integral_neg,
      integral_const_mul, integral_const_mul,
      integral_finset_sum _ fun j _ => (hY j).1,
      integral_finset_sum _ fun j _ => (hN j).1,
      Finset.sum_eq_zero fun j _ => (hY j).2, Finset.sum_eq_zero fun j _ => (hN j).2, hτzero]
    simp
  have hAc : Continuous (fun z => dotL (L0T ν Φ z) (E z)) :=
    (dotL.continuous.comp (srwf_L0T_isPhaseTest (ν := ν) hΦs).continuous).clm_apply
      hU.continuous
  have hA_int : Integrable (fun z => dotL (L0T ν Φ z) (E z)) (srwfSlab P) := by
    obtain ⟨RL, hRL⟩ := (srwf_L0T_isPhaseTest (ν := ν) hΦs).bounded_support
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P) hAc (R := RL)
      (fun t y hy => by simp [hRL t y hy])
  have hC_int : Integrable (fun z => dotL (Φ z) (L0 ν E z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (L0 ν E z)) =
        fun z => dotL (L0T ν Φ z) (E z) - srwf_lagRHS ν Φ E z := by
      funext z
      rw [← hlag z]
      ring
    rw [e]
    exact hA_int.sub hRHSint
  refine ⟨hA_int, hC_int, ?_⟩
  have e : (fun z => dotL (L0T ν Φ z) (E z)) =
      fun z => dotL (Φ z) (L0 ν E z) + srwf_lagRHS ν Φ E z :=
    funext fun z => by rw [← hlag z]; ring
  rw [e, integral_add hC_int hRHSint, hRHSzero, add_zero]

/-- The convective part: with `div V = 0` where `E ≠ 0`,
`∫ (V·∇Φ)·E = -∫ Φ·(V·∇E)`, both integrable. -/
theorem abs_adv_slab {P : ℝ} {Φ E Vc : ℝ × Space → CVec3} (hΦs : IsPhaseTest P Φ)
    (hE : ContDiff ℝ ∞ E) (hV : ContDiff ℝ ∞ Vc)
    (hdiv : ∀ x, E x ≠ 0 → ∑ j : Fin 3, dy j Vc x j = 0) :
    Integrable (fun z => dotL (advT Vc Φ z) (E z)) (srwfSlab P) ∧
      Integrable (fun z => dotL (Φ z) (advT Vc E z)) (srwfSlab P) ∧
      ∫ z, dotL (advT Vc Φ z) (E z) ∂(srwfSlab P) =
        -∫ z, dotL (Φ z) (advT Vc E z) ∂(srwfSlab P) := by
  obtain ⟨R, hR⟩ := hΦs.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦs.smooth
  have hD : ContDiff ℝ ∞ (dotFn Φ E) := srwf_dotFn_contDiff hΦc hE
  have hAdvc : Continuous (advT Vc Φ) := by
    unfold advT
    exact continuous_finset_sum _ fun k _ =>
      (srwf_coord_contDiff hV k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hΦc k).continuous
  have hAdvE : Continuous (advT Vc E) := by
    unfold advT
    exact continuous_finset_sum _ fun k _ =>
      (srwf_coord_contDiff hV k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hE k).continuous
  have hB_int : Integrable (fun z => dotL (advT Vc Φ z) (E z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hAdvc).clm_apply hE.continuous) (R := R)
      (fun t y hy => by
        have h0 : advT Vc Φ (t, y) = 0 := by
          unfold advT
          exact Finset.sum_eq_zero fun k _ => by rw [srwf_dy_bdd hR k t y hy, smul_zero]
        simp [h0])
  have hD_int : Integrable (fun z => dotL (Φ z) (advT Vc E z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hΦc.continuous).clm_apply hAdvE) (R := R)
      (fun t y hy => by simp [hR t y hy])
  have hK : ∀ k : Fin 3,
      Integrable (fun z => dy k (fun w => Vc w k * dotFn Φ E w) z) (srwfSlab P) ∧
        ∫ z, dy k (fun w => Vc w k * dotFn Φ E w) z ∂(srwfSlab P) = 0 := by
    intro k
    exact srwf_slab_dy (R := R) ((srwf_coord_contDiff hV k).mul hD)
      (fun τ y hy => by simp [dotFn, hR τ y hy]) k
  have hsum : ∀ z, dotL (advT Vc Φ z) (E z) + dotL (Φ z) (advT Vc E z) =
      ∑ k : Fin 3, dy k (fun w => Vc w k * dotFn Φ E w) z := by
    intro z
    rw [abs_div_identity hΦc hE hV z]
    by_cases hz : E z = 0
    · simp [hz, dotFn]
    · rw [hdiv z hz]; simp
  refine ⟨hB_int, hD_int, ?_⟩
  have h0 : ∫ z, dotL (advT Vc Φ z) (E z) ∂(srwfSlab P) +
      ∫ z, dotL (Φ z) (advT Vc E z) ∂(srwfSlab P) = 0 := by
    rw [← integral_add hB_int hD_int]
    have e : (fun z => dotL (advT Vc Φ z) (E z) + dotL (Φ z) (advT Vc E z)) =
        fun z => ∑ k : Fin 3, dy k (fun w => Vc w k * dotFn Φ E w) z := funext hsum
    rw [e, integral_finset_sum _ fun k _ => (hK k).1,
      Finset.sum_eq_zero fun k _ => (hK k).2]
  linear_combination h0

/-- The pointwise transposition `(∇V)ᵀΦ·E = Φ·(E·∇)V`. -/
theorem abs_gradUT_dot {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (Φ E : ℝ × Space → CVec3)
    (x : ℝ × Space) :
    dotL (gradUT V Φ x) (E x) =
      dotL (Φ x) (advT E (fun w => realC (V w.1 w.2)) x) := by
  simp only [gradUT, advT, dotL_apply, Fin.sum_univ_three, dy_realC_comp hV,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Core**: the identity for a globally smooth `V` with `div V = 0` where `E ≠ 0`. -/
theorem absIBP_core {P ν : ℝ} (hP : 0 < P) {V : ℝ → SpatialField} {E : ℝ × Space → CVec3}
    {Φ : ℝ × Space → CVec3}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2))
    (hE : ContDiff ℝ ∞ E) (hEper : ∀ τ y, E (τ + P, y) = E (τ, y))
    (hdiv : ∀ x, E x ≠ 0 →
      ∑ j : Fin 3, ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single j 1)) j) = 0)
    (hΦ : IsPhaseTest P Φ) :
    pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
      pairF P Φ (fun x => L0 ν E x + advT (fun x => realC (V x.1 x.2)) E x +
        advT E (fun x => realC (V x.1 x.2)) x) := by
  set Vc : ℝ × Space → CVec3 := fun w => realC (V w.1 w.2) with hVc
  have hVcc : ContDiff ℝ ∞ Vc := contDiff_realC_field hV
  have hdivc : ∀ x, E x ≠ 0 → ∑ j : Fin 3, dy j Vc x j = 0 := by
    intro x hx
    have h := hdiv x hx
    have : ∑ j : Fin 3, dy j Vc x j = ((∑ j : Fin 3, ((fderiv ℝ (V x.1) x.2
        (EuclideanSpace.single j 1)) j) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => dy_realC_comp hV j j x
    rw [this, h]; simp
  obtain ⟨hB, hD, hBD⟩ := abs_adv_slab hΦ hE hVcc hdivc
  obtain ⟨hA, hC, hAC⟩ := abs_L0_slab (ν := ν) hP hΦ hE (fun x => hEper x.1 x.2)
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hG : Integrable (fun z => dotL (Φ z) (advT E Vc z)) (srwfSlab P) := by
    have hc : Continuous (advT E Vc) := by
      unfold advT
      exact continuous_finset_sum _ fun k _ =>
        (srwf_coord_contDiff hE k).continuous.smul
          (UnforcedLeray.PhaseSpace.contDiff_dy hVcc k).continuous
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hΦ.smooth.continuous).clm_apply hc) (R := R)
      (fun t y hy => by simp [hR t y hy])
  have e1 : pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
      phaseInt P (fun z => (dotL (L0T ν Φ z) (E z) + dotL (Φ z) (advT E Vc z)) -
        dotL (advT Vc Φ z) (E z)) := by
    unfold pairF
    congr 1
    funext z
    simp only [convT, map_add, map_sub, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    rw [abs_gradUT_dot hV]
    ring
  have e2 : pairF P Φ (fun x => L0 ν E x + advT Vc E x + advT E Vc x) =
      phaseInt P (fun z => (dotL (Φ z) (L0 ν E z) + dotL (Φ z) (advT Vc E z)) +
        dotL (Φ z) (advT E Vc z)) := by
    unfold pairF
    congr 1
    funext z
    simp only [map_add]
  have hAG : Integrable (fun z => dotL (L0T ν Φ z) (E z) + dotL (Φ z) (advT E Vc z))
      (srwfSlab P) := hA.add hG
  have hCD : Integrable (fun z => dotL (Φ z) (L0 ν E z) + dotL (Φ z) (advT Vc E z))
      (srwfSlab P) := hC.add hD
  have hI1 : Integrable (fun z => (dotL (L0T ν Φ z) (E z) + dotL (Φ z) (advT E Vc z)) -
      dotL (advT Vc Φ z) (E z)) (srwfSlab P) := hAG.sub hB
  have hI2 : Integrable (fun z => (dotL (Φ z) (L0 ν E z) + dotL (Φ z) (advT Vc E z)) +
      dotL (Φ z) (advT E Vc z)) (srwfSlab P) := hCD.add hG
  rw [e1, e2, srwf_phaseInt_eq hI1, srwf_phaseInt_eq hI2,
    integral_sub hAG hB, integral_add hA hG, integral_add hCD hG,
    integral_add hC hD, hAC, hBD]
  congr 1
  ring

/-- **`AbsPhaseIBP`** (SP 2370-2382). -/
theorem absPhaseIBP : UnforcedLeray.Short.IIb.AbsPhaseIBP := by
  intro P ν V E hP hVon _ hdivfree hE hEper hδ Φ hΦ
  obtain ⟨δ, hδpos, hEδ⟩ := hδ
  set χ : Space → ℝ := fun y => Real.smoothTransition ((Axi.ϱ y - δ / 4) / (δ / 4)) with hχdef
  have hq : 0 < δ / 4 := by positivity
  have hχ1 : ∀ y, δ / 2 ≤ Axi.ϱ y → χ y = 1 := by
    intro y hy
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hq]
    linarith
  have hχ0 : ∀ y, Axi.ϱ y ≤ δ / 4 → χ y = 0 := by
    intro y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hq.le
  obtain ⟨V', hV'def⟩ : ∃ V' : ℝ → SpatialField, ∀ τ y, V' τ y = χ y • V τ y :=
    ⟨fun τ y => χ y • V τ y, fun _ _ => rfl⟩
  have hOffOpen : IsOpen {x : ℝ × Space | x.2 ∉ Axi.axis} :=
    (Axi.isClosed_axis.isOpen_compl).preimage continuous_snd
  have hcontϱ : Continuous fun x : ℝ × Space => Axi.ϱ x.2 := Axi.continuous_ϱ.comp continuous_snd
  -- smoothness of the cut-off field
  have hV'c : ContDiff ℝ ∞ (fun x : ℝ × Space => V' x.1 x.2) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases h : Axi.ϱ x.2 < δ / 4
    · have hev : (fun w : ℝ × Space => V' w.1 w.2) =ᶠ[𝓝 x] fun _ => (0 : Space) := by
        filter_upwards [(isOpen_lt hcontϱ continuous_const).mem_nhds h] with w hw
        rw [hV'def, hχ0 _ hw.le, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push_neg at h
      have hy : x.2 ∉ Axi.axis := fun h' => by
        have := (Axi.mem_axis_iff _).1 h'
        linarith
      have h1 : ContDiffAt ℝ ∞ (fun w : ℝ × Space => V w.1 w.2) x :=
        hVon.contDiffAt (hOffOpen.mem_nhds hy)
      have hϱc : ContDiffAt ℝ ∞ Axi.ϱ x.2 :=
        Axi.contDiffOn_ϱ.contDiffAt (Axi.isClosed_axis.isOpen_compl.mem_nhds hy)
      have hχc : ContDiffAt ℝ ∞ (fun w : ℝ × Space => χ w.2) x := by
        have h2 : ContDiffAt ℝ ∞ (fun w : ℝ × Space => (Axi.ϱ w.2 - δ / 4) / (δ / 4)) x :=
          ((hϱc.comp x contDiff_snd.contDiffAt).sub contDiffAt_const).div_const _
        exact (Real.smoothTransition.contDiff.contDiffAt).comp x h2
      have := hχc.smul h1
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      exact hV'def w.1 w.2
  -- local agreement
  have hlocS : ∀ τ y, δ ≤ Axi.ϱ y → ∀ᶠ y' in 𝓝 y, V' τ y' = V τ y' := by
    intro τ y hy
    filter_upwards [(isOpen_lt continuous_const Axi.continuous_ϱ).mem_nhds
      (show δ / 2 < Axi.ϱ y by linarith)] with w hw
    rw [hV'def, hχ1 _ hw.le, one_smul]
  have hlocJ : ∀ x : ℝ × Space, δ ≤ Axi.ϱ x.2 →
      (fun w : ℝ × Space => V' w.1 w.2) =ᶠ[𝓝 x] fun w => V w.1 w.2 := by
    intro x hx
    filter_upwards [(isOpen_lt continuous_const hcontϱ).mem_nhds
      (show δ / 2 < Axi.ϱ x.2 by linarith)] with w hw
    rw [hV'def, hχ1 _ hw.le, one_smul]
  have hpt : ∀ τ y, δ ≤ Axi.ϱ y → V' τ y = V τ y := by
    intro τ y hy
    rw [hV'def, hχ1 _ (by linarith), one_smul]
  have hEz : ∀ x : ℝ × Space, E x ≠ 0 → δ ≤ Axi.ϱ x.2 := by
    intro x hx
    by_contra h
    exact hx (hEδ x.1 x.2 (not_le.1 h))
  have hdyE : ∀ (j : Fin 3) (x : ℝ × Space), Axi.ϱ x.2 < δ → dy j E x = 0 := by
    intro j x hx
    have hev : E =ᶠ[𝓝 x] fun _ => (0 : CVec3) := by
      filter_upwards [(isOpen_lt hcontϱ continuous_const).mem_nhds hx] with w hw
      exact hEδ w.1 w.2 hw
    simp [dy, hev.fderiv_eq]
  have hfd : ∀ x : ℝ × Space, δ ≤ Axi.ϱ x.2 → fderiv ℝ (V' x.1) x.2 = fderiv ℝ (V x.1) x.2 :=
    fun x hx =>
    Filter.EventuallyEq.fderiv_eq (hlocS x.1 x.2 hx)
  have hdyV : ∀ (k : Fin 3) (x : ℝ × Space), δ ≤ Axi.ϱ x.2 →
      dy k (fun w : ℝ × Space => realC (V' w.1 w.2)) x =
        dy k (fun w : ℝ × Space => realC (V w.1 w.2)) x := by
    intro k x hx
    have hev : (fun w : ℝ × Space => realC (V' w.1 w.2)) =ᶠ[𝓝 x]
        fun w : ℝ × Space => realC (V w.1 w.2) := by
      filter_upwards [hlocJ x hx] with w hw
      exact congrArg realC hw
    simp only [dy, hev.fderiv_eq]
  have hdiv' : ∀ x : ℝ × Space, E x ≠ 0 →
      ∑ j : Fin 3, ((fderiv ℝ (V' x.1) x.2 (EuclideanSpace.single j 1)) j) = 0 := by
    intro x hx
    have hxδ := hEz x hx
    rw [hfd x hxδ]
    exact hdivfree x.1 x.2 (fun h' => by
      have := (Axi.mem_axis_iff _).1 h'
      linarith)
  have core := absIBP_core (ν := ν) hP hV'c hE hEper hdiv' hΦ
  have hL : pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
      pairF P (fun x => L0T ν Φ x + convT V' Φ x) E := by
    unfold pairF
    congr 1
    funext x
    beta_reduce
    by_cases hx : E x = 0
    · simp [hx]
    · have hxδ := hEz x hx
      have hc : convT V' Φ x = convT V Φ x := by
        simp only [convT, gradUT, advT, hfd x hxδ, hpt x.1 x.2 hxδ]
      rw [hc]
  have hR : pairF P Φ (fun x => L0 ν E x + advT (fun x => realC (V x.1 x.2)) E x +
        advT E (fun x => realC (V x.1 x.2)) x) =
      pairF P Φ (fun x => L0 ν E x + advT (fun x => realC (V' x.1 x.2)) E x +
        advT E (fun x => realC (V' x.1 x.2)) x) := by
    unfold pairF
    congr 1
    funext x
    beta_reduce
    have h1 : advT (fun x => realC (V x.1 x.2)) E x =
        advT (fun x => realC (V' x.1 x.2)) E x := by
      by_cases hx : Axi.ϱ x.2 < δ
      · simp [advT, hdyE _ x hx]
      · have := hpt x.1 x.2 (not_lt.1 hx)
        simp only [advT, this]
    have h2 : advT E (fun x => realC (V x.1 x.2)) x =
        advT E (fun x => realC (V' x.1 x.2)) x := by
      by_cases hx : E x = 0
      · simp [advT, hx]
      · have hxδ := hEz x hx
        simp only [advT, hdyV _ x hxδ]
    rw [h1, h2]
  rw [hL, hR]
  exact core
end UnforcedLeray.Short.IIb
