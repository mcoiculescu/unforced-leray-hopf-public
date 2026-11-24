import UnforcedLeray.Short.PartIIa.Sub.F15
import UnforcedLeray.Short.PartIIa.Sub.F06
import UnforcedLeray.Short.PartIIa.Tasks.F12TensorDensity
import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing
import UnforcedLeray.Short.PartIIa.Tasks.F12aSmoothSymSubmodule
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.DivPairing
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.GradLimit
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce.SolSliceFixed
import UnforcedLeray.Units.B0414.PhaseOrthogonal

/-!
# Part II-a, task `PartII-a:F15/2`: the weak stress satisfies the weak equation (reduction)

Source of record: `the November 2 reference manuscript`, lines 1537, 1548.

`wsuWeakEq_of` proves `WSUWeakEq` from two named inputs:
* `WSULerayPair`: the Cartesian Leray projection on `Y_2` does not change the phase pairing
  against a divergence-free phase test (`⟨Φ, 𝐏f⟩ = ⟨Φ, f⟩`);
* `WSUTensorIBP`: integration by parts `⟨Φ, div G⟩ = -⟨∇Φ, G⟩` for smooth phase tensors.

Smooth tensors: `IsWeakStressInverse` gives `S T = w` with `(μ+L)w = 𝐏 div G`, and
`hasPhaseOp_body_of_D` turns this into a weak identity for `w`; the two inputs finish it.
Rough tensors: density (`smoothTensorsDense`) and continuity of both sides in `T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Input `WSULerayPair` (lines 1537, 1548): `⟨Φ, 𝐏f⟩ = ⟨Φ, f⟩` for a divergence-free phase test
`Φ` and every `f ∈ Y_2`. Proof route: `Φ(τ,·)` is distributionally solenoidal for a.e. `τ`
(spatial integration by parts), so the residual `f - 𝐏f` is orthogonal to `testElem (conj Φ)`
in `Y_2` (`B0414.inner_residualY_eq_zero`, `B0414.solenoidalY`). -/
def WSULerayPair : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    (∀ p, ∑ j, dy j Φ p j = 0) → ∀ f : Yq P 2,
      phasePair P 2 Φ (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) = phasePair P 2 Φ f

/-- Input `WSUTensorIBP` (line 1548): for phase tests `Φ` and `G_i`,
`⟨Φ, div G⟩ = -⟨∇Φ, G⟩` with `(div G)_i = ∑_j ∂_j G_ij` and `⟨∇Φ, G⟩ = ∑_i ⟨(∂_jΦ_i)_j, G_i⟩`.
Proof route: `phasePair_dy_testElem` applied to the test `Φ_i e_j` and the row `G_i`. -/
def WSUTensorIBP : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) (G : Fin 3 → ℝ × Space → CVec3),
    IsPhaseTest P Φ → (∀ i, IsPhaseTest P (G i)) →
      phasePair P 2 Φ (testElem P 2 (tensorDiv G)) = -tensorGradPair P Φ (smoothTensor P G)

/-- Continuity of `T ↦ ⟨∇Φ, T⟩` on `Y_2(Sym_3)`. -/
theorem continuous_tensorGradPair (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) :
    Continuous (fun T : symY2 P => tensorGradPair P Φ (T : Y2Sym P)) := by
  unfold tensorGradPair
  refine continuous_finsetSum _ fun i _ => ?_
  exact (phasePair P 2 _).continuous.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => Yq P 2) i).comp continuous_subtype_val)

/-- (F15/2) Reduction of `WeakStressUnique`'s weak equation to the two named inputs. -/
theorem wsuWeakEq_of (hL : WSULerayPair) (hI : WSUTensorIBP) : WSUWeakEq := by
  intro P _ ν hν μ hμ S hS
  have key : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → (∀ p, ∑ j, dy j Φ p j = 0) →
      ∀ T : symY2 P, phasePair P 2 (μ • Φ + L0T ν Φ) (S T) =
        -tensorGradPair P Φ (T : Y2Sym P) := by
    intro Φ hΦ hdiv
    have hcl : IsClosed {T : symY2 P | phasePair P 2 (μ • Φ + L0T ν Φ) (S T) =
        -tensorGradPair P Φ (T : Y2Sym P)} :=
      isClosed_eq ((phasePair P 2 _).continuous.comp S.continuous)
        (continuous_tensorGradPair P Φ).neg
    have hsub : {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
        (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} ⊆
        {T : symY2 P | phasePair P 2 (μ • Φ + L0T ν Φ) (S T) =
          -tensorGradPair P Φ (T : Y2Sym P)} := by
      rintro T ⟨G, hG, hsym, hT⟩
      obtain ⟨w, hwS, hw⟩ := hS T G hG hsym hT
      have hwL : HasPhaseOp (fun Φ' => μ • Φ' + L0T ν Φ') (w : Yq P 2)
          (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) := by
        have h := hasPhaseOp_body_of_D (μ := μ) w
        rwa [hw] at h
      show phasePair P 2 (μ • Φ + L0T ν Φ) (S T) = -tensorGradPair P Φ (T : Y2Sym P)
      rw [← hwS]
      refine (hwL Φ hΦ).trans ?_
      rw [hL P Φ hΦ hdiv, hI P Φ G hΦ hG, hT]
    have hd : Dense {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
        (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} :=
      smoothTensorsDense P
    intro T
    have hT : T ∈ closure {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
        (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} := by
      rw [hd.closure_eq]
      trivial
    exact closure_minimal hsub hcl hT
  intro T Φ hΦ hdiv
  exact key Φ hΦ hdiv T


/-! ### Discharge of `WSUTensorIBP` -/

theorem testElem_sum_loc {P : ℝ} [Fact (0 < P)] {ι : Type*} (s : Finset ι)
    {F : ι → ℝ × Space → CVec3} (h : ∀ i ∈ s, IsPhaseTest P (F i)) :
    testElem P 2 (∑ i ∈ s, F i) = ∑ i ∈ s, testElem P 2 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : ℝ × Space → CVec3) = (0 : ℂ) • (0 : ℝ × Space → CVec3) := by simp
    rw [h0, testElem_const_smul ((IsPhaseTest.zero (P := P)).isSliceTest 2)]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      testElem_add ((h a (Finset.mem_insert_self a s)).isSliceTest 2)
        ((IsPhaseTest.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)).isSliceTest 2),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- Component test `Φ_i e_j`. -/
def compCLM (i j : Fin 3) : CVec3 →L[ℝ] CVec3 :=
  ContinuousLinearMap.smulRight ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)
    (EuclideanSpace.single j (1 : ℂ) : CVec3)

theorem dy_clm_comp {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (L : CVec3 →L[ℝ] CVec3)
    (j : Fin 3) : dy j (fun p => L (Φ p)) = fun p => L (dy j Φ p) := by
  funext p
  have h := L.hasFDerivAt.comp p ((hΦ.smooth.differentiable (by simp)) p).hasFDerivAt
  have h2 : fderiv ℝ (fun p => L (Φ p)) p = L ∘L fderiv ℝ Φ p := h.fderiv
  simp only [dy]
  rw [h2]
  rfl

theorem wsuTensorIBP : WSUTensorIBP := by
  intro P _ Φ G hΦ hG
  classical
  set D : Fin 3 → Fin 3 → ℝ × Space → CVec3 := fun i j p =>
    (ContinuousLinearMap.smulRight ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)
      (EuclideanSpace.single i (1 : ℂ) : CVec3)) (dy j (G i) p) with hD
  set A : Fin 3 → Fin 3 → ℝ × Space → CVec3 := fun i j p => compCLM i j (Φ p) with hA
  have hDt : ∀ i j, IsPhaseTest P (D i j) := fun i j => ((hG i).dy j).clm_comp _
  have hAt : ∀ i j, IsPhaseTest P (A i j) := fun i j => hΦ.clm_comp _
  have hdiv : tensorDiv G = ∑ i, ∑ j, D i j := by
    funext p
    ext k
    simp only [tensorDiv, hD, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
    simp [Pi.single_apply]
  have h1 : ∀ i j, phasePair P 2 Φ (testElem P 2 (D i j)) =
      phasePair P 2 (-dy j (A i j)) (testElem P 2 (G i)) := by
    intro i j
    rw [phasePair_dy_testElem (hAt i j) (hG i) j,
      smoothSym_phasePair_testElem hΦ (hDt i j),
      smoothSym_phasePair_testElem (hAt i j) ((hG i).dy j)]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [hD, hA, compCLM, dotL_apply, Pi.single_apply, mul_comm]
  have hθ : ∀ i, (fun p => (WithLp.toLp 2 fun j => dy j Φ p i : CVec3)) = ∑ j, dy j (A i j) := by
    intro i
    funext p
    ext k
    have : ∀ j, dy j (A i j) p = compCLM i j (dy j Φ p) := fun j => by
      have := dy_clm_comp hΦ (compCLM i j) j
      exact congrFun this p
    simp [Finset.sum_apply, this, compCLM, Pi.single_apply]
  have hdyA : ∀ i j, IsPhaseTest P (dy j (A i j)) := fun i j => (hAt i j).dy j
  unfold tensorGradPair
  rw [hdiv, testElem_sum_loc _ fun i _ => IsPhaseTest.sum _ fun j _ => hDt i j]
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [testElem_sum_loc _ fun j _ => hDt i j] 
  simp only [map_sum]
  simp only [h1]
  have hth := hθ i
  show _ = -phasePair P 2 (fun p => (WithLp.toLp 2 fun j => dy j Φ p i : CVec3)) (testElem P 2 (G i))
  rw [hth, phasePair_sum _ fun j _ => hdyA i j, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => phasePair_neg (hdyA i j) _

/-! ### Discharge of `WSULerayPair` -/

theorem isSolenoidalC_congr_loc {F G : Space → CVec3} (h : F =ᵐ[volume] G)
    (hF : B0414.IsSolenoidalC F) : B0414.IsSolenoidalC G := by
  obtain ⟨a, b⟩ := (B0414.isSolenoidalC_iff F).1 hF
  refine (B0414.isSolenoidalC_iff G).2 ⟨Leray.solenoidal_congr_ae a ?_,
    Leray.solenoidal_congr_ae b ?_⟩
  · exact h.mono fun x hx => by simp [hx]
  · exact h.mono fun x hx => by simp [hx]

theorem fderiv_slice_eq_spatial_loc {Φ : ℝ × Space → CVec3}
    (hΦ : Differentiable ℝ Φ) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => Φ (τ, x)) y v = fderiv ℝ Φ (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : Space => (τ, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hΦ (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : Space →L[ℝ] CVec3 => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] using h

theorem testElem_conj_mem_solenoidalY {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (hdiv : ∀ p, ∑ j, dy j Φ p j = 0) :
    testElem P 2 (conjF Φ) ∈ B0414.solenoidalY P := by
  have hΨ := conjF_isPhaseTest hΦ
  have hs : IsSliceTest P 2 (conjF Φ) := hΨ.isSliceTest 2
  have hae : ⇑(testElem P 2 (conjF Φ)) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hs) := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space)) (p := 2)
      (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  rw [B0414.mem_solenoidalY_iff_slices]
  filter_upwards [hae] with τ hτ
  rw [hτ]
  induction τ using QuotientAddGroup.induction_on with
  | H t =>
    rw [circleSlice_coe, B0414.mem_solenoidalC_iff]
    refine isSolenoidalC_congr_loc (MemLp.coeFn_toLp (hs.2.memLp t)).symm ?_
    have hΨd : Differentiable ℝ (conjF Φ) := hΨ.smooth.differentiable (by simp)
    refine IIb.ssf_isSolenoidalC ?_ (hΨ.hasCompactSupport_slice t) ?_
    · exact hΨ.smooth.comp (contDiff_const.prodMk contDiff_id)
    · intro y
      have e : ∀ j : Fin 3, fderiv ℝ (fun x : Space => conjF Φ (t, x)) y (coordinateVector j) =
          dy j (conjF Φ) (t, y) := fun j => fderiv_slice_eq_spatial_loc hΨd t y _
      simp only [e, dy_conjF hΦ]
      have := congrArg star (hdiv (t, y))
      simpa [conjF, Finset.sum_apply] using this

theorem wsuLerayPair : WSULerayPair := by
  intro P _ Φ hΦ hdiv f
  have hΨ := conjF_isPhaseTest hΦ
  have hg := testElem_conj_mem_solenoidalY hΦ hdiv
  have hin := B0414.inner_residualY_eq_zero f hg
  have hpair : ∀ h : Yq P 2, inner ℂ (testElem P 2 (conjF Φ)) h = phasePair P 2 Φ h := by
    intro h
    have := (phaseInnerEqPairing P (conjF Φ) hΨ).2 h
    have hcc : conjF (conjF Φ) = Φ := by
      funext p
      ext k
      simp [conjF]
    rwa [hcc] at this
  have h0 : phasePair P 2 Φ (f - lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) = 0 := by
    rw [← hpair, ← inner_conj_symm, hin]
    simp
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

theorem wsuWeakEq : WSUWeakEq := wsuWeakEq_of wsuLerayPair wsuTensorIBP

end UnforcedLeray.Short.PartIIa
