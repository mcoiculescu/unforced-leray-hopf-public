import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2_2
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.StressInvH1Grad.Lift
import UnforcedLeray.Short.PartIIa.Tasks.F15cWSUPressure
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry

/-!
# `PartIII-b:IIIb-D5/2/2/1`: Helmholtz approximation for periodic mode tests

Source `the November 2 reference manuscript` 167-182,
4145-4147, 5975-5985.

For a real `P`-periodic test `φ : SpaceTime → Space` (`P = 2 * L.ε * cOf L.ν`), we construct
real-valued solenoidal phase tests `ψ_k` from the `F15c` joint Newton Helmholtz potentials of `φ`
cut off by `cutχ k`, prove `(L₀ᵗ + μ)ψ_k → (L₀ᵗ + μ)φ` against the solenoidal lifted velocity
`velPhys b` via `PartIIa.pressure_kills_gradient` and `F15c.tendsto_curlScalar_add_gradT_cutS`, and
prove `stressPair P (strPhys (strSum (-(B.M b)))) (cplxT (ψ_k))` converges to
`P⁻¹ ∫_0^P projectedCoupling U b_* φ` via second-derivative cutoff convergence `tendsto_dy_dy_cut`,
`IIb.lerayPairSol`, `RieszLp.lerayY_isPhaseSolenoidal`, and `cartLiftSymOuter_proved`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HelmholtzApproxAux

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Axi UnforcedLeray.RieszLp
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Short.PartIIa (pressure_kills_gradient L0T_add_wp)
open UnforcedLeray.Short.PartIIa.F15c
open UnforcedLeray.Short.PartIIIb
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux

/-! ### 1. Real-valued Helmholtz cutoff approximants -/

private theorem isPhaseTest_cplxT {P : ℝ} {φ : SpaceTime → Space}
    (hφ : UnforcedLeray.Short.Interface.IsPeriodicTest P φ) :
    IsPhaseTest P (B0005.cplxT φ) where
  smooth := B0005.cplxL.contDiff.comp hφ.smooth
  periodic τ y := by
    change B0005.cplxL (φ ((τ, y).1 + P, (τ, y).2)) = B0005.cplxL (φ (τ, y))
    rw [hφ.periodic (τ, y)]
  bounded_support := by
    obtain ⟨K, hK, hφ0⟩ := hφ.space_compact
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
    refine ⟨max R 0, fun τ y hy => ?_⟩
    have hyK : y ∉ K := by
      intro hm
      have hle : ‖y‖ ≤ max R 0 := by
        have hb := hR hm
        rw [Metric.mem_closedBall, dist_zero_right] at hb
        exact hb.trans (le_max_left R 0)
      exact not_lt_of_ge hle hy
    change B0005.cplxL (φ (τ, y)) = 0
    rw [hφ0 (τ, y) hyK, map_zero]

private theorem im_dy_eq_zero {α : ℝ × Space → ℂ} (hα : Differentiable ℝ α)
    (him : ∀ p, (α p).im = 0) (j : Fin 3) (p : ℝ × Space) :
    (dy j α p).im = 0 := by
  have hc := congrFun (dy_clm_gen Complex.imCLM hα j) p
  simp only [Complex.imCLM_apply] at hc
  rw [← hc]
  have hz : (fun q => (α q).im) = fun _ => (0 : ℝ) := funext him
  rw [hz]
  simp [dy]

private theorem real_curl_approx {P : ℝ} [Fact (0 < P)] {φ : SpaceTime → Space}
    (hφ : UnforcedLeray.Short.Interface.IsPeriodicTest P φ) :
    ∃ (Ac : Fin 3 → ℝ × Space → ℂ) (Nc : ℝ × Space → ℂ) (ψ : ℕ → SpaceTime → Space),
      (∀ i, IsGoodScalar P (Ac i)) ∧
      IsGoodScalar P Nc ∧
      curlScalar Ac + gradT Nc = B0005.cplxT φ ∧
      (∀ k, B0005.cplxT (ψ k) = curlScalar (fun m => cutS k (Ac m))) ∧
      (∀ k, UnforcedLeray.Cons.C03.Concrete.IsSolTest P (B0005.cplxT (ψ k))) := by
  let Φ : ℝ × Space → CVec3 := B0005.cplxT φ
  have hΦ : IsPhaseTest P Φ := isPhaseTest_cplxT hφ
  have hΦm : ∀ m : Fin 3, IsPhaseTest P (fun p => Φ p m) :=
    fun m => hΦ.clm_comp (B0005.projC m)
  let Bc : Fin 3 → ℝ × Space → ℂ := fun m => newtonJointC (fun p => Φ p m)
  let Ac : Fin 3 → ℝ × Space → ℂ := fun i => dy (i + 1) (Bc (i + 2)) - dy (i + 2) (Bc (i + 1))
  let Nc : ℝ × Space → ℂ := -∑ k : Fin 3, dy k (Bc k)
  have hB_smooth : ∀ m, ContDiff ℝ ∞ (Bc m) := fun m => contDiff_newtonJointC (hΦm m)
  have hB_dy : ∀ m k, IsGoodScalar P (dy k (Bc m)) :=
    fun m k => isGoodScalar_dy_newtonJointC (hΦm m) k
  have hAc : ∀ i, IsGoodScalar P (Ac i) :=
    fun i => (hB_dy (i + 2) (i + 1)).sub (hB_dy (i + 1) (i + 2))
  have hNc : IsGoodScalar P Nc :=
    (IsGoodScalar.sum _ fun k _ => hB_dy k k).neg
  have hsplit : curlScalar Ac + gradT Nc = Φ := by
    have h1 := curlScalar_curl_add_gradT_neg_div hB_smooth
    have h2 : (fun p => WithLp.toLp 2 fun i => -lapT (Bc i) p) = Φ := by
      funext p
      ext i
      rw [WithLp.ofLp_toLp, congrFun (lapT_newtonJointC (hΦm i)) p, Pi.neg_apply, neg_neg]
    exact h1.trans h2
  have hB_im : ∀ m p, (Bc m p).im = 0 := by
    intro m p
    have him0 : imPart (fun q => Φ q m) = fun _ => 0 := by
      funext q
      simp [imPart, Φ, B0005.cplxT, B0005.cplxL_apply]
    simp [Bc, newtonJointC, him0, UnforcedLeray.Short.IIb.LTS.newtonJoint, newtonConv]
  have hdyB_im : ∀ m j p, (dy j (Bc m) p).im = 0 :=
    fun m j p => im_dy_eq_zero ((hB_smooth m).differentiable (by simp)) (hB_im m) j p
  have hAc_im : ∀ i p, (Ac i p).im = 0 := by
    intro i p
    simp [Ac, hdyB_im]
  have hcut_im : ∀ k m p, (cutS k (Ac m) p).im = 0 := by
    intro k m p
    simp [cutS, Complex.real_smul, hAc_im m p]
  let Ψ : ℕ → ℝ × Space → CVec3 := fun k => curlScalar (fun m => cutS k (Ac m))
  let ψ : ℕ → SpaceTime → Space := fun k p => B0005.reL (Ψ k p)
  have ha_cut : ∀ k m, IsPhaseTest P (cutS k (Ac m)) :=
    fun k m => isPhaseTest_cutS (hAc m) k
  have hΨ_im : ∀ k p i, (Ψ k p i).im = 0 := by
    intro k p i
    have hd : ∀ m, Differentiable ℝ (cutS k (Ac m)) :=
      fun m => (ha_cut k m).smooth.differentiable (by simp)
    rw [curlScalar_apply hd p i]
    have h1 := im_dy_eq_zero (hd (i + 2)) (hcut_im k (i + 2)) (i + 1) p
    have h2 := im_dy_eq_zero (hd (i + 1)) (hcut_im k (i + 1)) (i + 2) p
    simp [h1, h2]
  have hcplx : ∀ k, B0005.cplxT (ψ k) = Ψ k := by
    intro k
    funext p
    ext i
    simp only [B0005.cplxT, B0005.cplxL_apply, ψ, B0005.reL_apply]
    exact Complex.ext rfl (hΨ_im k p i).symm
  refine ⟨Ac, Nc, ψ, hAc, hNc, hsplit, hcplx, fun k => ?_⟩
  rw [hcplx k]
  exact ⟨isPhaseTest_curlScalar (ha_cut k),
    div_curlScalar_eq_zero (fun m => (ha_cut k m).smooth)⟩

/-! ### 2. Second-derivative cutoff convergence in `Y_{2'}` -/

private theorem dy_dy_cut_decomp {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ k, IsPhaseSchwartz P r (dy k U)) (j i : Fin 3) (n : ℕ) :
    dy j (dy i (mulT (cutχ n) U)) =
      dy j (mulT (cutχ n) (dy i U)) +
        (mulT (sd i (cutχ n)) (dy j U) + mulT (sd j (sd i (cutχ n))) U) := by
  have h1 : dy i (mulT (cutχ n) U) = mulT (cutχ n) (dy i U) + mulT (sd i (cutχ n)) U :=
    dy_mulT ((contDiff_cutχ n).differentiable (by simp)) (hU.smooth.differentiable (by simp)) i
  have hd1 : Differentiable ℝ (mulT (cutχ n) (dy i U)) :=
    (contDiff_mulT (contDiff_cutχ n) (hdU i).smooth).differentiable (by simp)
  have hd2 : Differentiable ℝ (mulT (sd i (cutχ n)) U) :=
    (contDiff_mulT (contDiff_sd (contDiff_cutχ n) i) hU.smooth).differentiable (by simp)
  rw [h1, dy_add hd1 hd2 j,
    dy_mulT ((contDiff_sd (contDiff_cutχ n) i).differentiable (by simp))
      (hU.smooth.differentiable (by simp)) j]

private theorem tendsto_dy_dy_cut {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ k, IsPhaseSchwartz P r (dy k U)) (j i : Fin 3) :
    Tendsto (fun n => testElem P r (dy j (dy i (mulT (cutχ n) U)))) atTop
      (𝓝 (testElem P r (dy j (dy i U)))) := by
  have hnull : NullSeq P r (fun n =>
      mulT (sd i (cutχ n)) (dy j U) + mulT (sd j (sd i (cutχ n))) U) :=
    (NullSeq.mulT hr (smallProfile_sd_cutχ i).goodMult (hdU j).sliceTest).add
      (NullSeq.mulT hr ((smallProfile_sd_cutχ i).sd j).goodMult hU.sliceTest)
  have hs1 : ∀ n, IsSliceTest P r (dy j (mulT (cutχ n) (dy i U))) :=
    fun n => (((hdU i).isPhaseTest_cut n).dy j).isSliceTest r
  have heq : (fun n => testElem P r (dy j (dy i (mulT (cutχ n) U)))) =
      fun n => testElem P r (dy j (mulT (cutχ n) (dy i U))) +
        testElem P r (mulT (sd i (cutχ n)) (dy j U) + mulT (sd j (sd i (cutχ n))) U) := by
    funext n
    rw [dy_dy_cut_decomp hU hdU j i n, testElem_add (hs1 n) (hnull.slice n)]
  rw [heq]
  simpa using (tendsto_dy_cut hr (hdU i) j).add hnull.tendsto

private theorem dy_sub_vec {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) (j : Fin 3) :
    dy j (A - B) = dy j A - dy j B := by
  funext p
  simp [dy, fderiv_sub (hA p) (hB p)]

private theorem dy_sum_vec {ι : Type*} (s : Finset ι) (F : ι → ℝ × Space → CVec3)
    (hF : ∀ k ∈ s, Differentiable ℝ (F k)) (j : Fin 3) :
    dy j (∑ k ∈ s, F k) = ∑ k ∈ s, dy j (F k) := by
  funext p
  simp only [dy, Finset.sum_apply]
  rw [fderiv_sum fun k hk => (hF k hk) p]
  simp

private theorem isSliceTest_neg {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G) :
    IsSliceTest P r (-G) := by
  have h : -G = (-1 : ℂ) • G := by funext p; simp
  rw [h]
  exact hG.const_smul (-1 : ℂ)

private theorem isSliceTest_sub {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {A B : ℝ × Space → CVec3} (hA : IsSliceTest P r A) (hB : IsSliceTest P r B) :
    IsSliceTest P r (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add (isSliceTest_neg hB)

private theorem isSliceTest_sum {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (hF : ∀ i ∈ s, IsSliceTest P r (F i)) :
    IsSliceTest P r (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsPhaseTest.zero (P := P)).isSliceTest r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

private theorem testElem_sub_slice {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {A B : ℝ × Space → CVec3} (hA : IsSliceTest P r A) (hB : IsSliceTest P r B) :
    testElem P r (A - B) = testElem P r A - testElem P r B := by
  rw [sub_eq_add_neg, testElem_add hA (isSliceTest_neg hB), testElem_neg hB, ← sub_eq_add_neg]

private theorem testElem_sum_slice {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (hF : ∀ i ∈ s, IsSliceTest P r (F i)) :
    testElem P r (∑ i ∈ s, F i) = ∑ i ∈ s, testElem P r (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (testElem_zero (P := P) (r := r))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      testElem_add (hF a (Finset.mem_insert_self a s))
        (isSliceTest_sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

private theorem tendsto_dy_curlScalar_add_gradT_cutS {P : ℝ} [Fact (0 < P)]
    {Ac : Fin 3 → ℝ × Space → ℂ} {Nc : ℝ × Space → ℂ}
    (hAc : ∀ i, IsGoodScalar P (Ac i)) (hNc : IsGoodScalar P Nc) (j : Fin 3) :
    Tendsto (fun k => testElem P (conjExp 2)
        (dy j (curlScalar (fun m => cutS k (Ac m)) + gradT (cutS k Nc)))) atTop
      (𝓝 (testElem P (conjExp 2) (dy j (curlScalar Ac + gradT Nc)))) := by
  have hr : conjExp 2 ≠ ⊤ := by simp [conjExp]
  have ha_cut : ∀ k m, IsPhaseTest P (cutS k (Ac m)) := fun k m => isPhaseTest_cutS (hAc m) k
  have hn_cut : ∀ k, IsPhaseTest P (cutS k Nc) := fun k => isPhaseTest_cutS hNc k
  have hcurl_cut : ∀ k, IsPhaseTest P (curlScalar (fun m => cutS k (Ac m))) :=
    fun k => isPhaseTest_curlScalar (ha_cut k)
  have hgrad_cut : ∀ k, IsPhaseTest P (gradT (cutS k Nc)) := fun k => (hn_cut k).gradT
  have hSL_A_cut : ∀ k i l m, IsSliceTest P (conjExp 2)
      (dy j (dy l (mulT (cutχ k) (fun p => B0005.embedJ i (Ac m p))))) :=
    fun k i l m => (((((hAc m).schwartz i).isPhaseTest_cut k).dy l).dy j).isSliceTest _
  have hSL_N_cut : ∀ k i, IsSliceTest P (conjExp 2)
      (dy j (dy i (mulT (cutχ k) (fun p => B0005.embedJ i (Nc p))))) :=
    fun k i => ((((hNc.schwartz i).isPhaseTest_cut k).dy i).dy j).isSliceTest _
  have hSL_A : ∀ i l m, IsSliceTest P (conjExp 2)
      (dy j (dy l (fun p => B0005.embedJ i (Ac m p)))) :=
    fun i l m => ((hAc m).schwartz_dy i l).sliceTest_dy j
  have hSL_N : ∀ i, IsSliceTest P (conjExp 2)
      (dy j (dy i (fun p => B0005.embedJ i (Nc p)))) :=
    fun i => (hNc.schwartz_dy i i).sliceTest_dy j
  have hcurl_dy_cut : ∀ k, dy j (curlScalar (fun m => cutS k (Ac m))) =
      ∑ i : Fin 3, (dy j (dy (i + 1) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 2) p)))) -
        dy j (dy (i + 2) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 1) p))))) := by
    intro k
    have hc : curlScalar (fun m => cutS k (Ac m)) =
        ∑ i : Fin 3, (dy (i + 1) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 2) p))) -
          dy (i + 2) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 1) p)))) := by
      unfold curlScalar
      exact Finset.sum_congr rfl fun i _ => by rw [embedJ_cutS, embedJ_cutS]
    rw [hc, dy_sum_vec Finset.univ
      (fun i => dy (i + 1) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 2) p))) -
        dy (i + 2) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 1) p))))
      (fun i _ =>
        ((((((hAc (i + 2)).schwartz i).isPhaseTest_cut k).dy (i + 1)).sub
          ((((hAc (i + 1)).schwartz i).isPhaseTest_cut k).dy (i + 2))).smooth.differentiable
          (by simp))) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact dy_sub_vec
      (((((hAc (i + 2)).schwartz i).isPhaseTest_cut k).dy (i + 1)).smooth.differentiable (by simp))
      (((((hAc (i + 1)).schwartz i).isPhaseTest_cut k).dy (i + 2)).smooth.differentiable (by simp))
      j
  have hgrad_dy_cut : ∀ k, dy j (gradT (cutS k Nc)) =
      ∑ i : Fin 3, dy j (dy i (mulT (cutχ k) (fun p => B0005.embedJ i (Nc p)))) := by
    intro k
    rw [gradT_eq_sum_dy_embedJ ((hn_cut k).smooth.differentiable (by simp))]
    have heq : (∑ i : Fin 3, dy i (fun p => B0005.embedJ i (cutS k Nc p))) =
        ∑ i : Fin 3, dy i (mulT (cutχ k) (fun p => B0005.embedJ i (Nc p))) :=
      Finset.sum_congr rfl fun i _ => by rw [embedJ_cutS]
    rw [heq]
    exact dy_sum_vec Finset.univ
      (fun i => dy i (mulT (cutχ k) (fun p => B0005.embedJ i (Nc p))))
      (fun i _ =>
        ((((hNc.schwartz i).isPhaseTest_cut k).dy i).smooth.differentiable (by simp))) j
  have hcurl_dy_uncut : dy j (curlScalar Ac) =
      ∑ i : Fin 3, (dy j (dy (i + 1) (fun p => B0005.embedJ i (Ac (i + 2) p))) -
        dy j (dy (i + 2) (fun p => B0005.embedJ i (Ac (i + 1) p)))) := by
    unfold curlScalar
    rw [dy_sum_vec Finset.univ
      (fun i => dy (i + 1) (fun p => B0005.embedJ i (Ac (i + 2) p)) -
        dy (i + 2) (fun p => B0005.embedJ i (Ac (i + 1) p)))
      (fun i _ =>
        (((hAc (i + 2)).schwartz_dy i (i + 1)).smooth.sub
          ((hAc (i + 1)).schwartz_dy i (i + 2)).smooth).differentiable (by simp)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact dy_sub_vec
      (((hAc (i + 2)).schwartz_dy i (i + 1)).smooth.differentiable (by simp))
      (((hAc (i + 1)).schwartz_dy i (i + 2)).smooth.differentiable (by simp)) j
  have hgrad_dy_uncut : dy j (gradT Nc) =
      ∑ i : Fin 3, dy j (dy i (fun p => B0005.embedJ i (Nc p))) := by
    rw [gradT_eq_sum_dy_embedJ (hNc.smooth.differentiable (by simp))]
    exact dy_sum_vec Finset.univ
      (fun i => dy i (fun p => B0005.embedJ i (Nc p)))
      (fun i _ => ((hNc.schwartz_dy i i).smooth.differentiable (by simp))) j
  have h_elem : ∀ k, testElem P (conjExp 2)
      (dy j (curlScalar (fun m => cutS k (Ac m)) + gradT (cutS k Nc))) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (dy j (dy (i + 1) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 2) p))))) -
        testElem P (conjExp 2)
          (dy j (dy (i + 2) (mulT (cutχ k) (fun p => B0005.embedJ i (Ac (i + 1) p))))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (dy j (dy i (mulT (cutχ k) (fun p => B0005.embedJ i (Nc p))))) := by
    intro k
    rw [dy_add ((hcurl_cut k).smooth.differentiable (by simp))
        ((hgrad_cut k).smooth.differentiable (by simp)) j,
      testElem_add (((hcurl_cut k).dy j).isSliceTest _) (((hgrad_cut k).dy j).isSliceTest _),
      hcurl_dy_cut k, hgrad_dy_cut k,
      testElem_sum_slice _ fun i _ =>
        isSliceTest_sub (hSL_A_cut k i (i + 1) (i + 2)) (hSL_A_cut k i (i + 2) (i + 1)),
      testElem_sum_slice _ fun i _ => hSL_N_cut k i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_sub_slice (hSL_A_cut k i (i + 1) (i + 2)) (hSL_A_cut k i (i + 2) (i + 1))
  have hSL_curl_dy : IsSliceTest P (conjExp 2) (dy j (curlScalar Ac)) := by
    rw [hcurl_dy_uncut]
    exact isSliceTest_sum _ fun i _ =>
      isSliceTest_sub (hSL_A i (i + 1) (i + 2)) (hSL_A i (i + 2) (i + 1))
  have hSL_grad_dy : IsSliceTest P (conjExp 2) (dy j (gradT Nc)) := by
    rw [hgrad_dy_uncut]
    exact isSliceTest_sum _ fun i _ => hSL_N i
  have hcurl_smooth : ContDiff ℝ ∞ (curlScalar Ac) := by
    have hs : IsPhaseSchwartz P (conjExp 2) (curlScalar Ac) :=
      isPhaseSchwartz_sum _ fun i _ =>
        isPhaseSchwartz_sub ((hAc (i + 2)).schwartz_dy i (i + 1))
          ((hAc (i + 1)).schwartz_dy i (i + 2))
    exact hs.smooth
  have hgrad_smooth : ContDiff ℝ ∞ (gradT Nc) := by
    rw [gradT_eq_sum_dy_embedJ (hNc.smooth.differentiable (by simp))]
    exact (isPhaseSchwartz_sum (P := P) (r := conjExp 2) _ fun i _ => hNc.schwartz_dy i i).smooth
  have h_elem_uncut : testElem P (conjExp 2) (dy j (curlScalar Ac + gradT Nc)) =
      (∑ i : Fin 3, (testElem P (conjExp 2)
          (dy j (dy (i + 1) (fun p => B0005.embedJ i (Ac (i + 2) p)))) -
        testElem P (conjExp 2)
          (dy j (dy (i + 2) (fun p => B0005.embedJ i (Ac (i + 1) p)))))) +
      ∑ i : Fin 3, testElem P (conjExp 2)
        (dy j (dy i (fun p => B0005.embedJ i (Nc p)))) := by
    rw [dy_add (hcurl_smooth.differentiable (by simp)) (hgrad_smooth.differentiable (by simp)) j,
      testElem_add hSL_curl_dy hSL_grad_dy,
      hcurl_dy_uncut, hgrad_dy_uncut,
      testElem_sum_slice _ fun i _ =>
        isSliceTest_sub (hSL_A i (i + 1) (i + 2)) (hSL_A i (i + 2) (i + 1)),
      testElem_sum_slice _ fun i _ => hSL_N i]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      testElem_sub_slice (hSL_A i (i + 1) (i + 2)) (hSL_A i (i + 2) (i + 1))
  simp only [h_elem, h_elem_uncut]
  exact (tendsto_finsetSum _ fun i _ =>
      (tendsto_dy_dy_cut hr ((hAc (i + 2)).schwartz i) ((hAc (i + 2)).schwartz_dy i) j (i + 1)).sub
        (tendsto_dy_dy_cut hr ((hAc (i + 1)).schwartz i)
          ((hAc (i + 1)).schwartz_dy i) j (i + 2))).add
    (tendsto_finsetSum _ fun i _ =>
      tendsto_dy_dy_cut hr (hNc.schwartz i) (hNc.schwartz_dy i) j i)

/-! ### 3. Solenoidality and gradient commutation of `dy j` -/

private theorem isSolTest_dy {P : ℝ} {Θ : ℝ × Space → CVec3}
    (hΘ : UnforcedLeray.Cons.C03.Concrete.IsSolTest P Θ) (j : Fin 3) :
    UnforcedLeray.Cons.C03.Concrete.IsSolTest P (dy j Θ) := by
  refine ⟨hΘ.1.dy j, fun p => ?_⟩
  have hcomm : ∀ i : Fin 3, dy i (dy j Θ) p i = dy j (fun q => dy i Θ q i) p := by
    intro i
    rw [PhaseSpace.dy_dy_comm hΘ.1.smooth i j]
    have hc := congrFun (dy_clm_gen (B0005.projC i)
      ((PhaseSpace.contDiff_dy hΘ.1.smooth i).differentiable (by simp)) j) p
    simpa only [B0005.projC_apply] using hc.symm
  simp only [hcomm]
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Differentiable ℝ (fun q => dy i Θ q i) :=
    fun i _ => ((B0005.projC i).contDiff.comp (PhaseSpace.contDiff_dy hΘ.1.smooth i)).differentiable
      (by simp)
  have hsum := congrFun (dy_sum_c Finset.univ hd j) p
  simp only [Finset.sum_apply] at hsum
  rw [← hsum]
  have hz : (∑ i : Fin 3, fun q => dy i Θ q i) = fun _ => (0 : ℂ) := by
    funext q
    simpa [Finset.sum_apply] using hΘ.2 q
  rw [hz]
  simp [dy]

private theorem dy_gradT_comm {α : ℝ × Space → ℂ} (hα : ContDiff ℝ ∞ α) (j : Fin 3) :
    dy j (gradT α) = gradT (dy j α) := by
  have hdα : Differentiable ℝ α := hα.differentiable (by simp)
  have hd_dy : Differentiable ℝ (dy j α) := (contDiff_dy_c hα j).differentiable (by simp)
  rw [gradT_eq_sum_dy_embedJ hdα, gradT_eq_sum_dy_embedJ hd_dy,
    dy_sum_vec Finset.univ (fun i => dy i (fun p => B0005.embedJ i (α p)))
      (fun i _ =>
        ((PhaseSpace.contDiff_dy ((B0005.embedJ i).contDiff.comp hα) i).differentiable (by simp)))
      j]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcomm : dy j (dy i (fun p => B0005.embedJ i (α p))) =
      dy i (dy j (fun p => B0005.embedJ i (α p))) :=
    PhaseSpace.dy_dy_comm ((B0005.embedJ i).contDiff.comp hα) j i
  rw [hcomm]
  exact congrArg (dy i) (dy_clm_gen (B0005.embedJ i) hdα j)

private theorem stressPair_eq_sum_phasePair_cols {P : ℝ} [hP : Fact (0 < P)]
    {Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ} (hsym : ∀ x i j, Tp x i j = Tp x j i)
    (hrow : ∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (StressLiftY.rowsOf Tp j))
    (C : Fin 3 → Yq P 2)
    (hC : ∀ j, UnforcedLeray.Short.IIb.HasRepY (C j) (StressLiftY.rowsOf Tp j))
    {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    stressPair P Tp Θ = ∑ j : Fin 3, phasePair P 2 (dy j Θ) (C j) := by
  have heq : ∀ j, phasePair P 2 (dy j Θ) (C j) =
      UnforcedLeray.Cons.C03.Concrete.pairF P (dy j Θ) (StressLiftY.rowsOf Tp j) :=
    fun j => UnforcedLeray.Short.IIb.phasePair_eq_pairF_of_hasRepY (C j) _ (hC j) (hΘ.dy j)
  simp only [heq]
  have hint : ∀ j, Integrable (fun x => dotL (dy j Θ x) (StressLiftY.rowsOf Tp j x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) :=
    fun j => UnforcedLeray.Short.IIb.integrable_dotL_phaseTest_Yr hP.out one_lt_two
      (hΘ.dy j) (hrow j)
  unfold UnforcedLeray.Cons.C03.Concrete.pairF
  rw [← StressLiftY.phaseInt_sum_cell' hint]
  unfold stressPair
  congr 1
  funext x
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [StressLiftY.rowsOf, hsym x j i, mul_comm]

/-! ### 4. Pointwise axisymmetry without swirl of `U = V + rb` on a ball split -/

private theorem reV_gC (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) :
    reV (B0412.gC g v) = g (reV v) := by
  ext i
  change (B0412.gC g v i).re = (g (reV v)) i
  rw [B0412.gC_apply]
  have hx : reV v = ∑ j : Fin 3, (reV v) j • EuclideanSpace.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [reV_apply, B0412.gEntry, Complex.re_sum, Complex.mul_re, map_smul, mul_comm]

private theorem axiNoSwirlPt_of_ballSplit (p : UnforcedLeray.Cons.C03.Concrete.Params)
    {ρ : ℝ} {V rb : ℝ → SpatialField}
    (hball : IsBallSplit p ρ V rb)
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2 + rb x.1 x.2))
    (τ : ℝ) :
    AxiNoSwirlPt (fun y => V τ y + rb τ y) := by
  have hfq0 : Fact (1 ≤ B0412.q0E) := ⟨by unfold B0412.q0E; norm_num [B0281.q0]⟩
  obtain ⟨z₀, -, hV, hrb, -⟩ := hball
  let U : ℝ → SpatialField := fun t y => V t y + rb t y
  have hU_eq : ∀ t y, U t y =
      (p.raw t y + ∑ i : Fin 2, p.coord z₀ i • p.inlet i t y) + p.corr z₀ t y := by
    intro t y
    dsimp only [U]
    rw [hV t y, hrb]
  intro g hg y₀
  let F₁ : ℝ × Space → Space := fun x => g (U x.1 (g.symm x.2))
  let F₂ : ℝ × Space → Space := fun x => U x.1 x.2
  have hF₂ : Continuous F₂ := hsmooth.continuous
  have hF₁ : Continuous F₁ :=
    g.continuous.comp (hF₂.comp (continuous_fst.prodMk (g.symm.continuous.comp continuous_snd)))
  suffices hF : F₁ = F₂ from congrFun hF (τ, y₀)
  refine (hF₁.ae_eq_iff_eq (volume : Measure (ℝ × Space)) hF₂).mp ?_
  rw [Measure.volume_eq_prod ℝ Space]
  refine (Measure.ae_prod_iff_ae_ae (isClosed_eq hF₁ hF₂).measurableSet).mpr ?_
  have hraw : ∀ t : ℝ, ∀ᵐ y : Space, g (p.raw t (g.symm y)) = p.raw t y := by
    intro t
    let rawNv : Space → Space :=
      Axi.Nv p.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) t
    have hae_off : p.raw t =ᵐ[volume] rawNv := by
      filter_upwards [Axi.ae_not_mem_axis] with y hy
      exact p.raw_eq_off_axis t y hy
    have hcomp := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp hae_off
    filter_upwards [hcomp, hae_off, Axi.isAxisymmetricNoSwirl_Nv p.ε⁻¹ _ t g hg] with y h1 h2 h3
    change p.raw t (g.symm y) = rawNv (g.symm y) at h1
    rw [h1, h2]
    exact h3
  have hinlet : ∀ (i : Fin 2) (t : ℝ), ∀ᵐ y : Space, g (p.inlet i t (g.symm y)) = p.inlet i t y :=
    fun i t => Axi.isAxisymmetricNoSwirl_Nv p.R (p.inletProfile i) t g hg
  have hcorr_prod : ∀ᵐ t : ℝ, (fun y => p.corr z₀ t y) =ᵐ[volume]
      fun y => UnforcedLeray.Cons.C03.Concrete.reP
        (UnforcedLeray.Cons.C03.Concrete.rep (p.wOf z₀) t y) := by
    have hc := UnforcedLeray.Cons.C03.Concrete.contRep_ae (p.wOf z₀)
    rw [Measure.volume_eq_prod ℝ Space] at hc
    exact Measure.ae_ae_of_ae_prod hc
  let hTime := B0412.hasPhaseOp_T0X (p.graphX z₀)
  let tr := UnforcedLeray.PhaseTrace.phaseRepC (q := B0412.q0E) B0412.q0E_ne_top hTime
  have htr_ae : ∀ᵐ t : ℝ, p.wOf z₀ (t : AddCircle p.period) = tr (t : AddCircle p.period) :=
    UnforcedLeray.PhaseTrace.ae_comp_mk
      (UnforcedLeray.PhaseTrace.phaseRepC_ae B0412.q0E_ne_top hTime)
  filter_upwards [hcorr_prod, htr_ae] with t hct htrt
  have hcorr_v : (fun y => p.corr z₀ t y) =ᵐ[volume]
      fun y => reV ((tr (t : AddCircle p.period) : Space → CVec3) y) := by
    refine hct.trans ?_
    have hrs := UnforcedLeray.Cons.C03.Concrete.rep_slice (p.wOf z₀) t
    rw [htrt] at hrs
    filter_upwards [hrs] with y hy
    rw [hy]
    rfl
  have hact_g := p.phaseRepC_spatialAct_eq z₀ g hg t
  have hspatial := (B0412.spatialAct_eq_iff g (tr (t : AddCircle p.period))).1 hact_g
  have hcomp_c := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp hcorr_v
  filter_upwards [hraw t, hinlet 0 t, hinlet 1 t, hcomp_c, hcorr_v, hspatial]
    with y hr0 hi0 hi1 hc1 hc2 hs
  change g (U t (g.symm y)) = U t y
  rw [hU_eq t (g.symm y), hU_eq t y, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [map_add, map_smul]
  rw [hr0, hi0, hi1]
  congr 1
  change p.corr z₀ t (g.symm y) = reV (tr (t : AddCircle p.period) (g.symm y)) at hc1
  rw [hc1, hc2, ← reV_gC g, hs]

/-! ### 5. Identification of the Leray-projected stress pairing with `projectedCoupling` -/

private theorem dy_cplxT_eq_ofReV_testPartial {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ)
    (j : Fin 3) (t : ℝ) (y : Space) :
    dy j (B0005.cplxT φ) (t, y) = ofReV (testPartial (slice φ t) j y) := by
  have hφd : HasFDerivAt φ (fderiv ℝ φ (t, y)) (t, y) :=
    (hφ.differentiable (by simp) (t, y)).hasFDerivAt
  have hcd : HasFDerivAt (B0005.cplxT φ) (B0005.cplxL.comp (fderiv ℝ φ (t, y))) (t, y) :=
    B0005.cplxL.hasFDerivAt.comp (t, y) hφd
  have hsd : HasFDerivAt (slice φ t)
      ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hφd.comp y (hasFDerivAt_prodMk_right t y)
  simp only [dy, testPartial, hcd.fderiv, hsd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  rfl

private theorem integrableOn_period_phasePair {P : ℝ} [hP : Fact (0 < P)]
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) (f : Yq P 2) :
    Integrable (fun t : ℝ => ∫ y, dotL (Ψ (t, y)) ((f (t : AddCircle P) : Space → CVec3) y))
      (volume.restrict (Ioc (0 : ℝ) P)) := by
  have hs := hΨ.isSliceTest (conjExp 2)
  let g : ℝ → ℂ := fun t => innerPair 2 (circleSlice hs (t : AddCircle P)) (f (t : AddCircle P))
  have hgeq : g = fun t : ℝ => ∫ y, dotL (Ψ (t, y)) ((f (t : AddCircle P) : Space → CVec3) y) := by
    funext t
    dsimp only [g]
    rw [circleSlice_coe, innerPair_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
    simp only [sliceMap] at hy ⊢
    rw [hy]
  rw [← hgeq]
  have hf_int : Integrable (fun t : ℝ => f (t : AddCircle P))
      (volume.restrict (Ioc (0 : ℝ) P)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hP.out.le).mp
      (UnforcedLeray.PhaseTrace.intervalIntegrable_comp_mk f 0 P)
  have hcs_cont : Continuous (fun t : ℝ => circleSlice hs (t : AddCircle P)) :=
    (circleSlice hs).continuous.comp (AddCircle.continuous_mk' P)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcs_cont.continuousOn (s := Icc (0 : ℝ) P))
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) P)) :=
    (innerPair 2).aestronglyMeasurable_comp₂ hcs_cont.aestronglyMeasurable
      hf_int.aestronglyMeasurable
  refine (hf_int.norm.const_mul (‖innerPair 2‖ * max M 0)).mono' hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  have ht' : t ∈ Icc (0 : ℝ) P := Ioc_subset_Icc_self ht
  have hcs_le : ‖circleSlice hs (t : AddCircle P)‖ ≤ max M 0 :=
    (hM t ht').trans (le_max_left M 0)
  calc ‖g t‖
      ≤ ‖innerPair 2‖ * ‖circleSlice hs (t : AddCircle P)‖ * ‖f (t : AddCircle P)‖ :=
        (innerPair 2).le_opNorm₂ _ _
    _ ≤ ‖innerPair 2‖ * max M 0 * ‖f (t : AddCircle P)‖ := by
        gcongr

private theorem slice_leray_eq_inner {S G : SpatialField}
    (hG_cont : Continuous G) (hG_cs : HasCompactSupport G)
    {H : Lp CVec3 2 (volume : Measure Space)}
    (hH : (H : Space → CVec3) =ᵐ[volume] fun y => -ofReV (S y)) :
    ∫ y, dotL (ofReV (G y)) (lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top H y) =
      ((-inner ℝ (toL2 S) (Leray.projection (toL2 G)) : ℝ) : ℂ) := by
  have hre : (reV.compLpL 2 volume H : Space → Space) =ᵐ[volume] fun y => -S y := by
    filter_upwards [reV.coeFn_compLpL (p := 2) (μ := volume) H, hH] with y hy1 hy2
    rw [hy1, hy2, map_neg]
    ext i
    simp
  have him : (imV.compLpL 2 volume H : Space → Space) =ᵐ[volume] 0 := by
    filter_upwards [imV.coeFn_compLpL (p := 2) (μ := volume) H, hH] with y hy1 hy2
    rw [hy1, hy2, map_neg]
    ext i
    simp
  have hS_mem : MemLp S 2 volume := by
    have hneg' : MemLp (fun y => -S y) 2 volume :=
      (Lp.memLp (reV.compLpL 2 volume H)).ae_eq hre
    have hnn : (fun y => - -S y) = S := funext fun y => neg_neg (S y)
    exact hnn ▸ hneg'.neg
  have hre_eq : reV.compLpL 2 volume H = -toL2 S := by
    apply Lp.ext
    filter_upwards [hre, Lp.coeFn_neg (toL2 S), coeFn_toL2 hS_mem] with y h1 h2 h3
    rw [h1, h2, Pi.neg_apply, h3]
  have him_eq : imV.compLpL 2 volume H = 0 := by
    apply Lp.ext
    exact him.trans (Lp.coeFn_zero _ _ _).symm
  have hLC : (lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top H : Space → CVec3) =ᵐ[volume]
      fun y => -ofReV (lerayLp 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (toL2 S) y) := by
    filter_upwards [coeFn_lerayC ENNReal.one_lt_two ENNReal.ofNat_ne_top H,
      Lp.coeFn_neg (lerayLp 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (toL2 S)),
      Lp.coeFn_zero Space 2 (volume : Measure Space)] with y hc hneg hz
    rw [hc, hre_eq, him_eq, map_neg, map_zero, hneg, hz, Pi.neg_apply, Pi.zero_apply,
      map_neg, map_zero, add_zero]
  have hdot : (fun y => dotL (ofReV (G y)) (lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top H y))
      =ᵐ[volume] fun y =>
        ((-inner ℝ (lerayLp 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (toL2 S) y)
          (G y) : ℝ) : ℂ) := by
    filter_upwards [hLC] with y hy
    rw [hy, map_neg]
    have hcplx : ∀ v : Space, ofReV v = B0005.cplxL v := fun _ => rfl
    rw [hcplx, hcplx, B0005.dotL_cplxL, Complex.ofReal_neg]
  rw [integral_congr_ae hdot]
  have hG2 : MemLp G 2 volume := hG_cont.memLp_of_hasCompactSupport hG_cs
  have h2c : (2 : ℝ≥0∞).conjExponent = 2 := by
    simpa [NNReal.HolderConjugate.two_two.conjExponent_eq] using
      (ENNReal.coe_conjExponent (p := (2 : ℝ≥0)) one_lt_two).symm
  have hGc : MemLp G (2 : ℝ≥0∞).conjExponent volume := by
    rwa [h2c]
  rw [integral_complex_ofReal, integral_neg,
    integral_inner_lerayLp_eq_projection ENNReal.one_lt_two ENNReal.ofNat_ne_top (toL2 S) hGc hG2,
    ← L2.inner_def]

/-! ### 6. Per-level Helmholtz approximation -/

private theorem helmholtzApprox_level {Pl : PlanarData} {K : ReturnConsts}
    {L : ReturnLevel} {μ : ℝ}
    (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K)
    (hax : ∀ τ, AxiNoSwirlPt (L.U τ))
    (hperU : ∀ τ y, L.U (τ + 2 * L.ε * cOf L.ν) y = L.U τ y)
    (B : ReturnBase (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν (AffSp K.as))
    (hB : IsExactMultiplier B L.ε⁻¹ L.V L.rb)
    (b : LVel Pl L)
    (hH1 : IsH1Periodic (2 * L.ε * cOf L.ν) (modeBstar L b))
    (φ : SpaceTime → Space)
    (hφ : UnforcedLeray.Short.Interface.IsPeriodicTest (2 * L.ε * cOf L.ν) φ) :
    ∃ ψ : ℕ → SpaceTime → Space,
      (∀ k, UnforcedLeray.Cons.C03.Concrete.IsSolTest (2 * L.ε * cOf L.ν)
        (B0005.cplxT (ψ k))) ∧
      Tendsto (fun k => UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
          (fun x => L0T L.ν (B0005.cplxT (ψ k)) x + (μ : ℂ) • B0005.cplxT (ψ k) x)
          (velPhys L.ε⁻¹ (cOf L.ν) b)) atTop
        (𝓝 (UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
          (fun x => L0T L.ν (B0005.cplxT φ) x + (μ : ℂ) • B0005.cplxT φ x)
          (velPhys L.ε⁻¹ (cOf L.ν) b))) ∧
      Tendsto (fun k => stressPair (2 * L.ε * cOf L.ν)
          (strPhys L.ε⁻¹ (cOf L.ν) (strSum (-(B.M b))))
          (B0005.cplxT (ψ k))) atTop
        (𝓝 ((((2 * L.ε * cOf L.ν)⁻¹ *
          ∫ τ in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν),
            projectedCoupling L.U (modeBstar L b) φ τ : ℝ)) : ℂ)) := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP0 : 0 < 2 * L.ε * cOf L.ν := mul_pos (mul_pos two_pos L.ε_pos) hc
  have : Fact (0 < 2 * L.ε * cOf L.ν) := ⟨hP0⟩
  have hΦ : IsPhaseTest (2 * L.ε * cOf L.ν) (B0005.cplxT φ) := isPhaseTest_cplxT hφ
  obtain ⟨Ac, Nc, ψ, hAc, hNc, hsplit, hcplx, hψ_sol⟩ := real_curl_approx hφ
  let Ψ : ℕ → ℝ × Space → CVec3 := fun k => curlScalar (fun m => cutS k (Ac m))
  refine ⟨ψ, hψ_sol, ?_, ?_⟩
  · -- First Tendsto: `(L0T L.ν + μ)` pairing with `velPhys b`
    let v : Yq (2 * L.ε * cOf L.ν) 2 := B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L b)
    have hv : IsPhaseSolenoidal v :=
      (modeBstar_isY2 L b).isPhaseSolenoidal_of_ae hH1.value.solenoidal
    obtain ⟨h1_lim, h2_lim⟩ := tendsto_curlScalar_add_gradT_cutS L.ν hAc hNc
    rw [hsplit] at h1_lim h2_lim
    have c1 : Tendsto (fun k => phasePair (2 * L.ε * cOf L.ν) 2 (Ψ k + gradT (cutS k Nc)) v)
        atTop (𝓝 (phasePair (2 * L.ε * cOf L.ν) 2 (B0005.cplxT φ) v)) :=
      (((phasePairing (2 * L.ε * cOf L.ν) 2).flip v).continuous.tendsto _).comp h1_lim
    have c2 : Tendsto
        (fun k => phasePair (2 * L.ε * cOf L.ν) 2 (L0T L.ν (Ψ k + gradT (cutS k Nc))) v)
        atTop (𝓝 (phasePair (2 * L.ε * cOf L.ν) 2 (L0T L.ν (B0005.cplxT φ)) v)) :=
      (((phasePairing (2 * L.ε * cOf L.ν) 2).flip v).continuous.tendsto _).comp h2_lim
    have hpair_eq : ∀ {Θ : ℝ × Space → CVec3}, IsPhaseTest (2 * L.ε * cOf L.ν) Θ →
        UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
          (fun x => L0T L.ν Θ x + (μ : ℂ) • Θ x) (velPhys L.ε⁻¹ (cOf L.ν) b) =
        (μ : ℂ) * phasePair (2 * L.ε * cOf L.ν) 2 Θ v +
          phasePair (2 * L.ε * cOf L.ν) 2 (L0T L.ν Θ) v := by
      intro Θ hΘ
      have hfun : (fun x => L0T L.ν Θ x + (μ : ℂ) • Θ x) = (μ : ℂ) • Θ + L0T L.ν Θ := by
        funext x
        simp [add_comm]
      rw [hfun, ← phasePair_toY_modeBstar L b ((hΘ.const_smul (μ : ℂ)).add (isPhaseTest_L0T hΘ L.ν)),
        phasePair_add (hΘ.const_smul (μ : ℂ)) (isPhaseTest_L0T hΘ L.ν),
        phasePair_const_smul hΘ (μ : ℂ)]
    have hk_eq : ∀ k, UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
          (fun x => L0T L.ν (B0005.cplxT (ψ k)) x + (μ : ℂ) • B0005.cplxT (ψ k) x)
          (velPhys L.ε⁻¹ (cOf L.ν) b) =
        (μ : ℂ) * phasePair (2 * L.ε * cOf L.ν) 2 (Ψ k + gradT (cutS k Nc)) v +
          phasePair (2 * L.ε * cOf L.ν) 2 (L0T L.ν (Ψ k + gradT (cutS k Nc))) v := by
      intro k
      have hΨk : IsPhaseTest (2 * L.ε * cOf L.ν) (Ψ k) := by
        dsimp only [Ψ]
        rw [← hcplx k]
        exact (hψ_sol k).1
      have hNk : IsPhaseTest (2 * L.ε * cOf L.ν) (cutS k Nc) := isPhaseTest_cutS hNc k
      have hgk : IsPhaseTest (2 * L.ε * cOf L.ν) (gradT (cutS k Nc)) := hNk.gradT
      have hkill := pressure_kills_gradient L.ν (μ : ℂ) hv hNk
      rw [phasePair_add (hgk.const_smul (μ : ℂ)) (isPhaseTest_L0T hgk L.ν),
        phasePair_const_smul hgk (μ : ℂ)] at hkill
      rw [hcplx k]
      change UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
        (fun x => L0T L.ν (Ψ k) x + (μ : ℂ) • (Ψ k) x) (velPhys L.ε⁻¹ (cOf L.ν) b) = _
      rw [hpair_eq hΨk, L0T_add_wp L.ν hΨk hgk,
        phasePair_add (isPhaseTest_L0T hΨk L.ν) (isPhaseTest_L0T hgk L.ν),
        phasePair_add hΨk hgk]
      linear_combination -hkill
    have hfn : (fun k => UnforcedLeray.Cons.C03.Concrete.pairF (2 * L.ε * cOf L.ν)
          (fun x => L0T L.ν (B0005.cplxT (ψ k)) x + (μ : ℂ) • B0005.cplxT (ψ k) x)
          (velPhys L.ε⁻¹ (cOf L.ν) b)) =
        fun k => (μ : ℂ) * phasePair (2 * L.ε * cOf L.ν) 2 (Ψ k + gradT (cutS k Nc)) v +
          phasePair (2 * L.ε * cOf L.ν) 2 (L0T L.ν (Ψ k + gradT (cutS k Nc))) v :=
      funext hk_eq
    rw [hfn, hpair_eq hΦ]
    exact (c1.const_mul (μ : ℂ)).add c2
  · -- Second Tendsto: `stressPair` limit and evaluation as `projectedCoupling`
    let Tp₀ := strPhys L.ε⁻¹ (cOf L.ν) (strSum (-(B.M b)))
    have hrow : ∀ j, UnforcedLeray.Short.IIb.IsInYr (2 * L.ε * cOf L.ν) 2
        (StressLiftY.rowsOf Tp₀ j) :=
      fun j => StressLiftY.isInYr_rowsOf_strPhys L.ε_pos hc
        (StressLiftY.measurable_strSum (-(B.M b)))
        (StressLiftY.memLp_strSum L.ν_pos hmZ hρ (-(B.M b))) j
    have hexC : ∀ j, ∃ F : Yq (2 * L.ε * cOf L.ν) 2,
        UnforcedLeray.Short.IIb.HasRepY F (StressLiftY.rowsOf Tp₀ j) := by
      intro j
      obtain ⟨F, hF, -⟩ := UnforcedLeray.Short.IIb.exists_hasRepY_q (2 * L.ε * cOf L.ν) 2 two_pos
        (q := 2) ENNReal.ofNat_ne_top (by norm_num) _ (hrow j)
      exact ⟨F, hF⟩
    choose C hC using hexC
    let CL : Fin 3 → Yq (2 * L.ε * cOf L.ν) 2 :=
      fun j => lerayY (2 * L.ε * cOf L.ν) 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (C j)
    have hstress_k : ∀ k, stressPair (2 * L.ε * cOf L.ν) Tp₀ (B0005.cplxT (ψ k)) =
        ∑ j : Fin 3, phasePair (2 * L.ε * cOf L.ν) 2 (dy j (Ψ k + gradT (cutS k Nc))) (CL j) := by
      intro k
      have hΨk_sol : UnforcedLeray.Cons.C03.Concrete.IsSolTest (2 * L.ε * cOf L.ν) (Ψ k) := by
        dsimp only [Ψ]
        rw [← hcplx k]
        exact hψ_sol k
      have hNk : IsPhaseTest (2 * L.ε * cOf L.ν) (cutS k Nc) := isPhaseTest_cutS hNc k
      have hgk : IsPhaseTest (2 * L.ε * cOf L.ν) (gradT (cutS k Nc)) := hNk.gradT
      rw [hcplx k]
      change stressPair (2 * L.ε * cOf L.ν) Tp₀ (Ψ k) = _
      rw [stressPair_eq_sum_phasePair_cols (fun x i j => StressLiftY.strPhys_symm _ _ _ x i j)
        hrow C hC hΨk_sol.1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsol_pair : phasePair (2 * L.ε * cOf L.ν) 2 (dy j (Ψ k)) (C j) =
          phasePair (2 * L.ε * cOf L.ν) 2 (dy j (Ψ k)) (CL j) :=
        (UnforcedLeray.Short.IIb.lerayPairSol 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          (2 * L.ε * cOf L.ν) (C j) (dy j (Ψ k)) (isSolTest_dy hΨk_sol j)).symm
      have hgrad_zero : phasePair (2 * L.ε * cOf L.ν) 2 (dy j (gradT (cutS k Nc))) (CL j) = 0 := by
        rw [dy_gradT_comm hNk.smooth j]
        exact lerayY_isPhaseSolenoidal ENNReal.one_lt_two ENNReal.ofNat_ne_top (C j)
          (dy j (cutS k Nc)) (hNk.dy j)
      rw [dy_add (hΨk_sol.1.smooth.differentiable (by simp))
          (hgk.smooth.differentiable (by simp)) j,
        phasePair_add (hΨk_sol.1.dy j) (hgk.dy j) (CL j), hsol_pair, hgrad_zero, add_zero]
    have hlim_CL : Tendsto
        (fun k => stressPair (2 * L.ε * cOf L.ν) Tp₀ (B0005.cplxT (ψ k))) atTop
        (𝓝 (∑ j : Fin 3, phasePair (2 * L.ε * cOf L.ν) 2 (dy j (B0005.cplxT φ)) (CL j))) := by
      have hfn : (fun k => stressPair (2 * L.ε * cOf L.ν) Tp₀ (B0005.cplxT (ψ k))) =
          fun k => ∑ j : Fin 3,
            phasePair (2 * L.ε * cOf L.ν) 2 (dy j (Ψ k + gradT (cutS k Nc))) (CL j) :=
        funext hstress_k
      rw [hfn]
      refine tendsto_finsetSum _ fun j _ => ?_
      have hdy := tendsto_dy_curlScalar_add_gradT_cutS hAc hNc j
      rw [hsplit] at hdy
      exact (((phasePairing (2 * L.ε * cOf L.ν) 2).flip (CL j)).continuous.tendsto _).comp hdy
    suffices heval :
        (∑ j : Fin 3, phasePair (2 * L.ε * cOf L.ν) 2 (dy j (B0005.cplxT φ)) (CL j)) =
        ((((2 * L.ε * cOf L.ν)⁻¹ * ∫ τ in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν),
          projectedCoupling L.U (modeBstar L b) φ τ : ℝ)) : ℂ) by
      rwa [heval] at hlim_CL
    have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
    have hP_eq : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
    let g₁ : Chart → Ten3 := fun p =>
      NearInst.ten3Of
        (UnforcedLeray.Short.IIIa.symOuter (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.U p)
          (-(b p)))
    have hg_ae : strSum (-(B.M b)) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] g₁ := by
      have hnegM : -(B.M b) = B.M (-b) := (B.M.map_neg b).symm
      rw [hnegM]
      have h1 := strSumExactAE_proved B hc hρ L.ε L.V L.rb hB (-b)
      have h2 := (ageμ_neg_half_absCont_body (cOf L.ν) (gRate Pl) L.ν).ae_le (Lp.coeFn_neg b)
      filter_upwards [h1, h2] with p hp1 hp2
      rw [hp1]
      change NearInst.ten3Of
          (UnforcedLeray.Short.IIIa.symOuter (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.U p)
            ((-b : LVel Pl L) p)) =
        g₁ p
      rw [hp2]
      rfl
    obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
      (s := {p | strSum (-(B.M b)) p ≠ g₁ p}) (μ := ageμ (cOf L.ν) (-1 / 2)) (ae_iff.1 hg_ae)
    have hN5 : ageμ (cOf L.ν) (-5 / 2) N = 0 :=
      NearInst.ageμ_absCont (cOf L.ν) (-5 / 2) (-1 / 2) hN0
    have hnull := NearInst.stressPairAE_null L.ε⁻¹ (cOf L.ν) (2 * L.ε * cOf L.ν)
      hR hc hP_eq N hNm hN5
    have hae_tp : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (2 * L.ε * cOf L.ν))), ∀ᵐ y : Space,
        Tp₀ (t, y) = symProd (L.U t y) (-modeBstar L b t y) := by
      have hU_per : ∀ τ y, L.U (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.U τ y := by
        intro τ y
        rw [← hP_eq]
        exact hperU τ y
      have hcart : ∀ τ x, NearInst.cartLift L.ε⁻¹ (cOf L.ν) g₁ τ x =
          symProd (L.U τ x) (Nv L.ε⁻¹ (perExt (cOf L.ν) (fun p => -(b p))) τ x) :=
        cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.U hR hc hax hU_per (fun p => -(b p))
      filter_upwards [Measure.ae_ae_of_ae_prod hnull] with t ht
      filter_upwards [ht] with y hy
      have hgg : strSum (-(B.M b)) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) y t) =
          g₁ (NearInst.chartOf L.ε⁻¹ (cOf L.ν) y t) := by
        by_contra hne
        exact hy (hsub hne)
      have h1 : Tp₀ (t, y) = NearInst.cartLift L.ε⁻¹ (cOf L.ν) g₁ t y := by
        simp only [Tp₀, strPhys, NearInst.cartLift, hgg]
      rw [h1, hcart t y]
      have hnv : Nv L.ε⁻¹ (perExt (cOf L.ν) (fun p => -(b p))) t y = -modeBstar L b t y := by
        simp [Nv, perExt, modeBstar, map_neg, smul_neg]
      rw [hnv]
    let fC : Fin 3 → ℝ → ℂ := fun j t =>
      ∫ y, dotL (dy j (B0005.cplxT φ) (t, y))
        ((CL j (t : AddCircle (2 * L.ε * cOf L.ν)) : Space → CVec3) y)
    let fR : Fin 3 → ℝ → ℝ := fun j t =>
      -inner ℝ (toL2 (symTensorColumns (L.U t) (modeBstar L b t) j))
        (Leray.projection (toL2 (testPartial (slice φ t) j)))
    have hf_ae : ∀ j : Fin 3, fC j =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * L.ε * cOf L.ν))]
        fun t => ((fR j t : ℝ) : ℂ) := by
      intro j
      have hCL_ae : ∀ᵐ t : ℝ, CL j (t : AddCircle (2 * L.ε * cOf L.ν)) =
          lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
            (C j (t : AddCircle (2 * L.ε * cOf L.ν))) :=
        UnforcedLeray.PhaseTrace.ae_comp_mk
          (coeFn_lerayY ENNReal.one_lt_two ENNReal.ofNat_ne_top (C j))
      filter_upwards [hae_tp, ae_restrict_of_ae ((hC j).slice), ae_restrict_of_ae hCL_ae]
        with t htp hCs hCLs
      have hCj_ae : (C j (t : AddCircle (2 * L.ε * cOf L.ν)) : Space → CVec3) =ᵐ[volume]
          fun y => -ofReV (symTensorColumns (L.U t) (modeBstar L b t) j y) := by
        filter_upwards [hCs, htp] with y hyC hyT
        rw [← hyC]
        ext i
        simp [StressLiftY.rowsOf, hyT, symProd, symTensorColumns]
      have hdy_eq : ∀ y, dy j (B0005.cplxT φ) (t, y) = ofReV (testPartial (slice φ t) j y) :=
        dy_cplxT_eq_ofReV_testPartial hφ.smooth j t
      have hG_eq : testPartial (slice φ t) j = fun y => reV (dy j (B0005.cplxT φ) (t, y)) := by
        funext y
        rw [hdy_eq y]
        ext i
        simp
      have hG_cont : Continuous (testPartial (slice φ t) j) := by
        rw [hG_eq]
        exact reV.continuous.comp
          ((hΦ.dy j).smooth.continuous.comp (continuous_const.prodMk continuous_id))
      have hG_cs : HasCompactSupport (testPartial (slice φ t) j) := by
        rw [hG_eq]
        exact ((hΦ.dy j).hasCompactSupport_slice t).comp_left reV.map_zero
      change ∫ y, dotL (dy j (B0005.cplxT φ) (t, y))
        ((CL j (t : AddCircle (2 * L.ε * cOf L.ν)) : Space → CVec3) y) = ((fR j t : ℝ) : ℂ)
      rw [hCLs]
      simp_rw [hdy_eq]
      exact slice_leray_eq_inner hG_cont hG_cs hCj_ae
    have hfC_int : ∀ j : Fin 3,
        Integrable (fC j) (volume.restrict (Ioc (0 : ℝ) (2 * L.ε * cOf L.ν))) :=
      fun j => integrableOn_period_phasePair (hΦ.dy j) (CL j)
    have hfR_int : ∀ j : Fin 3,
        Integrable (fR j) (volume.restrict (Ioc (0 : ℝ) (2 * L.ε * cOf L.ν))) := by
      intro j
      have hc_int : Integrable (fun t => ((fR j t : ℝ) : ℂ))
          (volume.restrict (Ioc (0 : ℝ) (2 * L.ε * cOf L.ν))) :=
        (hfC_int j).congr (hf_ae j)
      simpa using Complex.reCLM.integrable_comp hc_int
    have hpair_j : ∀ j : Fin 3,
        phasePair (2 * L.ε * cOf L.ν) 2 (dy j (B0005.cplxT φ)) (CL j) =
          (2 * L.ε * cOf L.ν)⁻¹ •
            (((∫ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), fR j t : ℝ)) : ℂ) := by
      intro j
      rw [phasePair_eq_periodIntegral (hΦ.dy j) (CL j), zero_add]
      change (2 * L.ε * cOf L.ν)⁻¹ • (∫ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), fC j t) = _
      rw [integral_congr_ae (hf_ae j), integral_complex_ofReal]
    simp_rw [hpair_j, ← Finset.smul_sum]
    rw [Complex.real_smul, Complex.ofReal_mul]
    congr 1
    rw [← Complex.ofReal_sum, ← integral_finsetSum Finset.univ (fun j _ => hfR_int j)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [fR, projectedCoupling, lerayDivPairing, Finset.sum_neg_distrib]

end HelmholtzApproxAux

open HelmholtzApproxAux
open UnforcedLeray.Short.PartIIIb.Concrete

theorem helmholtzApprox_proved :
    UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.HelmholtzApprox := by
  intro D dm dp hst n hact z _hz _hne _hp _hμ0 _hμ1 B hB b hH1 φ hφ
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hρ : 0 < (D.level n).ρb D.Pl D.K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((D.level n).params D.Pl).ν := (D.level n).ν_pos
    have h2 : 0 < ((D.level n).params D.Pl).ε := (D.level n).ε_pos
    have := hst.C0_pos
    positivity
  have hax : ∀ τ, AxiNoSwirlPt ((D.level n).U τ) :=
    axiNoSwirlPt_of_ballSplit ((D.level n).params D.Pl) hact.ball hact.profile.smoothU
  exact helmholtzApprox_level hmZ hρ hax hact.profile.periodicU B hB b hH1 φ hφ
