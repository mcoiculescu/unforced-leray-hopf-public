import UnforcedLeray.Units.B0005.Bridge.Weak
import UnforcedLeray.Units.B0005.Unique
import UnforcedLeray.Analysis.Heat.KernelEvolution
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# B0447, part 1: the phase identity `νΔw = a` holds on almost every phase slice

Blueprint unit B0447 (`eq:free-stress-20`, `eq:free-stress-21`), `paper/main.tex` lines
7635–7661. The second line of (20), `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart` (tex 7645), is a
statement about the spatial slices of `w`, because the comoving chart
`(t, z) ↦ (τ₀ + t, e^{-t/2}(y₀ + √ν z))` (tex 7640) maps the slice `{t} × ℝ³` affinely onto
the phase slice `{τ₀ + t} × ℝ³`. This file proves the slice form of the free-graph identity
`νΔw = a` (`HasPhaseOp (nuLapT ν) w a`, unit B0411, tex 7322–7327):

* `slice_identity_ae`: for each spatial test `ψ` and `e ∈ ℂ³`, for a.e. `τ ∈ ℝ`,
  `ν ∫ Δψ e · w(τ) = ∫ ψ e · a(τ)`. The periodization of the product test `φ(τ) ψ(y) e`
  (`B0005.prodTest`, `PhaseTrace.perT`) is a phase test, the Laplacian commutes with
  periodization (`B0005.lapT_perT`) and falls on `ψ` (`lapT_prodTest`), the pairing unfolds
  (`PhaseTrace.phasePair_perT`), and Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
  removes the time test `φ`.
* `slice_identity_ae_all` (`1 < q`): the null set can be chosen independently of `(ψ, e)`,
  i.e. `νΔ w(τ) = a(τ)` in `D'(ℝ³)` for a.e. `τ`. The pairs `(ψ e, Δψ e)` form a subset of the
  second-countable space `L^{q'} × L^{q'}` (`q' < ∞` because `q > 1`), which has a countable
  dense subset; the defect is continuous on `L^{q'} × L^{q'}` for each fixed `τ`.

The spatial Laplacian of a test is the library's Cartesian `Heat.laplacian`
(`lean/UnforcedLeray/Analysis/Heat/KernelEvolution.lean`).

Status: infrastructure for `Units/B0447.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0447

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Spatial tests and their Laplacian -/

theorem contDiff_fderiv_apply {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y v) :=
  (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_laplacian {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (Heat.laplacian ψ) := by
  show ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ ψ y (coordinateVector i)) x (coordinateVector i))
  exact ContDiff.sum fun i _ => contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _

theorem hasCompactSupport_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Space → ℝ}
    (hf : ∀ i, HasCompactSupport (f i)) : HasCompactSupport (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih

theorem hasCompactSupport_laplacian {ψ : Space → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (Heat.laplacian ψ) := by
  show HasCompactSupport (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ ψ y (coordinateVector i)) x (coordinateVector i))
  exact hasCompactSupport_finsetSum _ fun i =>
    (hψc.fderiv_apply (𝕜 := ℝ) (coordinateVector i)).fderiv_apply (𝕜 := ℝ) (coordinateVector i)

/-! ### The Laplacian of a product test -/

theorem dy_prodTest {φ : ℝ → ℝ} {g : Space → ℝ} (hφ : Differentiable ℝ φ)
    (hg : Differentiable ℝ g) (e : CVec3) (j : Fin 3) :
    dy j (B0005.prodTest φ g e) =
      B0005.prodTest φ (fun y => fderiv ℝ g y (coordinateVector j)) e := by
  funext p
  have hS : DifferentiableAt ℝ (fun p : ℝ × Space => φ p.1 * g p.2) p :=
    ((hφ.comp differentiable_fst).mul (hg.comp differentiable_snd)) p
  have hF : fderiv ℝ (B0005.prodTest φ g e) p =
      (fderiv ℝ (fun p : ℝ × Space => φ p.1 * g p.2) p).smulRight e :=
    fderiv_smul_const hS e
  have hline : HasDerivAt
      (fun s : ℝ => (fun p : ℝ × Space => φ p.1 * g p.2) (p + s • ((0 : ℝ), coordinateVector j)))
      (φ p.1 * fderiv ℝ g p.2 (coordinateVector j)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => p.2 + s • coordinateVector j)
        ((1 : ℝ) • coordinateVector j) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).smul_const _).const_add _
    have h4 := (hg p.2).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have h5 := h4.const_mul (φ p.1)
    rw [one_smul] at h5
    refine h5.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp
  have hd := fderiv_apply_of_hasDerivAt hS hline
  simp only [dy, hF, ContinuousLinearMap.smulRight_apply, hd, B0005.prodTest]

/-- `Δ_y (φ(τ) ψ(y) e) = φ(τ) (Δψ)(y) e`. -/
theorem lapT_prodTest {φ : ℝ → ℝ} {ψ : Space → ℝ} (hφ : Differentiable ℝ φ)
    (hψ : ContDiff ℝ ∞ ψ) (e : CVec3) :
    lapT (B0005.prodTest φ ψ e) = B0005.prodTest φ (Heat.laplacian ψ) e := by
  funext p
  have h1 : ∀ j, dy j (B0005.prodTest φ ψ e) =
      B0005.prodTest φ (fun y => fderiv ℝ ψ y (coordinateVector j)) e :=
    fun j => dy_prodTest hφ (hψ.differentiable (by simp)) e j
  have h2 : ∀ j, dy j (B0005.prodTest φ (fun y => fderiv ℝ ψ y (coordinateVector j)) e) =
      B0005.prodTest φ (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y (coordinateVector j)) y
        (coordinateVector j)) e :=
    fun j => dy_prodTest hφ ((contDiff_fderiv_apply hψ _).differentiable (by simp)) e j
  simp only [lapT, h1, h2, B0005.prodTest, Heat.laplacian, Finset.mul_sum, Finset.sum_smul]

/-! ### The slice identity for one test -/

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

theorem locallyIntegrable_clm_comp {u : ℝ → Lp CVec3 q (volume : Measure Space)}
    (hu : LocallyIntegrable u volume) (L : Lp CVec3 q (volume : Measure Space) →L[ℝ] ℂ) :
    LocallyIntegrable (fun t => L (u t)) volume := by
  rw [locallyIntegrable_iff] at hu ⊢
  intro K hK
  exact L.integrable_comp (hu K hK)

/-- **Slice identity, one test.** If `νΔw = a` in distributions on `Y_q` (tex 7322–7327),
then for each smooth compactly supported `ψ : ℝ³ → ℝ` and `e ∈ ℂ³`, for a.e. `τ ∈ ℝ`,
`ν ∫ Δψ(y) e · w(τ)(y) dy = ∫ ψ(y) e · a(τ)(y) dy`. -/
theorem slice_identity_ae {ν : ℝ} {w a : Yq P q} (h : HasPhaseOp (nuLapT ν) w a)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    ∀ᵐ τ : ℝ ∂volume,
      (ν : ℂ) * ∫ y, Heat.laplacian ψ y • dotL e ((w (τ : AddCircle P) : Space → CVec3) y) =
        ∫ y, ψ y • dotL e ((a (τ : AddCircle P) : Space → CVec3) y) := by
  have hΔ := contDiff_laplacian hψ
  have hΔc := hasCompactSupport_laplacian hψc
  obtain ⟨L1, hL1⟩ := exists_ell (q := q) hΔ.continuous hΔc e
  obtain ⟨L2, hL2⟩ := exists_ell (q := q) hψ.continuous hψc e
  set wt : ℝ → Lp CVec3 q (volume : Measure Space) := fun t => w (t : AddCircle P) with hwt
  set at' : ℝ → Lp CVec3 q (volume : Measure Space) := fun t => a (t : AddCircle P) with hat
  have hw_loc : LocallyIntegrable wt volume := B0005.locallyIntegrable_comp_mk w
  have ha_loc : LocallyIntegrable at' volume := B0005.locallyIntegrable_comp_mk a
  have hw1 := locallyIntegrable_clm_comp hw_loc L1
  have ha2 := locallyIntegrable_clm_comp ha_loc L2
  set f : ℝ → ℂ := fun t => (ν : ℂ) * L1 (wt t) - L2 (at' t) with hf
  have hf_loc : LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff] at hw1 ha2 ⊢
    intro K hK
    exact ((hw1 K hK).const_mul (ν : ℂ)).sub (ha2 K hK)
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ), f t = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf_loc fun φ hφ hφc => ?_
    obtain ⟨A, B, hAB, hφAB⟩ := B0005.exists_Icc_of_hasCompactSupport hφc
    have hG0 := B0005.isPhaseTest_prodTest hφ hψ hψc e
    have hGT := B0005.timeSupp_prodTest hφAB ψ e
    have hH0 := B0005.isPhaseTest_prodTest hφ hΔ hΔc e
    have hHT := B0005.timeSupp_prodTest hφAB (Heat.laplacian ψ) e
    have hΦ := isPhaseTest_perT hP.out hGT hG0
    have hΨ := isPhaseTest_perT hP.out hHT hH0
    have key := h _ hΦ
    have hlap : nuLapT ν (perT P (B0005.prodTest φ ψ e)) =
        ν • perT P (B0005.prodTest φ (Heat.laplacian ψ) e) := by
      simp only [nuLapT]
      rw [B0005.lapT_perT hP.out hGT hG0.smooth,
        lapT_prodTest (hφ.differentiable (by simp)) hψ]
    rw [hlap, phasePair_real_smul hΨ, phasePair_perT hH0 hAB hHT,
      phasePair_perT hG0 hAB hGT] at key
    have hpw : ∀ t, pairH hH0 w t = φ t • L1 (wt t) := fun t => by
      rw [B0005.pairH_prodTest, hL1]
    have hpa : ∀ t, pairH hG0 a t = φ t • L2 (at' t) := fun t => by
      rw [B0005.pairH_prodTest, hL2]
    simp_rw [hpw, hpa] at key
    have hI1 : Integrable (fun t => φ t • L1 (wt t)) :=
      hw1.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hI2 : Integrable (fun t => φ t • L2 (at' t)) :=
      ha2.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hP' : ((P⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero hP.out.ne'
    have key' : (ν : ℂ) * ∫ t, φ t • L1 (wt t) = ∫ t, φ t • L2 (at' t) := by
      rw [Complex.real_smul, Complex.real_smul, ← mul_assoc, mul_comm (ν : ℂ), mul_assoc] at key
      exact mul_left_cancel₀ hP' key
    calc ∫ t, φ t • f t = ∫ t, ((ν : ℂ) * (φ t • L1 (wt t)) - φ t • L2 (at' t)) := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [hf, smul_sub, Complex.real_smul]
          ring
      _ = (ν : ℂ) * (∫ t, φ t • L1 (wt t)) - ∫ t, φ t • L2 (at' t) := by
          rw [integral_sub (hI1.const_mul _) hI2, integral_const_mul]
      _ = 0 := by rw [key', sub_self]
  filter_upwards [hzero] with t ht
  rw [← hL1, ← hL2]
  exact sub_eq_zero.mp ht

/-! ### One null set for all tests -/

omit hq in
theorem conjExp_ne_top (hq1 : 1 < q) : conjExp q ≠ (⊤ : ℝ≥0∞) := by
  unfold conjExp
  rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
  exact ENNReal.inv_lt_one.mpr hq1

/-- Pairing an `L^{q'}` representative of `ψ e` with `g ∈ L^q`. -/
theorem innerPair_testVec {u : Lp CVec3 (conjExp q) (volume : Measure Space)} {ψ : Space → ℝ}
    {e : CVec3} (hu : (u : Space → CVec3) =ᵐ[volume] fun y => ψ y • e)
    (g : Lp CVec3 q (volume : Measure Space)) :
    innerPair q u g = ∫ y, ψ y • dotL e ((g : Space → CVec3) y) := by
  rw [innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [hu] with y hy
  rw [hy, ContinuousLinearMap.map_smul_of_tower, smul_apply]

/-- **Slice identity, all tests at once** (`1 < q`). If `νΔw = a` in distributions on `Y_q`,
then for a.e. `τ ∈ ℝ`, `νΔ(w(τ)) = a(τ)` in distributions on `ℝ³`: for every smooth compactly
supported `ψ : ℝ³ → ℝ` and `e ∈ ℂ³`, `ν ∫ Δψ e · w(τ) = ∫ ψ e · a(τ)`. -/
theorem slice_identity_ae_all (hq1 : 1 < q) {ν : ℝ} {w a : Yq P q}
    (h : HasPhaseOp (nuLapT ν) w a) :
    ∀ᵐ τ : ℝ ∂volume, ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ e : CVec3,
      (ν : ℂ) * ∫ y, Heat.laplacian ψ y • dotL e ((w (τ : AddCircle P) : Space → CVec3) y) =
        ∫ y, ψ y • dotL e ((a (τ : AddCircle P) : Space → CVec3) y) := by
  have : Fact (conjExp q ≠ (⊤ : ℝ≥0∞)) := ⟨conjExp_ne_top hq1⟩
  let T : Set (Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) :=
    {x | ∃ ψ : Space → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∃ e : CVec3,
      (x.1 : Space → CVec3) =ᵐ[volume] (fun y => ψ y • e) ∧
      (x.2 : Space → CVec3) =ᵐ[volume] (fun y => Heat.laplacian ψ y • e)}
  let F : ℝ → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space) → ℂ := fun τ x =>
    (ν : ℂ) * innerPair q x.2 (w (τ : AddCircle P)) - innerPair q x.1 (a (τ : AddCircle P))
  have hFcont : ∀ τ, Continuous (F τ) := fun τ =>
    (continuous_const.mul
      (((innerPair q).flip (w (τ : AddCircle P))).continuous.comp continuous_snd)).sub
      (((innerPair q).flip (a (τ : AddCircle P))).continuous.comp continuous_fst)
  have hFT : ∀ x ∈ T, ∀ᵐ τ : ℝ ∂volume, F τ x = 0 := by
    rintro x ⟨ψ, hψ, hψc, e, h1, h2⟩
    filter_upwards [slice_identity_ae h hψ hψc e] with τ hτ
    simp only [F]
    rw [innerPair_testVec h2, innerPair_testVec h1, hτ, sub_self]
  have hsc1 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space)) :=
    inferInstance
  have hsc : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  have hsT : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology T
  have hsep : TopologicalSpace.SeparableSpace T := inferInstance
  obtain ⟨s, hs, hsd⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable s := hs.to_subtype
  have hall : ∀ᵐ τ : ℝ ∂volume, ∀ x : s, F τ (x : T).1 = 0 := by
    rw [ae_all_iff]
    intro x
    exact hFT _ (x : T).2
  filter_upwards [hall] with τ hτ
  have hzero : (fun x : T => F τ x.1) = fun _ => 0 :=
    Continuous.ext_on hsd ((hFcont τ).comp continuous_subtype_val) continuous_const
      (fun x hx => hτ ⟨x, hx⟩)
  intro ψ hψ hψc e
  have hm1 := memLp_testVec hψ.continuous hψc e (conjExp q)
  have hm2 := memLp_testVec (contDiff_laplacian hψ).continuous
    (hasCompactSupport_laplacian hψc) e (conjExp q)
  have hxT : (hm1.toLp _, hm2.toLp _) ∈ T := ⟨ψ, hψ, hψc, e, hm1.coeFn_toLp, hm2.coeFn_toLp⟩
  have h0 := congrFun hzero ⟨_, hxT⟩
  simp only [F] at h0
  rw [innerPair_testVec hm2.coeFn_toLp, innerPair_testVec hm1.coeFn_toLp] at h0
  exact sub_eq_zero.mp h0

end UnforcedLeray.B0447
