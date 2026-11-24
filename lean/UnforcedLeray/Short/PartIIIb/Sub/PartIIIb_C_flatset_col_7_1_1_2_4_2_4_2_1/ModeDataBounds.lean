import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.MeridTestDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.MeridTestBounded
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoeffPdQ
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoeffNormLe
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoeffDEta
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# `ModeDataBounds` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/14`)

Source of record `the November 2 reference manuscript`
lines 1713-1727: the inverse `q`-derivative costs `|k|⁻¹`, so two integrations by parts in `q` give
`‖ĝ(n)‖ ≤ M / k_n²` for every band test `g`; the `η`-derivative commutes with the `q`-coefficient.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- The mode frequency `k_n = 2π n / c` is nonzero for `n ≠ 0`. -/
theorem mdb_nzk_ne {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) : nzk c n ≠ 0 := by
  unfold nzk
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn') hc.ne'

/-- `∂_η` of a `j`-th component of a `q`-coefficient is the `j`-th component of the `q`-coefficient
of `∂_η h` (the coordinate map is a continuous linear map, and `coeffDEta` commutes `∂_η`). -/
theorem mdb_coord_dEta (c : ℝ) (n : ℤ) (h : Profile → MeridC) (hh : ContDiff ℝ ∞ h) (j : Fin 2)
    (x : ℝ × ℝ) :
    dEta2 (fun y => nzCoeff c n h y j) x = nzCoeff c n (pdEta h) x j := by
  have hD : ContDiff ℝ ∞ (nzCoeff c n h) := nztt_coeff_smooth intervalParamSmooth_proof c n h hh
  have hdiff : DifferentiableAt ℝ (nzCoeff c n h) x :=
    (hD.differentiable (by simp)).differentiableAt
  let L : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj j : MeridC →L[ℂ] ℂ).restrictScalars ℝ
  have hL : HasFDerivAt (fun y => L (nzCoeff c n h y)) (L.comp (fderiv ℝ (nzCoeff c n h) x)) x :=
    L.hasFDerivAt.comp x hdiff.hasFDerivAt
  have hcoeff := coeffDEta c h hh n x
  unfold dEta2
  show fderiv ℝ (fun y => L (nzCoeff c n h y)) x (0, 1) = _
  rw [hL.fderiv, ContinuousLinearMap.comp_apply, hcoeff]
  rfl

/-- A band test has `q`-coefficients of size `O(k_n⁻²)` uniformly in `(s, η)`. -/
theorem mdb_bound_of_test {c : ℝ} (hc : 0 < c) {h : Profile → MeridC} (hh : IsMeridTest c h) :
    ∃ M : ℝ, ∀ n : ℤ, n ≠ 0 → ∀ x : ℝ × ℝ, ‖nzCoeff c n h x‖ ≤ M / nzk c n ^ 2 := by
  have hq := meridTestDeriv c h hh
  have hqq := meridTestDeriv c (pdQ h) hq.1
  obtain ⟨M, hM⟩ := meridTestBounded c hc (pdQ (pdQ h)) hqq.1
  refine ⟨M, fun n hn x => ?_⟩
  have hk := mdb_nzk_ne hc hn
  have h1 := coeffPdQ c hc (pdQ h) hq.1 n x
  have h2 := coeffPdQ c hc h hh n x
  have hI : ‖(Complex.I * (nzk c n : ℂ))‖ = |nzk c n| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 : ‖nzCoeff c n (pdQ (pdQ h)) x‖ = nzk c n ^ 2 * ‖nzCoeff c n h x‖ := by
    rw [h1, h2, smul_smul, norm_smul, norm_mul, hI, ← sq_abs (nzk c n)]
    ring
  have hle : ‖nzCoeff c n (pdQ (pdQ h)) x‖ ≤ M :=
    coeffNormLe c hc (pdQ (pdQ h)) M hqq.1.smooth.continuous hM n x
  have hpos : 0 < nzk c n ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))
  rw [h3] at hle
  rw [le_div_iff₀ hpos, mul_comm]
  exact hle

/-- **Task target: the mode data bounds** (source 1713-1727). -/
theorem modeDataBounds : ModeDataBounds := by
  intro c hc f hf
  obtain ⟨-, hg, -⟩ := fOsc_isMeridTest hc hf
  have hpg : IsMeridTest c (pdEta (fOsc c f)) := (meridTestDeriv c _ hg).2
  have hppg : IsMeridTest c (pdEta (pdEta (fOsc c f))) := (meridTestDeriv c _ hpg).2
  obtain ⟨M1, hM1⟩ := mdb_bound_of_test hc hg
  obtain ⟨M2, hM2⟩ := mdb_bound_of_test hc hpg
  obtain ⟨M3, hM3⟩ := mdb_bound_of_test hc hppg
  refine ⟨|M1| + |M2| + |M3|, fun n hn x => ?_⟩
  have key : ∀ a b : ℝ, a ≤ b → a / nzk c n ^ 2 ≤ b / nzk c n ^ 2 := fun a b hab => by gcongr
  have hD1 : M1 / nzk c n ^ 2 ≤ (|M1| + |M2| + |M3|) / nzk c n ^ 2 :=
    key _ _ (by linarith [le_abs_self M1, abs_nonneg M2, abs_nonneg M3])
  have hD2 : M2 / nzk c n ^ 2 ≤ (|M1| + |M2| + |M3|) / nzk c n ^ 2 :=
    key _ _ (by linarith [le_abs_self M2, abs_nonneg M1, abs_nonneg M3])
  have hD3 : M3 / nzk c n ^ 2 ≤ (|M1| + |M2| + |M3|) / nzk c n ^ 2 :=
    key _ _ (by linarith [le_abs_self M3, abs_nonneg M1, abs_nonneg M2])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (PiLp.norm_apply_le (nzCoeff c n (fOsc c f) x) 1)
      (le_trans (hM1 n hn x) hD1)
  · have e : dEta2 (coefR c f n) x = nzCoeff c n (pdEta (fOsc c f)) x 0 :=
      mdb_coord_dEta c n (fOsc c f) hg.smooth 0 x
    rw [e]
    exact le_trans (PiLp.norm_apply_le (nzCoeff c n (pdEta (fOsc c f)) x) 0)
      (le_trans (hM2 n hn x) hD2)
  · have e : dEta2 (coefZ c f n) x = nzCoeff c n (pdEta (fOsc c f)) x 1 :=
      mdb_coord_dEta c n (fOsc c f) hg.smooth 1 x
    rw [e]
    exact le_trans (PiLp.norm_apply_le (nzCoeff c n (pdEta (fOsc c f)) x) 1)
      (le_trans (hM2 n hn x) hD2)
  · have e1 : dEta2 (coefR c f n) = fun y => nzCoeff c n (pdEta (fOsc c f)) y 0 :=
      funext fun y => mdb_coord_dEta c n (fOsc c f) hg.smooth 0 y
    have e2 : dEta2 (dEta2 (coefR c f n)) x = nzCoeff c n (pdEta (pdEta (fOsc c f))) x 0 := by
      rw [e1]
      exact mdb_coord_dEta c n (pdEta (fOsc c f)) hpg.smooth 0 x
    rw [e2]
    exact le_trans (PiLp.norm_apply_le (nzCoeff c n (pdEta (pdEta (fOsc c f))) x) 0)
      (le_trans (hM3 n hn x) hD3)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
