import UnforcedLeray.Lib.Parabolic.Fundamental
import UnforcedLeray.Lib.Parabolic.LqBound

/-!
# The `q = 2` case of eq:free-stress-11, distributional form (INF02 T8 at `q = 2`, T10)


targets T8 (at `q = 2`) and T10 ("eq:11 at `q = 2` with constant 1, from T6 and the `q = 2`
part of T8, with no CZ"). Manuscript: eq:free-stress-11 (`paper/main.tex` lines 7447–7477,
blueprint unit B0423) at `q = 2`.

This file: calculus helpers for the identification.

* `dirD_comm`, `contDiff_dirD`, `dirD_mul`, `tD_comp_trev`, `dirD_comp_smul`.
* `backTest_heatAdj`: the backward test `Ψ = backTest ν i j φ` solves
  `-∂_t Ψ - νΔΨ = ∂_i∂_j φ` (from the fundamental solution identity `duhamel_heatOp`).
* `sD_backTest`: `∂_k Ψ = backTest ν i j (∂_k φ)`, so `∇Ψ ∈ L²`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section Calculus

theorem contDiff_dirD {f : PS d → ℝ} (hf : ContDiff ℝ ∞ f) (v : PS d) :
    ContDiff ℝ ∞ (dirD v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dirD_dirD_eq' {f : PS d → ℝ} (hf : ContDiff ℝ ∞ f) (u w X : PS d) :
    dirD u (dirD w f) X = fderiv ℝ (fderiv ℝ f) X u w := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  show fderiv ℝ (fun y => fderiv ℝ f y w) X u = _
  rw [fderiv_clm_apply (hd X) (differentiableAt_const w)]
  simp

theorem dirD_comm {f : PS d → ℝ} (hf : ContDiff ℝ ∞ f) (u w : PS d) :
    dirD u (dirD w f) = dirD w (dirD u f) := by
  funext X
  rw [dirD_dirD_eq' hf, dirD_dirD_eq' hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem dirD_mul {f g : PS d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v : PS d) : dirD v (fun X => f X * g X) = fun X => f X * dirD v g X + g X * dirD v f X := by
  funext X
  simp only [dirD]
  have h : HasFDerivAt (fun X => f X * g X) (f X • fderiv ℝ g X + g X • fderiv ℝ f X) X :=
    (hf X).hasFDerivAt.mul (hg X).hasFDerivAt
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem tD_comp_trev {g : PS d → ℝ} (hg : Differentiable ℝ g) :
    tD (g ∘ trev) = fun X => -tD g (trev X) := by
  funext X
  simp only [tD, dirD]
  have h : HasFDerivAt (g ∘ trev) ((fderiv ℝ g (trev X)).comp (trevCLM d)) X := by
    rw [trev_eq_clm]; exact (hg (trevCLM d X)).hasFDerivAt.comp X (trevCLM d).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have e : trevCLM d tdir = (-1 : ℝ) • (tdir : PS d) := by
    ext <;> simp [trevCLM]
  rw [e, map_smul, smul_eq_mul, neg_one_mul]

theorem dirD_comp_smul {f : PS d → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (v : PS d) :
    dirD v (fun X => f (c • X)) = fun X => c * dirD v f (c • X) := by
  funext X
  simp only [dirD]
  have h : HasFDerivAt (fun X : PS d => f (c • X)) ((fderiv ℝ f (c • X)).comp
      (c • ContinuousLinearMap.id ℝ (PS d))) X :=
    (hf (c • X)).hasFDerivAt.comp X ((hasFDerivAt_id (𝕜 := ℝ) X).const_smul c)
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  simp [map_smul, smul_eq_mul]

end Calculus

section BackTest

variable {ν : ℝ}

theorem contDiff_backTest (hν : 0 < ν) {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d) :
    ContDiff ℝ ∞ (backTest ν i j φ) := by
  unfold backTest secondDerivTest
  rw [trev_eq_clm]
  exact (contDiff_duhamel hν (hφ.comp_trev.sD2 i j)).comp (trevCLM d).contDiff

/-- `sLap (w ∘ trev) = (sLap w) ∘ trev` for `C^∞` `w`. -/
theorem sLap_comp_trev {w : PS d → ℝ} (hw : ContDiff ℝ ∞ w) :
    sLap (w ∘ trev) = (sLap w) ∘ trev := by
  funext X
  simp only [sLap, Function.comp_apply]
  congr 1; funext k
  show sD k (sD k (w ∘ trev)) X = sD k (sD k w) (trev X)
  rw [dirD_comp_trev (hw.differentiable (by simp)) k,
    dirD_comp_trev ((contDiff_dirD hw _).differentiable (by simp)) k]
  rfl

/-- **The backward test solves the backward heat equation.**
`-∂_t Ψ - νΔΨ = ∂_i∂_j φ` for `Ψ = backTest ν i j φ`. -/
theorem backTest_heatAdj (hν : 0 < ν) {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d) (X : PS d) :
    -tD (backTest ν i j φ) X - ν * sLap (backTest ν i j φ) X = sD2 i j φ X := by
  set A := sD2 i j (φ ∘ trev) with hAdef
  have hA : IsSTTest A := hφ.comp_trev.sD2 i j
  set w := duhamel ν A with hwdef
  have hw : ContDiff ℝ ∞ w := contDiff_duhamel hν hA
  have hbt : backTest ν i j φ = w ∘ trev := rfl
  rw [hbt, tD_comp_trev (hw.differentiable (by simp)), sLap_comp_trev hw]
  simp only [Function.comp_apply, neg_neg]
  -- `tD w - ν sLap w = A`
  have htD : tD w = duhamel ν (tD A) := dirD_duhamel hν hA tdir
  have hsD2 : ∀ k : Fin d, sD2 k k w = duhamel ν (sD2 k k A) := by
    intro k
    unfold sD2 sD
    rw [dirD_duhamel hν hA, dirD_duhamel hν (hA.dirD _)]
  have hFS := congrFun (duhamel_heatOp hν hA) (trev X)
  have hlin : duhamel ν (tD A - ν • sLap A) (trev X) =
      duhamel ν (tD A) (trev X) - ν * ∑ k : Fin d, duhamel ν (sD2 k k A) (trev X) := by
    simp only [duhamel]
    have i1 := integrable_causalHeat_mul hν (hA.dirD tdir).continuous (hA.dirD tdir).2 (trev X)
    have i2 : ∀ k : Fin d, Integrable (fun Y => causalHeat ν Y * sD2 k k A (trev X - Y)) volume :=
      fun k => integrable_causalHeat_mul hν (hA.sD2 k k).continuous (hA.sD2 k k).2 (trev X)
    have hpt : ∀ Y, causalHeat ν Y * (tD A - ν • sLap A) (trev X - Y) =
        causalHeat ν Y * tD A (trev X - Y) -
          ν * ∑ k : Fin d, causalHeat ν Y * sD2 k k A (trev X - Y) := by
      intro Y
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sLap]
      have hs : ∑ k : Fin d, causalHeat ν Y * sD2 k k A (trev X - Y) =
          causalHeat ν Y * ∑ k : Fin d, sD2 k k A (trev X - Y) := by rw [Finset.mul_sum]
      rw [hs]; ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub i1
      ((integrable_finsetSum _ fun k _ => i2 k).const_mul ν), integral_const_mul,
      integral_finsetSum _ fun k _ => i2 k]
  have hsl : sLap w (trev X) = ∑ k : Fin d, duhamel ν (sD2 k k A) (trev X) := by
    simp only [sLap]; congr 1; funext k; rw [hsD2 k]
  rw [htD, hsl, ← hlin, hFS, hAdef, sD2_comp_trev hφ i j]
  simp

/-- `∂_k (backTest ν i j φ) = backTest ν i j (∂_k φ)`. -/
theorem sD_backTest (hν : 0 < ν) {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j k : Fin d) :
    sD k (backTest ν i j φ) = backTest ν i j (sD k φ) := by
  have hA : IsSTTest (sD2 i j (φ ∘ trev)) := hφ.comp_trev.sD2 i j
  have hw : ContDiff ℝ ∞ (duhamel ν (sD2 i j (φ ∘ trev))) := contDiff_duhamel hν hA
  unfold backTest secondDerivTest
  rw [dirD_comp_trev (hw.differentiable (by simp)) k]
  have e1 : sD k (duhamel ν (sD2 i j (φ ∘ trev))) = duhamel ν (sD k (sD2 i j (φ ∘ trev))) :=
    dirD_duhamel hν hA _
  have e2 : sD k φ ∘ trev = sD k (φ ∘ trev) := (dirD_comp_trev hφ.differentiable k).symm
  rw [e1, e2]
  congr 2
  have hc := hφ.comp_trev
  show dirD (sdir k) (dirD (sdir i) (dirD (sdir j) (φ ∘ trev))) =
    dirD (sdir i) (dirD (sdir j) (dirD (sdir k) (φ ∘ trev)))
  rw [dirD_comm (contDiff_dirD hc.1 _) (sdir k) (sdir i), dirD_comm hc.1 (sdir k) (sdir j)]

end BackTest

section Cutoff

/-- A fixed bump, `1` on the unit ball. -/
def bump1 (d : ℕ) : ContDiffBump (0 : PS d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The scaled cutoffs `ψ_n(X) = ψ_1(X / (n+1))`. -/
def scut (n : ℕ) (X : PS d) : ℝ := (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X)

theorem bump1_isSTTest : IsSTTest (bump1 d : PS d → ℝ) :=
  ⟨(bump1 d).contDiff, (bump1 d).hasCompactSupport⟩

theorem scut_isSTTest (n : ℕ) : IsSTTest (scut (d := d) n) := by
  refine ⟨bump1_isSTTest.1.comp (contDiff_const_smul _), ?_⟩
  have hc : ((n : ℝ) + 1)⁻¹ ≠ 0 := by positivity
  exact bump1_isSTTest.2.comp_homeomorph (Homeomorph.smulOfNeZero _ hc)

theorem scut_nonneg (n : ℕ) (X : PS d) : 0 ≤ scut n X := (bump1 d).nonneg

theorem scut_le_one (n : ℕ) (X : PS d) : scut n X ≤ 1 := (bump1 d).le_one

theorem tendsto_scut (X : PS d) : Tendsto (fun n => scut (d := d) n X) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖X‖
  filter_upwards [eventually_ge_atTop N] with n hn
  refine ((bump1 d).one_of_mem_closedBall ?_).symm
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [inv_mul_le_iff₀ (by positivity)]
  change ‖X‖ ≤ ((n : ℝ) + 1) * 1
  linarith

theorem dirD_scut (n : ℕ) (v : PS d) (X : PS d) :
    dirD v (scut n) X = ((n : ℝ) + 1)⁻¹ * dirD v (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X) :=
  congrFun (dirD_comp_smul bump1_isSTTest.differentiable _ v) X

theorem sD2_scut (n : ℕ) (k : Fin d) (X : PS d) :
    sD2 k k (scut n) X = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ *
      sD2 k k (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X) := by
  have h1 : sD k (scut (d := d) n) = ((n : ℝ) + 1)⁻¹ •
      fun X => sD k (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X) := by
    funext Y; rw [Pi.smul_apply, smul_eq_mul]; exact dirD_scut n _ Y
  show sD k (sD k (scut n)) X = _
  rw [h1]
  show dirD (sdir k) (((n : ℝ) + 1)⁻¹ • fun X => sD k (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X)) X
    = _
  have hdd : Differentiable ℝ (fun X => sD k (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X)) :=
    ((bump1_isSTTest.dirD (sdir k)).differentiable).comp
      ((contDiff_const_smul (n := 1) (((n : ℝ) + 1)⁻¹) : ContDiff ℝ 1
        (fun p : PS d => ((n : ℝ) + 1)⁻¹ • p)).differentiable (by norm_num))
  rw [dirD_smul _ hdd, Pi.smul_apply, smul_eq_mul,
    dirD_comp_smul (bump1_isSTTest.dirD (sdir k)).differentiable]
  ring

/-- The cutoff derivatives decay like `1/(n+1)`. -/
theorem exists_scut_bound (ν : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (X : PS d),
    |-tD (scut n) X - ν * sLap (scut n) X| ≤ K / ((n : ℝ) + 1) ∧
      ∀ k : Fin d, |sD k (scut n) X| ≤ K / ((n : ℝ) + 1) := by
  obtain ⟨Bt, hBt0, hBt⟩ := (bump1_isSTTest (d := d)).dirD tdir |>.bounded
  have hk1 : ∀ k : Fin d, ∃ B, 0 ≤ B ∧ ∀ Y, |sD k (bump1 d : PS d → ℝ) Y| ≤ B :=
    fun k => ((bump1_isSTTest (d := d)).dirD (sdir k)).bounded
  have hk2 : ∀ k : Fin d, ∃ B, 0 ≤ B ∧ ∀ Y, |sD2 k k (bump1 d : PS d → ℝ) Y| ≤ B :=
    fun k => ((bump1_isSTTest (d := d)).sD2 k k).bounded
  choose B1 hB10 hB1 using hk1
  choose B2 hB20 hB2 using hk2
  refine ⟨Bt + |ν| * ∑ k, B2 k + ∑ k, B1 k, add_nonneg (add_nonneg hBt0 (mul_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun k _ => hB20 k))) (Finset.sum_nonneg fun k _ => hB10 k),
    fun n X => ⟨?_, fun k => ?_⟩⟩
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
    have ht : |tD (scut (d := d) n) X| ≤ Bt / ((n : ℝ) + 1) := by
      rw [show tD (scut (d := d) n) X = _ from dirD_scut n tdir X, abs_mul,
        abs_of_pos (inv_pos.2 hn), div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hBt _) (inv_pos.2 hn).le
    have hl : |sLap (scut (d := d) n) X| ≤ (∑ k, B2 k) / ((n : ℝ) + 1) := by
      simp only [sLap]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [sD2_scut, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hn), div_eq_inv_mul]
      calc ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ *
            |sD2 k k (bump1 d : PS d → ℝ) (((n : ℝ) + 1)⁻¹ • X)|
          ≤ ((n : ℝ) + 1)⁻¹ * 1 * B2 k := by
            gcongr
            exact hB2 k _
        _ = ((n : ℝ) + 1)⁻¹ * B2 k := by ring
    calc |-tD (scut (d := d) n) X - ν * sLap (scut n) X|
        ≤ |tD (scut (d := d) n) X| + |ν| * |sLap (scut (d := d) n) X| := by
          rw [← abs_mul]
          refine (abs_sub _ _).trans ?_
          rw [abs_neg]
      _ ≤ Bt / ((n : ℝ) + 1) + |ν| * ((∑ k, B2 k) / ((n : ℝ) + 1)) := by gcongr
      _ ≤ (Bt + |ν| * ∑ k, B2 k + ∑ k, B1 k) / ((n : ℝ) + 1) := by
          rw [mul_div_assoc', ← add_div]
          apply div_le_div_of_nonneg_right _ hn.le
          have : 0 ≤ ∑ k, B1 k := Finset.sum_nonneg fun k _ => hB10 k
          linarith
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show sD k (scut (d := d) n) X = _ from dirD_scut n (sdir k) X, abs_mul,
      abs_of_pos (inv_pos.2 hn), div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ((hB1 k _).trans ?_) (inv_pos.2 hn).le
    have h1 : B1 k ≤ ∑ k, B1 k := Finset.single_le_sum (fun k _ => hB10 k) (Finset.mem_univ k)
    have h2 : 0 ≤ |ν| * ∑ k, B2 k := mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => hB20 k)
    linarith

end Cutoff

section Product

/-- **The backward heat operator on a product.** -/
theorem heatAdj_mul {ψ Ψ : PS d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hΨ : ContDiff ℝ ∞ Ψ) (ν : ℝ)
    (X : PS d) :
    -tD (fun Y => ψ Y * Ψ Y) X - ν * sLap (fun Y => ψ Y * Ψ Y) X =
      ψ X * (-tD Ψ X - ν * sLap Ψ X) + Ψ X * (-tD ψ X - ν * sLap ψ X) -
        2 * ν * ∑ k : Fin d, sD k ψ X * sD k Ψ X := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have ht : tD (fun Y => ψ Y * Ψ Y) X = ψ X * tD Ψ X + Ψ X * tD ψ X :=
    congrFun (dirD_mul hψd hΨd tdir) X
  have hk : ∀ k : Fin d, sD2 k k (fun Y => ψ Y * Ψ Y) X =
      ψ X * sD2 k k Ψ X + Ψ X * sD2 k k ψ X + 2 * (sD k ψ X * sD k Ψ X) := by
    intro k
    have hψk : Differentiable ℝ (sD k ψ) := (contDiff_dirD hψ _).differentiable (by simp)
    have hΨk : Differentiable ℝ (sD k Ψ) := (contDiff_dirD hΨ _).differentiable (by simp)
    show dirD (sdir k) (dirD (sdir k) (fun Y => ψ Y * Ψ Y)) X = _
    rw [dirD_mul hψd hΨd (sdir k)]
    show dirD (sdir k) ((fun Y => ψ Y * sD k Ψ Y) + fun Y => Ψ Y * sD k ψ Y) X = _
    have hd1 : Differentiable ℝ (fun Y => ψ Y * sD k Ψ Y) := hψd.mul hΨk
    have hd2 : Differentiable ℝ (fun Y => Ψ Y * sD k ψ Y) := hΨd.mul hψk
    rw [dirD_add hd1 hd2, Pi.add_apply, dirD_mul hψd hΨk, dirD_mul hΨd hψk]
    beta_reduce
    ring
  rw [ht]
  simp only [sLap, hk, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Product

section Identification

variable {ν : ℝ} {u F : PS d → ℝ}

/-- **The identification at `q = 2`.** If `u, F ∈ L²` and `(∂_t - νΔ)u = F` against tests,
then `∫ u ∂_i∂_j φ = ∫ F · backTest ν i j φ` for every test `φ`. -/
theorem integral_mul_sD2_eq (hν : 0 < ν) (hu : MemLp u 2 volume) (hF : MemLp F 2 volume)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X)
    {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d) :
    ∫ X, u X * sD2 i j φ X = ∫ X, F X * backTest ν i j φ X := by
  set Ψ := backTest ν i j φ with hΨdef
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_backTest hν hφ i j
  have hΨ2 : MemLp Ψ 2 volume := memLp_backTest hν hφ i j
  have hΨk : ∀ k : Fin d, MemLp (sD k Ψ) 2 volume := fun k => by
    rw [hΨdef, sD_backTest hν hφ i j k]; exact memLp_backTest hν (hφ.dirD _) i j
  obtain ⟨K, hK0, hK⟩ := exists_scut_bound (d := d) ν
  -- integrable products
  have iFΨ : Integrable (fun X => F X * Ψ X) volume := hF.integrable_mul hΨ2
  have iuφ : Integrable (fun X => u X * sD2 i j φ X) volume :=
    hu.integrable_mul ((hφ.sD2 i j).memLp 2)
  have iuΨ : Integrable (fun X => |u X| * |Ψ X|) volume := (hu.integrable_mul hΨ2).abs.congr
    (Eventually.of_forall fun X => by simp [abs_mul])
  have iuk : ∀ k : Fin d, Integrable (fun X => |u X| * |sD k Ψ X|) volume := fun k =>
    (hu.integrable_mul (hΨk k)).abs.congr (Eventually.of_forall fun X => by simp [abs_mul])
  set M : ℝ := ∫ X, (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) with hM
  have iM : Integrable (fun X => |u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|)
      volume := iuΨ.add ((integrable_finsetSum _ fun k _ => iuk k).const_mul _)
  -- the equation tested against `scut n * Ψ`
  have hχ : ∀ n : ℕ, IsSTTest (fun X => scut n X * Ψ X) := fun n =>
    ⟨(scut_isSTTest n).1.mul hΨ, (scut_isSTTest n).2.mul_right⟩
  set R : ℕ → PS d → ℝ := fun n X => Ψ X * (-tD (scut n) X - ν * sLap (scut n) X) -
    2 * ν * ∑ k : Fin d, sD k (scut n) X * sD k Ψ X with hR
  have hRb : ∀ (n : ℕ) (X : PS d), ‖u X * R n X‖ ≤ K / ((n : ℝ) + 1) *
      (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) := by
    intro n X
    obtain ⟨h1, h2⟩ := hK n X
    have hn : (0 : ℝ) ≤ K / ((n : ℝ) + 1) := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    have hRX : |R n X| ≤ K / ((n : ℝ) + 1) *
        (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|) := by
      simp only [hR]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have hs : |∑ k : Fin d, sD k (scut n) X * sD k Ψ X| ≤
          K / ((n : ℝ) + 1) * ∑ k : Fin d, |sD k Ψ X| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h2 k) (abs_nonneg _)
      calc |Ψ X| * |-tD (scut n) X - ν * sLap (scut n) X| +
            2 * |ν| * |∑ k : Fin d, sD k (scut n) X * sD k Ψ X|
          ≤ |Ψ X| * (K / ((n : ℝ) + 1)) +
            2 * |ν| * (K / ((n : ℝ) + 1) * ∑ k : Fin d, |sD k Ψ X|) := by
            gcongr
        _ = K / ((n : ℝ) + 1) * (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|) := by ring
    calc |u X| * |R n X| ≤ |u X| * (K / ((n : ℝ) + 1) *
          (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|)) :=
          mul_le_mul_of_nonneg_left hRX (abs_nonneg _)
      _ = K / ((n : ℝ) + 1) *
          (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) := by
          rw [← Finset.mul_sum]; ring
  have hRc : ∀ n : ℕ, Continuous (R n) := by
    intro n
    rw [hR]
    have hs := scut_isSTTest (d := d) n
    have hsl : Continuous (sLap (scut (d := d) n)) := by
      have e : sLap (scut (d := d) n) = fun X => ∑ k : Fin d, sD2 k k (scut n) X := rfl
      rw [e]; exact continuous_finsetSum _ fun k _ => (hs.sD2 k k).continuous
    exact (hΨ.continuous.mul ((hs.dirD tdir).continuous.neg.sub (continuous_const.mul hsl))).sub
      (continuous_const.mul (continuous_finsetSum _ fun k _ =>
        (hs.dirD (sdir k)).continuous.mul (contDiff_dirD hΨ _).continuous))
  have iR : ∀ n : ℕ, Integrable (fun X => u X * R n X) volume := fun n =>
    (iM.const_mul (K / ((n : ℝ) + 1))).mono' (hu.1.mul (hRc n).aestronglyMeasurable)
      (Eventually.of_forall fun X => hRb n X)
  have hsplit : ∀ n : ℕ, ∫ X, F X * (scut n X * Ψ X) =
      (∫ X, u X * (scut n X * sD2 i j φ X)) + ∫ X, u X * R n X := by
    intro n
    rw [← heq _ (hχ n)]
    have hpt : ∀ X, u X * (-tD (fun Y => scut n Y * Ψ Y) X -
        ν * sLap (fun Y => scut n Y * Ψ Y) X) = u X * (scut n X * sD2 i j φ X) + u X * R n X := by
      intro X
      rw [heatAdj_mul (scut_isSTTest n).1 hΨ ν X, hΨdef, backTest_heatAdj hν hφ i j X]
      simp only [hR]; ring
    have i1 : Integrable (fun X => u X * (scut n X * sD2 i j φ X)) volume := by
      have ht : IsSTTest (fun X => scut n X * sD2 i j φ X) :=
        ⟨(scut_isSTTest n).1.mul (hφ.sD2 i j).1, (hφ.sD2 i j).2.mul_left⟩
      exact hu.integrable_mul (ht.memLp 2)
    have i2 : Integrable (fun X => u X * R n X) volume := iR n
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add i1 i2]
  -- limits
  have L1 : Tendsto (fun n : ℕ => ∫ X, F X * (scut n X * Ψ X)) atTop (𝓝 (∫ X, F X * Ψ X)) := by
    refine tendsto_integral_of_dominated_convergence (fun X => |F X * Ψ X|)
      (fun n => hF.1.mul ((scut_isSTTest n).continuous.mul hΨ.continuous).aestronglyMeasurable)
      iFΨ.abs (fun n => Eventually.of_forall fun X => ?_) (Eventually.of_forall fun X => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (scut_nonneg n X),
        mul_left_comm]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (scut_le_one n X)
    · have := ((tendsto_scut X).mul_const (Ψ X)).const_mul (F X)
      simpa using this
  have L2 : Tendsto (fun n : ℕ => ∫ X, u X * (scut n X * sD2 i j φ X)) atTop
      (𝓝 (∫ X, u X * sD2 i j φ X)) := by
    refine tendsto_integral_of_dominated_convergence (fun X => |u X * sD2 i j φ X|)
      (fun n => hu.1.mul ((scut_isSTTest n).continuous.mul
        (hφ.sD2 i j).continuous).aestronglyMeasurable)
      iuφ.abs (fun n => Eventually.of_forall fun X => ?_) (Eventually.of_forall fun X => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (scut_nonneg n X),
        mul_left_comm]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (scut_le_one n X)
    · have := ((tendsto_scut X).mul_const (sD2 i j φ X)).const_mul (u X)
      simpa using this
  have L3 : Tendsto (fun n : ℕ => ∫ X, u X * R n X) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => K * M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * M)
    refine squeeze_zero_norm (fun n => ?_) hlim
    refine (norm_integral_le_of_norm_le ((iM.const_mul (K / ((n : ℝ) + 1))))
      (Eventually.of_forall fun X => hRb n X)).trans (le_of_eq ?_)
    rw [integral_const_mul, ← hM]; ring
  have L4 := L2.add L3
  rw [add_zero] at L4
  have L5 : Tendsto (fun n : ℕ => ∫ X, F X * (scut n X * Ψ X)) atTop
      (𝓝 (∫ X, u X * sD2 i j φ X)) := L4.congr fun n => (hsplit n).symm
  exact tendsto_nhds_unique L5 L1

end Identification

section MainTwo

variable {ν : ℝ} {u F : PS d → ℝ}

theorem eLpNorm_smul_secondDerivOp_le (hν : 0 < ν) (i j : Fin d) (hF : MemLp F 2 volume) :
    eLpNorm (fun X => ν * secondDerivOp hν i j (hF.toLp F) X) 2 volume ≤ eLpNorm F 2 volume := by
  set G := hF.toLp F
  have hae : (fun X => ν * secondDerivOp hν i j G X) =ᵐ[volume] ⇑(ν • secondDerivOp hν i j G) := by
    filter_upwards [Lp.coeFn_smul ν (secondDerivOp hν i j G)] with X hX
    rw [hX, Pi.smul_apply, smul_eq_mul]
  rw [eLpNorm_congr_ae hae]
  have h1 : ‖ν • secondDerivOp hν i j G‖ ≤ ‖G‖ := by
    have := (ν • secondDerivOp hν i j).le_opNorm G
    rw [smul_apply] at this
    exact this.trans (by
      have h := norm_smul_secondDerivOp_le hν i j
      calc ‖ν • secondDerivOp hν i j‖ * ‖G‖ ≤ 1 * ‖G‖ := by gcongr
        _ = ‖G‖ := one_mul _)
  have e1 : eLpNorm (⇑(ν • secondDerivOp hν i j G)) 2 volume =
      ENNReal.ofReal ‖ν • secondDerivOp hν i j G‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  rw [e1]
  calc ENNReal.ofReal ‖ν • secondDerivOp hν i j G‖ ≤ ENNReal.ofReal ‖G‖ :=
        ENNReal.ofReal_le_ofReal h1
    _ = eLpNorm F 2 volume := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
          eLpNorm_congr_ae hF.coeFn_toLp]

/-- **INF02 T8 at `q = 2` and T10 (eq:free-stress-11 at `q = 2`, distributional form).**
Let `ν > 0` and `u, F ∈ L²(ℝ × ℝ^d)` with `(∂_t - νΔ)u = F` against test functions:
`∫ u (-∂_t φ - νΔφ) = ∫ F φ`. Then `u` has weak second spatial derivatives `D2 i j ∈ L²` and a
weak time derivative `Dt ∈ L²`, with `‖ν D2 i j‖₂ ≤ ‖F‖₂` (constant `1`, independent of `ν`)
and `‖Dt‖₂ ≤ (1 + d) ‖F‖₂`. (The manuscript also assumes `u` compactly supported in time;
at `q = 2` this is not needed.) -/
theorem heat_maximal_regularity_two (hν : 0 < ν) (hu : MemLp u 2 volume) (hF : MemLp F 2 volume)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X) :
    ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
      (∀ i j, MemLp (D2 i j) 2 volume ∧
        ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X) ∧
      MemLp Dt 2 volume ∧
      (∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * tD φ X = -∫ X, Dt X * φ X) ∧
      (∀ i j, eLpNorm (fun X => ν * D2 i j X) 2 volume ≤ eLpNorm F 2 volume) ∧
      eLpNorm Dt 2 volume ≤ ENNReal.ofReal (1 + d) * eLpNorm F 2 volume := by
  set G := hF.toLp F with hGdef
  set D2 : Fin d → Fin d → PS d → ℝ := fun i j => ⇑(secondDerivOp hν i j G) with hD2
  have hD2m : ∀ i j, MemLp (D2 i j) 2 volume := fun i j => Lp.memLp _
  -- weak second derivatives
  have hweak : ∀ i j (φ : PS d → ℝ), IsSTTest φ →
      ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X := by
    intro i j φ hφ
    rw [integral_mul_sD2_eq hν hu hF heq hφ i j]
    have h := integral_secondDerivOp_mul hν i j G ((hφ.memLp 2).toLp φ)
    rw [backOp_toLp hν hφ i j] at h
    have e1 : ∫ X, F X * backTest ν i j φ X =
        ∫ X, G X * ((memLp_backTest hν hφ i j).toLp _ : Lp ℝ 2 volume) X := by
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp, (memLp_backTest hν hφ i j).coeFn_toLp] with X h1 h2
      rw [h1, h2]
    have e2 : ∫ X, D2 i j X * φ X =
        ∫ X, secondDerivOp hν i j G X * ((hφ.memLp 2).toLp φ : Lp ℝ 2 volume) X := by
      refine integral_congr_ae ?_
      filter_upwards [(hφ.memLp 2).coeFn_toLp] with X h1
      rw [h1]
    rw [e1, ← h, ← e2]
  -- the time derivative `Dt = F + ν Σ D2 i i`
  set Dt : PS d → ℝ := fun X => F X + ν * ∑ i : Fin d, D2 i i X with hDt
  have hDtm : MemLp Dt 2 volume := by
    have hs : MemLp (fun X => ∑ i : Fin d, D2 i i X) 2 volume :=
      memLp_finsetSum (f := fun i => D2 i i) Finset.univ fun i _ => hD2m i i
    exact hF.add (hs.const_mul ν)
  refine ⟨D2, Dt, fun i j => ⟨hD2m i j, hweak i j⟩, hDtm, fun φ hφ => ?_, fun i j => ?_, ?_⟩
  · -- weak time derivative
    have hφ2 := hφ.memLp 2
    have iT : Integrable (fun X => u X * tD φ X) volume :=
      hu.integrable_mul ((isSTTest_tD hφ).memLp 2)
    have iL : ∀ k : Fin d, Integrable (fun X => u X * sD2 k k φ X) volume :=
      fun k => hu.integrable_mul ((hφ.sD2 k k).memLp 2)
    have iD : ∀ k : Fin d, Integrable (fun X => D2 k k X * φ X) volume :=
      fun k => (hD2m k k).integrable_mul hφ2
    have iFφ : Integrable (fun X => F X * φ X) volume := hF.integrable_mul hφ2
    have h1 := heq φ hφ
    have e1 : ∫ X, u X * (-tD φ X - ν * sLap φ X) =
        -(∫ X, u X * tD φ X) - ν * ∑ k : Fin d, ∫ X, u X * sD2 k k φ X := by
      have hpt : ∀ X, u X * (-tD φ X - ν * sLap φ X) =
          -(u X * tD φ X) - ν * ∑ k : Fin d, u X * sD2 k k φ X := by
        intro X
        simp only [sLap]
        rw [← Finset.mul_sum]; ring
      have iTn : Integrable (fun X => -(u X * tD φ X)) volume := iT.neg
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iTn
        ((integrable_finsetSum _ fun k _ => iL k).const_mul ν), integral_neg,
        integral_const_mul, integral_finsetSum _ fun k _ => iL k]
    have e2 : ∫ X, Dt X * φ X = (∫ X, F X * φ X) + ν * ∑ k : Fin d, ∫ X, D2 k k X * φ X := by
      have hpt : ∀ X, Dt X * φ X = F X * φ X + ν * ∑ k : Fin d, D2 k k X * φ X := by
        intro X
        simp only [hDt]
        rw [add_mul, mul_assoc, Finset.sum_mul]
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_add iFφ
        ((integrable_finsetSum _ fun k _ => iD k).const_mul ν), integral_const_mul,
        integral_finsetSum _ fun k _ => iD k]
    have e3 : ∀ k : Fin d, ∫ X, u X * sD2 k k φ X = ∫ X, D2 k k X * φ X :=
      fun k => hweak k k φ hφ
    simp_rw [e3] at e1
    rw [e2]
    linarith
  · exact eLpNorm_smul_secondDerivOp_le hν i j hF
  · -- `‖Dt‖₂ ≤ (1 + d) ‖F‖₂`
    have hm : ∀ i : Fin d, AEStronglyMeasurable (fun X => ν * D2 i i X) volume :=
      fun i => ((hD2m i i).1.const_mul ν)
    have hsum : (fun X => ν * ∑ i : Fin d, D2 i i X) = ∑ i : Fin d, fun X => ν * D2 i i X := by
      funext X; rw [Finset.sum_apply, Finset.mul_sum]
    have hDt' : Dt = F + ∑ i : Fin d, fun X => ν * D2 i i X := by
      funext X; simp only [hDt, Pi.add_apply]; rw [← hsum]
    rw [hDt']
    calc eLpNorm (F + ∑ i : Fin d, fun X => ν * D2 i i X) 2 volume
        ≤ eLpNorm F 2 volume + eLpNorm (∑ i : Fin d, fun X => ν * D2 i i X) 2 volume :=
          eLpNorm_add_le hF.1 (Finset.aestronglyMeasurable_sum _ fun i _ => hm i) (by norm_num)
      _ ≤ eLpNorm F 2 volume + ∑ i : Fin d, eLpNorm (fun X => ν * D2 i i X) 2 volume := by
          gcongr
          exact eLpNorm_sum_le (fun i _ => hm i) (by norm_num)
      _ ≤ eLpNorm F 2 volume + ∑ _i : Fin d, eLpNorm F 2 volume := by
          gcongr with i
          exact eLpNorm_smul_secondDerivOp_le hν i i hF
      _ = ENNReal.ofReal (1 + d) * eLpNorm F 2 volume := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_natCast]
          ring

end MainTwo

end UnforcedLeray.Parabolic
