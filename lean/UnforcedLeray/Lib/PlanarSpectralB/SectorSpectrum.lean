import UnforcedLeray.Lib.PlanarSpectralB.CompactPerturb
import UnforcedLeray.Lib.PlanarSpectralB.LogGreen

/-!
# The growing spectrum of the sector generators on `L²_M` (INF10 target G-2)


§5, Level G, target **G-2** (`spectrum_Lsec_rightHalf`); decision D7 of `scoping/README.md`
(G1 at `j = 0`, sector by sector, bounded generators). Manuscript (`paper/main.tex`):
lines 1347–1356 (units `B0077`, `B0078`, `B0080`: no nonreal modes for `n ≥ 3`, `n = 0`
stationary, `n = ±1` excluded by the explicit solution `r(Ω - c)`), lines 1380–1400 (units `B0081`–`B0083`:
transfer to `L²_M`, the growing spectrum is `{λ}` in sector `2`), lines 1432–1437 (`B0088`: for
`Re z > 0`, `z - 𝓛_n = (z + inΩ)(I - (z + inΩ)⁻¹K_n)`, a Fredholm alternative).

Main declarations (namespace `UnforcedLeray.Planar`):
* `isUnit_sub_smul_omega`, `isUnit_sub_transportSec`: for `Re z > 0` and imaginary `a`,
  `z - aΩ` is invertible (multiplication by `(z - aΩ)⁻¹`, norm `≤ (Re z)⁻¹`);
* `mem_spectrum_Lsec_iff`: for `Re z > 0`, `z ∈ σ(𝓛_n)` iff `z` is an eigenvalue of `𝓛_n`
  (`Infra.CompactPerturb.exists_eigen_of_mem_spectrum`, Mathlib's Fredholm alternative);
* `Lsec_eigen_eq_zero_of_three_le` (`|n| ≥ 3`, via G-1 and the compiled
  `Sturm.eq_zero_of_phaseSpeed_eigen_of_three_le`), `Lsec_eigen_eq_zero_zero` (`n = 0`);
* `Lsec_eigen_unique_of_natAbs_eq_two` (`|n| = 2`: one growing eigenvalue, one-dimensional
  eigenspace; via G-1, the linearity of the transfer and the compiled
  `Sturm.phaseSpeed_two_unique`, extended to `Im c < 0` by conjugation);
* **G-2**: `spectrum_Lsec_rightHalf_of_three_le`, `spectrum_Lsec_rightHalf_zero`,
  `spectrum_Lsec_rightHalf_of_natAbs_one`, `spectrum_Lsec_rightHalf_of_ne_two`,
  `spectrum_Lsec_rightHalf_subsingleton`, `spectrum_Lsec_rightHalf_eq_singleton`,
  `spectrum_Lsec_rightHalf`.

**Named hypothesis.** The sectors `n = ±1` are excluded in the manuscript by the explicit
regular solution `φ₁ = r(Ω - c)` (tex lines 1350–1356, target O13 `sector_one_eigen_eq_zero`
of the scoping note, assigned to the mode-regularity part of block 3F, not built here). The
statements that cover `|n| = 1` take it as the hypothesis `SectorOneStable hM`, which is exactly
the manuscript's claim on `L²_M`: no eigenvector of `𝓛_{±1}` with `Re z > 0`.

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Infra.CompactPerturb

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An eigenvalue is a spectral point. -/
theorem mem_spectrum_of_eigen {A : X →L[ℂ] X} {z : ℂ} {w : X} (hw0 : w ≠ 0)
    (h : A w = z • w) : z ∈ spectrum ℂ A := by
  refine spectrum.mem_iff.2 fun hu => hw0 ?_
  have h1 : (algebraMap ℂ (X →L[ℂ] X) z - A) w = 0 := by
    rw [ContinuousLinearMap.sub_apply, algebraMap_apply, h, sub_self]
  calc w = (Ring.inverse (algebraMap ℂ (X →L[ℂ] X) z - A) *
        (algebraMap ℂ (X →L[ℂ] X) z - A)) w := by
        rw [Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply]
    _ = 0 := by rw [ContinuousLinearMap.mul_apply, h1, map_zero]

end UnforcedLeray.Infra.CompactPerturb

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)
open UnforcedLeray.Infra.CompactPerturb (mem_spectrum_of_eigen)

/-! ### The transport part is invertible on the right half-plane -/

/-- For `Re z > 0` and `Re a = 0`, `z - aΩ` is invertible on `L²(μ)` (any measure on `ℝ`), for
any operator `O` acting as multiplication by `Ω = e^{-r²/4}`. -/
theorem isUnit_sub_smul_omega {μ : Measure ℝ} (O : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hO : ∀ f, ⇑(O f) =ᵐ[μ] fun r => (radialOmega r : ℂ) * f r) {a : ℂ} (ha : a.re = 0)
    {z : ℂ} (hz : 0 < z.re) :
    IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - a • O) := by
  set m : ℝ → ℂ := fun r => z - a * (radialOmega r : ℂ) with hm
  have hre : ∀ r, (m r).re = z.re := by
    intro r
    simp [hm, Complex.mul_re, ha]
  have hne : ∀ r, m r ≠ 0 := by
    intro r h
    have := hre r
    rw [h, Complex.zero_re] at this
    linarith
  have hnorm : ∀ r, ‖(m r)⁻¹‖ ≤ z.re⁻¹ := by
    intro r
    rw [norm_inv]
    exact inv_anti₀ hz ((hre r).symm ▸ Complex.re_le_norm (m r))
  have hcont : Continuous fun r => (m r)⁻¹ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp B0012.continuous_radialOmega))).inv₀ hne
  set B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := Infra.Mult.mulOp (fun r => (m r)⁻¹)
    hcont.aestronglyMeasurable (Eventually.of_forall hnorm) with hB
  have hBf : ∀ f, ⇑(B f) =ᵐ[μ] fun r => (m r)⁻¹ * f r := fun f =>
    Infra.Mult.coeFn_mulOp _ _ f
  have key : ∀ g : Lp ℂ 2 μ, ⇑((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - a • O) g) =ᵐ[μ]
      fun r => m r * g r := by
    intro g
    rw [ContinuousLinearMap.sub_apply, Infra.CompactPerturb.algebraMap_apply,
      ContinuousLinearMap.smul_apply]
    filter_upwards [Lp.coeFn_sub (z • g) (a • O g), Lp.coeFn_smul z g, Lp.coeFn_smul a (O g),
      hO g] with r h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul]
    simp only [hm]
    ring
  refine ⟨⟨_, B, ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun f => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    apply Lp.ext
    filter_upwards [key (B f), hBf f] with r h1 h2
    rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (hne r), one_mul]
  · refine ContinuousLinearMap.ext fun f => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    apply Lp.ext
    filter_upwards [hBf ((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - a • O) f), key f]
      with r h1 h2
    rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ (hne r), one_mul]

/-- `z - (-inΩ)` is invertible on `L²_M` profiles for `Re z > 0` (tex line 1433, at `j = 0`). -/
theorem isUnit_sub_transportSec (M : ℝ) (n : ℤ) {z : ℂ} (hz : 0 < z.re) :
    IsUnit (algebraMap ℂ (ProfL2 M →L[ℂ] ProfL2 M) z - transportSec M n) :=
  isUnit_sub_smul_omega (omegaP M) (coeFn_omegaP M) (by simp) hz

/-! ### Spectral points in the right half-plane are eigenvalues -/

theorem exists_eigen_of_mem_spectrum_Lsec {M : ℝ} (hM : 1 < M) (n : ℤ) {z : ℂ}
    (hz : 0 < z.re) (h : z ∈ spectrum ℂ (Lsec hM n)) :
    ∃ w : ProfL2 M, w ≠ 0 ∧ Lsec hM n w = z • w :=
  Infra.CompactPerturb.exists_eigen_of_mem_spectrum (isCompactOperator_couplingSec hM n)
    (isUnit_sub_transportSec M n hz) h

/-- For `Re z > 0`: `z ∈ σ(𝓛_n)` iff `z` is an eigenvalue of `𝓛_n` on `L²_M` profiles. -/
theorem mem_spectrum_Lsec_iff {M : ℝ} (hM : 1 < M) (n : ℤ) {z : ℂ} (hz : 0 < z.re) :
    z ∈ spectrum ℂ (Lsec hM n) ↔ ∃ w : ProfL2 M, w ≠ 0 ∧ Lsec hM n w = z • w :=
  ⟨exists_eigen_of_mem_spectrum_Lsec hM n hz, fun ⟨_, hw0, hw⟩ => mem_spectrum_of_eigen hw0 hw⟩

/-! ### Exclusion of the sectors `n = 0` and `|n| ≥ 3` -/

/-- The phase speed `c = iz/m` of an eigenvalue `z` in sector `m`: `Im c · m = Re z`. -/
theorem im_mul_of_mul_eq {m : ℤ} {z c : ℂ} (hcz : c * m = Complex.I * z) :
    c.im * (m : ℝ) = z.re := by
  have h := congrArg Complex.im hcz
  simpa [Complex.mul_im] using h

/-- **Sectors `|n| ≥ 3`** (B0077, tex lines 1347–1349): `𝓛_n` has no eigenvector with
`Re z > 0`. -/
theorem Lsec_eigen_eq_zero_of_three_le {M : ℝ} (hM : 1 < M) {n : ℤ} (hn : 3 ≤ n.natAbs)
    {z : ℂ} (hz : 0 < z.re) {w : ProfL2 M} (hw : Lsec hM n w = z • w) : w = 0 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn0
  have hcz : Complex.I * z / n * n = Complex.I * z := div_mul_cancel₀ _ hnC
  obtain ⟨hc, hpos, hF, hinj⟩ := transfer_sector_eigen hM hn0 hz.ne' hcz hw
  by_contra h0
  apply hinj h0
  exact Sturm.eq_zero_of_phaseSpeed_eigen_of_three_le (m := (n.natAbs : ℝ))
    (by exact_mod_cast hn) hc hF

/-- **Sector `0`** (B0078(i), tex line 1356): `𝓛₀ = 0` has no eigenvalue with `Re z > 0`. -/
theorem Lsec_eigen_eq_zero_zero {M : ℝ} (hM : 1 < M) {z : ℂ} (hz : 0 < z.re) {w : ProfL2 M}
    (hw : Lsec hM 0 w = z • w) : w = 0 := by
  rw [Lsec_zero, ContinuousLinearMap.zero_apply] at hw
  have hz0 : z ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  exact (smul_eq_zero.1 hw.symm).resolve_left hz0

/-- **Named hypothesis for the sectors `n = ±1`** (target O13 of the scoping note; manuscript
tex lines 1350–1356, unit `B0080`: the regular solution `r(Ω - c)` is not decaying, so there
is no nonreal `n = ±1` eigenmode): `𝓛_{±1}` has no eigenvector with `Re z > 0` on `L²_M`. -/
def SectorOneStable {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ n : ℤ, n.natAbs = 1 → ∀ (z : ℂ) (w : ProfL2 M), 0 < z.re → Lsec hM n w = z • w → w = 0

/-- Every sector `n` with `|n| ≠ 2` has no eigenvector with `Re z > 0` (given the `|n| = 1`
input `SectorOneStable`). -/
theorem Lsec_eigen_eq_zero_of_ne_two {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM) {n : ℤ}
    (hn : n.natAbs ≠ 2) {z : ℂ} (hz : 0 < z.re) {w : ProfL2 M} (hw : Lsec hM n w = z • w) :
    w = 0 := by
  rcases Nat.lt_or_ge n.natAbs 3 with h | h
  · have h01 : n.natAbs = 0 ∨ n.natAbs = 1 := by omega
    rcases h01 with h0 | h1'
    · have hn0 : n = 0 := Int.natAbs_eq_zero.1 h0
      subst hn0
      exact Lsec_eigen_eq_zero_zero hM hz hw
    · exact h1 n h1' z w hz hw
  · exact Lsec_eigen_eq_zero_of_three_le hM h hz hw

/-! ### The sectors `n = ±2`: one eigenvalue, one-dimensional eigenspace -/

/-- Phase-speed uniqueness at `m = 2` for two speeds in the same open half-plane (the compiled
`Sturm.phaseSpeed_two_unique` covers `Im c > 0`; the lower half-plane follows by conjugation). -/
theorem phaseSpeed_unique_sameSign {mR : ℝ} (hm2 : mR = 2) (hm : 0 < mR) {c c' : ℂ}
    {f f' : Sturm.ComplexL2} (hcc : 0 < c.im * c'.im)
    (hf : Sturm.phaseSpeedOp hm f = c • f) (hf' : Sturm.phaseSpeedOp hm f' = c' • f')
    (h0 : f ≠ 0) (h0' : f' ≠ 0) : c' = c ∧ ∃ μ : ℂ, f' = μ • f := by
  subst hm2
  have hc0 : c.im ≠ 0 := fun h => by
    rw [h, zero_mul] at hcc
    exact lt_irrefl _ hcc
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hc'neg : c'.im < 0 := by
      by_contra h
      push_neg at h
      nlinarith
    have hs : Sturm.phaseSpeedOp hm (star f) = conj c • (star f : Sturm.ComplexL2) := by
      rw [Sturm.phaseSpeedOp_star, hf, Sturm.star_smul_L2]
    have hs' : Sturm.phaseSpeedOp hm (star f') = conj c' • (star f' : Sturm.ComplexL2) := by
      rw [Sturm.phaseSpeedOp_star, hf', Sturm.star_smul_L2]
    have hi : 0 < (conj c).im := by
      rw [Complex.conj_im]
      linarith
    have hi' : 0 < (conj c').im := by
      rw [Complex.conj_im]
      linarith
    obtain ⟨h1, μ, h2⟩ := Sturm.phaseSpeed_two_unique hi hi' hs hs' (star_ne_zero_L2 h0)
      (star_ne_zero_L2 h0')
    refine ⟨?_, conj μ, ?_⟩
    · have := congrArg (starRingEnd ℂ) h1
      simpa using this
    · rw [← star_star f', h2, Sturm.star_smul_L2, star_star]
  · have hc'pos : 0 < c'.im := by
      by_contra h
      push_neg at h
      nlinarith
    exact Sturm.phaseSpeed_two_unique hpos hc'pos hf hf' h0 h0'

/-- **Sectors `n = ±2`** (B0076, B0081(a), B0082; tex lines 1317–1346, 1380–1388): two
eigenvectors of `𝓛_n` with eigenvalues in `{Re z > 0}` have the same eigenvalue and are
proportional. -/
theorem Lsec_eigen_unique_of_natAbs_eq_two {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    {z z' : ℂ} (hz : 0 < z.re) (hz' : 0 < z'.re) {w w' : ProfL2 M}
    (hw : Lsec hM m w = z • w) (hw' : Lsec hM m w' = z' • w') (h0 : w ≠ 0) (h0' : w' ≠ 0) :
    z' = z ∧ ∃ μ : ℂ, w' = μ • w := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm0
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm0
  have hcz : Complex.I * z / m * m = Complex.I * z := div_mul_cancel₀ _ hmC
  have hcz' : Complex.I * z' / m * m = Complex.I * z' := div_mul_cancel₀ _ hmC
  obtain ⟨hc, hpos, hF, hinj⟩ := transfer_sector_eigen hM hm0 hz.ne' hcz hw
  obtain ⟨hc', hpos', hF', hinj'⟩ := transfer_sector_eigen hM hm0 hz'.ne' hcz' hw'
  have e1 : (Complex.I * z / m).im = z.re / m := eq_div_of_mul_eq hmR (im_mul_of_mul_eq hcz)
  have e2 : (Complex.I * z' / m).im = z'.re / m := eq_div_of_mul_eq hmR (im_mul_of_mul_eq hcz')
  have hcc : 0 < (Complex.I * z / m).im * (Complex.I * z' / m).im := by
    rw [e1, e2, div_mul_div_comm]
    exact div_pos (mul_pos hz hz') (mul_self_pos.2 hmR)
  have hm2 : ((m.natAbs : ℕ) : ℝ) = 2 := by
    rw [hm]
    norm_num
  obtain ⟨hceq, μ, hμ⟩ := phaseSpeed_unique_sameSign hm2 hpos hcc hF hF' (hinj h0) (hinj' h0')
  have hzz : z' = z := by
    have h := congrArg (· * (m : ℂ)) hceq
    simp only [hcz, hcz'] at h
    exact mul_left_cancel₀ Complex.I_ne_zero h
  subst hzz
  refine ⟨rfl, μ, ?_⟩
  have hd : Lsec hM m (w' - μ • w) = z' • (w' - μ • w) := by
    rw [map_sub, map_smul, hw, hw', smul_sub, smul_comm μ z' w]
  obtain ⟨hc'', hpos'', -, hinj''⟩ := transfer_sector_eigen hM hm0 hz'.ne' hcz' hd
  by_contra hne
  apply hinj'' (sub_ne_zero.2 hne)
  rw [transfer_sub, transfer_smul, hμ, sub_self]

/-! ### G-2 -/

/-- **G-2, `|n| ≥ 3`**: `σ(𝓛_n) ∩ {Re z > 0} = ∅` on `L²_M`. -/
theorem spectrum_Lsec_rightHalf_of_three_le {M : ℝ} (hM : 1 < M) {n : ℤ} (hn : 3 ≤ n.natAbs) :
    {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hspec
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum_Lsec hM n hz hspec
  exact hw0 (Lsec_eigen_eq_zero_of_three_le hM hn hz hw)

/-- **G-2, `n = 0`**. -/
theorem spectrum_Lsec_rightHalf_zero {M : ℝ} (hM : 1 < M) :
    {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM 0) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hspec
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum_Lsec hM 0 hz hspec
  exact hw0 (Lsec_eigen_eq_zero_zero hM hz hw)

/-- **G-2, `|n| ≠ 2`** (given `SectorOneStable` for `|n| = 1`). -/
theorem spectrum_Lsec_rightHalf_of_ne_two {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM)
    {n : ℤ} (hn : n.natAbs ≠ 2) : {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hspec
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum_Lsec hM n hz hspec
  exact hw0 (Lsec_eigen_eq_zero_of_ne_two hM h1 hn hz hw)

/-- **G-2, `|n| = 1`** (from the named hypothesis). -/
theorem spectrum_Lsec_rightHalf_of_natAbs_one {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM)
    {n : ℤ} (hn : n.natAbs = 1) : {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) = ∅ :=
  spectrum_Lsec_rightHalf_of_ne_two hM h1 (by omega)

/-- **G-2, `|n| = 2`**: at most one growing spectral point. -/
theorem spectrum_Lsec_rightHalf_subsingleton {M : ℝ} (hM : 1 < M) {n : ℤ} (hn : n.natAbs = 2) :
    ({z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n)).Subsingleton := by
  rintro z ⟨hz, hzs⟩ z' ⟨hz', hzs'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum_Lsec hM n hz hzs
  obtain ⟨w', hw0', hw'⟩ := exists_eigen_of_mem_spectrum_Lsec hM n hz' hzs'
  exact ((Lsec_eigen_unique_of_natAbs_eq_two hM hn hz hz' hw hw' hw0 hw0').1).symm

/-- **G-2, `|n| = 2`, with the growing mode**: if `𝓛_n q = λ q`, `q ≠ 0`, `Re λ > 0` (the
mode of Prop. `gaussian-existence`, built in the INF18 part of block 3F), then
`σ(𝓛_n) ∩ {Re z > 0} = {λ}`. -/
theorem spectrum_Lsec_rightHalf_eq_singleton {M : ℝ} (hM : 1 < M) {n : ℤ} (hn : n.natAbs = 2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM n q = z₀ • q) :
    {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) = {z₀} :=
  (spectrum_Lsec_rightHalf_subsingleton hM hn).eq_singleton_of_mem
    ⟨hz₀, mem_spectrum_of_eigen hq0 hq⟩

/-- **G-2** (`spectrum_Lsec_rightHalf`, scoping note §5): on `L²_M`, `M > 1`,
`σ(𝓛_n) ∩ {Re z > 0} = ∅` for `|n| ≠ 2` and has at most one point for `|n| = 2`; the
`|n| = 1` case uses the named input `SectorOneStable hM` (target O13). -/
theorem spectrum_Lsec_rightHalf {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM) (n : ℤ) :
    (n.natAbs ≠ 2 → {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) = ∅) ∧
      (n.natAbs = 2 → ({z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n)).Subsingleton) :=
  ⟨fun hn => spectrum_Lsec_rightHalf_of_ne_two hM h1 hn,
    fun hn => spectrum_Lsec_rightHalf_subsingleton hM hn⟩

end UnforcedLeray.Planar
