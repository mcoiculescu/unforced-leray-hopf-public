import UnforcedLeray.Lib.PlanarSpectralB.Eigenfunctional
import UnforcedLeray.Lib.PlanarSectorsB.EulerGroup

/-!
# The growing eigenvalue is simple and isolated; sector gap bounds (INF10 target G-4)


§5, Level G, target **G-4** (`isSimpleSpectralProj_Lsec_two :
IsSimpleSpectralProj (Lsec hM 2) (rankOneProj ℓ q) λ`, "deflation + Fredholm alternative").
Manuscript (`paper/main.tex`): lines 1390–1400 (unit `B0083`: the growing eigenvalues are
algebraically simple), lines 1432–1448 (units `B0088`, `B0089`: rank-one Riesz projection and
the exponential decay of the complement, here sector by sector), lines 1547–1559 (unit
`B0100`, `eq:st18-t00072`: the complement bound, decision D7 at `j = 0`).

Main declarations (namespace `UnforcedLeray.Planar`):
* **G-4** `isSimpleSpectralProj_Lsec_two` (from the abstract
  `Infra.CompactPerturb.isSimpleSpectralProj_of_compact`, the eigenfunctional of G-3 and the
  eigenvalue uniqueness of G-2) and its packaged form `exists_isSimpleSpectralProj_Lsec_two`;
* `exists_norm_expSec_mul_one_sub_le`: `‖exp(t𝓛_m)(1 - P)‖ ≤ C e^{ηt}` (`|m| = 2`, every
  `η > 0`; vendored `Dunford.IsSimpleSpectralProj.exists_norm_exp_mul_one_sub_le`);
* `exists_norm_expSec_le_of_ne_two`: `‖exp(t𝓛_n)‖ ≤ C e^{ηt}` for `|n| ≠ 2`
  (vendored `Dunford.exists_norm_exp_le_of_spectrum_re_lt`, given `SectorOneStable`);
* conjugation: `coeFn_star_prof`, `greenN_star`, `Lsec_star` (`𝓛_{-n} w̄ = conj(𝓛_n w)`,
  tex line 1356: "negative angular indices are complex conjugates"), `Lsec_star_eigen`: the mode
  `(λ, q)` in sector `2` gives `(λ̄, q̄)` in sector `-2`.

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)
open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-! ### G-4 -/

/-- **G-4** (`isSimpleSpectralProj_Lsec_two`): for `|m| = 2`, an eigenvector `𝓛_m q = z₀ q`,
`q ≠ 0`, `Re z₀ > 0`, with phase speed `c = i z₀/m`, the rank-one operator
`P = ℓ(·) q`, `ℓ = eigenfunctional`, is the spectral projection of the simple isolated
eigenvalue `z₀` of `𝓛_m` on `L²_M` (the Laurent form `Dunford.IsSimpleSpectralProj`). -/
theorem isSimpleSpectralProj_Lsec_two {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    (hn : 0 < (m.natAbs : ℝ)) {z₀ c : ℂ} (hc : c.im ≠ 0) (hcz : c * m = Complex.I * z₀)
    (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q) :
    IsSimpleSpectralProj (Lsec hM m) (rankOneProj (eigenfunctional hM m hn hc q) q) z₀ := by
  obtain ⟨hcomp, hone⟩ := eigenfunctional_spec hM hm hn hc hcz hz₀ hq0 hq
  exact Infra.CompactPerturb.isSimpleSpectralProj_of_compact (T := transportSec M m)
    (K := couplingSec hM m) (isCompactOperator_couplingSec hM m) (U := {z : ℂ | 0 < z.re})
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun z hz => isUnit_sub_transportSec M m hz) hz₀ hq hcomp hone
    (fun z hz w hw0 hw => Lsec_eigen_unique_of_natAbs_eq_two hM hm hz₀ hz hq hw hq0 hw0)

/-- **G-4, packaged**: the growing eigenvalue of sector `±2` has a bounded eigenfunctional `ℓ`,
`ℓ q = 1`, `ℓ ∘ 𝓛_m = z₀ ℓ`, and `ℓ(·) q` is its simple spectral projection. -/
theorem exists_isSimpleSpectralProj_Lsec_two {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q) :
    ∃ ℓ : ProfL2 M →L[ℂ] ℂ, ℓ q = 1 ∧ ℓ.comp (Lsec hM m) = z₀ • ℓ ∧
      IsSimpleSpectralProj (Lsec hM m) (rankOneProj ℓ q) z₀ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm0
  have hcz : Complex.I * z₀ / m * m = Complex.I * z₀ := div_mul_cancel₀ _ hmC
  obtain ⟨hc, hn, -, -⟩ := transfer_sector_eigen hM hm0 hz₀.ne' hcz hq
  obtain ⟨hcomp, hone⟩ := eigenfunctional_spec hM hm hn hc hcz hz₀ hq0 hq
  exact ⟨_, hone, hcomp, isSimpleSpectralProj_Lsec_two hM hm hn hc hcz hz₀ hq0 hq⟩

/-! ### Sector gap bounds -/

/-- The spectrum of `𝓛_m`, `|m| = 2`, other than the growing eigenvalue lies in `{Re z ≤ 0}`. -/
theorem re_le_zero_of_mem_spectrum_Lsec_two {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q)
    {z : ℂ} (hz : z ∈ spectrum ℂ (Lsec hM m)) (hzz : z ≠ z₀) : z.re ≤ 0 := by
  by_contra h
  push_neg at h
  have hmem : z ∈ {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM m) := ⟨h, hz⟩
  rw [spectrum_Lsec_rightHalf_eq_singleton hM hm hz₀ hq0 hq] at hmem
  exact hzz hmem

/-- The spectrum of `𝓛_n`, `|n| ≠ 2`, lies in `{Re z ≤ 0}` (given `SectorOneStable`). -/
theorem re_le_zero_of_mem_spectrum_Lsec_of_ne_two {M : ℝ} (hM : 1 < M)
    (h1 : SectorOneStable hM) {n : ℤ} (hn : n.natAbs ≠ 2) {z : ℂ}
    (hz : z ∈ spectrum ℂ (Lsec hM n)) : z.re ≤ 0 := by
  by_contra h
  push_neg at h
  have hmem : z ∈ {z : ℂ | 0 < z.re} ∩ spectrum ℂ (Lsec hM n) := ⟨h, hz⟩
  rw [spectrum_Lsec_rightHalf_of_ne_two hM h1 hn] at hmem
  exact hmem

/-- **Sector `±2` complement bound** (B0089 at `j = 0`, sector form): for every `η > 0`,
`‖exp(t𝓛_m)(1 - P)‖ ≤ C e^{ηt}`, `t ≥ 0`, for the simple spectral projection `P` of G-4. -/
theorem exists_norm_expSec_mul_one_sub_le {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q)
    {P : ProfL2 M →L[ℂ] ProfL2 M} (hP : IsSimpleSpectralProj (Lsec hM m) P z₀) {η : ℝ}
    (hη : 0 < η) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖expSec hM t m * (1 - P)‖ ≤ C * Real.exp (η * t) :=
  hP.exists_norm_exp_mul_one_sub_le fun z hz hzz =>
    (re_le_zero_of_mem_spectrum_Lsec_two hM hm hz₀ hq0 hq hz hzz).trans_lt hη

/-- **Sectors `|n| ≠ 2`** (B0100 at `j = 0`, sector form): for every `η > 0`,
`‖exp(t𝓛_n)‖ ≤ C e^{ηt}` for `t ≥ 0`. -/
theorem exists_norm_expSec_le_of_ne_two {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM)
    {n : ℤ} (hn : n.natAbs ≠ 2) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ‖expSec hM t n‖ ≤ C * Real.exp (η * t) :=
  Infra.Dunford.exists_norm_exp_le_of_spectrum_re_lt (Lsec hM n) fun z hz =>
    (re_le_zero_of_mem_spectrum_Lsec_of_ne_two hM h1 hn hz).trans_lt hη

/-! ### Complex conjugation: sector `-n` is the conjugate of sector `n` -/

theorem coeFn_star_prof {M : ℝ} (f : ProfL2 M) :
    (star f : ProfL2 M) =ᵐ[profileMeasure M] fun r => conj (f r) :=
  Lp.coeFn_star f

theorem star_smul_prof {M : ℝ} (a : ℂ) (u : ProfL2 M) :
    (star (a • u) : ProfL2 M) = conj a • star u := by
  apply Lp.ext
  filter_upwards [coeFn_star_prof (a • u), Lp.coeFn_smul a u, Lp.coeFn_smul (conj a) (star u),
    coeFn_star_prof u] with t h1 h2 h3 h4
  rw [h1, h3, h2, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul, map_mul]

theorem star_zero_prof {M : ℝ} : (star (0 : ProfL2 M) : ProfL2 M) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_star_prof (0 : ProfL2 M), Lp.coeFn_zero ℂ 2 (profileMeasure M)]
    with t h1 h2
  rw [h1, h2, Pi.zero_apply, map_zero]

theorem star_ne_zero_prof {M : ℝ} {f : ProfL2 M} (h0 : f ≠ 0) : (star f : ProfL2 M) ≠ 0 := by
  intro h
  apply h0
  rw [← star_star f, h, star_zero_prof]

/-- The Green inverse has a real kernel: `Δ_n⁻¹ w̄ = conj (Δ_n⁻¹ w)`. -/
theorem greenN_star {M : ℝ} (n : ℕ) (f : ProfL2 M) (r : ℝ) :
    greenN n (⇑(star f)) r = conj (greenN n f r) := by
  rw [greenN_congr n (coeFn_star_prof f), greenN, greenN, map_mul, map_neg, Complex.conj_ofReal,
    ← integral_conj]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ρ => ?_)
  simp only [map_mul, Complex.conj_ofReal]

/-- **Conjugate sectors** (tex line 1356): `𝓛_{-n} w̄ = conj (𝓛_n w)`. -/
theorem Lsec_star {M : ℝ} (hM : 1 < M) (n : ℤ) (w : ProfL2 M) :
    Lsec hM (-n) (star w) = star (Lsec hM n w) := by
  apply Lp.ext
  filter_upwards [coeFn_Lsec hM (-n) (star w), coeFn_star_prof (Lsec hM n w),
    coeFn_Lsec hM n w, coeFn_star_prof w] with r h1 h2 h3 h4
  rw [h1, h2, h3, h4, Int.natAbs_neg, greenN_star]
  simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- The conjugate of a sector-`n` eigenvector is a sector-`(-n)` eigenvector with the
conjugate eigenvalue: `(λ, q)` in sector `2` gives `(λ̄, q̄)` in sector `-2`. -/
theorem Lsec_star_eigen {M : ℝ} (hM : 1 < M) {n : ℤ} {z : ℂ} {q : ProfL2 M}
    (hq : Lsec hM n q = z • q) : Lsec hM (-n) (star q) = conj z • star q := by
  rw [Lsec_star, hq, star_smul_prof]

end UnforcedLeray.Planar
