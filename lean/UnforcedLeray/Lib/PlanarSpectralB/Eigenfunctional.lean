import UnforcedLeray.Lib.PlanarSpectralB.SectorSpectrum

/-!
# The eigenfunctional of the growing mode on `L²_M` (INF10 target G-3)


§5, Level G, target **G-3** (`eigenfunctional`: a bounded functional `ℓ` with
`ℓ ∘ 𝓛_2 = λ ℓ`, `ℓ q = 1`). Manuscript (`paper/main.tex`): the rank-one Riesz projection
`P f = q ℓ(f)` of the growing eigenvalue (lines 1432–1448, units `B0088`, `B0089`; lines
1518–1524, units `B0096`, `B0097`: `ℓ(f) = ⟨f, q^†⟩`, normalized by the nonzero bilinear
pairing `J_q`), and the bypass B2(c) of the scoping note (`J_q ≠ 0` from the index lemma).

**Construction (bypass of the adjoint eigenvector).** Instead of the `L²_M`-adjoint eigenvector
`q^†`, the functional is built in the phase-speed coordinates of the compiled Sturm layer. With
`c = iλ/m` (`c m = iλ`), `F₀ = transfer q` (target G-1) and the bilinear pairing
`b(F, G) = ∫ F (1 - N_m) G = ⟪star F, (1 - N_m) G⟫`,
`ℓ₀(g) = b(F₀, greenLogOp ((Ω - c)⁻¹ g))`. Then:
* `eigenfunctional0_comp_Lsec`: `ℓ₀ ∘ 𝓛_m = λ ℓ₀`, because `(Ω - c)⁻¹(i/m)(𝓛_m - λ)w` is the `u`
  of the intertwining identity `phaseSpeedOp_transfer_sub`, and `b(F₀, ·)` annihilates the
  range of `C_m - c` (`eq:st18-t00058`);
* `eigenfunctional0_self`: `ℓ₀(q) = b(F₀, F₀)` (`greenLog_divP_eigen`), which is nonzero for
  `|m| = 2` (`inner_star_B_ne_zero`, the index lemma S3).
`eigenfunctional = ℓ₀(q)⁻¹ ℓ₀`; **G-3** is `eigenfunctional_spec`. As a by-product,
`not_exists_jordan_Lsec_two`: the growing eigenvalue has no Jordan chain (B0076(b), tex line
1346).

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-- The profile form of `𝓛_m - z`: `(i/m)(𝓛_m w - z w) = (Ω - c) w - k Δ_{|m|}⁻¹ w` a.e., for
`c m = i z`. -/
theorem coeFn_Lsec_sub_smul {M : ℝ} (hM : 1 < M) {m : ℤ} (hm0 : m ≠ 0) {z c : ℂ}
    (hcz : c * m = Complex.I * z) (w : ProfL2 M) :
    ∀ᵐ r ∂profileMeasure M, ((Complex.I / m) • (Lsec hM m w - z • w)) r =
      ((radialOmega r : ℂ) - c) * w r - (radialK r : ℂ) * greenN m.natAbs w r := by
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm0
  filter_upwards [Lp.coeFn_smul (Complex.I / m) (Lsec hM m w - z • w),
    Lp.coeFn_sub (Lsec hM m w) (z • w), coeFn_Lsec hM m w, Lp.coeFn_smul z w] with r h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    div_mul_eq_mul_div, div_eq_iff hmC]
  linear_combination ((m : ℂ) * (radialK r : ℂ) * greenN m.natAbs w r -
    (m : ℂ) * (radialOmega r : ℂ) * w r) * Complex.I_sq + w r * hcz

/-- The unnormalized eigenfunctional `ℓ₀(g) = ⟪star F₀, (1 - N_{|m|}) greenLogOp((Ω - c)⁻¹g)⟫`,
`F₀ = transfer q`. -/
def eigenfunctional0 {M : ℝ} (hM : 1 < M) (m : ℤ) (hn : 0 < (m.natAbs : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) (q : ProfL2 M) : ProfL2 M →L[ℂ] ℂ :=
  (innerSL ℂ (star (transfer hM m.natAbs hc q) : Sturm.ComplexL2)) ∘L
    ((1 - Sturm.birmanSchwingerOperator hn) ∘L (greenLogOp hM m.natAbs ∘L divP M hc))

theorem eigenfunctional0_apply {M : ℝ} (hM : 1 < M) (m : ℤ) (hn : 0 < (m.natAbs : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) (q g : ProfL2 M) :
    eigenfunctional0 hM m hn hc q g =
      ⟪(star (transfer hM m.natAbs hc q) : Sturm.ComplexL2),
        (1 - Sturm.birmanSchwingerOperator hn) (greenLogOp hM m.natAbs (divP M hc g))⟫_ℂ :=
  rfl

/-- `ℓ₀` annihilates every `g` of the form `(Ω - c) w - k Δ_{|m|}⁻¹ w`. -/
theorem eigenfunctional0_eq_zero {M : ℝ} (hM : 1 < M) (m : ℤ) (hn : 0 < (m.natAbs : ℝ))
    {c : ℂ} (hc : c.im ≠ 0) {q : ProfL2 M}
    (hF : Sturm.phaseSpeedOp hn (transfer hM m.natAbs hc q) = c • transfer hM m.natAbs hc q)
    (w g : ProfL2 M)
    (hg : ∀ᵐ r ∂profileMeasure M,
      g r = ((radialOmega r : ℂ) - c) * w r - (radialK r : ℂ) * greenN m.natAbs w r) :
    eigenfunctional0 hM m hn hc q g = 0 := by
  have hu : ∀ᵐ r ∂profileMeasure M, ((radialOmega r : ℂ) - c) * (divP M hc g) r =
      ((radialOmega r : ℂ) - c) * w r - (radialK r : ℂ) * greenN m.natAbs w r := by
    filter_upwards [coeFn_divP M hc g, hg] with r h1 h2
    rw [h1, ← mul_assoc, mul_inv_cancel₀ (omega_sub_ne_zero hc _), one_mul, h2]
  rw [eigenfunctional0_apply, ← phaseSpeedOp_transfer_sub hM hn hc w (divP M hc g) hu]
  exact inner_star_B_phaseSpeed_sub hn hF _

/-- **`ℓ₀` is a left eigenvector**: `ℓ₀ ∘ 𝓛_m = z₀ ℓ₀` for `c m = i z₀`. -/
theorem eigenfunctional0_comp_Lsec {M : ℝ} (hM : 1 < M) {m : ℤ} (hm0 : m ≠ 0)
    (hn : 0 < (m.natAbs : ℝ)) {z₀ c : ℂ} (hc : c.im ≠ 0) (hcz : c * m = Complex.I * z₀)
    {q : ProfL2 M}
    (hF : Sturm.phaseSpeedOp hn (transfer hM m.natAbs hc q) = c • transfer hM m.natAbs hc q) :
    (eigenfunctional0 hM m hn hc q).comp (Lsec hM m) = z₀ • eigenfunctional0 hM m hn hc q := by
  refine ContinuousLinearMap.ext fun w => ?_
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm0
  have h0 := eigenfunctional0_eq_zero hM m hn hc hF w _ (coeFn_Lsec_sub_smul hM hm0 hcz w)
  rw [map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul] at h0
  have hI : Complex.I / m ≠ 0 := div_ne_zero Complex.I_ne_zero hmC
  have h1 := (mul_eq_zero.1 h0).resolve_left hI
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact sub_eq_zero.1 h1

/-- **`ℓ₀(q)` is the bilinear self-pairing** `b(F₀, F₀) = ⟪star F₀, (1 - N) F₀⟫` of the transferred
eigenvector. -/
theorem eigenfunctional0_self {M : ℝ} (hM : 1 < M) {m : ℤ} (hm0 : m ≠ 0)
    (hn : 0 < (m.natAbs : ℝ)) {z₀ c : ℂ} (hc : c.im ≠ 0) (hcz : c * m = Complex.I * z₀)
    {q : ProfL2 M} (hq : Lsec hM m q = z₀ • q)
    (hF : Sturm.phaseSpeedOp hn (transfer hM m.natAbs hc q) = c • transfer hM m.natAbs hc q) :
    eigenfunctional0 hM m hn hc q q =
      ⟪(star (transfer hM m.natAbs hc q) : Sturm.ComplexL2),
        (1 - Sturm.birmanSchwingerOperator hn) (transfer hM m.natAbs hc q)⟫_ℂ := by
  have hq' : ∀ᵐ r ∂profileMeasure M,
      (radialOmega r : ℂ) * q r - (radialK r : ℂ) * greenN m.natAbs q r = c * q r := by
    have h0 : (Complex.I / m) • (Lsec hM m q - z₀ • q) = 0 := by rw [hq, sub_self, smul_zero]
    filter_upwards [coeFn_Lsec_sub_smul hM hm0 hcz q, Lp.coeFn_zero ℂ 2 (profileMeasure M)]
      with r h1 h2
    rw [h0, h2] at h1
    simp only [Pi.zero_apply] at h1
    linear_combination -h1
  rw [eigenfunctional0_apply, greenLog_divP_eigen hM hn hc hq', map_sub, inner_sub_right,
    inner_star_B_phaseSpeed_sub hn hF, sub_zero]

/-- `b(F, F) ≠ 0` at `|m| = 2` (the index lemma), stated for the cast `((m.natAbs : ℕ) : ℝ)`. -/
theorem inner_star_B_ne_zero_of_eq_two {mR : ℝ} (hm2 : mR = 2) (hm : 0 < mR) {c : ℂ}
    {f : Sturm.ComplexL2} (hc : c.im ≠ 0) (h0 : f ≠ 0)
    (hf : Sturm.phaseSpeedOp hm f = c • f) :
    ⟪(star f : Sturm.ComplexL2), (1 - Sturm.birmanSchwingerOperator hm) f⟫_ℂ ≠ 0 := by
  subst hm2
  exact inner_star_B_ne_zero hc h0 hf

/-- **The eigenfunctional** `ℓ = ℓ₀(q)⁻¹ ℓ₀` of the sector-`m` eigenvector `q` with phase speed
`c` (`c m = iλ`). For `|m| = 2`, `q ≠ 0` and `Re λ > 0` it satisfies `ℓ ∘ 𝓛_m = λ ℓ` and
`ℓ q = 1` (`eigenfunctional_spec`). -/
def eigenfunctional {M : ℝ} (hM : 1 < M) (m : ℤ) (hn : 0 < (m.natAbs : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) (q : ProfL2 M) : ProfL2 M →L[ℂ] ℂ :=
  (eigenfunctional0 hM m hn hc q q)⁻¹ • eigenfunctional0 hM m hn hc q

/-- **G-3** (`eigenfunctional`, scoping note §5, Level G): for `|m| = 2`, an eigenvector
`𝓛_m q = z₀ q`, `q ≠ 0`, `Re z₀ > 0`, and the phase speed `c = i z₀/m`, the functional
`ℓ = eigenfunctional` is a bounded left eigenvector, `ℓ ∘ 𝓛_m = z₀ ℓ`, normalized by `ℓ q = 1`
(tex lines 1432–1448, 1518–1524). -/
theorem eigenfunctional_spec {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2)
    (hn : 0 < (m.natAbs : ℝ)) {z₀ c : ℂ} (hc : c.im ≠ 0) (hcz : c * m = Complex.I * z₀)
    (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q) :
    (eigenfunctional hM m hn hc q).comp (Lsec hM m) = z₀ • eigenfunctional hM m hn hc q ∧
      eigenfunctional hM m hn hc q q = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  obtain ⟨hc1, hn1, hF, hinj⟩ := transfer_sector_eigen hM hm0 hz₀.ne' hcz hq
  have hF' : Sturm.phaseSpeedOp hn (transfer hM m.natAbs hc q) =
      c • transfer hM m.natAbs hc q := hF
  have hm2 : ((m.natAbs : ℕ) : ℝ) = 2 := by
    rw [hm]
    norm_num
  have hself := eigenfunctional0_self hM hm0 hn hc hcz hq hF'
  have hne : eigenfunctional0 hM m hn hc q q ≠ 0 := by
    rw [hself]
    exact inner_star_B_ne_zero_of_eq_two hm2 hn hc (hinj hq0) hF'
  refine ⟨?_, ?_⟩
  · rw [eigenfunctional, ContinuousLinearMap.smul_comp,
      eigenfunctional0_comp_Lsec hM hm0 hn hc hcz hF', smul_comm]
  · rw [eigenfunctional, ContinuousLinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]

/-- **No Jordan chain at the growing eigenvalue** (B0076(b), tex line 1346; also the algebraic
simplicity in B0083): for `|m| = 2`, `𝓛_m q = z₀ q`, `q ≠ 0`, `Re z₀ > 0`, there is no `w`
with `(𝓛_m - z₀) w = q`. -/
theorem not_exists_jordan_Lsec_two {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m.natAbs = 2) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM m q = z₀ • q) :
    ¬ ∃ w : ProfL2 M, Lsec hM m w - z₀ • w = q := by
  rintro ⟨w, hw⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm0
  have hcz : Complex.I * z₀ / m * m = Complex.I * z₀ := div_mul_cancel₀ _ hmC
  obtain ⟨hc, hn, -, -⟩ := transfer_sector_eigen hM hm0 hz₀.ne' hcz hq
  obtain ⟨hcomp, hone⟩ := eigenfunctional_spec hM hm hn hc hcz hz₀ hq0 hq
  have h := congrArg (fun T : ProfL2 M →L[ℂ] ℂ => T w) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  have h2 : eigenfunctional hM m hn hc q (Lsec hM m w - z₀ • w) = 0 := by
    rw [map_sub, map_smul, h, smul_eq_mul, sub_self]
  rw [hw, hone] at h2
  exact one_ne_zero h2

end UnforcedLeray.Planar
