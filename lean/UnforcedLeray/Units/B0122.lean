import UnforcedLeray.Units.B0122.Coeff
import UnforcedLeray.Units.B0086

/-!
# B0122: `L₀` is bounded on every `X_{G,j}`

Blueprint unit **B0122** (lemma, `unlabeled:1867`), `paper/main.tex` lines 1867--1871 (proof of
"Finite-order regularity", Section `sec:st18-2021`). Dependencies: B0121 (`eq:st18-t00100`,
`Units/B0121.lean`: graph norms of `X_{G,j}` are Gaussian-weighted Sobolev norms), B0086
(`eq:st18-t00062`, `Units/B0086.lean`: the pointwise Green bound), B0012 (`eq:st18-t00006`,
`Units/B0012.lean`: `L₀ = -2iΩ + 2ikR` as a bounded operator on `X_G`). Infrastructure INF11
(global elliptic regularity), INF21 (Leibniz in weighted Sobolev norms).

## The manuscript's claim (tex lines 1867--1871)

"The bounded Euler operator preserves every `X_{G,j}`. Multiplication by `Ω` is bounded by
Leibniz. For `kRf`, `eq:st18-t00062` gives `‖Rf‖₂ ≤ C‖f‖_{X_G}`; global elliptic regularity gives
`‖Rf‖_{H^j} ≤ C_j(‖f‖_{H^{max(j-2,0)}} + ‖f‖_{X_G})`. Every `G^{-1/2}∂^α k` is bounded, so another
Leibniz expansion gives `‖kRf‖_{X_{G,j}} ≤ C_j‖f‖_{X_{G,j}}`."

## What is formalized

* **`L0_mem_XGj`** (the unit): for every `j`, there is `C_j` such that for all `f ∈ X_{G,j}`,
  `L₀ f ∈ X_{G,j}` and `‖L₀ f‖²_{X_{G,j}} ≤ C_j ‖f‖²_{X_{G,j}}` (squared graph norms
  `B0121.graphNormSq`); `L0_mem_XGj_norm` is the same with the graph norms themselves. It is
  conditional on the named hypothesis `GreenEllipticRegularity j` (below).
* **`omegaOp_mem_XGj`** (unconditional): multiplication by `Ω` maps `X_{G,j}` boundedly into
  itself ("Multiplication by `Ω` is bounded by Leibniz").
* **`kROp_mem_XGj`**: `f ↦ kRf` maps `X_{G,j}` boundedly into itself, given
  `GreenEllipticRegularity j`.

## The route (as in the manuscript)

B0121 turns `f ∈ X_{G,j}` into weak derivatives `∂^α f ∈ L²(ℝ², G⁻¹dy)`, `|α| ≤ j`, controlled
by the graph norm, and back. Both coefficients are `√G ψ` with `ψ` Schwartz
(`Units/B0122/Coeff.lean`: `Ω = √G psiOmega`, `k = √G psiK`), and `∂ᵢ(√G ψ) = √G (∂ᵢ - yᵢ/4)ψ`;
so every `G^{-1/2}∂^α Ω` and `G^{-1/2}∂^α k` is bounded (`exists_AopL_bound`), and the Leibniz
expansion `Units/B0122/Leibniz.lean` (`leibniz_hasWeakDerivOn`, `eLpNorm_leibC_le`) bounds the
Gaussian norms of `∂^α(√G ψ · F)` by the plain `L²(ℝ²)` norms of `∂^β F`, `|β| ≤ |α|`
(`mem_XGj_of_planar_eq`). For `Ω f` these are bounded by the Gaussian norms of `∂^β f`; for
`kRf` they are the `H^j(ℝ²)` norm of `Rf`, which the elliptic estimate bounds by
`‖f‖_{H^{max(j-2,0)}} + ‖f‖_{X_G}`, and `‖f‖_{H^{j-2}} ≤ (4π)^{-1/2}‖f‖_{L²(G⁻¹dy)}`-type bounds
(`integral_sq_le_gauss`) close the estimate.

## The named hypothesis (missing theory: INF11 S9a, global elliptic regularity)

`GreenEllipticRegularity j` is the displayed inequality of tex line 1869 for the planar function
`u = Rf(r)e^{2iϑ}`: whenever the planar function of `f ∈ X_G` has weak derivatives
`∂^α f ∈ L²(ℝ²)` for `|α| ≤ max(j-2, 0)`, `u` has weak derivatives `∂^β u ∈ L²(ℝ²)` for
`|β| ≤ j`, with `∑_{|β|≤j} ‖∂^β u‖²₂ ≤ C_j(∑_{|α|≤j-2} ‖∂^α f‖²₂ + ‖f‖²_{X_G})`. It is the
manuscript's own statement, a consequence of (i) `Δu = f` in `𝒟'(ℝ²)` (the Green inverse
`R = Δ₂⁻¹`, B0011, glued across the origin), (ii) `u ∈ L²(ℝ²)` with `‖u‖₂ ≤ C‖f‖_{X_G}`
(B0086), and (iii) the Fourier-multiplier estimate `‖u‖_{H^{m+2}} ≤ C(‖Δu‖_{H^m} + ‖u‖₂)` on
`ℝ²`, none of which (i, iii) is built.

## Junk values

* `HasWeakDerivOn` pairs with Bochner integrals, which are `0` for non-integrable integrands. The
  hypothesis is meaningful because `u` is locally integrable: `locallyIntegrable_planarR`
  (from B0086, `|Rf| ≤ C‖f‖ min(r, r⁻²) ≤ C‖f‖`, and `R f 0 = 0`), so the order-zero derivative
  of the hypothesis is `u` itself a.e. (`ae_eq_zero_index`).
* `B0011.R` is only meaningful at `r > 0`; `u` uses it at `r = |y| > 0` off the null set `{0}`.
* `X_{G,j}` is `B0121.XGj j`, the domain of `(I - D)^{j/2}`, and the graph norm is
  `B0121.graphNormSq` (`‖f‖² + ‖(I - D)^{j/2} f‖²`), so no junk value of an unbounded operator
  enters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ENNReal ContDiff Real

namespace UnforcedLeray.B0122

open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0010

/-! ## `L²` norms on `ℝ²` -/

theorem eLpNorm_eq_sqrt_integral {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 volume) :
    eLpNorm g 2 volume = ENNReal.ofReal (Real.sqrt (∫ z, ‖g z‖ ^ 2)) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

/-- `‖F‖²_{L²(ℝ²)} ≤ (4π)⁻¹ ‖F‖²_{L²(ℝ², G⁻¹dy)}` (`G ≤ (4π)⁻¹`). -/
theorem integral_sq_le_gauss {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) :
    ∫ z, ‖F z‖ ^ 2 ≤ B0093.sqrtConst ^ 2 * gaussNormSq F := by
  have hc : MemLp (B0093.conjG F) 2 volume := hF
  have i1 : Integrable (fun z => ‖B0093.conjG F z‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).1 hc
  have i2 : Integrable (fun z => ‖F z‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.memLp.aestronglyMeasurable).1 hF.memLp
  have e : gaussNormSq F = ∫ z, ‖B0093.conjG F z‖ ^ 2 := by
    rw [gaussNormSq]
    congr 1
    funext z
    rw [norm_conjG_sq]
  rw [e, ← integral_const_mul]
  refine integral_mono i2 (i1.const_mul _) (fun z => ?_)
  have h := sqGc_mul_conjG F z
  calc ‖F z‖ ^ 2 = ‖sqGc z‖ ^ 2 * ‖B0093.conjG F z‖ ^ 2 := by rw [← h, norm_mul, mul_pow]
    _ ≤ B0093.sqrtConst ^ 2 * ‖B0093.conjG F z‖ ^ 2 := by
        gcongr
        exact norm_sqGc_le z

theorem conjG_sqGc_mul (L : ℝ × ℝ → ℂ) : B0093.conjG (fun z => sqGc z * L z) = L := by
  funext z
  rw [conjG_apply, sqGc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (sqG_pos z).ne',
    Complex.ofReal_one, one_mul]

theorem memGaussL2_sqGc_mul {L : ℝ × ℝ → ℂ} (hL : MemLp L 2 volume) :
    MemGaussL2 (fun z => sqGc z * L z) := by
  unfold MemGaussL2
  rw [conjG_sqGc_mul]
  exact hL

/-- The Gaussian norm of `√G L` is the plain `L²` norm of `L`. -/
theorem gaussNormSq_sqGc_mul (L : ℝ × ℝ → ℂ) :
    ∫ z, ‖sqGc z * L z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ = ∫ z, ‖L z‖ ^ 2 := by
  congr 1
  funext z
  have h := norm_conjG_sq (fun z => sqGc z * L z) z
  rw [conjG_sqGc_mul] at h
  exact h.symm

/-- The order-zero member of a weak-derivative family is the function itself, a.e. -/
theorem ae_eq_zero_index {F : ℝ × ℝ → ℂ} {G : ℕ × ℕ → ℝ × ℝ → ℂ} (hF : LocallyIntegrable F)
    (hG : LocallyIntegrable (G (0, 0))) (h : HasWeakDerivOn univ (pdListR (0, 0)) F (G (0, 0))) :
    G (0, 0) =ᵐ[volume] F := by
  have h0 : HasWeakDerivOn univ (pdListR (0, 0)) F F := by
    intro φ _
    simp [pdListR]
  have := hasWeakDerivOn_ae_eq isOpen_univ (hG.locallyIntegrableOn univ)
    (hF.locallyIntegrableOn univ) h h0
  filter_upwards [this] with z hz using hz (mem_univ z)

/-! ## The transfer: a Leibniz family gives membership in `X_{G,j}` -/

/-- If the planar function of `h' ∈ X_G` is `√G ψ · g []` a.e., where `g u = ∂_u (g [])` weakly
in `L²(ℝ²)` with `‖g u‖₂ ≤ N` for `|u| ≤ j`, and every `A_{us}ψ`, `|us| ≤ j`, is bounded by
`M`, then `h' ∈ X_{G,j}` with `‖h'‖²_{X_{G,j}} ≤ 2^j/π · #{|α| ≤ j} · (2^j M N)²`. -/
theorem mem_XGj_of_planar_eq {j : ℕ} (h' : XG) (ψ : S2) (g : List (Fin 2) → ℝ × ℝ → ℂ)
    (hg : IsLFam j g) (hpl : planar h' =ᵐ[volume] fun z => gS ψ z * g [] z)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ us : List (Fin 2), us.length ≤ j → ∀ z, ‖AopL us ψ z‖ ≤ M)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ u : List (Fin 2), u.length ≤ j → eLpNorm (g u) 2 volume ≤ ENNReal.ofReal N) :
    ∃ hm : h' ∈ XGj j,
      graphNormSq j ⟨h', hm⟩ ≤ 2 ^ j / π * ((multiIdx j).card * (2 ^ j * M * N) ^ 2) := by
  set H : ℕ × ℕ → ℝ × ℝ → ℂ := fun α z => sqGc z * leibC (wordOf α) ψ g z with hH
  have hlen : ∀ α ∈ multiIdx j, (wordOf α).length ≤ j := fun α hα => by
    rw [length_wordOf]
    exact mem_multiIdx.1 hα
  have hmem : ∀ α ∈ multiIdx j, MemLp (leibC (wordOf α) ψ g) 2 volume := fun α hα =>
    memLp_leibC _ ψ g fun u hu => hg.memLp u (hu.trans (hlen α hα))
  have hfam : ∀ α ∈ multiIdx j,
      MemGaussL2 (H α) ∧ HasWeakDerivOn univ (pdListR α) (planar h') (H α) := by
    intro α hα
    refine ⟨memGaussL2_sqGc_mul (hmem α hα), ?_⟩
    have hl := leibniz_hasWeakDerivOn (wordOf α) ψ g (hg.mono (hlen α hα))
    rw [dl_wordOf] at hl
    exact hasWeakDerivOn_congr hl hpl.symm (Eventually.of_forall fun z => rfl)
  have hbound : ∀ α ∈ multiIdx j,
      ∫ z, ‖H α z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ ≤ (2 ^ j * M * N) ^ 2 := by
    intro α hα
    rw [hH, gaussNormSq_sqGc_mul]
    have hb := eLpNorm_leibC_le (wordOf α) ψ g M (ENNReal.ofReal N)
      (fun us hus z => hM us (hus.trans (hlen α hα)) z)
      (fun u hu => hg.memLp u (hu.trans (hlen α hα)))
      (fun u hu => hN u (hu.trans (hlen α hα)))
    rw [eLpNorm_eq_sqrt_integral (hmem α hα)] at hb
    have h2 : (2 : ℝ≥0∞) ^ (wordOf α).length * (ENNReal.ofReal M * ENNReal.ofReal N) ≤
        ENNReal.ofReal (2 ^ j * M * N) := by
      have e : ENNReal.ofReal (2 ^ j * M * N) =
          2 ^ j * (ENNReal.ofReal M * ENNReal.ofReal N) := by
        rw [mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hM0,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      rw [e]
      gcongr ?_ * _
      exact pow_le_pow_right₀ (by norm_num) (hlen α hα)
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hb.trans h2)
    have h4 : 0 ≤ ∫ z, ‖leibC (wordOf α) ψ g z‖ ^ 2 := integral_nonneg fun z => by positivity
    calc ∫ z, ‖leibC (wordOf α) ψ g z‖ ^ 2
        = Real.sqrt (∫ z, ‖leibC (wordOf α) ψ g z‖ ^ 2) ^ 2 := (Real.sq_sqrt h4).symm
      _ ≤ (2 ^ j * M * N) ^ 2 := by gcongr
  obtain ⟨hm, h1, -⟩ := graphNorm_equiv j h' H hfam
  refine ⟨hm, ?_⟩
  have hsum : ∑ α ∈ multiIdx j, ∫ z, ‖H α z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ ≤
      (multiIdx j).card * (2 ^ j * M * N) ^ 2 := by
    calc _ ≤ ∑ α ∈ multiIdx j, (2 ^ j * M * N) ^ 2 := Finset.sum_le_sum hbound
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpi := Real.pi_pos
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h5 := h1.trans hsum
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  rw [div_mul_eq_mul_div, div_le_iff₀ h2j] at h5
  linarith

/-! ## The Gaussian derivatives of `f ∈ X_{G,j}` (B0121) -/

/-- B0121: `f ∈ X_{G,j}` has weak derivatives `∂^α f ∈ L²(ℝ², G⁻¹dy)`, `|α| ≤ j`, with
`∑_α ‖∂^α f‖²_{L²(G⁻¹dy)} ≤ 2π(j+1)(j+2)^j ‖f‖²_{X_{G,j}}`. -/
theorem gauss_family (j : ℕ) (f : XG) (hf : f ∈ XGj j) :
    ∃ G : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ α ∈ multiIdx j, MemGaussL2 (G α) ∧ HasWeakDerivOn univ (pdListR α) (planar f) (G α)) ∧
      ∑ α ∈ multiIdx j, gaussNormSq (G α) ≤
        2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩ := by
  obtain ⟨G, hG⟩ := exists_weakDerivs j f hf
  obtain ⟨_, -, h2⟩ := graphNorm_equiv j f G hG
  exact ⟨G, hG, h2⟩

theorem graphNormSq_nonneg (j : ℕ) (f : (fracPow j).domain) : 0 ≤ graphNormSq j f := by
  unfold graphNormSq
  positivity

theorem norm_sq_le_graphNormSq (j : ℕ) (f : (fracPow j).domain) :
    ‖(f : XG)‖ ^ 2 ≤ graphNormSq j f := by
  unfold graphNormSq
  have := sq_nonneg ‖fracPow j f‖
  linarith

/-! ## Multiplication by `Ω` -/

/-- **Multiplication by `Ω` is bounded on `X_{G,j}`** (tex line 1868, "Multiplication by `Ω` is
bounded by Leibniz"): for every `j` there is `C_j` with `Ω f ∈ X_{G,j}` and
`‖Ω f‖²_{X_{G,j}} ≤ C_j ‖f‖²_{X_{G,j}}` for all `f ∈ X_{G,j}`. -/
theorem omegaOp_mem_XGj (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ XGj j,
      ∃ hm : B0012.omegaOp f ∈ XGj j,
        graphNormSq j ⟨B0012.omegaOp f, hm⟩ ≤ C * graphNormSq j ⟨f, hf⟩ := by
  obtain ⟨M, hM0, hM⟩ := exists_AopL_bound j psiOmega
  have hc1 : 0 ≤ 2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j := by positivity
  refine ⟨2 ^ j / π * ((multiIdx j).card * (2 ^ j * M * B0093.sqrtConst) ^ 2 *
      (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j)),
    mul_nonneg (div_nonneg (by positivity) Real.pi_pos.le) (mul_nonneg (by positivity) hc1),
    fun f hf => ?_⟩
  obtain ⟨G, hG, hsum⟩ := gauss_family j f hf
  have hT := graphNormSq_nonneg j ⟨f, hf⟩
  have hfam : ∀ α ∈ multiIdx j,
      MemLp (G α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) (planar f) (G α) :=
    fun α hα => ⟨(hG α hα).1.memLp, (hG α hα).2⟩
  have hg := isLFam_of_family hfam
  have hone : ∀ α ∈ multiIdx j, gaussNormSq (G α) ≤
      2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩ := fun α hα =>
    (Finset.single_le_sum (fun β _ => gaussNormSq_nonneg (G β)) hα).trans hsum
  have hN : ∀ u : List (Fin 2), u.length ≤ j → eLpNorm (G (cnt u)) 2 volume ≤
      ENNReal.ofReal (B0093.sqrtConst * Real.sqrt
        (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩)) := by
    intro u hu
    have hα : cnt u ∈ multiIdx j := by
      rw [mem_multiIdx, cnt_le]
      exact hu
    rw [eLpNorm_eq_sqrt_integral (hG _ hα).1.memLp]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := integral_sq_le_gauss (hG _ hα).1
    have h2 := hone _ hα
    have hs := B0093.sqrtConst_pos
    calc Real.sqrt (∫ z, ‖G (cnt u) z‖ ^ 2)
        ≤ Real.sqrt (B0093.sqrtConst ^ 2 *
            (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩)) :=
          Real.sqrt_le_sqrt (h1.trans (by gcongr))
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le]
  have h00 := hG _ (zero_mem_multiIdx j)
  have hpl : planar (B0012.omegaOp f) =ᵐ[volume] fun z => gS psiOmega z * G (0, 0) z := by
    have h0 : G (0, 0) =ᵐ[volume] planar f :=
      ae_eq_zero_index (memGaussL2_planar f).locallyIntegrable h00.1.locallyIntegrable h00.2
    have h1 : planar (B0012.omegaOp f) =ᵐ[volume]
        angularTwoField (fun r => (GaussianVortex.radialOmega r : ℂ) * f r) :=
      angularTwoField_ae_eq_of_xG (B0012.coeFn_omegaOp f)
    filter_upwards [h0, h1] with z hz0 hz1
    rw [hz1, angularTwoField_mul, hz0, gS_psiOmega]
    rfl
  obtain ⟨hm, hb⟩ := mem_XGj_of_planar_eq (B0012.omegaOp f) psiOmega (fun u => G (cnt u)) hg
    hpl hM0 (fun us hus z => hM us hus z)
    (mul_nonneg B0093.sqrtConst_pos.le (Real.sqrt_nonneg _)) hN
  refine ⟨hm, hb.trans (le_of_eq ?_)⟩
  have hs2 := Real.sq_sqrt (mul_nonneg hc1 hT)
  rw [show ∀ a b c d : ℝ, (a * b * (c * d)) ^ 2 = (a * b * c) ^ 2 * d ^ 2 from
    fun a b c d => by ring, hs2]
  ring

/-! ## The Green term `kRf` -/

/-- **Named hypothesis: global elliptic regularity for the Green inverse `R`** (tex lines
1868--1869, "global elliptic regularity gives `‖Rf‖_{H^j} ≤ C_j(‖f‖_{H^{max(j-2,0)}} +
‖f‖_{X_G})`"; infrastructure INF11 S9a, the `p = 2` Fourier bridge with `ellipticH2`, not yet
built). For the planar function `u = Rf(r)e^{2iϑ}` of `f ∈ X_G` (`B0011.R`, the Green inverse
`eq:st18-t00007`): if the planar function of `f` has weak derivatives `gF α = ∂^α f ∈ L²(ℝ²)` for
all `|α| ≤ max(j-2, 0)` (natural subtraction `j - 2`), then `u` has weak derivatives
`gu β = ∂^β u ∈ L²(ℝ²)` for all `|β| ≤ j` and
`∑_{|β|≤j} ‖∂^β u‖²₂ ≤ C_j (∑_{|α|≤j-2} ‖∂^α f‖²₂ + ‖f‖²_{X_G})` (the squared form of the
manuscript's inequality). `u` is locally integrable (`locallyIntegrable_planarR`), so the weak
derivatives are not junk. -/
def GreenEllipticRegularity (j : ℕ) : Prop :=
  ∃ C : ℝ, ∀ f : XG, ∀ gF : ℕ × ℕ → ℝ × ℝ → ℂ,
    (∀ α ∈ multiIdx (j - 2), MemLp (gF α) 2 volume ∧
      HasWeakDerivOn univ (pdListR α) (planar f) (gF α)) →
    ∃ gu : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ β ∈ multiIdx j, MemLp (gu β) 2 volume ∧
        HasWeakDerivOn univ (pdListR β) (angularTwoField (B0011.R ⇑f)) (gu β)) ∧
      ∑ β ∈ multiIdx j, ∫ z, ‖gu β z‖ ^ 2 ≤
        C * ((∑ α ∈ multiIdx (j - 2), ∫ z, ‖gF α z‖ ^ 2) + ‖f‖ ^ 2)

theorem polarRadius_pos {z : ℝ × ℝ} (hz : z ≠ 0) : 0 < (polarCoord z).1 := by
  show 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2)
  rw [Real.sqrt_pos]
  by_contra hle
  push Not at hle
  have h1 : z.1 ^ 2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  have h2 : z.2 ^ 2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  exact hz (Prod.ext (pow_eq_zero_iff two_ne_zero |>.1 h1) (pow_eq_zero_iff two_ne_zero |>.1 h2))

/-- The planar function `u = Rf(r)e^{2iϑ}` of `f ∈ X_G` is bounded (by B0086,
`|Rf(r)| ≤ C‖f‖ min(r, r⁻²) ≤ C‖f‖`, and `Rf(0) = 0`), hence locally integrable. -/
theorem locallyIntegrable_planarR (f : XG) :
    LocallyIntegrable (angularTwoField (B0011.R ⇑f)) volume := by
  obtain ⟨C, hC0, hC⟩ := B0086.green_bound_XG
  have hbd : ∀ z, ‖angularTwoField (B0011.R ⇑f) z‖ ≤ C * ‖f‖ := by
    intro z
    rw [angularTwoField, norm_mul, norm_exp_two_mul_I, mul_one]
    rcases eq_or_ne z 0 with h | h
    · have h0 : (polarCoord z).1 = 0 := by
        rw [h]
        show Real.sqrt ((0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2) = 0
        simp
      rw [h0]
      simp only [B0011.R, Complex.ofReal_zero, intervalIntegral.integral_same, mul_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, norm_zero]
      positivity
    · have hr := polarRadius_pos h
      refine (hC f _ hr).1.trans ?_
      have hmin : min (polarCoord z).1 ((polarCoord z).1 ^ 2)⁻¹ ≤ 1 := by
        rcases le_or_gt (polarCoord z).1 1 with h1 | h1
        · exact (min_le_left _ _).trans h1
        · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ (by nlinarith))
      have h0 : 0 ≤ C * ‖f‖ := by positivity
      calc C * ‖f‖ * min (polarCoord z).1 ((polarCoord z).1 ^ 2)⁻¹ ≤ C * ‖f‖ * 1 := by gcongr
        _ = C * ‖f‖ := mul_one _
  have hr : Continuous fun z : ℝ × ℝ => (polarCoord z).1 := by
    show Continuous fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)
    fun_prop
  have hcont : ContinuousOn (fun z : ℝ × ℝ => B0011.R ⇑f (polarCoord z).1) ({0}ᶜ : Set (ℝ × ℝ)) :=
    (B0012.continuousOn_R f).comp hr.continuousOn fun z hz => polarRadius_pos hz
  have hae1 : AEStronglyMeasurable (fun z : ℝ × ℝ => B0011.R ⇑f (polarCoord z).1) volume := by
    have h := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ × ℝ)).compl
    have hfull : volume.restrict ({0}ᶜ : Set (ℝ × ℝ)) = volume :=
      Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (measure_singleton 0))
    rwa [hfull] at h
  have hae2 : AEStronglyMeasurable
      (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * ((polarCoord z).2 : ℂ))) volume :=
    ((Complex.measurable_ofReal.comp measurable_polarCoord_fun.snd).const_mul
      (2 * Complex.I)).cexp.aestronglyMeasurable
  have haesm : AEStronglyMeasurable (angularTwoField (B0011.R ⇑f)) volume := hae1.mul hae2
  exact (memLp_top_of_bound haesm (C * ‖f‖) (Eventually.of_forall hbd)).locallyIntegrable le_top

/-- **The Green term is bounded on `X_{G,j}`** (tex lines 1868--1871): given the elliptic
estimate `GreenEllipticRegularity j`, for every `j` there is `C_j` with `kRf ∈ X_{G,j}` and
`‖kRf‖²_{X_{G,j}} ≤ C_j ‖f‖²_{X_{G,j}}` for all `f ∈ X_{G,j}`. -/
theorem kROp_mem_XGj (j : ℕ) (hE : GreenEllipticRegularity j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ XGj j,
      ∃ hm : B0012.kROp f ∈ XGj j,
        graphNormSq j ⟨B0012.kROp f, hm⟩ ≤ C * graphNormSq j ⟨f, hf⟩ := by
  obtain ⟨CE, hCE⟩ := hE
  obtain ⟨M, hM0, hM⟩ := exists_AopL_bound j psiK
  have hc1 : 0 ≤ 2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j := by positivity
  have hCE' : 0 ≤ max CE 0 := le_max_right _ _
  have hK : 0 ≤ max CE 0 * (B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j) + 1) :=
    mul_nonneg hCE' (by positivity)
  refine ⟨2 ^ j / π * ((multiIdx j).card * (2 ^ j * M) ^ 2 *
      (max CE 0 * (B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j) + 1))),
    mul_nonneg (div_nonneg (by positivity) Real.pi_pos.le) (mul_nonneg (by positivity) hK),
    fun f hf => ?_⟩
  obtain ⟨G, hG, hsum⟩ := gauss_family j f hf
  have hT := graphNormSq_nonneg j ⟨f, hf⟩
  have hfT : ‖f‖ ^ 2 ≤ graphNormSq j ⟨f, hf⟩ := norm_sq_le_graphNormSq j ⟨f, hf⟩
  have hsub : multiIdx (j - 2) ⊆ multiIdx j := multiIdx_mono (Nat.sub_le j 2)
  obtain ⟨gu, hgu, hgub⟩ := hCE f G fun α hα => ⟨(hG α (hsub hα)).1.memLp, (hG α (hsub hα)).2⟩
  have hS : ∑ α ∈ multiIdx (j - 2), ∫ z, ‖G α z‖ ^ 2 ≤
      B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩) := by
    calc ∑ α ∈ multiIdx (j - 2), ∫ z, ‖G α z‖ ^ 2
        ≤ ∑ α ∈ multiIdx (j - 2), B0093.sqrtConst ^ 2 * gaussNormSq (G α) :=
          Finset.sum_le_sum fun α hα => integral_sq_le_gauss (hG α (hsub hα)).1
      _ ≤ ∑ α ∈ multiIdx j, B0093.sqrtConst ^ 2 * gaussNormSq (G α) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            fun α _ _ => mul_nonneg (sq_nonneg _) (gaussNormSq_nonneg _)
      _ = B0093.sqrtConst ^ 2 * ∑ α ∈ multiIdx j, gaussNormSq (G α) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by gcongr
  have hS0 : 0 ≤ ∑ α ∈ multiIdx (j - 2), ∫ z, ‖G α z‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => integral_nonneg fun z => by positivity
  have hB : ∑ β ∈ multiIdx j, ∫ z, ‖gu β z‖ ^ 2 ≤
      max CE 0 * (B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j) + 1) *
        graphNormSq j ⟨f, hf⟩ := by
    calc ∑ β ∈ multiIdx j, ∫ z, ‖gu β z‖ ^ 2
        ≤ CE * ((∑ α ∈ multiIdx (j - 2), ∫ z, ‖G α z‖ ^ 2) + ‖f‖ ^ 2) := hgub
      _ ≤ max CE 0 * ((∑ α ∈ multiIdx (j - 2), ∫ z, ‖G α z‖ ^ 2) + ‖f‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS0 (sq_nonneg _))
      _ ≤ max CE 0 * (B0093.sqrtConst ^ 2 *
            (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩) +
              graphNormSq j ⟨f, hf⟩) := by gcongr
      _ = _ := by ring
  have hone : ∀ β ∈ multiIdx j, ∫ z, ‖gu β z‖ ^ 2 ≤
      max CE 0 * (B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j) + 1) *
        graphNormSq j ⟨f, hf⟩ := fun β hβ =>
    (Finset.single_le_sum (fun β _ => integral_nonneg fun z => by positivity) hβ).trans hB
  have hg := isLFam_of_family hgu
  have hN : ∀ u : List (Fin 2), u.length ≤ j → eLpNorm (gu (cnt u)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (max CE 0 *
        (B0093.sqrtConst ^ 2 * (2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j) + 1) *
          graphNormSq j ⟨f, hf⟩)) := by
    intro u hu
    have hα : cnt u ∈ multiIdx j := by
      rw [mem_multiIdx, cnt_le]
      exact hu
    rw [eLpNorm_eq_sqrt_integral (hgu _ hα).1]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hone _ hα))
  have h00 := hgu _ (zero_mem_multiIdx j)
  have hpl : planar (B0012.kROp f) =ᵐ[volume] fun z => gS psiK z * gu (0, 0) z := by
    have h0 : gu (0, 0) =ᵐ[volume] angularTwoField (B0011.R ⇑f) :=
      ae_eq_zero_index (locallyIntegrable_planarR f) (h00.1.locallyIntegrable (by norm_num)) h00.2
    have h1 : planar (B0012.kROp f) =ᵐ[volume]
        angularTwoField (fun r => (GaussianVortex.radialK r : ℂ) * B0011.R ⇑f r) :=
      angularTwoField_ae_eq_of_xG (B0012.coeFn_kROp f)
    filter_upwards [h0, h1] with z hz0 hz1
    rw [hz1, angularTwoField_mul, hz0, gS_psiK]
  obtain ⟨hm, hb⟩ := mem_XGj_of_planar_eq (B0012.kROp f) psiK (fun u => gu (cnt u)) hg
    hpl hM0 (fun us hus z => hM us hus z) (Real.sqrt_nonneg _) hN
  refine ⟨hm, hb.trans (le_of_eq ?_)⟩
  have hs2 := Real.sq_sqrt (mul_nonneg hK hT)
  rw [show ∀ a b d : ℝ, (a * b * d) ^ 2 = (a * b) ^ 2 * d ^ 2 from fun a b d => by ring, hs2]
  ring

/-! ## `L₀ = -2iΩ + 2ikR` -/

theorem sq_norm_combo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c d : ℂ) (x y : E) :
    ‖c • x + d • y‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 * ‖x‖ ^ 2 + 2 * ‖d‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 := norm_add_le (c • x) (d • y)
  rw [norm_smul, norm_smul] at h1
  have h2 : ‖c • x + d • y‖ ^ 2 ≤ (‖c‖ * ‖x‖ + ‖d‖ * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖c‖ * ‖x‖ - ‖d‖ * ‖y‖)]

theorem graphNormSq_combo (j : ℕ) (c d : ℂ) (a b : (fracPow j).domain) :
    graphNormSq j (c • a + d • b) ≤
      2 * ‖c‖ ^ 2 * graphNormSq j a + 2 * ‖d‖ ^ 2 * graphNormSq j b := by
  unfold graphNormSq
  rw [LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_smul]
  have hc : ((c • a + d • b : (fracPow j).domain) : XG) = c • (a : XG) + d • (b : XG) := rfl
  rw [hc]
  have k1 := sq_norm_combo c d (a : XG) (b : XG)
  have k2 := sq_norm_combo c d (fracPow j a) (fracPow j b)
  linarith

/-- **B0122 (tex lines 1867--1871): `L₀` maps every `X_{G,j}` boundedly into itself.** For every
`j ≥ 0` there is `C_j` such that for all `f ∈ X_{G,j} = 𝒟((I - D)^{j/2})`, `L₀ f ∈ X_{G,j}`
and `‖L₀ f‖²_{X_{G,j}} ≤ C_j ‖f‖²_{X_{G,j}}` (squared graph norms), where
`L₀ = -2iΩ + 2ikR` is B0012's bounded operator on `X_G` (`eq:st18-t00006`). Conditional on the
global elliptic estimate for `R` at order `j` (`GreenEllipticRegularity j`, tex line 1869); the
`Ω` part (`omegaOp_mem_XGj`) is unconditional. -/
theorem L0_mem_XGj (j : ℕ) (hE : GreenEllipticRegularity j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ XGj j,
      ∃ hL : B0012.L0 f ∈ XGj j, graphNormSq j ⟨B0012.L0 f, hL⟩ ≤ C * graphNormSq j ⟨f, hf⟩ := by
  obtain ⟨C1, hC1, h1⟩ := omegaOp_mem_XGj j
  obtain ⟨C2, hC2, h2⟩ := kROp_mem_XGj j hE
  refine ⟨8 * (C1 + C2), by positivity, fun f hf => ?_⟩
  obtain ⟨hm1, hb1⟩ := h1 f hf
  obtain ⟨hm2, hb2⟩ := h2 f hf
  have hL : B0012.L0 f = (-2 * Complex.I) • B0012.omegaOp f + (2 * Complex.I) • B0012.kROp f :=
    rfl
  have hmem : B0012.L0 f ∈ XGj j := by
    rw [hL]
    exact (XGj j).add_mem ((XGj j).smul_mem _ hm1) ((XGj j).smul_mem _ hm2)
  refine ⟨hmem, ?_⟩
  have e : (⟨B0012.L0 f, hmem⟩ : (fracPow j).domain) =
      (-2 * Complex.I) • (⟨B0012.omegaOp f, hm1⟩ : (fracPow j).domain) +
        (2 * Complex.I) • (⟨B0012.kROp f, hm2⟩ : (fracPow j).domain) := Subtype.ext hL
  rw [e]
  refine (graphNormSq_combo j _ _ _ _).trans ?_
  have n1 : ‖(-2 * Complex.I)‖ ^ 2 = 4 := by
    rw [norm_mul, norm_neg, Complex.norm_I]
    norm_num
  have n2 : ‖(2 * Complex.I)‖ ^ 2 = 4 := by
    rw [norm_mul, Complex.norm_I]
    norm_num
  rw [n1, n2]
  have hT := graphNormSq_nonneg j ⟨f, hf⟩
  nlinarith

/-- **B0122, graph-norm form**: `‖L₀ f‖_{X_{G,j}} ≤ C_j ‖f‖_{X_{G,j}}` with the graph norm
`‖f‖_{X_{G,j}} = (‖f‖² + ‖(I - D)^{j/2} f‖²)^{1/2}`. -/
theorem L0_mem_XGj_norm (j : ℕ) (hE : GreenEllipticRegularity j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ XGj j,
      ∃ hL : B0012.L0 f ∈ XGj j,
        Real.sqrt (graphNormSq j ⟨B0012.L0 f, hL⟩) ≤ C * Real.sqrt (graphNormSq j ⟨f, hf⟩) := by
  obtain ⟨C, hC, h⟩ := L0_mem_XGj j hE
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun f hf => ?_⟩
  obtain ⟨hL, hb⟩ := h f hf
  refine ⟨hL, ?_⟩
  rw [← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt hb

end UnforcedLeray.B0122
