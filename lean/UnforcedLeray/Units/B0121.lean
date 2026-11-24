import UnforcedLeray.Units.B0121.Backward

/-!
# B0121 (`eq:st18-t00100`): graph norms of `X_{G,j}` are Gaussian-weighted Sobolev norms

Blueprint unit **B0121**, label `eq:st18-t00100`, `paper/main.tex` lines 1856--1865 (proof of
"Finite-order regularity", Section `sec:st18-2021`). Dependencies: B0093 (`eq:st18-t00067`,
`Units/B0093.lean`: the conjugation `U_G f = f/√G` of `D = Δ + ½ y·∇ + 2` to the oscillator
`Δ - |y|²/16 + 3/2`) and B0094 (`eq:st18-t00068`, `Units/B0094.lean`: `D` is selfadjoint on
`X_G` with orthonormal eigenbasis `oscBasis`, `D e_ℓ = -ℓ e_ℓ`, the `ℓ`-th eigenvector being the
angular-two Hermite level of total degree `N = 2 + 2ℓ`).

## The manuscript's claim (tex lines 1858--1864)

For fixed `j`, the squared graph norm on `X_{G,j} = 𝒟((I - D)^{j/2})` (`eq:st18-t00014`, tex
line 748) is comparable to `∑_{|α| ≤ j} ‖∂^α f‖²_{L²(ℝ², G⁻¹ dy)}`, the derivatives being
measured in the ambient Gaussian `L²` space of the planar function `f(r, ϑ) = f₂(r) e^{2iϑ}`.

## What is formalized

* `fracPow j`: `(I - D)^{j/2}` (the spectral calculus of `D = diag(-ℓ)`; `fracPow_two`: for
  `j = 2` it is `I - D`), with domain `XGj j = X_{G,j}`; `graphNormSq j f = ‖f‖² +
  ‖(I - D)^{j/2} f‖²`.
* `planar f`: the planar function of `f ∈ X_G` (B0010's `angularTwoField`); `MemGaussL2 F`:
  `F ∈ L²(ℝ², G⁻¹ dy)`; `∂^α f = g` is the distributional derivative
  `UnforcedLeray.PlanarBS.Sob.HasWeakDerivOn univ (pdListR α)` (smooth compactly supported test
  functions, `∂^α = ∂₁^{α₁} ∂₂^{α₂}`); the multi-indices `|α| ≤ j` are the library's
  `multiIdx j`.
* **`graphNorm_equiv`** (the unit): if the planar function of `f ∈ X_G` has weak derivatives
  `g α ∈ L²(ℝ², G⁻¹ dy)` for all `|α| ≤ j`, then `f ∈ X_{G,j}` and
  `π/2^j · ‖f‖²_{X_{G,j}} ≤ ∑_{|α|≤j} ∫ |g α|² G⁻¹ dy ≤ 2π (j+1)(j+2)^j · ‖f‖²_{X_{G,j}}`;
  **`exists_weakDerivs`**: conversely every `f ∈ X_{G,j}` has such derivatives;
  `mem_XGj_iff_weakDerivs` combines both.
* `sum_words_gaussNormSq_eq` (the exact identity behind the comparison, tex line 1863): the sum
  over all ordered products `∂_{w 0} ⋯ ∂_{w (k-1)}`, `k ≤ j`, of the squared Gaussian norms is
  `2π ∑_ℓ (∑_{k≤j} ∏_{m<k} (2 + ℓ + m/2)) |⟪e_ℓ, f⟫|²`.

## Route (tex lines 1862--1864)

Conjugation turns `∂ᵢ` into `Aᵢ = ∂ᵢ - yᵢ/4` (`dop_gS`), an oscillator creation operator up to
a constant; with its formal adjoint `Bᵢ`, `B₁A₁ + B₂A₂ = 2 - osc` and the ladder relation give
`∑_{|w|=k} B_w A_w = ∏_{m<k}(2 - osc + m/2)` (`Units/B0121/Ops.lean`). On the Hermite level `ℓ`
(`N = 2 + 2ℓ`) this is `∏_{m<k}(2 + ℓ + m/2)`, comparable to `(1 + ℓ)^k`
(`Units/B0121/Spectral.lean`). Summing the orthogonal levels: for `f ∈ X_{G,j}` the truncations
to finitely many levels converge and give the weak derivatives with the exact norm identity
(`Units/B0121/Forward.lean`); conversely, duality against the truncations (polynomial test
functions, `Units/B0121/Gauss.lean`) bounds the level sums by the derivatives
(`Units/B0121/Backward.lean`). Weak derivatives are unique a.e. (reference formalization,
`Units/B0121/WeakDeriv.lean`). The `2π` comes from the `X_G` pairing omitting the angular
factor (tex line 678; `gaussNormSq_angularTwoField`); the factor `2^j` compares ordered
products of derivatives with multi-indices.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate Real ENNReal

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.B0010 UnforcedLeray.PlanarBS.Sob

theorem gaussNormSq_nonneg (F : ℝ × ℝ → ℂ) : 0 ≤ gaussNormSq F :=
  integral_nonneg fun z =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.2 (B0093.gaussianWeight_pos z).le)

/-- Uniqueness of weak derivatives: any family of Gaussian-`L²` weak derivatives has the norms
of the constructed ones. -/
theorem gaussNormSq_word_eq {j : ℕ} {f : XG} (hf : f ∈ XGj j) {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j (planar f) g) {k : ℕ} (hk : k ≤ j) (w : Fin k → Fin 2) :
    gaussNormSq (g (mi w)) = ‖gam f k w‖ ^ 2 := by
  have hw := h.word hk w
  have hae := hasWeakDerivOn_ae_eq isOpen_univ
    (hw.1.locallyIntegrable.locallyIntegrableOn univ)
    ((memGaussL2_wd f k w).locallyIntegrable.locallyIntegrableOn univ) hw.2
    (hasWeakDerivOn_wd hf hk w)
  rw [← gaussNormSq_wd]
  refine integral_congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz (mem_univ z)]

/-- **The exact identity** (tex line 1863): for weak derivatives `g α = ∂^α f` in
`L²(ℝ², G⁻¹ dy)`, `|α| ≤ j`, the sum over all ordered products `∂_w` of order `k ≤ j` of
`‖∂_w f‖²_{L²(ℝ², G⁻¹ dy)}` equals `2π ∑_ℓ qsum j ℓ |⟪e_ℓ, f⟫|²`, where
`qsum j ℓ = ∑_{k ≤ j} ∏_{m<k} (2 + ℓ + m/2)` is the weight of the Hermite level `N = 2 + 2ℓ`. -/
theorem sum_words_gaussNormSq_eq {j : ℕ} {f : XG} {g : ℕ × ℕ → ℝ × ℝ → ℂ}
    (h : IsWeakFamily j (planar f) g) :
    ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) =
      2 * π * ∑' ℓ : ℕ, qsum j ℓ * ‖coef f ℓ‖ ^ 2 := by
  have hf := mem_XGj_of_isWeakFamily h
  have e1 : ∀ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) =
      2 * π * ∑' ℓ : ℕ, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 := by
    intro k hk
    have hk' : k ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [← sum_norm_sq_gam hf hk']
    exact Finset.sum_congr rfl fun w _ => gaussNormSq_word_eq hf h hk' w
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum fun k hk =>
    summable_qpoly_coef hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
  congr 1
  funext ℓ
  rw [qsum, Finset.sum_mul]

/-- Multi-index sums against word sums: `M ≤ W ≤ 2^j M`. -/
theorem multiIdx_le_words (j : ℕ) (h : ℕ × ℕ → ℝ) (hh : ∀ α, 0 ≤ h α) :
    ∑ α ∈ multiIdx j, h α ≤ ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, h (mi w) := by
  rw [sum_multiIdx]
  exact Finset.sum_le_sum fun k _ => sum_antidiagonal_le_sum_words k h hh

theorem words_le_multiIdx (j : ℕ) (h : ℕ × ℕ → ℝ) (hh : ∀ α, 0 ≤ h α) :
    ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, h (mi w) ≤
      2 ^ j * ∑ α ∈ multiIdx j, h α := by
  rw [sum_multiIdx, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine (sum_words_le k h hh).trans ?_
  have h0 : 0 ≤ ∑ α ∈ Finset.antidiagonal k, h α := Finset.sum_nonneg fun α _ => hh α
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk'
  exact mul_le_mul_of_nonneg_right h2 h0

/-- **B0121 (`eq:st18-t00100`, tex lines 1858--1864): the derivatives control the graph
norm, and conversely.** Let `f ∈ X_G` and let `g α ∈ L²(ℝ², G⁻¹ dy)` be the distributional
derivatives `∂^α f = ∂₁^{α₁} ∂₂^{α₂} f` of its planar function `f(r, ϑ) = f₂(r) e^{2iϑ}`,
`|α| ≤ j`. Then `f ∈ X_{G,j} = 𝒟((I - D)^{j/2})` and the squared graph norm is comparable to
`∑_{|α| ≤ j} ‖∂^α f‖²_{L²(ℝ², G⁻¹ dy)}`:
`π/2^j ‖f‖²_{X_{G,j}} ≤ ∑_{|α|≤j} ∫ |∂^α f|² G⁻¹ dy ≤ 2π (j+1)(j+2)^j ‖f‖²_{X_{G,j}}`. -/
theorem graphNorm_equiv (j : ℕ) (f : XG) (g : ℕ × ℕ → ℝ × ℝ → ℂ)
    (hg : ∀ α ∈ multiIdx j, MemGaussL2 (g α) ∧ HasWeakDerivOn univ (pdListR α) (planar f) (g α)) :
    ∃ hf : f ∈ (fracPow j).domain,
      π / 2 ^ j * graphNormSq j ⟨f, hf⟩ ≤
          ∑ α ∈ multiIdx j, ∫ z, ‖g α z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ ∧
        ∑ α ∈ multiIdx j, ∫ z, ‖g α z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ ≤
          2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * graphNormSq j ⟨f, hf⟩ := by
  have h : IsWeakFamily j (planar f) g := hg
  have hf : f ∈ (fracPow j).domain := mem_XGj_of_isWeakFamily h
  refine ⟨hf, ?_⟩
  set Msum := ∑ α ∈ multiIdx j, gaussNormSq (g α) with hM
  set W := ∑ k ∈ Finset.range (j + 1), ∑ w : Fin k → Fin 2, gaussNormSq (g (mi w)) with hW
  set Q := ∑' ℓ : ℕ, qsum j ℓ * ‖coef f ℓ‖ ^ 2 with hQ
  set Gr := graphNormSq j ⟨f, hf⟩ with hGr
  have hWQ : W = 2 * π * Q := sum_words_gaussNormSq_eq h
  have hMW : Msum ≤ W := multiIdx_le_words j _ fun α => gaussNormSq_nonneg _
  have hWM : W ≤ 2 ^ j * Msum := words_le_multiIdx j _ fun α => gaussNormSq_nonneg _
  have hGr' : Gr = ∑' ℓ : ℕ, (1 + (1 + (ℓ : ℝ)) ^ j) * ‖coef f ℓ‖ ^ 2 := graphNormSq_eq j _
  have hs1 : Summable fun ℓ : ℕ => (1 + (1 + (ℓ : ℝ)) ^ j) * ‖coef f ℓ‖ ^ 2 := by
    have := (summable_coef_sq f).add ((mem_XGj_iff j f).1 hf)
    refine this.congr fun ℓ => ?_
    simp only [coef]
    ring
  have hs2 : Summable fun ℓ : ℕ => qsum j ℓ * ‖coef f ℓ‖ ^ 2 :=
    summable_qsum_of_isWeakFamily h
  have hQlow : Gr / 2 ≤ Q := by
    rw [hGr', ← tsum_div_const]
    refine hs1.div_const 2 |>.tsum_le_tsum (fun ℓ => ?_) hs2
    have := qsum_ge j ℓ
    calc (1 + (1 + (ℓ : ℝ)) ^ j) * ‖coef f ℓ‖ ^ 2 / 2
        = (1 + (1 + (ℓ : ℝ)) ^ j) / 2 * ‖coef f ℓ‖ ^ 2 := by ring
      _ ≤ qsum j ℓ * ‖coef f ℓ‖ ^ 2 := by gcongr
  have hQup : Q ≤ ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * Gr := by
    rw [hGr', ← tsum_mul_left]
    refine hs2.tsum_le_tsum (fun ℓ => ?_) (hs1.mul_left _)
    have := qsum_le j ℓ
    calc qsum j ℓ * ‖coef f ℓ‖ ^ 2
        ≤ ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * (1 + (1 + (ℓ : ℝ)) ^ j) * ‖coef f ℓ‖ ^ 2 := by
          gcongr
      _ = ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * ((1 + (1 + (ℓ : ℝ)) ^ j) * ‖coef f ℓ‖ ^ 2) := by
          ring
  have hpi := Real.pi_pos
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  refine ⟨?_, ?_⟩
  · show π / 2 ^ j * Gr ≤ Msum
    rw [div_mul_eq_mul_div, div_le_iff₀ h2j]
    nlinarith
  · show Msum ≤ 2 * π * ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * Gr
    nlinarith

/-- **B0121, converse: the graph norm controls the derivatives.** Every `f ∈ X_{G,j}` has
distributional derivatives `∂^α f ∈ L²(ℝ², G⁻¹ dy)` for all `|α| ≤ j` (and then
`graphNorm_equiv` gives the two-sided comparison). -/
theorem exists_weakDerivs (j : ℕ) (f : XG) (hf : f ∈ (fracPow j).domain) :
    ∃ g : ℕ × ℕ → ℝ × ℝ → ℂ, ∀ α ∈ multiIdx j,
      MemGaussL2 (g α) ∧ HasWeakDerivOn univ (pdListR α) (planar f) (g α) := by
  have hw : ∀ α : ℕ × ℕ, ∃ w : Fin (α.1 + α.2) → Fin 2, mi w = α := fun α =>
    exists_word (by rw [Finset.mem_antidiagonal])
  refine ⟨fun α => wd f (α.1 + α.2) (hw α).choose, fun α hα => ?_⟩
  have hk : α.1 + α.2 ≤ j := (mem_multiIdx).1 hα
  refine ⟨memGaussL2_wd _ _ _, ?_⟩
  have h1 := hasWeakDerivOn_wd hf hk (hw α).choose
  have h2 := hasWeakDerivOn_perm (dirs_perm (hw α).choose) h1
  rwa [(hw α).choose_spec] at h2

/-- **B0121, membership form**: `f ∈ X_{G,j}` iff the planar function of `f` has distributional
derivatives `∂^α f ∈ L²(ℝ², G⁻¹ dy)` for all `|α| ≤ j`. -/
theorem mem_XGj_iff_weakDerivs (j : ℕ) (f : XG) :
    f ∈ (fracPow j).domain ↔ ∃ g : ℕ × ℕ → ℝ × ℝ → ℂ, ∀ α ∈ multiIdx j,
      MemGaussL2 (g α) ∧ HasWeakDerivOn univ (pdListR α) (planar f) (g α) := by
  constructor
  · exact exists_weakDerivs j f
  · rintro ⟨g, hg⟩
    exact (graphNorm_equiv j f g hg).1

end UnforcedLeray.B0121
