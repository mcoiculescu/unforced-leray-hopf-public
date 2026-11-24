import UnforcedLeray.Units.B0059.GradL2

/-!
# B0059: Biot–Savart bounds on the weighted spaces

Blueprint unit **B0059**, label `eq:st18-t00048`, `paper/main.tex` lines 1206–1213 (proof of
"Compactness of the Euler interaction", section `sec:st18-1373`). Dependencies: B0008 (the
weighted spaces `H^j_M`, `UnforcedLeray.B0008`) and B0009 (the planar Biot–Savart velocity
`biotSavart f i`, `UnforcedLeray.B0009`).

**Statement (tex 1206–1213).** Since `M > 1`, `‖f‖₁ ≤ C_M ‖f‖_{L²_M}`. Split the Biot–Savart
kernel smoothly at distance one. The near part is in `L¹`, so it maps `L²` to `L²`; the far part
is bounded, so it maps `L¹` to `L^∞`. For derivatives of positive order the Fourier multiplier of
`∂^α K` has order `|α| - 1` with bounded angular multiplier. Consequently
`‖∂^α Kf‖₂ ≤ C_α ‖f‖_{H^{|α|-1}}` (`|α| ≥ 1`) and `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`.
No global weighted velocity estimate is inferred from this.

**Formalization.** All statements are unconditional and componentwise (`(Kf)_i = biotSavart f i`,
`i = 0, 1`), for `f ∈ H^j_M` with `M > 1`:
* `‖f‖₁ ≤ C_M ‖f‖_{L²_M}` for every `f` with `⟨y⟩^M f ∈ L²` (`integrable_and_integral_norm_le`,
  `C_M = (∫ ⟨y⟩^{-2M})^{1/2}` is B0008's `CM M`), hence `∫ |f| ≤ C_M ‖f‖_{H^j_M}` on `H^j_M`
  (`integral_norm_value_le`, `Units/B0059/Basic.lean`);
* the smooth split at distance one (`cutoff`, `nearKernel`, `farKernel`, `nearPart`, `farPart`,
  `Units/B0059/Basic.lean`): `integrable_nearKernel`, `memLp_nearPart` (`L² → L²`, Young),
  `norm_farKernel_le`, `norm_farPart_le` (`L¹ → L^∞`), `biotSavart_ae_eq_near_add_far`;
* `l2_weakPartial_biotSavart_le`: `‖∂^α Kf‖₂ ≤ 2 ‖f‖_{H^{|α|-1}}` for `1 ≤ |α| ≤ j + 1`
  (`C_α = 2`), with `∂^α` the weak derivative and `‖·‖_{H^m}` the unweighted Sobolev norm;
* `memHOn_biotSavart_ball`: `Kf ∈ H^{j+1}(B_R)` and `‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`;
* `unit_statement`: all of these together.
Nothing global and weighted is asserted for `Kf` (tex 1213).

**Proof route.** The derivative bounds come from (i) the commutation `∂^β(Kf) = K(∂^β f)` weakly
(`hasWeakDerivOn_biotSavart`, Fubini against the split kernel), and (ii) the first-order bound
`‖∂_k (Kg)_i‖₂ ≤ 2 ‖g‖₂` on `L¹ ∩ L²` (`gradL2Bound_two`, `Units/B0059/GradL2.lean`). The latter
is the manuscript's multiplier sentence at `|α| = 1`; it is proved without Fourier analysis by the
NonUniqueEuler reference argument
(`NonUniqueEuler/lean/NonUniqueEuler/P/Sec2/Velocity.lean:223`, `gradL2_velocity`: density
of `C_c^∞` in `L¹ ∩ L²` and the identity `‖∂₁v‖² + ‖∂₂v‖² = ‖ω‖²` for smooth `ω`). Its import
closure is reused from the vendored drafts `Lib/Kernels/PlanarBS/` (namespace
`UnforcedLeray.PlanarBS`: Biot–Savart kernel, `BSBasic`, `KernelSplit`, polar coordinates, Young,
the Sobolev definitions); only the reference modules that are not vendored there are transported
under `Units/B0059/NUE/` (namespace `UnforcedLeray.B0059.NUE`). The constant `2` (instead of `1`)
comes from splitting complex data into real and imaginary parts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace UnforcedLeray.B0059

open NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0009

/-- **`‖∂^α Kf‖₂ ≤ C_α ‖f‖_{H^{|α|-1}}` for `|α| ≥ 1`** (`paper/main.tex:1210`, first estimate of
`eq:st18-t00048`; blueprint unit B0059). For `f ∈ H^j_M` with `M > 1`, each component `i` and each
multi-index `α` with `1 ≤ |α| ≤ j + 1`: the weak derivative `∂^α (Kf)_i` exists (`weakPartial α`,
the chosen locally integrable weak derivative on the plane, is one), lies in `L²`, and
`‖∂^α (Kf)_i‖₂ ≤ 2 ‖f‖_{H^{|α|-1}}`, the norm on the right being the unweighted Sobolev norm
`normH (|α| - 1) f` (meaningful since `f ∈ H^j`, `HjM.memH_value`). -/
theorem l2_weakPartial_biotSavart_le {j : ℕ} {M : ℝ} (hM : 1 < M) (F : B0008.HjM j M)
    (i : Fin 2) {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ j + 1) (hα1 : 1 ≤ α.1 + α.2) :
    HasWeakDerivOn univ (pdList α) (biotSavart F.value i)
        (weakPartial α (biotSavart F.value i)) ∧
      MemLp (weakPartial α (biotSavart F.value i)) 2 volume ∧
      l2 (weakPartial α (biotSavart F.value i)) ≤
        2 * normH (α.1 + α.2 - 1) (F.value : ℂ → ℂ) :=
  l2_weakPartial_biotSavart_le_of_gradL2Bound gradL2Bound_two hM F i hα hα1

/-- **`‖Kf‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`** (`paper/main.tex:1211`, second estimate of
`eq:st18-t00048`; blueprint unit B0059). For `M > 1`, every `j` and every radius `R` there is a
constant `C_{j,M,R} ≥ 0` such that for every `f ∈ H^j_M` and each component `i`,
`(Kf)_i ∈ H^{j+1}(B_R)` (`MemHOn`: `L²(B_R)` together with all weak derivatives of order
`≤ j + 1` on `B_R`) and `‖(Kf)_i‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}` (`normHOn`, the sum of
squares of those `L²(B_R)` norms). -/
theorem memHOn_biotSavart_ball {M : ℝ} (hM : 1 < M) (j : ℕ) (R : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (F : B0008.HjM j M) (i : Fin 2),
      MemHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ∧
        normHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ≤ C' * ‖F‖ :=
  memHOn_biotSavart_ball_of_gradL2Bound gradL2Bound_two hM j R

/-- **B0059** (`paper/main.tex:1206–1213`, `eq:st18-t00048`), assembled. For `M > 1` and every
`j`:
1. `‖f‖₁ ≤ C_M ‖f‖_{L²_M}` (`C_M = (∫ ⟨y⟩^{-2M})^{1/2}`): every `f` with `⟨y⟩^M f ∈ L²` is
   integrable with `∫ |f| ≤ C_M ‖⟨y⟩^M f‖₂`; in particular `∫ |f| ≤ C_M ‖f‖_{H^j_M}` on `H^j_M`;
2. the smooth split `K_i = K_near,i + K_far,i` at distance one: `K_near,i ∈ L¹`, and
   `f ↦ f ⋆ K_near,i` maps `L²` to `L²` with norm `≤ ‖K_near,i‖₁`; `|K_far,i| ≤ 1/π`, and
   `f ↦ f ⋆ K_far,i` maps `L¹` to `L^∞` with norm `≤ 1/π`; `(Kf)_i = f ⋆ K_near,i + f ⋆ K_far,i`
   a.e. for `f ∈ L¹`;
3. `∂^α (Kf)_i` exists weakly, lies in `L²`, and `‖∂^α (Kf)_i‖₂ ≤ 2 ‖f‖_{H^{|α|-1}}` for
   `1 ≤ |α| ≤ j + 1`;
4. for every `R`, `‖(Kf)_i‖_{H^{j+1}(B_R)} ≤ C_{j,M,R} ‖f‖_{H^j_M}`.
No global weighted velocity estimate is asserted (tex 1213). -/
theorem unit_statement {M : ℝ} (hM : 1 < M) (j : ℕ) :
    (∀ f : ℂ → ℂ, MemLp (fun y => bracket y ^ M • f y) 2 volume →
      Integrable f volume ∧
        ∫ y, ‖f y‖ ≤ CM M * (eLpNorm (fun y => bracket y ^ M • f y) 2 volume).toReal) ∧
    (∀ F : B0008.HjM j M, ∫ y, ‖F.value y‖ ≤ CM M * ‖F‖) ∧
    (∀ i : Fin 2, nearKernel i + farKernel i = kernel i ∧ Integrable (nearKernel i) volume ∧
      (∀ z, ‖farKernel i z‖ ≤ Real.pi⁻¹) ∧
      (∀ f : ℂ → ℂ, MemLp f 2 volume → MemLp (nearPart f i) 2 volume ∧
        eLpNorm (nearPart f i) 2 volume ≤ (∫⁻ z, ‖nearKernel i z‖ₑ) * eLpNorm f 2 volume) ∧
      (∀ f : ℂ → ℂ, Integrable f volume →
        (∀ y, ‖farPart f i y‖ ≤ Real.pi⁻¹ * ∫ t, ‖f t‖) ∧
        biotSavart f i =ᵐ[volume] nearPart f i + farPart f i)) ∧
    (∀ (F : B0008.HjM j M) (i : Fin 2) (α : ℕ × ℕ), α.1 + α.2 ≤ j + 1 → 1 ≤ α.1 + α.2 →
      HasWeakDerivOn univ (pdList α) (biotSavart F.value i)
          (weakPartial α (biotSavart F.value i)) ∧
        MemLp (weakPartial α (biotSavart F.value i)) 2 volume ∧
        l2 (weakPartial α (biotSavart F.value i)) ≤
          2 * normH (α.1 + α.2 - 1) (F.value : ℂ → ℂ)) ∧
    (∀ R : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (F : B0008.HjM j M) (i : Fin 2),
      MemHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ∧
        normHOn (j + 1) (ball (0 : ℂ) R) (biotSavart F.value i) ≤ C' * ‖F‖) :=
  ⟨fun _ hf => integrable_and_integral_norm_le hM hf,
    unit_statement_of_gradL2Bound gradL2Bound_two hM j⟩

end UnforcedLeray.B0059
