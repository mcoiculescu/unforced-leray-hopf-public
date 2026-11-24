import UnforcedLeray.Units.B0581.Multiplier
import UnforcedLeray.Units.B0581.Coeff

/-!
# B0581: the nonzero-mode Biot–Savart bound on the cylinder

Blueprint unit **B0581** (label `unlabeled:9407`), `paper/main.tex` lines 9407–9412
(Section P1, "Weighted negative sources and velocity reconstruction"):

> If `ω ∈ X_m` has zero total circulation and `m > 1`, decompose into horizontal mean and
> nonzero modes. For `k ≠ 0`, the Biot–Savart multiplier has modulus at most
> `|k|^{-1} ≤ c/(2π)`, so its `L²` velocity norm is at most `Cc‖ω‖₂`.

Here `k ∈ (2π/c)ℤ` is the horizontal frequency on the cylinder `(ℝ/cℤ) × ℝ`, `X_m` is the
weighted space of `B0579` (`paper/main.tex:9373`), and `K_c` is the cylinder Biot–Savart law.

## Lean statement

* Mixed Fourier analysis on the cell `[-c/2, c/2) × ℝ` (`B0581/Modes.lean`, `B0581/Coeff.lean`):
  horizontal modes `e_k(q) = exp(2πikq/c)`; mode synthesis
  `synth c : ℓ²(ℤ; L²(ℝ)) →ₗᵢ L²(cell)`, `(g_k) ↦ ∑ₖ (√c)⁻¹ e_k(q) g_k(η)` (`hasSum_synth`,
  `coeFn_tensorLM`); horizontal Fourier coefficients `modes c` (its adjoint, `modes_synth`,
  `norm_modes_le`), explicitly `(modes ω)_k = √c · ω_k` a.e. with
  `ω_k(η) = c⁻¹ ∫_{-c/2}^{c/2} e^{-2πikq/c} ω(q, η) dq` (`modes_apply_ae`, `modeCoeff`).
* The Biot–Savart multiplier (`B0581/Multiplier.lean`): `bsSym κ ζ = (iζ, -iκ)/(κ² + ζ²)` is the
  symbol of `K_c = ∇^⊥Δ^{-1}`, `∇^⊥ = (-∂_η, ∂_q)` (`paper/main.tex:2138`, `662`);
  `norm_bsSym_le` and `norm_bsSymbol_le`: modulus `≤ |κ|⁻¹ ≤ c/(2π)` for `κ = 2πk/c`, `k ≠ 0`
  (lines 9410–9411).
* `meanPart c ω` (`ω̄(η) = c⁻¹ ∫ ω(q, η) dq` as a field on the cell, `meanPart_ae`) and
  `nonzeroPart c ω = ω - ω̄` (`ω_ne`, `nonzeroPart_ae`), the decomposition of line 9409
  (`meanPart_add_nonzeroPart`, `modes_nonzeroPart`, `norm_nonzeroPart_le`).
* `velNe c : L²(cell; ℂ) →L L²(cell; ℂ²)`: the Biot–Savart velocity of the nonzero modes,
  `synth ∘ (mode-wise multiplier) ∘ modes`, i.e. the series
  `∑_{k ≠ 0} (√c)⁻¹ e_k(q) 𝓕⁻¹(bsSymbol c k · 𝓕 (√c ω_k))(η)` (`hasSum_velNe`). Its modes are
  characterized by `modes_velNe_zero` (mode `0` vanishes) and `fourier_modes_velNe` (for
  `k ≠ 0`, the `η`-Fourier transform of the velocity mode is `bsSymbol c k` times that of the
  vorticity mode); `velNe_nonzeroPart`: it depends only on `ω_ne`.
* Main results: `norm_velNe_nonzeroPart_le` (`‖K_c ω_ne‖₂ ≤ (c/2π)‖ω_ne‖₂ ≤ (c/2π)‖ω‖₂`, so
  `C = 1/(2π)`), and `nonzero_mode_velocity_bound` with exactly the manuscript's hypotheses
  (`ω ∈ X_m`, `m > 1`, zero total circulation, `c > 0`), which also records
  `‖ω‖₂ ≤ ‖ω‖_{X_m}`.

## Hypotheses made explicit

`c > 0` (the manuscript's `c = ν^{-ρ}`) is the instance `[Fact (0 < c)]`. The real vorticity
`ω ∈ X_m` enters as its complexification `ofX c m hm ω ∈ L²(cell; ℂ)` (`m ≥ 0`); the velocity is
`ℂ²`-valued (for real `ω` it is the complexification of the real velocity; that it is real is
not needed for the norm bound and is not proved here). The hypotheses `m > 1` and zero total
circulation are needed only for the zero mode (`B0582`, `paper/main.tex:9412-9425`); the
nonzero-mode bound holds for every `ω ∈ L²(cell)` (`norm_velNe_nonzeroPart_le`), and
`nonzero_mode_velocity_bound` carries them unused, so no hypothesis is stronger than the
manuscript's. Completeness of the horizontal modes (Parseval, injectivity of `modes`) is not
needed for the bound and is not proved; `velNe` is given by the explicit mode series above.
The gradient bound "by the Fourier multiplier of order zero" is at `paper/main.tex:9425-9426`
(unit `B0583`); only its symbol-level part, `norm_smul_bsSym_le` (`|κ · bsSym|, |ζ · bsSym| ≤ 1`),
is recorded here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex FourierTransform
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0581

/-! ### Horizontal mean and nonzero modes (`paper/main.tex:9409`) -/

section Decomposition

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (c : ℝ) [hc : Fact (0 < c)]

/-- The horizontal-mean part `ω̄`: the `k = 0` mode of `ω`, as a field on the cell
(`(√c)⁻¹ (modes ω)_0(η)`, independent of `q`). -/
def meanPart (ω : Lp F 2 (cellVol c)) : Lp F 2 (cellVol c) :=
  tensorLI c 0 ((modes c ω : ModeSeq F) 0)

/-- The nonzero-mode part `ω_ne = ω - ω̄`. -/
def nonzeroPart (ω : Lp F 2 (cellVol c)) : Lp F 2 (cellVol c) := ω - meanPart c ω

theorem meanPart_add_nonzeroPart (ω : Lp F 2 (cellVol c)) :
    meanPart c ω + nonzeroPart c ω = ω := by
  rw [nonzeroPart, add_sub_cancel]

theorem meanPart_eq_synth (ω : Lp F 2 (cellVol c)) :
    meanPart c ω = synth c (lp.single 2 0 ((modes c ω : ModeSeq F) 0) : ModeSeq F) := by
  rw [synth_single, meanPart]

theorem modes_meanPart (ω : Lp F 2 (cellVol c)) :
    modes c (meanPart c ω) = (lp.single 2 0 ((modes c ω : ModeSeq F) 0) : ModeSeq F) := by
  rw [meanPart_eq_synth, modes_synth]

/-- The modes of `ω_ne`: mode `0` vanishes, the others are those of `ω`. -/
theorem modes_nonzeroPart (ω : Lp F 2 (cellVol c)) (k : ℤ) :
    (modes c (nonzeroPart c ω) : ModeSeq F) k =
      if k = 0 then 0 else (modes c ω : ModeSeq F) k := by
  rw [nonzeroPart, map_sub, modes_meanPart, lp.coeFn_sub, Pi.sub_apply, lp.single_apply]
  split_ifs with hk
  · subst hk
    rw [Pi.single_eq_same, sub_self]
  · rw [Pi.single_eq_of_ne hk, sub_zero]

/-- The horizontal mean explicitly: `ω̄(q, η) = ω_0(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q', η) dq'` a.e. on
the cell (`modeCoeff_zero`). -/
theorem meanPart_ae (ω : Lp F 2 (cellVol c)) :
    (meanPart c ω : B0579.Plane → F) =ᵐ[cellVol c] fun x => modeCoeff c 0 ω x.2 := by
  have h1 := coeFn_tensorLM c 0 ((modes c ω : ModeSeq F) 0)
  have h2 := tensorFun_ae_congr c 0 (modes_apply_ae c 0 ω)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [meanPart, tensorLI_apply, hx1, hx2]
  simp only [tensorFun, eMode_zero, mul_one]
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hc.out).ne',
    Complex.ofReal_one, one_smul]

/-- The nonzero-mode part explicitly: `ω_ne(q, η) = ω(q, η) - ω̄(η)` a.e. on the cell. -/
theorem nonzeroPart_ae (ω : Lp F 2 (cellVol c)) :
    (nonzeroPart c ω : B0579.Plane → F) =ᵐ[cellVol c]
      fun x => (ω : B0579.Plane → F) x - modeCoeff c 0 ω x.2 := by
  filter_upwards [Lp.coeFn_sub ω (meanPart c ω), meanPart_ae c ω] with x h1 h2
  rw [nonzeroPart, h1, Pi.sub_apply, h2]

theorem inner_meanPart_nonzeroPart (ω : Lp F 2 (cellVol c)) :
    ⟪meanPart c ω, nonzeroPart c ω⟫_ℂ = 0 := by
  have h1 : ⟪meanPart c ω, ω⟫_ℂ =
      ⟪(modes c ω : ModeSeq F) 0, (modes c ω : ModeSeq F) 0⟫_ℂ := by
    rw [meanPart, ← inner_modes_apply]
  have h2 : ⟪meanPart c ω, meanPart c ω⟫_ℂ =
      ⟪(modes c ω : ModeSeq F) 0, (modes c ω : ModeSeq F) 0⟫_ℂ := by
    rw [meanPart]
    exact LinearIsometry.inner_map_map _ _ _
  rw [nonzeroPart, inner_sub_right, h1, h2, sub_self]

/-- `‖ω_ne‖₂ ≤ ‖ω‖₂` (orthogonality of the horizontal mean and the nonzero modes). -/
theorem norm_nonzeroPart_le (ω : Lp F 2 (cellVol c)) : ‖nonzeroPart c ω‖ ≤ ‖ω‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
    (inner_meanPart_nonzeroPart c ω)
  rw [meanPart_add_nonzeroPart] at h
  have h2 : ‖nonzeroPart c ω‖ * ‖nonzeroPart c ω‖ ≤ ‖ω‖ * ‖ω‖ := by
    rw [h]; nlinarith [norm_nonneg (meanPart c ω)]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr h2

end Decomposition

/-! ### The Biot–Savart velocity of the nonzero modes -/

section Velocity

variable (c : ℝ) [hc : Fact (0 < c)]

/-- **`K_c` on the nonzero modes**: the cylinder Biot–Savart velocity `K_c ω_ne`, built mode by
mode as `synth ∘ velModes ∘ modes` (`u_0 = 0`, `û_k = bsSymbol c k · ω̂_k` for `k ≠ 0`). -/
def velNe : Lp ℂ 2 (cellVol c) →L[ℂ] Lp Vel 2 (cellVol c) :=
  (synth (F := Vel) c).toContinuousLinearMap ∘L velModes c ∘L modes (F := ℂ) c

theorem velNe_apply (ω : Lp ℂ 2 (cellVol c)) :
    velNe c ω = synth c (velModes c (modes c ω)) := rfl

/-- `K_c ω_ne` as the mode series `∑ₖ (√c)⁻¹ e_k(q) u_k(η)`, `u_k = (velModes (modes ω))_k`
(`coeFn_tensorLM`: `tensorLI c k g = (√c)⁻¹ e_k(q) g(η)` a.e.). -/
theorem hasSum_velNe (ω : Lp ℂ 2 (cellVol c)) :
    HasSum (fun k => tensorLI c k ((velModes c (modes c ω) : ModeSeq Vel) k)) (velNe c ω) :=
  hasSum_synth c _

/-- The horizontal modes of the velocity are the multiplier applied to those of `ω`. -/
theorem modes_velNe (ω : Lp ℂ 2 (cellVol c)) :
    modes c (velNe c ω) = velModes c (modes c ω) :=
  modes_synth c _

/-- The mean (`k = 0`) mode of `K_c ω_ne` vanishes. -/
theorem modes_velNe_zero (ω : Lp ℂ 2 (cellVol c)) :
    (modes c (velNe c ω) : ModeSeq Vel) 0 = 0 := by
  rw [modes_velNe, velModes_apply, bsModeCLM_zero, ContinuousLinearMap.zero_apply]

/-- For `k ≠ 0`, the `η`-Fourier transform of the `k`-th velocity mode is the Biot–Savart
symbol times that of the `k`-th vorticity mode (`paper/main.tex:9410`). -/
theorem fourier_modes_velNe (ω : Lp ℂ 2 (cellVol c)) {k : ℤ} (hk : k ≠ 0) :
    ((𝓕 ((modes c (velNe c ω) : ModeSeq Vel) k) : Lp Vel 2 (volume : Measure ℝ)) :
        ℝ → Vel) =ᵐ[volume]
      fun ξ => ((𝓕 ((modes c ω : ModeSeq ℂ) k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ •
        bsSymbol c k ξ := by
  rw [modes_velNe, velModes_apply]
  exact fourier_bsModeCLM c hk _

/-- `K_c` on the nonzero modes only sees `ω_ne`. -/
theorem velNe_nonzeroPart (ω : Lp ℂ 2 (cellVol c)) :
    velNe c (nonzeroPart c ω) = velNe c ω := by
  rw [velNe_apply, velNe_apply]
  congr 1
  ext1
  funext k
  rw [velModes_apply, velModes_apply, modes_nonzeroPart]
  split_ifs with hk
  · subst hk
    rw [bsModeCLM_zero, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  · rfl

theorem velNe_meanPart (ω : Lp ℂ 2 (cellVol c)) : velNe c (meanPart c ω) = 0 := by
  have h := velNe_nonzeroPart c ω
  rw [nonzeroPart, map_sub, sub_eq_self] at h
  exact h

/-- `‖K_c ω‖₂ ≤ (c/2π)‖ω‖₂` for the nonzero-mode velocity. -/
theorem norm_velNe_le (ω : Lp ℂ 2 (cellVol c)) : ‖velNe c ω‖ ≤ c / (2 * π) * ‖ω‖ := by
  have hC : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  rw [velNe_apply, LinearIsometry.norm_map]
  calc ‖velModes c (modes c ω)‖ ≤ c / (2 * π) * ‖modes c ω‖ := norm_velModes_apply_le c _
    _ ≤ c / (2 * π) * ‖ω‖ := mul_le_mul_of_nonneg_left (norm_modes_le c ω) hC

/-- **B0581, `L²` form.** For every `ω ∈ L²(cell)` and `c > 0`, the Biot–Savart velocity of the
nonzero modes satisfies `‖K_c ω_ne‖₂ ≤ (c/2π)‖ω_ne‖₂ ≤ (c/2π)‖ω‖₂` (`paper/main.tex:9410-9412`,
`C = 1/(2π)`). -/
theorem norm_velNe_nonzeroPart_le (ω : Lp ℂ 2 (cellVol c)) :
    ‖velNe c (nonzeroPart c ω)‖ ≤ c / (2 * π) * ‖nonzeroPart c ω‖ ∧
      c / (2 * π) * ‖nonzeroPart c ω‖ ≤ c / (2 * π) * ‖ω‖ := by
  have hC : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  exact ⟨norm_velNe_le c _, mul_le_mul_of_nonneg_left (norm_nonzeroPart_le c ω) hC⟩

end Velocity

/-! ### Vorticities in `X_m` (`B0579`, `paper/main.tex:9373`) -/

theorem cellVol_le_cellMeasure (c : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    cellVol c ≤ B0579.cellMeasure c m := by
  rw [cellVol, B0579.cellMeasure]
  conv_lhs => rw [← withDensity_one (μ := volume.restrict (B0579.cell c))]
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  simp only [Pi.one_apply]
  have h1 : (1 : ℝ) ≤ (B0579.density m x : ℝ) := by
    rw [B0579.coe_density]
    refine Real.one_le_rpow ?_ hm
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  exact_mod_cast h1

theorem memLp_ofX (c : ℝ) {m : ℝ} (hm : 0 ≤ m) (ω : B0579.X c m) :
    MemLp (fun x => ((ω x : ℝ) : ℂ)) 2 (cellVol c) :=
  ((Lp.memLp ω).mono_measure (cellVol_le_cellMeasure c hm)).ofReal

/-- The complexification of `ω ∈ X_m` (`m ≥ 0`) as an element of `L²(cell; ℂ)`. -/
def ofX (c m : ℝ) (hm : 0 ≤ m) (ω : B0579.X c m) : Lp ℂ 2 (cellVol c) :=
  (memLp_ofX c hm ω).toLp _

theorem coeFn_ofX (c m : ℝ) (hm : 0 ≤ m) (ω : B0579.X c m) :
    ofX c m hm ω =ᵐ[cellVol c] fun x => ((ω x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- `‖ω‖_{L²(cell)} ≤ ‖ω‖_{X_m}` for `m ≥ 0`. -/
theorem norm_ofX_le (c m : ℝ) (hm : 0 ≤ m) (ω : B0579.X c m) : ‖ofX c m hm ω‖ ≤ ‖ω‖ := by
  rw [ofX, Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top ω) ?_
  calc eLpNorm (fun x => ((ω x : ℝ) : ℂ)) 2 (cellVol c) = eLpNorm (ω : B0579.Plane → ℝ) 2
        (cellVol c) := eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)
    _ ≤ eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) :=
        eLpNorm_mono_measure _ (cellVol_le_cellMeasure c hm)

/-- **B0581** (`paper/main.tex:9407-9412`), with exactly the manuscript's hypotheses: `c > 0`,
`ω ∈ X_m`, `m > 1`, zero total circulation. Decompose `ω = ω̄ + ω_ne` into horizontal mean and
nonzero modes (`meanPart_add_nonzeroPart`); the Biot–Savart velocity of the nonzero modes
satisfies `‖K_c ω_ne‖₂ ≤ (c/2π)‖ω‖₂`, and `‖ω‖₂ ≤ ‖ω‖_{X_m}`. -/
theorem nonzero_mode_velocity_bound {c m : ℝ} [Fact (0 < c)] (hm : 1 < m) (ω : B0579.X c m)
    (_hcirc : ∫ x in B0579.cell c, ω x = 0) :
    meanPart c (ofX c m (by linarith) ω) + nonzeroPart c (ofX c m (by linarith) ω) =
        ofX c m (by linarith) ω ∧
      ‖velNe c (nonzeroPart c (ofX c m (by linarith) ω))‖ ≤
        c / (2 * π) * ‖ofX c m (by linarith) ω‖ ∧
      ‖ofX c m (by linarith) ω‖ ≤ ‖ω‖ := by
  refine ⟨meanPart_add_nonzeroPart c _, ?_, norm_ofX_le c m _ ω⟩
  obtain ⟨h1, h2⟩ := norm_velNe_nonzeroPart_le c (ofX c m (by linarith) ω)
  exact h1.trans h2

end UnforcedLeray.B0581
