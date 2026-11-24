import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/3`: continuity of the tested right-hand side (`AdjTestedRhsCont`)

Source: `the November 2 reference manuscript` lines 3060-3061 (reverse-time adjoint,
its tested form), 3052-3058 (the localized term, bounded by weighted Cauchy-Schwarz).

With `M r x = ν Δψ - v(r)·∇ψ - uψ·∇E(r)` (`adjM`), `adjIntegrand tr (φ r) r ψ uψ x = φ r x * M r x`.
The proof is the abstract lemma `weighted_pair_cont` (proved here from the weighted
Cauchy-Schwarz leaf `WeightedCS`: `φ ∈ C([t,s]; X_{-m})`, `|M r| ≤ B` with `B ∈ X_m`, `M r x`
continuous in `r`: continuity of `r ↦ ∫ φ(r) M(r)`), and three train/test leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The real multiplier `Aψ(r) = νΔψ - v(r)·∇ψ - uψ·∇E(r)` of `adjIntegrand`. -/
def adjM {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ)
    (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) : ℝ :=
  ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) -
      (uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x)

theorem adjIntegrand_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℂ)
    (r : ℝ) (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) :
    adjIntegrand tr φ r ψ uψ x = φ x * ((adjM tr r ψ uψ x : ℝ) : ℂ) := rfl

/-- **Leaf 1** (weighted Cauchy-Schwarz on the cell; SP 3052-3058): `cellMeasure c m` has density
`jb^m` with respect to Lebesgue measure on the cell, so
`∫_cell |f| |B| ≤ ‖f‖_{X_{-m}} ‖B‖_{X_m}` (Hölder with `jb^{-m/2} · jb^{m/2} = 1`). -/
def WeightedCS : Prop :=
  ∀ (c m : ℝ) (f : ℝ × ℝ → ℂ) (B : ℝ × ℝ → ℝ),
    AEStronglyMeasurable f (B0579.cellMeasure c (-m)) →
    AEStronglyMeasurable B (B0579.cellMeasure c m) →
    ∫⁻ x in B0579.cell c, ‖f x‖ₑ * ‖B x‖ₑ ≤
      xNorm c (-m) f * eLpNorm B 2 (B0579.cellMeasure c m)

/-- **Leaf 2** (domination; SP 3060-3061, 3052-3058): for a train with `LadTrainBdd` on `[0, S]`,
`|adjM r| ≤ B` on the cell for `r ∈ [t, s]`, with
`B = ν|Δψ| + C(|∂₀ψ| + |∂₁ψ|) + C jb^{-(m+2)/2}(|uψ₀| + |uψ₁|) ∈ X_m` (`ψ` smooth and zero for
`|x₂|` large; `uψ - meanShear ∈ L²(cell)` and `meanShear` bounded; `jb^m · jb^{-(m+2)} = jb^{-2}`
is integrable on the cell). -/
def AdjMDominated (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s →
      ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
        IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
        ∃ B : ℝ × ℝ → ℝ, MemLp B 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
          ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)), |adjM tr r ψ uψ x| ≤ B x

/-- **Leaf 3** (pointwise continuity in the age; `tr.isTrain.smooth_v`): for fixed `x`,
`r ↦ adjM r x` is continuous on `[0, ∞)` (the velocity and the partials of `Ec` are smooth on
`Ici 0 ×ˢ univ`). -/
def AdjMPointwiseCont : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      ∀ x : ℝ × ℝ, ContinuousOn (fun r => adjM tr r ψ uψ x) (Ici 0)

/-- **Leaf 4** (measurability): for `r ≥ 0`, `adjM r` is a.e. strongly measurable on the cell
(`v r`, `Ec r` smooth, `ψ` smooth, `uψ j` measurable by `IsKernelBiotSavart`). -/
def AdjMMeasurable : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ → ∀ r : ℝ, 0 ≤ r →
        AEStronglyMeasurable (adjM tr r ψ uψ) (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))

theorem measurableSet_cell' (c : ℝ) : MeasurableSet (B0579.cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

theorem aesm_ofReal {μ : Measure (ℝ × ℝ)} {N : ℝ × ℝ → ℝ} (h : AEStronglyMeasurable N μ) :
    AEStronglyMeasurable (fun x => ((N x : ℝ) : ℂ)) μ :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable h

/-- `∫⁻ ‖f N‖ ≤ ‖f‖_{X_{-m}} ‖Bp‖_{X_m}` when `|N| ≤ Bp` on the cell. -/
theorem lint_pair_le (hCS : WeightedCS) {c m : ℝ} {f : ℝ × ℝ → ℂ} {N Bp : ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f (B0579.cellMeasure c (-m)))
    (hB : AEStronglyMeasurable Bp (B0579.cellMeasure c m))
    (hNB : ∀ x ∈ B0579.cell c, |N x| ≤ Bp x) :
    ∫⁻ x in B0579.cell c, ‖f x * ((N x : ℝ) : ℂ)‖ₑ ≤
      xNorm c (-m) f * eLpNorm Bp 2 (B0579.cellMeasure c m) := by
  refine le_trans ?_ (hCS c m f Bp hf hB)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell' c)] with x hx
  rw [enorm_mul]
  gcongr
  have h1 : ‖N x‖ ≤ ‖Bp x‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hNB x hx).trans (le_abs_self _)
  have h2 : ‖((N x : ℝ) : ℂ)‖ₑ = ‖N x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  rw [h2]
  exact enorm_le_iff_norm_le.2 h1

theorem integrable_pair (hCS : WeightedCS) {c m K : ℝ} {f : ℝ × ℝ → ℂ} {N B : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hB : MemLp B 2 (B0579.cellMeasure c m))
    (hN : AEStronglyMeasurable N (volume.restrict (B0579.cell c)))
    (hNB : ∀ x ∈ B0579.cell c, |N x| ≤ K * B x) :
    Integrable (fun x => f x * ((N x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := by
  refine ⟨?_, ?_⟩
  · exact (hf.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))).mul (aesm_ofReal hN)
  · have hKB : MemLp (fun x => K * B x) 2 (B0579.cellMeasure c m) := hB.const_mul K
    have := lint_pair_le hCS hf.aestronglyMeasurable hKB.aestronglyMeasurable hNB
    refine lt_of_le_of_lt this (ENNReal.mul_lt_top ?_ ?_)
    · exact hf.2
    · exact hKB.2

/-- Abstract continuity of a weighted pairing (SP 3060): `φ ∈ C([t,s]; X_{-m})`, a multiplier
dominated by `B ∈ X_m` and continuous in the parameter. -/
theorem weighted_pair_cont (hCS : WeightedCS) {c m t s : ℝ} (φ : ℝ → ℝ × ℝ → ℂ)
    (M : ℝ → ℝ × ℝ → ℝ) (B : ℝ × ℝ → ℝ)
    (hφm : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m)))
    (hφc : ∀ r ∈ Icc t s,
      Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0))
    (hB : MemLp B 2 (B0579.cellMeasure c m))
    (hMB : ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell c, |M r x| ≤ B x)
    (hMm : ∀ r ∈ Icc t s, AEStronglyMeasurable (M r) (volume.restrict (B0579.cell c)))
    (hMc : ∀ x ∈ B0579.cell c, ∀ r₀ ∈ Icc t s,
      Tendsto (fun r => M r x) (𝓝[Icc t s] r₀) (𝓝 (M r₀ x))) :
    ContinuousOn (fun r => ∫ x in B0579.cell c, φ r x * ((M r x : ℝ) : ℂ)) (Icc t s) := by
  intro r₀ hr₀
  have hμ := measurableSet_cell' c
  have hint : ∀ r ∈ Icc t s, Integrable (fun x => φ r x * ((M r x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := fun r hr =>
    integrable_pair hCS (K := 1) (hφm r hr) hB (hMm r hr) (fun x hx => by simpa using hMB r hr x hx)
  have hdiff : ∀ r ∈ Icc t s, Integrable
      (fun x => (φ r x - φ r₀ x) * ((M r x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
    fun r hr => integrable_pair hCS (K := 1) ((hφm r hr).sub (hφm r₀ hr₀)) hB (hMm r hr)
      (fun x hx => by simpa using hMB r hr x hx)
  have hdiff2 : ∀ r ∈ Icc t s, Integrable
      (fun x => φ r₀ x * (((M r x - M r₀ x : ℝ)) : ℂ)) (volume.restrict (B0579.cell c)) :=
    fun r hr => integrable_pair hCS (K := 2) (hφm r₀ hr₀) hB ((hMm r hr).sub (hMm r₀ hr₀))
      (fun x hx => by
        have h1 := hMB r hr x hx
        have h2 := hMB r₀ hr₀ x hx
        calc |M r x - M r₀ x| ≤ |M r x| + |M r₀ x| := abs_sub _ _
          _ ≤ 2 * B x := by linarith)
  have hBnn : ∀ x ∈ B0579.cell c, 0 ≤ B x := fun x hx =>
    (abs_nonneg _).trans (hMB r₀ hr₀ x hx)
  have hBm : AEStronglyMeasurable B (volume.restrict (B0579.cell c)) :=
    hB.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m)
  have hbint : Integrable (fun x => 2 * ‖φ r₀ x * ((B x : ℝ) : ℂ)‖)
      (volume.restrict (B0579.cell c)) :=
    (integrable_pair hCS (K := 1) (hφm r₀ hr₀) hB hBm
      (fun x hx => by rw [one_mul, abs_of_nonneg (hBnn x hx)])).norm.const_mul 2
  have hT : Tendsto (fun r => ∫ x in B0579.cell c, φ r₀ x * (((M r x - M r₀ x : ℝ)) : ℂ))
      (𝓝[Icc t s] r₀) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (B0579.cell c)) (l := 𝓝[Icc t s] r₀)
      (F := fun r x => φ r₀ x * (((M r x - M r₀ x : ℝ)) : ℂ)) (f := fun _ => (0 : ℂ))
      (bound := fun x => 2 * ‖φ r₀ x * ((B x : ℝ) : ℂ)‖) ?_ ?_ hbint ?_
    · simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hdiff2 r hr).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      filter_upwards [ae_restrict_mem hμ] with x hx
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (hBnn x hx)]
      have h1 := hMB r hr x hx
      have h2 := hMB r₀ hr₀ x hx
      have : |M r x - M r₀ x| ≤ 2 * B x := by
        calc |M r x - M r₀ x| ≤ |M r x| + |M r₀ x| := abs_sub _ _
          _ ≤ 2 * B x := by linarith
      calc ‖φ r₀ x‖ * |M r x - M r₀ x| ≤ ‖φ r₀ x‖ * (2 * B x) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = 2 * (‖φ r₀ x‖ * B x) := by ring
    · filter_upwards [ae_restrict_mem hμ] with x hx
      have h := (hMc x hx r₀ hr₀).sub_const (M r₀ x)
      rw [sub_self] at h
      have h' := (Complex.continuous_ofReal.tendsto 0).comp h
      have h'' := h'.const_mul (φ r₀ x)
      simpa using h''
  -- first piece by the weighted Cauchy-Schwarz bound
  have heB : eLpNorm B 2 (B0579.cellMeasure c m) ≠ ⊤ := hB.2.ne
  have hfin : ∀ r ∈ Icc t s, xNorm c (-m) (φ r - φ r₀) ≠ ⊤ := fun r hr =>
    ((hφm r hr).sub (hφm r₀ hr₀)).2.ne
  have hG : Tendsto (fun r => (xNorm c (-m) (φ r - φ r₀) *
      eLpNorm B 2 (B0579.cellMeasure c m)).toReal) (𝓝[Icc t s] r₀) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const (hφc r₀ hr₀) (Or.inr heB)
    rw [zero_mul] at h1
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by have := hG.add hT.norm; rwa [norm_zero, add_zero] at this)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsplit : (∫ x in B0579.cell c, φ r x * ((M r x : ℝ) : ℂ)) -
      (∫ x in B0579.cell c, φ r₀ x * ((M r₀ x : ℝ) : ℂ)) =
      (∫ x in B0579.cell c, (φ r x - φ r₀ x) * ((M r x : ℝ) : ℂ)) +
      ∫ x in B0579.cell c, φ r₀ x * (((M r x - M r₀ x : ℝ)) : ℂ) := by
    rw [← integral_add (hdiff r hr) (hdiff2 r hr), ← integral_sub (hint r hr) (hint r₀ hr₀)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.ofReal_sub]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (hfin r hr) heB) ?_
  have := lint_pair_le hCS (f := φ r - φ r₀) (N := M r) (Bp := B)
    ((hφm r hr).sub (hφm r₀ hr₀)).aestronglyMeasurable hB.aestronglyMeasurable (hMB r hr)
  simp only [ofReal_norm]
  exact this

/-- `AdjTestedRhsCont` from the four leaves. -/
theorem adjTestedRhsCont_of (m : ℝ) (h1 : WeightedCS) (h2 : AdjMDominated m)
    (h3 : AdjMPointwiseCont) (h4 : AdjMMeasurable) : AdjTestedRhsCont m := by
  intro ν hν hν1 tr hbdd t s ht hts g φ hφ ψ uψ hψ hu
  obtain ⟨B, hB, hMB⟩ := h2 ν hν hν1 tr hbdd t s ht hts ψ uψ hψ hu
  exact weighted_pair_cont h1 φ (fun r => adjM tr r ψ uψ) B hφ.memX hφ.strongCont hB hMB
    (fun r hr => h4 ν hν hν1 tr ψ uψ hψ hu r (ht.trans hr.1))
    (fun x _ r₀ hr₀ => ((h3 ν hν hν1 tr ψ uψ hψ x) r₀ (ht.trans hr₀.1)).mono
      (fun r hr => ht.trans hr.1))

end UnforcedLeray.Short.IIIa
