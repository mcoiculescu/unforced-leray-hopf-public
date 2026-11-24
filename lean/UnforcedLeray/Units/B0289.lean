import UnforcedLeray.Units.B0289.Assembly

/-!
# B0289: the free graph bound (imported)

Unit B0289 of `paper/main.tex` (unlabelled display, tex lines 4771–4775, in
§`sec:mixed-background`); blueprint unit B0289 of

on B0284 (`background:eq:2.24`, the flat inverse `T̄`). The manuscript states, for
`b₀ = T̄F` and `F ∈ H_p`, `p = 11/4`:

`‖b₀‖_{H_p} + ‖√(νs) D b₀‖_{H_p} + ‖ν s D² b₀‖_{H_p} ≤ C_p ‖F‖_{H_p}`,

"The free graph gives" it; the proof is the flat-map paragraph of
§`sec:free-flat-body-graph` (tex lines 3772–3819) at `μ = 0`: heat contraction and Minkowski
for `b₀` (B0284), a cutoff on each dyadic age window `[a, 2a]` and the heat estimate
eq:free-stress-11 on the cylinder for `ν s D² b₀` (tex lines 3784–3810), spatial heat
interpolation for `√s ∇ b₀` (tex lines 3811–3815).

## What is formalized

`freeGraph_bound` proves the bound for every `1 ≤ p < 3` (the manuscript's `p = 11/4` is
`freeGraph_bound_eleven_quarters`): there are jointly measurable, periodic weak second spatial
derivatives `D2 i j = ∂_i∂_j b₀` and periodic weak first derivatives `D1 i = ∂_i b₀` of
`b₀(s) = flatInverse ν c F s` on the cylinder (test domain `Sob.cylinder c`), for almost every
age `s > 0`, with

`‖b₀‖_{H_p} + Σ_i ‖√(νs) ∂_i b₀‖_{H_p} + Σ_{i,j} ‖ν s ∂_i∂_j b₀‖_{H_p} ≤ K ‖F‖_{H_p}`,

`K = freeGraphConst p C_L C_M C_I` (the predicate `FreeGraphBound`). Derivatives are the
periodic weak derivatives of the manuscript (tex lines 4573–4577), `D` is the spatial gradient
in `(q, η)`, and `H_p = L^p(s^{p/2-5/2} ds; L^p(dq/c dη))` (`B0284.HpNorm`).

## Hypotheses

* `ν > 0`, `c > 0`, `1 ≤ p < 3`, `F ∈ H_p` (`HpNorm c p F < ⊤`): the manuscript's.
* `hmeas`, `hLeray`: the two consequences of the `L^p` theory of the flat Leray projection
  `𝕡₀` (Grafakos Cor. 5.2.8, blueprint INF01) used by B0284, with the same statements as
  `B0284.flatInverse_Hp_le`.
* `CylHeatMaxReg ν c p C_M`: parabolic maximal regularity on the cylinder, eq:free-stress-11
  (blueprint INF02 T8/T9; built by another wave in `Lib/Parabolic`), Duhamel form.
* `CylGradInterp c p C_I`: the gradient interpolation on the cylinder (blueprint INF01 §4.4,
  INF11 S9b).

`K` depends only on `p`, `C_L`, `C_M`, `C_I` and the fixed cutoff, so it is uniform in `ν`
and `c` whenever these three constants are (as eq:free-stress-11, the Leray bound and the
interpolation inequality provide).

## Proof route (Lean)

The dyadic cutoff argument is carried out in Duhamel form: `duhamel_cutoff`
(`Units/B0289/Cutoff.lean`) proves `χ(s) b₀(s) = ∫_0^s e^{ν(s-t)Δ}[χ 𝕡₀F/t + χ' b₀] dt` from
the heat semigroup law (`Units/B0289/Semigroup.lean`); `CylHeatMaxReg` is applied to this
source on every window `[2^k, 2^{k+1})` (`exists_D2`, `Units/B0289/Assembly.lean`), and the
windows are summed with the weight comparison of `Units/B0289/Dyadic.lean`. A jointly
measurable periodic version of `t ↦ 𝕡₀(F(t)/t)` is produced in `Units/B0289/Periodize.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-! ## The constants -/

/-- `C_L γ_p^{-1}`, the constant of B0284 (`‖b₀‖_{H_p} ≤ C_L γ_p^{-1} ‖F‖_{H_p}`). -/
def freeGraphConstLeray (p : ℝ) (CL : ℝ≥0) : ℝ≥0∞ := CL * ENNReal.ofReal (gammaP p)⁻¹

/-- The constant of the second-derivative bound `‖ν s ∂_i∂_j b₀‖_{H_p} ≤ K_D ‖F‖_{H_p}`. -/
def freeGraphConstD2 (p : ℝ) (CL CM : ℝ≥0) : ℝ≥0∞ :=
  384 * CM * (2 * CL + cutoffBound * freeGraphConstLeray p CL)

/-- The constant `C_p` of the free graph bound. -/
def freeGraphConst (p : ℝ) (CL CM CI : ℝ≥0) : ℝ≥0∞ :=
  freeGraphConstLeray p CL + 2 * (CI * (freeGraphConstLeray p CL + 4 * freeGraphConstD2 p CL CM)) +
    4 * freeGraphConstD2 p CL CM

theorem freeGraphConst_lt_top (p : ℝ) (CL CM CI : ℝ≥0) : freeGraphConst p CL CM CI < ⊤ := by
  unfold freeGraphConst freeGraphConstD2 freeGraphConstLeray
  finiteness

/-! ## The statement -/

/-- **The free graph bound** for `b₀ = T̄F` with constant `K` (tex lines 4771–4775): periodic
weak first and second spatial derivatives of `b₀(s)` on the cylinder exist for almost every
age `s > 0` (the second ones jointly measurable), and
`‖b₀‖_{H_p} + Σ_i ‖√(νs) ∂_i b₀‖_{H_p} + Σ_{i,j} ‖ν s ∂_i∂_j b₀‖_{H_p} ≤ K ‖F‖_{H_p}`. -/
def FreeGraphBound (ν c p : ℝ) (F : ℝ → Plane → Plane) (K : ℝ≥0∞) : Prop :=
  ∃ (D1 : Fin 2 → ℝ → Plane → Plane) (D2 : Fin 2 → Fin 2 → ℝ → Plane → Plane),
    (∀ i j, StronglyMeasurable (Function.uncurry (D2 i j))) ∧
    (∀ i s, IsQPeriodic c (D1 i s)) ∧ (∀ i j s, IsQPeriodic c (D2 i j s)) ∧
    (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i,
      Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i] (flatInverse ν c F s) (D1 i s)) ∧
    (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i j,
      Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (flatInverse ν c F s)
        (D2 i j s)) ∧
    HpNorm c p (flatInverse ν c F) +
        ∑ i, HpNorm c p (fun s => Real.sqrt (ν * s) • D1 i s) +
        ∑ i, ∑ j, HpNorm c p (fun s => (ν * s) • D2 i j s) ≤
      K * HpNorm c p F

/-! ## The theorem -/

/-- **B0289, the free graph bound** (tex lines 4771–4775; proof tex lines 3772–3819), for
`1 ≤ p < 3`, conditional on the named hypotheses `CylHeatMaxReg` (INF02 T8/T9) and
`CylGradInterp` (INF01 §4.4 / INF11 S9b), and on the `L^p` theory of `𝕡₀` in the form
`hmeas`, `hLeray` of B0284. -/
theorem freeGraph_bound {ν c p : ℝ} (hν : 0 < ν) (hc : 0 < c) (hp1 : 1 ≤ p) (hp3 : p < 3)
    {F : ℝ → Plane → Plane} (hF : HpNorm c p F < ⊤) (CL : ℝ≥0)
    (hmeas : ∃ G : ℝ → Plane → Plane, StronglyMeasurable (Function.uncurry G) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi 0)), G t =ᵐ[volume] flatLeray c (t⁻¹ • F t))
    (hLeray : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c) ≤
        CL * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal p) (cellMeasure c))
    (CM : ℝ≥0) (hMR : CylHeatMaxReg ν c p CM) (CI : ℝ≥0) (hGI : CylGradInterp c p CI) :
    FreeGraphBound ν c p F (freeGraphConst p CL CM CI) := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  obtain ⟨G, hGm, hG⟩ := id hmeas
  obtain ⟨hĜm, hĜper, hĜae⟩ := periodic_version hc hGm
  set Ĝ : ℝ → Plane → Plane := fun t z => G t (wrap c z) with hĜdef
  have hĜ : ∀ᵐ t ∂(volume.restrict (Ioi 0)), Ĝ t =ᵐ[volume] flatLeray c (t⁻¹ • F t) := by
    filter_upwards [hG] with t ht
    exact hĜae t _ (flatLeray_periodic c _) ht
  have hb : flatInverse ν c F = duhamel ν Ĝ := flatInverse_eq_duhamel_of_ae hν hĜ
  have hum : StronglyMeasurable (Function.uncurry (duhamel ν Ĝ)) :=
    stronglyMeasurable_duhamel hĜm
  have huper : ∀ s, IsQPeriodic c (duhamel ν Ĝ s) := duhamel_periodic hĜper
  have hK0 : HpNorm c p (duhamel ν Ĝ) ≤ freeGraphConstLeray p CL * HpNorm c p F := by
    rw [← hb]
    exact flatInverse_Hp_le hν hc hp1 hp3 CL hmeas hLeray
  have hK0fin : freeGraphConstLeray p CL ≠ ⊤ := by
    unfold freeGraphConstLeray
    finiteness
  have hNG := NG_bound hp0 hĜ hLeray
  have hNGm : Measurable fun t => eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) :=
    measurable_eLpNorm_slice hĜm c hP0 ENNReal.ofReal_ne_top
  have hNum : Measurable fun t => eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c) :=
    measurable_eLpNorm_slice hum c hP0 ENNReal.ofReal_ne_top
  set Z : ℝ → ℝ≥0∞ := fun t =>
    2 * (ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c)) +
      (cutoffBound : ℝ≥0∞) * eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c)
    with hZdef
  have hZb : eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) ≤
      (2 * CL + cutoffBound * freeGraphConstLeray p CL) * HpNorm c p F := by
    have h1 : Measurable fun t =>
        ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) :=
      ENNReal.measurable_ofReal.mul hNGm
    calc eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2))
        ≤ eLpNorm (fun t => 2 * (ENNReal.ofReal t *
              eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c)))
            (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) +
          eLpNorm (fun t => (cutoffBound : ℝ≥0∞) *
              eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c))
            (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) :=
          eLpNorm_add_le (h1.const_mul 2).aestronglyMeasurable
            (hNum.const_mul _).aestronglyMeasurable hP1
      _ = 2 * eLpNorm (fun t => ENNReal.ofReal t *
              eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c))
            (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) +
          cutoffBound * HpNorm c p (duhamel ν Ĝ) := by
          rw [eLpNorm_const_mul_ennreal (by norm_num) _ hP0 ENNReal.ofReal_ne_top,
            eLpNorm_const_mul_ennreal ENNReal.coe_ne_top _ hP0 ENNReal.ofReal_ne_top]
          rfl
      _ ≤ 2 * (CL * HpNorm c p F) +
          cutoffBound * (freeGraphConstLeray p CL * HpNorm c p F) := by
          gcongr
      _ = (2 * CL + cutoffBound * freeGraphConstLeray p CL) * HpNorm c p F := by ring
  have hconst : (2 * (CL : ℝ≥0∞) + cutoffBound * freeGraphConstLeray p CL) ≠ ⊤ := by
    unfold freeGraphConstLeray
    finiteness
  have hZ : eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) < ⊤ :=
    hZb.trans_lt (ENNReal.mul_lt_top hconst.lt_top hF)
  have hNGfin := ae_lintegral_lt_top hp1 hp3 hNGm
    (hNG.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hF))
  have hfinA : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ᵐ z ∂(volume : Measure Plane),
      ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z < ⊤ := by
    filter_upwards [hNGfin] with s hs
    exact ae_heatAbs_lt_top hν hc hp1 hĜm hĜper hs
  obtain ⟨D2, hD2m, hD2per, hD2w, hD2b⟩ :=
    exists_D2 hν hp1 hp3 hĜm hĜper hfinA hZdef hZ hMR
  have hD2b' : ∀ i j, HpNorm c p (fun s => (ν * s) • D2 i j s) ≤
      freeGraphConstD2 p CL CM * HpNorm c p F := by
    intro i j
    refine (hD2b i j).trans ?_
    calc 384 * (CM : ℝ≥0∞) * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2))
        ≤ 384 * CM * ((2 * CL + cutoffBound * freeGraphConstLeray p CL) * HpNorm c p F) := by
          gcongr
      _ = freeGraphConstD2 p CL CM * HpNorm c p F := by
          unfold freeGraphConstD2
          ring
  have hD2fin : ∀ i j, HpNorm c p (fun s => (ν * s) • D2 i j s) < ⊤ := fun i j =>
    (hD2b i j).trans_lt (ENNReal.mul_lt_top (by finiteness) hZ)
  have hufin : HpNorm c p (duhamel ν Ĝ) < ⊤ :=
    hK0.trans_lt (ENNReal.mul_lt_top hK0fin.lt_top hF)
  obtain ⟨D1, hD1per, hD1w, hD1b⟩ :=
    exists_D1 hν hp1 hum huper hufin hD2m hD2per hD2w hD2fin hGI
  refine ⟨D1, D2, hD2m, hD1per, hD2per, ?_, ?_, ?_⟩
  · rw [hb]
    exact hD1w
  · rw [hb]
    exact hD2w
  · rw [hb]
    have h1 : ∑ i, HpNorm c p (fun s => Real.sqrt (ν * s) • D1 i s) ≤
        ∑ _i : Fin 2, (CI : ℝ≥0∞) * (freeGraphConstLeray p CL * HpNorm c p F +
          ∑ _k : Fin 2, ∑ _l : Fin 2, freeGraphConstD2 p CL CM * HpNorm c p F) := by
      refine Finset.sum_le_sum fun i _ => (hD1b i).trans ?_
      gcongr with k _ l _
      exact hD2b' k l
    have h2 : ∑ i, ∑ j, HpNorm c p (fun s => (ν * s) • D2 i j s) ≤
        ∑ _i : Fin 2, ∑ _j : Fin 2, freeGraphConstD2 p CL CM * HpNorm c p F :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hD2b' i j
    calc HpNorm c p (duhamel ν Ĝ) + ∑ i, HpNorm c p (fun s => Real.sqrt (ν * s) • D1 i s) +
          ∑ i, ∑ j, HpNorm c p (fun s => (ν * s) • D2 i j s)
        ≤ freeGraphConstLeray p CL * HpNorm c p F +
            ∑ _i : Fin 2, (CI : ℝ≥0∞) * (freeGraphConstLeray p CL * HpNorm c p F +
              ∑ _k : Fin 2, ∑ _l : Fin 2, freeGraphConstD2 p CL CM * HpNorm c p F) +
            ∑ _i : Fin 2, ∑ _j : Fin 2, freeGraphConstD2 p CL CM * HpNorm c p F :=
          add_le_add (add_le_add hK0 h1) h2
      _ = freeGraphConst p CL CM CI * HpNorm c p F := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_ofNat]
          unfold freeGraphConst
          ring

/-- **B0289 at the manuscript's exponent** `p = 11/4` (tex line 4751). -/
theorem freeGraph_bound_eleven_quarters {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {F : ℝ → Plane → Plane} (hF : HpNorm c (11 / 4) F < ⊤) (CL : ℝ≥0)
    (hmeas : ∃ G : ℝ → Plane → Plane, StronglyMeasurable (Function.uncurry G) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi 0)), G t =ᵐ[volume] flatLeray c (t⁻¹ • F t))
    (hLeray : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal (11 / 4)) (cellMeasure c) ≤
        CL * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal (11 / 4)) (cellMeasure c))
    (CM : ℝ≥0) (hMR : CylHeatMaxReg ν c (11 / 4) CM) (CI : ℝ≥0)
    (hGI : CylGradInterp c (11 / 4) CI) :
    FreeGraphBound ν c (11 / 4) F (freeGraphConst (11 / 4) CL CM CI) :=
  freeGraph_bound hν hc (by norm_num) (by norm_num) hF CL hmeas hLeray CM hMR CI hGI

end UnforcedLeray.B0289
