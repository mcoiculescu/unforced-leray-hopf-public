import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecay
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.GramInvSplit

/-!
# Part III-a, task `PartIII-a:T21/c5/2/1/1`: unnormalised heat/dilation dual decomposition and Gram-derivative bound (`MovLam0HeatDecomp`, SP 2905-2912, 2990-2997)

Source of record: `the November 2 reference manuscript` (SP), lines 2905-2912 and
2990-2997 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Proved results in this file

1. **Unnormalised `X_{-m, d}` heat bound and cell integrability against `perE`
   (`movLam0DualHeat_memLp_and_xNorm_of_sharpDecay`, `perE_memLp_cellMeasure`,
   `movLam0DualHeat_mul_perE_integrableOn_of_memLp`)**:
   * From `SeedLamPDSharpDecay κ`, shows that for every `m > 8`, `0 < ν`, `0 ≤ r`, `1 ≤ d`, and
     `k : Fin 2`, `MemLp (movLam0DualHeat κ ν r k) 2 (B0579.cellMeasure d (-m))` and
     `xNorm d (-m) (movLam0DualHeat κ ν r k) ≤ ENNReal.ofReal (C_0 / clockTheta ν r)`.
   * Combines `perEBound` and `FrameCont.perE_continuous` with
     `ComplCouplingSub.xNorm_pairing_bound` to prove that
     `fun y => movLam0DualHeat κ ν r k y * perE κ d j y` is integrable on `B0579.cell d`.
2. **Product-rule and Laplacian decomposition of `movLamDualHeat`
   (`lapCx_linear_comb_fin2`, `ladLapCx_physFrameLam_eq`, `ladDt_physFrameLam_eq`,
   `movLamDualHeat_eq_sum_of_diff`)**:
   * Proves linearity of `ladLapCx` on `Fin 2` linear combinations of `C²` planar fields and
     combines it with `ComplCouplingHeat.contDiff_perSum_physAdj` and
     `ComplCouplingHeat.hasDerivWithinAt_physFrameLam0` to establish the exact product-rule split
     `movLamDualHeat κ ν r i y = ∑ k, (perGram κ d)⁻¹ i k * movLam0DualHeat κ ν r k y + ∑ k, movGramInvDeriv κ ν r i k * perLam0 κ d k y`.
3. **Chain-rule reduction of `movGramInvDeriv` to `∂_d((perGram κ d)⁻¹)`
   (`hasDerivAt_perGram_inv_comp_cellLen`, `movGramInvDeriv_eq_of_hasDerivAt`,
   `norm_movGramInvDeriv_le_of_hasDerivAt`)**:
   * Uses `OscillatorForceSub.hasDerivAt_cellLen` (`∂_r d(r) = -(a(r)⁻² / (2 * θ(r))) * d(r)`) to
     prove that if `HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv' d` with
     `‖G_inv'‖ ≤ C_inv / d ^ 3`, then
     `movGramInvDeriv κ ν r i k = (-(1 / 2) * (clockTheta ν r)⁻¹ * d) • G_inv'` and
     `‖movGramInvDeriv κ ν r i k‖ ≤ (C_inv / 2) / (clockTheta ν r * d ^ 2)`.
4. **Conditional assemblies (`perGramInvHeatSplit_of`,
   `movLam0HeatDecomp_of`)**:
   * Assembles `ComplCouplingHeat.PerGramInvHeatSplit κ` and `MovLam0HeatDecomp κ` from
     `SeedLamPJet2Decay κ` and `PerGramInvDerivDecay κ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DirectHeatDecomp

open ComplCouplingSub ComplCouplingHeat DirectHeatSub

/-! ## 1. `X_{-m, d}` bound for `movLam0DualHeat` and cell integrability against `perE` -/

/-- `clockTheta ν r > 0` for `0 < ν` and `0 ≤ r`. -/
theorem clockTheta_pos {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 < clockTheta ν r := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  unfold clockTheta
  positivity

/-- `perE κ d j` belongs to `L²(B0579.cellMeasure d m)` for `m > 8` and `d ≥ 1`. -/
theorem perE_memLp_cellMeasure (κ : PlanarFrameKernels) {m : ℝ} (hm : 8 < m) :
    ∃ K_E : ℝ, 0 ≤ K_E ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ j : Fin 2,
      MemLp (perE κ d j) 2 (B0579.cellMeasure d m) ∧
      xNorm d m (perE κ d j) ≤ ENNReal.ofReal K_E := by
  obtain ⟨K₀, hK₀⟩ := perEBound κ m hm
  refine ⟨max K₀ 0, le_max_right _ _, fun {d} hd j => ?_⟩
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hcont : Continuous (perE κ d j) := FrameCont.perE_continuous κ hd_pos j
  have hmeas : AEStronglyMeasurable (perE κ d j) (B0579.cellMeasure d m) :=
    hcont.aestronglyMeasurable
  have hx : xNorm d m (perE κ d j) ≤ ENNReal.ofReal (max K₀ 0) :=
    (hK₀ d hd j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hlt : eLpNorm (perE κ d j) 2 (B0579.cellMeasure d m) < ⊤ :=
    lt_of_le_of_lt hx ENNReal.ofReal_lt_top
  exact ⟨⟨hmeas, hlt⟩, hx⟩

/-- Whenever `movLam0DualHeat κ ν r k` belongs to `L²(B0579.cellMeasure d (-m))` (`m > 8`, `d ≥ 1`),
its product with `perE κ d j` is integrable on `B0579.cell d`. -/
theorem movLam0DualHeat_mul_perE_integrableOn_of_memLp (κ : PlanarFrameKernels)
    {m ν r : ℝ} (hm : 8 < m)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (k j : Fin 2)
    (hMem : MemLp (movLam0DualHeat κ ν r k) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    IntegrableOn
      (fun y => movLam0DualHeat κ ν r k y *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y)
      (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) volume := by
  obtain ⟨K_E, -, hE⟩ := perE_memLp_cellMeasure κ hm
  have hMemE : MemLp (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    (hE hd j).1
  exact (xNorm_pairing_bound hMem hMemE).1

/-- From `SeedLamPDSharpDecay κ`, `movLam0DualHeat κ ν r k` belongs to `X_{-m, d}` with norm
`≤ C_0 / clockTheta ν r` and its product with `perE κ d j` is integrable on `B0579.cell d`. -/
theorem movLam0DualHeat_memLp_and_xNorm_of_sharpDecay (κ : PlanarFrameKernels)
    (hSharp : SeedLamPDSharpDecay κ) (hκ : IsSeedKernels κ) {m : ℝ} (hm : 8 < m) :
    ∃ C_0 : ℝ, 0 ≤ C_0 ∧
      ∀ {ν r : ℝ}, 0 < ν → 0 ≤ r →
        let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
        1 ≤ d →
        (∀ k : Fin 2,
          MemLp (movLam0DualHeat κ ν r k) 2 (B0579.cellMeasure d (-m)) ∧
          xNorm d (-m) (movLam0DualHeat κ ν r k) ≤ ENNReal.ofReal (C_0 / clockTheta ν r)) ∧
        (∀ k j : Fin 2,
          IntegrableOn (fun y => movLam0DualHeat κ ν r k y * perE κ d j y)
            (B0579.cell d) volume) := by
  have hm1 : 1 < m := by linarith
  obtain ⟨Ψ, C_sharp, -, hΨ_cont, hΨ_dec, hΨ_id⟩ := hSharp hκ
  obtain ⟨K_Ψ0, hK_Ψ0, hΨ0⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hΨ_cont 0) (hΨ_dec 0)
  obtain ⟨K_Ψ1, hK_Ψ1, hΨ1⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hΨ_cont 1) (hΨ_dec 1)
  set C_0 : ℝ := max K_Ψ0 K_Ψ1
  have hC_0 : 0 ≤ C_0 := le_trans hK_Ψ0 (le_max_left _ _)
  refine ⟨C_0, hC_0, fun {ν r} hν hr hd => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hθ : 0 < clockTheta ν r := clockTheta_pos hν hr
  have hPer : ∀ k : Fin 2,
      MemLp (perSum d (Ψ k)) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (perSum d (Ψ k)) ≤ ENNReal.ofReal C_0 := by
    intro k
    fin_cases k
    · exact ⟨(hΨ0 d hd).1, (hΨ0 d hd).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    · exact ⟨(hΨ1 d hd).1, (hΨ1 d hd).2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  have hmain : ∀ k : Fin 2,
      MemLp (movLam0DualHeat κ ν r k) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (movLam0DualHeat κ ν r k) ≤
        ENNReal.ofReal (C_0 / clockTheta ν r) := by
    intro k
    have heq : movLam0DualHeat κ ν r k =
        fun y => (clockTheta ν r : ℂ)⁻¹ * perSum d (Ψ k) y :=
      funext (hΨ_id hν hr hd k)
    rw [heq]
    refine ⟨(hPer k).1.const_mul (clockTheta ν r : ℂ)⁻¹, ?_⟩
    refine (xNorm_const_mul_le hC_0 (hPer k).2).trans (ENNReal.ofReal_le_ofReal ?_)
    have hnorm_θ : ‖(clockTheta ν r : ℂ)⁻¹‖ = (clockTheta ν r)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hθ.le]
    rw [hnorm_θ]
    linarith [div_eq_inv_mul C_0 (clockTheta ν r)]
  exact ⟨hmain, fun k j =>
    movLam0DualHeat_mul_perE_integrableOn_of_memLp κ hm hd k j (hmain k).1⟩

/-! ## 2. Linearity of `ladLapCx` and product-rule decomposition of `movLamDualHeat` -/

/-- `Cyl.laplacian` commutes with complex scalar multiplication on `C²` functions. -/
theorem cyl_laplacian_const_mul {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (c : ℂ) (z : ℝ × ℝ) :
    Cyl.laplacian (fun x => c * f x) z = c * Cyl.laplacian f z := by
  have hmul : ContDiff ℝ 2 (fun x => c * f x) := contDiff_const.mul hf
  rw [Gaussian.laplacian_eq_iteratedFDeriv hmul, Gaussian.laplacian_eq_iteratedFDeriv hf]
  have hiter : iteratedFDeriv ℝ 2 (fun x => c * f x) z = c • iteratedFDeriv ℝ 2 f z := by
    change iteratedFDeriv ℝ 2 (c • f) z = c • iteratedFDeriv ℝ 2 f z
    exact iteratedFDeriv_const_smul_apply hf.contDiffAt
  rw [hiter, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, mul_add]

/-- `Cyl.laplacian` is additive on `C²` functions. -/
theorem cyl_laplacian_add {f g : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (z : ℝ × ℝ) :
    Cyl.laplacian (fun x => f x + g x) z = Cyl.laplacian f z + Cyl.laplacian g z := by
  have hadd : ContDiff ℝ 2 (fun x => f x + g x) := hf.add hg
  rw [Gaussian.laplacian_eq_iteratedFDeriv hadd, Gaussian.laplacian_eq_iteratedFDeriv hf,
    Gaussian.laplacian_eq_iteratedFDeriv hg]
  have hiter : iteratedFDeriv ℝ 2 (fun x => f x + g x) z =
      iteratedFDeriv ℝ 2 f z + iteratedFDeriv ℝ 2 g z := by
    change iteratedFDeriv ℝ 2 (f + g) z = iteratedFDeriv ℝ 2 f z + iteratedFDeriv ℝ 2 g z
    exact iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt
  rw [hiter, add_apply, add_apply]
  ring

/-- `ladLapCx` is linear on a two-term linear combination of `C²` planar functions. -/
theorem lapCx_linear_comb_fin2 (c : Fin 2 → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ)
    (hf : ∀ k : Fin 2, ContDiff ℝ 2 (f k)) (z : ℝ × ℝ) :
    ladLapCx (fun x => ∑ k : Fin 2, c k * f k x) z =
      ∑ k : Fin 2, c k * ladLapCx (f k) z := by
  have hf0 : ContDiff ℝ 2 (f 0) := hf 0
  have hf1 : ContDiff ℝ 2 (f 1) := hf 1
  have hcf0 : ContDiff ℝ 2 (fun x => c 0 * f 0 x) := contDiff_const.mul hf0
  have hcf1 : ContDiff ℝ 2 (fun x => c 1 * f 1 x) := contDiff_const.mul hf1
  have hcomb : ContDiff ℝ 2 (fun x => ∑ k : Fin 2, c k * f k x) := by
    have heq : (fun x => ∑ k : Fin 2, c k * f k x) =
        fun x => c 0 * f 0 x + c 1 * f 1 x := by
      funext x; simp [Fin.sum_univ_two]
    rw [heq]
    exact hcf0.add hcf1
  rw [ladLapCx_eq_cyl_laplacian hcomb z]
  simp only [Fin.sum_univ_two]
  rw [cyl_laplacian_add hcf0 hcf1 z, cyl_laplacian_const_mul hf0 (c 0) z,
    cyl_laplacian_const_mul hf1 (c 1) z, ← ladLapCx_eq_cyl_laplacian hf0 z,
    ← ladLapCx_eq_cyl_laplacian hf1 z]

/-- Under `C²` regularity and `O((1 + |z₁|)⁻²)` second-jet bounds on `κ.lamP`, `physFrameLam0 κ ν r k`
is `C²` on `ℝ × ℝ` and `ladLapCx (physFrameLam κ ν r i)` distributes over the Gram-inverse sum. -/
theorem ladLapCx_physFrameLam_eq (κ : PlanarFrameKernels) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hL : ∀ k : Fin 2, ContDiff ℝ 2 (κ.lamP k)) {C : ℝ}
    (h0 : ∀ (k : Fin 2) (z : ℝ × ℝ), ‖κ.lamP k z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ 2 (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (i : Fin 2) (x : ℝ × ℝ) :
    ladLapCx (physFrameLam κ ν r i) x =
      ∑ k : Fin 2,
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k *
          ladLapCx (physFrameLam0 κ ν r k) x := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν (-2)).ne'
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hCD : ∀ k : Fin 2, ContDiff ℝ 2 (physFrameLam0 κ ν r k) := by
    intro k
    have heq : physFrameLam0 κ ν r k =
        perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν r) (κ.lamP k)) :=
      funext (physFrameLam0_eq_perSum_physAdj κ hν hr k)
    rw [heq]
    exact contDiff_perSum_physAdj (hL k) hc ha (h0 k) (h1 k) (h2 k)
  have hsum : physFrameLam κ ν r i =
      fun x' => ∑ k : Fin 2,
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k * physFrameLam0 κ ν r k x' :=
    funext (physFrameLam_eq_sum_perGram_inv κ ν r i)
  rw [hsum]
  exact lapCx_linear_comb_fin2 _ _ hCD x

/-- Product-rule expansion of `ladDt (fun s x' => physFrameLam κ ν s i x') r x` when
`s ↦ (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k` is differentiable within `Ici r` at `r`
and `κ.lamP k` is differentiable with `O((1 + |z₁|)⁻²)` first jet. -/
theorem ladDt_physFrameLam_eq (κ : PlanarFrameKernels) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hL : ∀ k : Fin 2, Differentiable ℝ (κ.lamP k)) {C : ℝ}
    (h0 : ∀ (k : Fin 2) (z : ℝ × ℝ), ‖κ.lamP k z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (i : Fin 2)
    (hG : ∀ k : Fin 2,
      DifferentiableWithinAt ℝ
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
        (Ici r) r)
    (x : ℝ × ℝ) :
    ladDt (fun s x' => physFrameLam κ ν s i x') r x =
      ∑ k : Fin 2,
        ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k *
          ladDt (fun s x' => physFrameLam0 κ ν s k x') r x +
        derivWithin (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
          (Ici r) r *
          physFrameLam0 κ ν r k x) := by
  set g : Fin 2 → ℝ → ℂ :=
    fun k s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k
  set f : Fin 2 → ℝ → ℂ := fun k s => physFrameLam0 κ ν s k x
  have hg : ∀ k : Fin 2, HasDerivWithinAt (g k) (derivWithin (g k) (Ici r) r) (Ici r) r :=
    fun k => (hG k).hasDerivWithinAt
  have hf : ∀ k : Fin 2,
      HasDerivWithinAt (f k) (ladDt (fun s x' => physFrameLam0 κ ν s k x') r x) (Ici r) r := by
    intro k
    have hder := hasDerivWithinAt_physFrameLam0 κ hν hr k (hL k) (h0 k) (h1 k) x
    have hdt : ladDt (fun s x' => physFrameLam0 κ ν s k x') r x = _ :=
      ladDt_physFrameLam0_eq κ hν hr k (hL k) (h0 k) (h1 k) x
    rw [hdt]
    exact hder
  have hmul : ∀ k : Fin 2,
      HasDerivWithinAt (fun s => g k s * f k s)
        (derivWithin (g k) (Ici r) r * f k r +
          g k r * ladDt (fun s x' => physFrameLam0 κ ν s k x') r x)
        (Ici r) r :=
    fun k => (hg k).mul (hf k)
  have hadd := (hmul 0).add (hmul 1)
  have hcongr : HasDerivWithinAt (fun s => physFrameLam κ ν s i x)
      ((derivWithin (g 0) (Ici r) r * f 0 r +
          g 0 r * ladDt (fun s x' => physFrameLam0 κ ν s 0 x') r x) +
        (derivWithin (g 1) (Ici r) r * f 1 r +
          g 1 r * ladDt (fun s x' => physFrameLam0 κ ν s 1 x') r x))
      (Ici r) r := by
    refine hadd.congr (fun s _ => ?_) ?_
    · rw [physFrameLam_eq_sum_perGram_inv κ ν s i x, Fin.sum_univ_two]
      rfl
    · rw [physFrameLam_eq_sum_perGram_inv κ ν r i x, Fin.sum_univ_two]
      rfl
  change derivWithin (fun s => physFrameLam κ ν s i x) (Ici r) r = _
  rw [hcongr.derivWithin (uniqueDiffWithinAt_Ici r), Fin.sum_univ_two]
  dsimp only [g, f]
  ring

/-- Evaluation of `physFrameLam0 κ ν r k` at `(√a(r) * y₁, √a(r) * y₂)`. -/
theorem physFrameLam0_scale_eval (κ : PlanarFrameKernels) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (k : Fin 2) (y : ℝ × ℝ) :
    physFrameLam0 κ ν r k (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      ((clockA ν r : ℝ) : ℂ) *
        perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hsa_ne : Real.sqrt (clockA ν r) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  unfold physFrameLam0 physAdj
  congr 2
  ext
  · exact mul_div_cancel_left₀ y.1 hsa_ne
  · exact mul_div_cancel_left₀ y.2 hsa_ne

/-- Exact product-rule and Laplacian decomposition of `movLamDualHeat κ ν r i y` when `κ.lamP` is
`C²` with `O((1 + |z₁|)⁻²)` second jet and `s ↦ (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k`
is differentiable within `Ici r` at `r`. -/
theorem movLamDualHeat_eq_sum_of_diff (κ : PlanarFrameKernels) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hL : ∀ k : Fin 2, ContDiff ℝ 2 (κ.lamP k)) {C : ℝ}
    (h0 : ∀ (k : Fin 2) (z : ℝ × ℝ), ‖κ.lamP k z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ (k : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ 2 (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (i : Fin 2)
    (hG : ∀ k : Fin 2,
      DifferentiableWithinAt ℝ
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
        (Ici r) r)
    (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movLamDualHeat κ ν r i y =
      (∑ k : Fin 2, (perGram κ d)⁻¹ i k * movLam0DualHeat κ ν r k y) +
      (∑ k : Fin 2, movGramInvDeriv κ ν r i k * perLam0 κ d k y) := by
  intro d
  set a := clockA ν r
  set x : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hLd : ∀ k : Fin 2, Differentiable ℝ (κ.lamP k) :=
    fun k => (hL k).differentiable (by norm_num)
  have hDt := ladDt_physFrameLam_eq κ hν hr hLd h0 h1 i hG x
  have hLap := ladLapCx_physFrameLam_eq κ hν hr hL h0 h1 h2 i x
  have heval0 : physFrameLam0 κ ν r 0 x = ((a : ℝ) : ℂ) * perLam0 κ d 0 y :=
    physFrameLam0_scale_eval κ hν hr 0 y
  have heval1 : physFrameLam0 κ ν r 1 x = ((a : ℝ) : ℂ) * perLam0 κ d 1 y :=
    physFrameLam0_scale_eval κ hν hr 1 y
  unfold movLamDualHeat movLam0DualHeat movGramInvDeriv movingPhi physLamDualHeat physLam0DualHeat
  change (((a ^ (2 : ℝ) : ℝ) : ℂ) *
    (((a⁻¹ : ℝ) : ℂ) *
      (ladDt (fun s x' => physFrameLam κ ν s i x') r x +
        (ν : ℂ) * ladLapCx (physFrameLam κ ν r i) x))) =
    (∑ k : Fin 2,
      (perGram κ d)⁻¹ i k *
        (((a ^ (2 : ℝ) : ℝ) : ℂ) *
          (((a⁻¹ : ℝ) : ℂ) *
            (ladDt (fun r' x' => physFrameLam0 κ ν r' k x') r x +
              (ν : ℂ) * ladLapCx (physFrameLam0 κ ν r k) x)))) +
    (∑ k : Fin 2,
      (((a ^ (2 : ℝ) : ℝ) : ℂ) *
        derivWithin (fun r' => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')))⁻¹ i k)
          (Ici r) r) *
        perLam0 κ d k y)
  rw [hDt, hLap]
  simp only [Fin.sum_univ_two]
  rw [heval0, heval1]
  dsimp only [d]
  push_cast
  field_simp [haC]
  ring

/-! ## 3. Chain-rule reduction of `movGramInvDeriv` to `∂_d((perGram κ d)⁻¹)` -/

/-- Chain rule for `s ↦ (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k` at `s = r` via
`OscillatorForceSub.hasDerivAt_cellLen`. -/
theorem hasDerivAt_perGram_inv_comp_cellLen (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i k : Fin 2) {G_inv' : ℂ}
    (hG : HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv'
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) :
    let ϑ := (clockA ν r) ^ (-2 : ℝ) * (clockTheta ν r)⁻¹
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    HasDerivAt
      (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
      ((-(ϑ / 2) * d) • G_inv') r := by
  intro ϑ d
  have hcell : HasDerivAt (fun s => cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-(ϑ / 2) * d) r :=
    OscillatorForceSub.hasDerivAt_cellLen hν hr
  exact HasDerivAt.scomp r hG hcell

/-- Explicit formula for `movGramInvDeriv κ ν r i k` in terms of the `d`-derivative `G_inv'` of
`(perGram κ ·)⁻¹ i k`. -/
theorem movGramInvDeriv_eq_of_hasDerivAt (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i k : Fin 2) {G_inv' : ℂ}
    (hG : HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv'
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) :
    movGramInvDeriv κ ν r i k =
      ((-(1 / 2) * (clockTheta ν r)⁻¹ * cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) : ℝ) • G_inv' := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have ha_ne : (clockA ν r : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hcomp := (hasDerivAt_perGram_inv_comp_cellLen κ hν hr i k hG).hasDerivWithinAt (s := Ici r)
  have hderiv := hcomp.derivWithin (uniqueDiffWithinAt_Ici r)
  unfold movGramInvDeriv
  rw [hderiv, Real.rpow_neg ha.le, Real.rpow_two, Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp [ha_ne]

/-- Bound `‖movGramInvDeriv κ ν r i k‖ ≤ (C_inv / 2) / (clockTheta ν r * d ^ 2)` from
`HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv' d` and `‖G_inv'‖ ≤ C_inv / d ^ 3`. -/
theorem norm_movGramInvDeriv_le_of_hasDerivAt (κ : PlanarFrameKernels) {ν r C_inv : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (i k : Fin 2) {G_inv' : ℂ}
    (hG : HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv'
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))
    (hG_bd : ‖G_inv'‖ ≤ C_inv / (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 3) :
    ‖movGramInvDeriv κ ν r i k‖ ≤
      (C_inv / 2) / (clockTheta ν r * (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2) := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hd_ne : d ≠ 0 := hd_pos.ne'
  have hθ_pos : 0 < clockTheta ν r := clockTheta_pos hν hr
  have hθ_ne : clockTheta ν r ≠ 0 := hθ_pos.ne'
  rw [movGramInvDeriv_eq_of_hasDerivAt κ hν hr i k hG, norm_smul, Real.norm_eq_abs]
  have habs : |-(1 / 2) * (clockTheta ν r)⁻¹ * d| = (1 / 2) * (clockTheta ν r)⁻¹ * d := by
    have : -(1 / 2) * (clockTheta ν r)⁻¹ * d = -((1 / 2) * (clockTheta ν r)⁻¹ * d) := by ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  rw [habs]
  calc (1 / 2) * (clockTheta ν r)⁻¹ * d * ‖G_inv'‖
      ≤ (1 / 2) * (clockTheta ν r)⁻¹ * d * (C_inv / d ^ 3) :=
        mul_le_mul_of_nonneg_left hG_bd (by positivity)
    _ = (C_inv / 2) / (clockTheta ν r * d ^ 2) := by
        field_simp [hd_ne, hθ_ne]

/-! ## 4. From `∂_d (perGram κ d) = O(d⁻³)` to `PerGramInvDerivDecay`, and conditional assemblies -/

/-- For any `2 × 2` complex matrix `G` within `1 / 4` of the identity, `1 / 2 ≤ ‖G.det‖` and
`‖G.det⁻¹‖ ≤ 2`. -/
theorem gram_det_lower_and_inv_bound (G : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4) :
    1 / 2 ≤ ‖G.det‖ ∧ G.det ≠ 0 ∧ ‖G.det⁻¹‖ ≤ 2 := by
  have h00 := h 0 0
  have h11 := h 1 1
  have h01 := h 0 1
  have h10 := h 1 0
  simp only [ite_true, ite_false, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, sub_zero,
    one_ne_zero] at h00 h11 h01 h10
  have ha : 3 / 4 ≤ ‖G 0 0‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G 0 0)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hd : 3 / 4 ≤ ‖G 1 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G 1 1)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hdet : 1 / 2 ≤ ‖G.det‖ := by
    rw [Matrix.det_fin_two]
    have h1 := norm_sub_norm_le (G 0 0 * G 1 1) (G 0 1 * G 1 0)
    rw [norm_mul, norm_mul] at h1
    nlinarith [norm_nonneg (G 0 1), norm_nonneg (G 1 0),
      mul_le_mul ha hd (by norm_num) (norm_nonneg _),
      mul_le_mul h01 h10 (norm_nonneg _) (by norm_num)]
  have hne : G.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    linarith
  have hinv : ‖G.det⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  exact ⟨hdet, hne, hinv⟩

/-- Explicit `2 × 2` inverse entry derivative and bound: if `G : ℝ → Matrix (Fin 2) (Fin 2) ℂ` is
within `1 / 4` of the identity at `d` and each entry `G · i j` has derivative `G' i j` at `d`
bounded by `B` (`0 ≤ B`), then each inverse entry `(G ·)⁻¹ i k` is differentiable at `d` with
derivative bounded by `66 * B`. -/
theorem hasDerivAt_gram_inv_entry {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {G' : Matrix (Fin 2) (Fin 2) ℂ}
    {d B : ℝ} (hB0 : 0 ≤ B)
    (h14 : ∀ i j : Fin 2, ‖G d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hder : ∀ i j : Fin 2, HasDerivAt (fun d' => G d' i j) (G' i j) d)
    (hbd : ∀ i j : Fin 2, ‖G' i j‖ ≤ B) (i k : Fin 2) :
    ∃ G_inv' : ℂ,
      HasDerivAt (fun d' => (G d')⁻¹ i k) G_inv' d ∧
      ‖G_inv'‖ ≤ 66 * B := by
  have hentry : ∀ i' j' : Fin 2, ‖G d i' j'‖ ≤ 2 := gram_entry_bound (G d) h14
  obtain ⟨_, hdet_ne, hinv_det⟩ := gram_det_lower_and_inv_bound (G d) h14
  set det' : ℂ :=
    (G' 0 0 * G d 1 1 + G d 0 0 * G' 1 1) - (G' 0 1 * G d 1 0 + G d 0 1 * G' 1 0)
  have hdet_der : HasDerivAt (fun d' => (G d').det) det' d := by
    have heq : (fun d' => (G d').det) =
        fun d' => G d' 0 0 * G d' 1 1 - G d' 0 1 * G d' 1 0 :=
      funext fun d' => Matrix.det_fin_two (G d')
    rw [heq]
    exact ((hder 0 0).mul (hder 1 1)).sub ((hder 0 1).mul (hder 1 0))
  have hdet'_bd : ‖det'‖ ≤ 8 * B := by
    have h1 : ‖G' 0 0 * G d 1 1‖ ≤ 2 * B := by
      rw [norm_mul]
      nlinarith [hbd 0 0, hentry 1 1, norm_nonneg (G' 0 0), norm_nonneg (G d 1 1)]
    have h2 : ‖G d 0 0 * G' 1 1‖ ≤ 2 * B := by
      rw [norm_mul]
      nlinarith [hbd 1 1, hentry 0 0, norm_nonneg (G' 1 1), norm_nonneg (G d 0 0)]
    have h3 : ‖G' 0 1 * G d 1 0‖ ≤ 2 * B := by
      rw [norm_mul]
      nlinarith [hbd 0 1, hentry 1 0, norm_nonneg (G' 0 1), norm_nonneg (G d 1 0)]
    have h4 : ‖G d 0 1 * G' 1 0‖ ≤ 2 * B := by
      rw [norm_mul]
      nlinarith [hbd 1 0, hentry 0 1, norm_nonneg (G' 1 0), norm_nonneg (G d 0 1)]
    calc ‖det'‖
        ≤ ‖G' 0 0 * G d 1 1 + G d 0 0 * G' 1 1‖ +
            ‖G' 0 1 * G d 1 0 + G d 0 1 * G' 1 0‖ := norm_sub_le _ _
      _ ≤ (‖G' 0 0 * G d 1 1‖ + ‖G d 0 0 * G' 1 1‖) +
            (‖G' 0 1 * G d 1 0‖ + ‖G d 0 1 * G' 1 0‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ 8 * B := by linarith
  set inv_det' : ℂ := -det' / (G d).det ^ 2
  have hinv_der : HasDerivAt (fun d' => ((G d').det)⁻¹) inv_det' d :=
    hdet_der.inv hdet_ne
  have hinv_det'_bd : ‖inv_det'‖ ≤ 32 * B := by
    have hrew : inv_det' = -det' * ((G d).det⁻¹ * (G d).det⁻¹) := by
      dsimp [inv_det']
      rw [sq, div_eq_mul_inv, mul_inv]
    rw [hrew, norm_mul, norm_neg, norm_mul]
    have hsq : ‖(G d).det⁻¹‖ * ‖(G d).det⁻¹‖ ≤ 4 := by
      nlinarith [norm_nonneg (G d).det⁻¹]
    nlinarith [norm_nonneg det', norm_nonneg (G d).det⁻¹]
  have hpair : ∀ (A : ℝ → ℂ) (A' : ℂ),
      HasDerivAt A A' d → ‖A d‖ ≤ 2 → ‖A'‖ ≤ B →
      (∀ d', (G d')⁻¹ i k = ((G d').det)⁻¹ * A d') →
      ∃ G_inv' : ℂ, HasDerivAt (fun d' => (G d')⁻¹ i k) G_inv' d ∧ ‖G_inv'‖ ≤ 66 * B := by
    intro A A' hA hAd hA' heq
    refine ⟨inv_det' * A d + (G d).det⁻¹ * A', ?_, ?_⟩
    · have hmul := hinv_der.mul hA
      exact hmul.congr_of_eventuallyEq (Eventually.of_forall heq)
    · calc ‖inv_det' * A d + (G d).det⁻¹ * A'‖
          ≤ ‖inv_det' * A d‖ + ‖(G d).det⁻¹ * A'‖ := norm_add_le _ _
        _ = ‖inv_det'‖ * ‖A d‖ + ‖(G d).det⁻¹‖ * ‖A'‖ := by rw [norm_mul, norm_mul]
        _ ≤ 32 * B * 2 + 2 * B := by
            nlinarith [norm_nonneg inv_det', norm_nonneg (A d),
              norm_nonneg (G d).det⁻¹, norm_nonneg A']
        _ = 66 * B := by ring
  fin_cases i <;> fin_cases k
  · refine hpair (fun d' => G d' 1 1) (G' 1 1) (hder 1 1) (hentry 1 1) (hbd 1 1) (fun d' => ?_)
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp
  · refine hpair (fun d' => -G d' 0 1) (-G' 0 1) (hder 0 1).neg
      (by rw [norm_neg]; exact hentry 0 1) (by rw [norm_neg]; exact hbd 0 1) (fun d' => ?_)
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp
  · refine hpair (fun d' => -G d' 1 0) (-G' 1 0) (hder 1 0).neg
      (by rw [norm_neg]; exact hentry 1 0) (by rw [norm_neg]; exact hbd 1 0) (fun d' => ?_)
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp
  · refine hpair (fun d' => G d' 0 0) (G' 0 0) (hder 0 0) (hentry 0 0) (hbd 0 0) (fun d' => ?_)
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp

/-- **Analytical hypothesis for `d`-differentiability and `O(d⁻³)` decay of `perGram κ d`
(`PerGramDerivDecay`, SP 2898-2902, `∂_d G = O(d⁻³)`)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), in the regime `d ≥ D_d ≥ 1` the Gram matrix
entries `d' ↦ perGram κ d' i j` are differentiable at `d` with derivative bounded by `C_d / d ^ 3`. -/
def PerGramDerivDecay (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ C_d D_d : ℝ, 0 ≤ C_d ∧ 1 ≤ D_d ∧
    ∀ {d : ℝ}, D_d ≤ d → ∀ i j : Fin 2,
      ∃ G' : ℂ,
        HasDerivAt (fun d' => perGram κ d' i j) G' d ∧
        ‖G'‖ ≤ C_d / d ^ 3

/-- **Analytical hypothesis for `d`-differentiability and `O(d⁻³)` decay of `(perGram κ d)⁻¹`
(`PerGramInvDerivDecay`, SP 2898-2902)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), in the regime `d ≥ D_inv ≥ 1` the Gram inverse
entries `d' ↦ (perGram κ d')⁻¹ i k` are differentiable at `d` with derivative bounded by
`C_inv / d ^ 3`. -/
def PerGramInvDerivDecay (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ C_inv D_inv : ℝ, 0 ≤ C_inv ∧ 1 ≤ D_inv ∧
    ∀ {d : ℝ}, D_inv ≤ d → ∀ i k : Fin 2,
      ∃ G_inv' : ℂ,
        HasDerivAt (fun d' => (perGram κ d')⁻¹ i k) G_inv' d ∧
        ‖G_inv'‖ ≤ C_inv / d ^ 3

/-- `PerGramDerivDecay κ` (`∂_d G = O(d⁻³)`) implies `PerGramInvDerivDecay κ`
(`∂_d (G⁻¹) = O(d⁻³)`). -/
theorem perGramInvDerivDecay_of_perGramDerivDecay (κ : PlanarFrameKernels)
    (hGd : PerGramDerivDecay κ) :
    PerGramInvDerivDecay κ := by
  intro hκ
  obtain ⟨C_G, D_G, -, hDG1, hG_near⟩ := perGram_sub_id_bound κ
  obtain ⟨C_d, D_d, hCd0, hDd1, hG_der⟩ := hGd hκ
  refine ⟨66 * C_d, max D_G D_d, by positivity, le_trans hDG1 (le_max_left _ _),
    fun {d} hd i k => ?_⟩
  have hd_G : D_G ≤ d := le_trans (le_max_left _ _) hd
  have hd_d : D_d ≤ d := le_trans (le_max_right _ _) hd
  have hd1 : 1 ≤ d := le_trans hDG1 hd_G
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have h14 : ∀ i' j' : Fin 2, ‖perGram κ d i' j' - (if i' = j' then 1 else 0)‖ ≤ 1 / 4 :=
    fun i' j' => (hG_near d hd_G i' j').2
  let G' : Matrix (Fin 2) (Fin 2) ℂ := fun i' j' => (hG_der hd_d i' j').choose
  have hder : ∀ i' j' : Fin 2, HasDerivAt (fun d' => perGram κ d' i' j') (G' i' j') d :=
    fun i' j' => (hG_der hd_d i' j').choose_spec.1
  have hbd : ∀ i' j' : Fin 2, ‖G' i' j'‖ ≤ C_d / d ^ 3 :=
    fun i' j' => (hG_der hd_d i' j').choose_spec.2
  obtain ⟨G_inv', hInvDer, hInvBd⟩ :=
    hasDerivAt_gram_inv_entry (B := C_d / d ^ 3) (by positivity) h14 hder hbd i k
  refine ⟨G_inv', hInvDer, hInvBd.trans ?_⟩
  ring_nf
  rfl

/-- Conditional proof of `ComplCouplingHeat.PerGramInvHeatSplit κ` (`PartIII-a:T21/c5/3/1/2`) from
`SeedLamPJet2Decay κ` and `PerGramInvDerivDecay κ`. -/
theorem perGramInvHeatSplit_of (κ : PlanarFrameKernels)
    (hJet : SeedLamPJet2Decay κ) (hG : PerGramInvDerivDecay κ) :
    ComplCouplingHeat.PerGramInvHeatSplit κ := by
  intro hκ
  obtain ⟨hCD, C, -, h0, h1, h2⟩ := seedLamP_jet2_bounds_of κ hJet hκ
  obtain ⟨C_inv, D_inv, hC_inv0, hD_inv1, hG_der⟩ := hG hκ
  have ht : ∀ k : Fin 2,
      (∀ z : ℝ × ℝ, ‖κ.lamP k z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) :=
    fun k => translate_jet2_bounds (h0 k) (h1 k) (h2 k)
  refine ⟨C_inv / 2, D_inv, by positivity, hD_inv1, fun {ν r} hν hr hd i => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd1 : 1 ≤ d := le_trans hD_inv1 hd
  have hθ : 0 < clockTheta ν r := clockTheta_pos hν hr
  refine ⟨fun j => movGramInvDeriv κ ν r i j, fun j => ?_, fun y => ?_⟩
  · obtain ⟨G_inv', hGd, hGbd⟩ := hG_der hd i j
    have hle := norm_movGramInvDeriv_le_of_hasDerivAt κ hν hr hd1 i j hGd hGbd
    have hd2 : 1 ≤ d ^ 2 := by nlinarith
    refine hle.trans ?_
    calc (C_inv / 2) / (clockTheta ν r * d ^ 2)
        ≤ (C_inv / 2) / (clockTheta ν r * 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hd2 hθ.le)
      _ = C_inv / 2 * (1 / clockTheta ν r) := by ring
  · have hDiff : ∀ k : Fin 2,
        DifferentiableWithinAt ℝ
          (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
          (Ici r) r := by
      intro k
      obtain ⟨G_inv', hGd, -⟩ := hG_der hd i k
      exact (hasDerivAt_perGram_inv_comp_cellLen κ hν hr i k hGd).differentiableAt.differentiableWithinAt
    have hsplit := movLamDualHeat_eq_sum_of_diff κ hν hr hCD
      (fun k => (ht k).1) (fun k => (ht k).2.1) (fun k => (ht k).2.2) i hDiff y
    rw [hsplit, ← Finset.sum_add_distrib]
    rfl

/-- Conditional proof of `MovLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`) from
`SeedLamPJet2Decay κ` and `PerGramInvDerivDecay κ`. -/
theorem movLam0HeatDecomp_of (κ : PlanarFrameKernels)
    (hJet : SeedLamPJet2Decay κ) (hG : PerGramInvDerivDecay κ) :
    MovLam0HeatDecomp κ := by
  intro hκ m hm
  have hSharp : SeedLamPDSharpDecay κ := seedLamPDSharpDecay_of κ hJet
  obtain ⟨C_0, hC_0, hSharp_bd⟩ := movLam0DualHeat_memLp_and_xNorm_of_sharpDecay κ hSharp hκ hm
  obtain ⟨hCD, C, -, h0, h1, h2⟩ := seedLamP_jet2_bounds_of κ hJet hκ
  obtain ⟨C_inv, D_inv, hC_inv0, hD_inv1, hG_der⟩ := hG hκ
  have ht : ∀ k : Fin 2,
      (∀ z : ℝ × ℝ, ‖κ.lamP k z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (κ.lamP k) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) :=
    fun k => translate_jet2_bounds (h0 k) (h1 k) (h2 k)
  set C_0h : ℝ := max C_0 (C_inv / 2)
  refine ⟨C_0h, D_inv, le_trans hC_0 (le_max_left _ _), hD_inv1,
    fun ν hν r hr _hθ hd => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd1 : 1 ≤ d := le_trans hD_inv1 hd
  have hθ : 0 < clockTheta ν r := clockTheta_pos hν.1 hr
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  obtain ⟨hMem, hInt⟩ := hSharp_bd hν.1 hr hd1
  refine ⟨fun i y => ?_, fun k => ⟨(hMem k).1, ?_⟩, hInt, fun i k => ?_⟩
  · have hDiff : ∀ k : Fin 2,
        DifferentiableWithinAt ℝ
          (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i k)
          (Ici r) r := by
      intro k
      obtain ⟨G_inv', hGd, -⟩ := hG_der hd i k
      exact (hasDerivAt_perGram_inv_comp_cellLen κ hν.1 hr i k hGd).differentiableAt.differentiableWithinAt
    exact movLamDualHeat_eq_sum_of_diff κ hν.1 hr hCD
      (fun k => (ht k).1) (fun k => (ht k).2.1) (fun k => (ht k).2.2) i hDiff y
  · refine (hMem k).2.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_left _ _) hθ.le
  · obtain ⟨G_inv', hGd, hGbd⟩ := hG_der hd i k
    refine (norm_movGramInvDeriv_le_of_hasDerivAt κ hν.1 hr hd1 i k hGd hGbd).trans ?_
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

end DirectHeatDecomp

/-- Top-level alias for `DirectHeatDecomp.PerGramDerivDecay`. -/
abbrev PerGramDerivDecay (κ : PlanarFrameKernels) : Prop :=
  DirectHeatDecomp.PerGramDerivDecay κ

/-- Top-level alias for `DirectHeatDecomp.PerGramInvDerivDecay`. -/
abbrev PerGramInvDerivDecay (κ : PlanarFrameKernels) : Prop :=
  DirectHeatDecomp.PerGramInvDerivDecay κ

/-- Top-level proof that `PerGramDerivDecay κ` (`∂_d G = O(d⁻³)`) implies
`PerGramInvDerivDecay κ` (`∂_d (G⁻¹) = O(d⁻³)`). -/
theorem perGramInvDerivDecay_of_perGramDerivDecay (κ : PlanarFrameKernels)
    (hGd : PerGramDerivDecay κ) :
    PerGramInvDerivDecay κ :=
  DirectHeatDecomp.perGramInvDerivDecay_of_perGramDerivDecay κ hGd

/-- Top-level conditional proof of `MovLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`) from
`SeedLamPJet2Decay κ` and `PerGramInvDerivDecay κ`. -/
theorem movLam0HeatDecomp_of (κ : PlanarFrameKernels)
    (hJet : SeedLamPJet2Decay κ) (hG : PerGramInvDerivDecay κ) :
    MovLam0HeatDecomp κ :=
  DirectHeatDecomp.movLam0HeatDecomp_of κ hJet hG

/-- Top-level conditional proof of `MovLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`) from
`SeedLamPJet2Decay κ` and `PerGramDerivDecay κ` (`∂_d G = O(d⁻³)`). -/
theorem movLam0HeatDecomp_of_perGramDerivDecay (κ : PlanarFrameKernels)
    (hJet : SeedLamPJet2Decay κ) (hGd : PerGramDerivDecay κ) :
    MovLam0HeatDecomp κ :=
  DirectHeatDecomp.movLam0HeatDecomp_of κ hJet
    (DirectHeatDecomp.perGramInvDerivDecay_of_perGramDerivDecay κ hGd)

/-- **`PerGramDerivDecay κ`** (SP 2898-2902, `∂_d G = O(d⁻³)`): termwise differentiation of the
unfolded Gram series (`ComplCouplingHeat.hasDerivAt_perGram_and_bound`), with the `C²` regularity
and first-jet decay of `κ.lamP` supplied by `seedLamPJet2Decay_all`. -/
theorem perGramDerivDecay_proof (κ : PlanarFrameKernels) : PerGramDerivDecay κ := by
  intro hκ
  obtain ⟨hCD, C, -, -, h1, -⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨C_G, hCG, hG⟩ := ComplCouplingHeat.hasDerivAt_perGram_and_bound κ hCD h1
  refine ⟨C_G, 1, hCG, le_rfl, fun {d} hd i j => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  exact ⟨_, (hG hd0 i j).1, (hG hd0 i j).2⟩

/-- **`PartIII-a:T21/c5/2/1/1`** (SP 2905-2912, 2990-2997): the unnormalised heat/dilation
decomposition `MovLam0HeatDecomp κ`, from the seed jet decay `seedLamPJet2Decay_all` and the
Gram-derivative decay `perGramDerivDecay_proof`. -/
theorem movLam0HeatDecomp (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLam0HeatDecomp κ :=
  movLam0HeatDecomp_of_perGramDerivDecay κ (seedLamPJet2Decay_all κ) (perGramDerivDecay_proof κ)

end UnforcedLeray.Short.IIIa
