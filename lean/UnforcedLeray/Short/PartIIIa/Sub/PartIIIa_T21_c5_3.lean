import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly

/-!
# Part III-a, task `PartIII-a:T21/c5/3` decomposition (`Sub/PartIII-a_T21_c5_3.lean`, SP 2866-2918, 2990-2997, 3001-3004)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2918,
2990-2997, and 3001-3004 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Mathematical structure and proved reductions

For the periodized moving frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed
kernel `κ` (`IsSeedKernels κ`):

1. **Pullback of `physLamDual` and split into heat/dilation and Euler parts**:
   * `movLamDual κ tr r i = a(r)² * movingPhi ν (physLamDual κ tr · i) r` represents the moving-frame
     adjoint generator on `perLam κ d(r) i`, so that
     `movH0 κ tr r i W = ∫_{movingCell} movLamDual κ tr r i y * W y dy`
     (`movH0_eq_integral_movLamDual`).
   * Subtracting the planar seed eigenvalue `seedModeEigen lam i * perLam κ d(r) i` splits
     `movLamDualSub κ lam tr r i` into:
     - `movLamDualHeat κ ν r i`: the age-derivative and viscous/dilation part
       `a(r)² movingPhi(∂_r φ_i + ν Δ φ_i) = (θ(r)⁻¹ D^# + ∂_z)(perLam κ d(r) i)`, which by the
       dual periodization identity `θ⁻¹ D^#(P_d λ_i) + ∂_z(P_d λ_i) = θ⁻¹ P_d(D^# λ_i)` and the
       Gram-inverse derivative `(G⁻¹)_z = O(θ⁻¹ d⁻²)` is `O(θ(r)⁻¹)` in `X_{-m, d(r)}`
       (`MovLamDualHeatBound κ`, task `PartIII-a:T21/c5/3/1`).
     - `movLamDualEulerSub κ lam tr r i`: the linearised Euler adjoint minus the planar eigenvalue
       `a(r)² movingPhi(ladTransport - kerAdj) - λ_i perLam κ d(r) i`, which by planar seed
       duality `L_0^* λ_i = λ_i λ_i` combined with the Gram normalisation, cylinder Biot-Savart tail
       `O(d⁻²) = O(ν³ / θ(r))`, and rescaled BUC train comparison is `O(θ(r)⁻¹)` in `X_{-m, d(r)}`
       (`MovLamDualEulerSubBound κ`, task `PartIII-a:T21/c5/3/2`).

2. **Biorthogonality on the complement and weighted Cauchy-Schwarz (proved here)**:
   * `one_le_cellLen_of_theta` and `inv_cellLen_sq_eq_nu_cube_div_theta`: for `0 < ν ≤ 1`, `0 ≤ r`,
     and `1 ≤ clockTheta ν r`, the moving cell period satisfies `1 ≤ d(r)` and
     `1 / d(r)² = ν³ / clockTheta ν r`.
   * `memLp_movingW`, `memLp_compl`, and `integrableOn_perLam_mul`: along any `IsLinearisedFlow`,
     both `movingW ν w r` and `compl F w r` belong to `MemLp · 2 (B0579.cellMeasure d(r) m)`, and
     `perLam κ d(r) i * W` is integrable on `movingCell`.
   * `lam_pairing_compl_zero`: discharges the integrability hypotheses of
     `FrameAmplSub.lam_pairing_compl_eq_zero` to prove unconditionally that
     `∫_{movingCell} F.lam r i y * compl F w r y = 0` along any `IsLinearisedFlow`.
   * `xNorm_pairing_bound`: proves the `ℝ≥0∞` weighted Cauchy-Schwarz inequality
     `ENNReal.ofReal ‖∫_{cell d} G y * W y‖ ≤ xNorm d (-m) G * xNorm d m W`.
   * `movH0_compl_eq_sub` and `ofReal_norm_movH0_compl_le`: uses biorthogonality to replace
     `movLamDual` by `movLamDualSub = movLamDualHeat + movLamDualEulerSub` against `compl F w r`
     and bounds `ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖` by
     `(xNorm d (-m) movLamDualHeat + xNorm d (-m) movLamDualEulerSub) * xNorm d m (compl F w r)`.
   * `amplComplCoupling_of`: assembles `AmplComplCoupling κ` (`PartIII-a:T21/c5/3`) from
     `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`) and `MovLamDualEulerSubBound κ`
     (`PartIII-a:T21/c5/3/2`) with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Moving-frame dual generator and decomposition into heat/dilation and Euler parts -/

/-- Moving-variable dual generator `a(r)² * movingPhi ν (physLamDual κ tr · i) r` (SP 2905-2918). -/
def movLamDual (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' => physLamDual κ tr r' i) r y

/-- Physical-variable time-derivative + viscous Laplacian part of `physLamDual` (SP 2905-2912). -/
def physLamDualHeat (κ : PlanarFrameKernels) (ν r : ℝ) (i : Fin 2) (x : ℝ × ℝ) : ℂ :=
  ladDt (fun r' x' => physFrameLam κ ν r' i x') r x +
    (ν : ℂ) * ladLapCx (physFrameLam κ ν r i) x

/-- Physical-variable linearised Euler (drift + nonlocal Biot-Savart) part of `physLamDual`
(SP 2905-2918). -/
def physLamDualEuler (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  ladTransport tr r (physFrameLam κ ν r i) x -
    kerAdj (ν ^ (-2 : ℝ)) (fun k y => physFrameLam κ ν r i y *
      (B0579.pd k (UnforcedLeray.B0238.Ec tr r) y : ℂ)) x

/-- Eigenvalue `λ_i` associated with a complex planar seed eigenvalue `lam`: `lam` for `i = 0`,
`conj lam` for `i = 1` (SP 2891-2897). -/
def seedModeEigen (lam : ℂ) (i : Fin 2) : ℂ :=
  if i = 0 then lam else starRingEnd ℂ lam

/-- Moving-variable heat/dilation + age-derivative part of `movLamDual`:
`a(r)² * movingPhi ν (physLamDualHeat κ ν · i) r = (θ(r)⁻¹ D^# + ∂_z)(perLam κ d(r) i)`
(SP 2905-2912, 2990-2997). -/
def movLamDualHeat (κ : PlanarFrameKernels) (ν r : ℝ) (i : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' => physLamDualHeat κ ν r' i) r y

/-- Moving-variable linearised Euler adjoint minus the planar seed eigenvalue:
`a(r)² * movingPhi ν (physLamDualEuler κ tr · i) r - λ_i * perLam κ d(r) i`
(SP 2905-2918, 2990-2997). -/
def movLamDualEulerSub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y -
    seedModeEigen lam i * perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y

/-- Full eigenvalue-subtracted moving-variable dual generator
`movLamDual κ tr r i y - λ_i * perLam κ d(r) i y` (SP 2990-2997). -/
def movLamDualSub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movLamDual κ tr r i y -
    seedModeEigen lam i * perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y

/-! ## Analytical leaf specifications for `AmplComplCoupling` (`PartIII-a:T21/c5/3`) -/

/-- **Leaf 1 (`PartIII-a:T21/c5/3/1`, `MovLamDualHeatBound`, SP 2905-2912, 2990-2997)**:
By the dual periodization identity `θ⁻¹ D^#(P_d λ_i) + ∂_z(P_d λ_i) = θ⁻¹ P_d(D^# λ_i)` and the
Gram-inverse derivative bound `(G⁻¹)_z = O(θ⁻¹ d⁻²)`, the heat/dilation + age-derivative part
`movLamDualHeat κ ν r i` belongs to `X_{-m, d(r)}` and is bounded by `C_h / clockTheta ν r`.
Composed by task `PartIII-a:T21/c5/3` via `amplComplCoupling_of`. -/
def MovLamDualHeatBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ C_h b_h : ℝ, 0 ≤ C_h ∧ 1 ≤ b_h ∧
    ∀ b : ℝ, b_h ≤ b →
      ∃ ν_h : ℝ, 0 < ν_h ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_h →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ i : Fin 2,
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) ∧
          xNorm d (-m) (movLamDualHeat κ ν r i) ≤
            ENNReal.ofReal (C_h * (1 / clockTheta ν r))

/-- **Leaf 2 (`PartIII-a:T21/c5/3/2`, `MovLamDualEulerSubBound`, SP 2866-2889, 2905-2918, 2990-2997)**:
For the Part I seed eigenvalue `lam`, after subtracting `seedModeEigen lam i * perLam κ d(r) i`,
the linearised Euler adjoint `movLamDualEulerSub κ lam tr r i` (combining the planar seed duality
cancellation `L_0^* λ_i = λ_i λ_i`, the Gram-inverse error `G⁻¹ - I = O(d⁻²)`, the cylinder
Biot-Savart tail `O(d⁻²) = O(ν³ / θ(r))`, and the rescaled BUC train error) belongs to
`X_{-m, d(r)}` and is bounded by `C_e / clockTheta ν r`.
Composed by task `PartIII-a:T21/c5/3` via `amplComplCoupling_of`. -/
def MovLamDualEulerSubBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ lam : ℂ, ∃ C_e b_e : ℝ, 0 ≤ C_e ∧ 1 ≤ b_e ∧
    ∀ b : ℝ, b_e ≤ b →
      ∃ ν_e : ℝ, 0 < ν_e ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_e →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ i : Fin 2,
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          MemLp (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) ∧
          xNorm d (-m) (movLamDualEulerSub κ lam tr r i) ≤
            ENNReal.ofReal (C_e * (1 / clockTheta ν r))

namespace ComplCouplingSub

/-! ## Algebraic identities for `movH0` and `movLamDual` -/

theorem physLamDual_eq_heat_add_euler (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) :
    physLamDual κ tr r i x = physLamDualHeat κ ν r i x + physLamDualEuler κ tr r i x := by
  unfold physLamDual physLamDualHeat physLamDualEuler
  ring

theorem movLamDual_eq_heat_add_euler (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (y : ℝ × ℝ) :
    movLamDual κ tr r i y =
      movLamDualHeat κ ν r i y +
        (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
          movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y := by
  unfold movLamDual movLamDualHeat movingPhi
  dsimp only
  rw [physLamDual_eq_heat_add_euler]
  ring

theorem movLamDualSub_eq_add (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (y : ℝ × ℝ) :
    movLamDualSub κ lam tr r i y =
      movLamDualHeat κ ν r i y + movLamDualEulerSub κ lam tr r i y := by
  unfold movLamDualSub movLamDualEulerSub
  rw [movLamDual_eq_heat_add_euler]
  ring

theorem movH0_eq_integral_movLamDual (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (W : ℝ × ℝ → ℂ) :
    movH0 κ tr r i W =
      ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, movLamDual κ tr r i y * W y := by
  unfold movH0 movLamDual
  simp_rw [mul_assoc]
  rw [integral_const_mul]

/-! ## Cell-length and clock scaling identities -/

/-- Exact identity `1 / d(r)² = ν³ / clockTheta ν r` for `d(r) = ν⁻² / √a(r)` (SP 2896, 2992). -/
theorem inv_cellLen_sq_eq_nu_cube_div_theta {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    1 / (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2 = ν ^ 3 / clockTheta ν r := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hν_ne : ν ≠ 0 := hν.ne'
  have hrpow : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [← Real.rpow_natCast (ν ^ (-2 : ℝ)) 2, ← Real.rpow_mul hν.le]
    have : (-2 : ℝ) * ((2 : ℕ) : ℝ) = -((4 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hν.le, Real.rpow_natCast]
  unfold cellLen clockTheta
  rw [div_pow, Real.sq_sqrt ha0.le, hrpow]
  field_simp [ha0.ne', hν_ne]

/-- For `0 < ν ≤ 1`, `0 ≤ r`, and `1 ≤ clockTheta ν r`, the moving cell length satisfies
`1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`. -/
theorem one_le_cellLen_of_theta {ν r : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hr : 0 ≤ r) (hθ : 1 ≤ clockTheta ν r) :
    1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  have hinv_sq : 1 / (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2 ≤ 1 := by
    rw [inv_cellLen_sq_eq_nu_cube_div_theta hν hr]
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hθ)).2 (hν3.trans hθ)
  have hsq : 1 ≤ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2 := by
    have hpos2 : 0 < (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2 := sq_pos_of_pos hd_pos
    exact (div_le_one hpos2).1 hinv_sq
  nlinarith

/-! ## Weighted Cauchy-Schwarz on `B0579.cell d` in `ℝ≥0∞` -/

lemma enorm_ofReal_cx (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

lemma eLpNorm_cellMeasure_cx (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    eLpNorm f 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x) 2
        (volume.restrict (B0579.cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [enorm_ofReal_cx, mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0,
    ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

lemma memLp_scaled {c m : ℝ} {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F x) 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hF.1.mono_ac (B0579.ac_cellMeasure c m))
    exact (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)).aestronglyMeasurable
  · rw [← eLpNorm_cellMeasure_cx]; exact hF.2

/-- Weighted Cauchy-Schwarz on `B0579.cell d` in `ℝ≥0∞`:
`ENNReal.ofReal ‖∫_{cell d} G y * W y‖ ≤ xNorm d (-m) G * xNorm d m W`. -/
theorem xNorm_pairing_bound {d m : ℝ} {G W : ℝ × ℝ → ℂ}
    (hG : MemLp G 2 (B0579.cellMeasure d (-m)))
    (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun y => G y * W y) (B0579.cell d) ∧
      ENNReal.ofReal ‖∫ y in B0579.cell d, G y * W y‖ ≤
        xNorm d (-m) G * xNorm d m W := by
  have hA := memLp_scaled hG
  have hB := memLp_scaled hW
  have hprod : (fun y => (((B0579.jb y ^ (-m / 2) : ℝ) : ℂ) * G y) *
      (((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y)) = fun y => G y * W y := by
    funext y
    have : ((B0579.jb y ^ (-m / 2) : ℝ) : ℂ) * ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, B0579.jb_rpow_mul]
      have : -m / 2 + m / 2 = 0 := by ring
      rw [this, Real.rpow_zero]; simp
    calc _ = (((B0579.jb y ^ (-m / 2) : ℝ) : ℂ) * ((B0579.jb y ^ (m / 2) : ℝ) : ℂ)) *
          (G y * W y) := by ring
      _ = _ := by rw [this, one_mul]
  have hI : Integrable (fun y => G y * W y) (volume.restrict (B0579.cell d)) := by
    rw [← hprod]; exact hA.integrable_mul hB
  refine ⟨hI, ?_⟩
  have h1 : eLpNorm (fun y => G y * W y) 1 (volume.restrict (B0579.cell d)) ≤
      eLpNorm G 2 (B0579.cellMeasure d (-m)) * eLpNorm W 2 (B0579.cellMeasure d m) := by
    rw [eLpNorm_cellMeasure_cx, eLpNorm_cellMeasure_cx, ← hprod]
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hB.1 hA.1
      (μ := volume.restrict (B0579.cell d)) (φ := fun y => ((B0579.jb y ^ (-m / 2) : ℝ) : ℂ) * G y)
  unfold xNorm
  rw [ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact h1

/-! ## `MemLp` of `movingW` and `compl`, and unconditional biorthogonality on `compl` -/

theorem memLp_JscaleInv {c m a : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    MemLp (JscaleInv a g) 2 (B0579.cellMeasure (cellLen c a) m) := by
  obtain ⟨h, hmeas, hgh, _hnorm⟩ := ae_representative_xNorm c m g hg
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hJh_meas : Measurable (JscaleInv a h) := by
    unfold JscaleInv
    exact measurable_const.mul
      (hmeas.comp ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  have hgh' : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), g x = h x :=
    (B0579.ac_cellMeasure c m).ae_le hgh
  have hae := jscale_ae_of_ae c a ha0 g h hgh'
  have hae2 : JscaleInv a g =ᵐ[B0579.cellMeasure (cellLen c a) m] JscaleInv a h :=
    (B0579.cellMeasure_ac (cellLen c a) m).ae_le hae
  refine ⟨hJh_meas.aestronglyMeasurable.congr (EventuallyEq.symm hae2), ?_⟩
  have hle := xNorm_JscaleInv_le c m a hm ha g hg
  unfold xNorm at hle
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2)

theorem memLp_movingW {ν c m t r : ℝ} (hm : 0 ≤ m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r)
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    MemLp (movingW ν w r) 2 (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
  memLp_JscaleInv hm (one_le_clockA hν.le (ht.trans htr)) (hw.memX r htr)

theorem memLp_frame_E {ν c m b K r : ℝ} (F : MovingFrame ν c m b K)
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (j : Fin 2) :
    MemLp (F.E r j) 2 (B0579.cellMeasure (cellLen c (clockA ν r)) m) := by
  refine ⟨(F.E_meas r hr hbr j).mono_ac (B0579.cellMeasure_ac _ m), ?_⟩
  have hbdd := F.E_bdd r hr hbr j
  unfold xNorm at hbdd
  exact lt_of_le_of_lt hbdd ENNReal.ofReal_lt_top

theorem memLp_compl {ν c m b K t r : ℝ} (F : MovingFrame ν c m b K)
    (hm : 0 ≤ m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r) (hbr : b ≤ clockTheta ν r)
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    MemLp (compl F w r) 2 (B0579.cellMeasure (cellLen c (clockA ν r)) m) := by
  have hW := memLp_movingW hm hν ht htr hw
  have hE0 : MemLp (fun y => ampl F w r 0 * F.E r 0 y) 2
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
    (memLp_frame_E F (ht.trans htr) hbr 0).const_mul (ampl F w r 0)
  have hE1 : MemLp (fun y => ampl F w r 1 * F.E r 1 y) 2
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
    (memLp_frame_E F (ht.trans htr) hbr 1).const_mul (ampl F w r 1)
  have heq : compl F w r =
      fun y => movingW ν w r y - (ampl F w r 0 * F.E r 0 y + ampl F w r 1 * F.E r 1 y) := by
    funext y
    unfold compl
    simp [Fin.sum_univ_two]
  rw [heq]
  exact hW.sub (hE0.add hE1)

/-- For `8 < m`, `1 ≤ d`, and `W ∈ MemLp · 2 (B0579.cellMeasure d m)`, `perLam κ d i * W` is
integrable on `B0579.cell d`. -/
theorem integrableOn_perLam_mul (κ : PlanarFrameKernels) {d m : ℝ}
    (hm : 8 < m) (hd : 1 ≤ d) (i : Fin 2) {W : ℝ × ℝ → ℂ}
    (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun y => perLam κ d i y * W y) (B0579.cell d) := by
  obtain ⟨K_0, hK_0⟩ := Lam0B.perLam0BoundM κ m hm
  have hW_meas : AEStronglyMeasurable W (volume.restrict (B0579.cell d)) :=
    hW.1.mono_ac (B0579.ac_cellMeasure d m)
  have hW_fin : xNorm d m W ≠ ∞ := hW.2.ne
  have h0 : IntegrableOn (fun y => perLam0 κ d 0 y * W y) (B0579.cell d) :=
    (hK_0 d hd 0 W hW_meas hW_fin).1
  have h1 : IntegrableOn (fun y => perLam0 κ d 1 y * W y) (B0579.cell d) :=
    (hK_0 d hd 1 W hW_meas hW_fin).1
  have heq : (fun y => perLam κ d i y * W y) =
      fun y => (perGram κ d)⁻¹ i 0 * (perLam0 κ d 0 y * W y) +
        (perGram κ d)⁻¹ i 1 * (perLam0 κ d 1 y * W y) := by
    funext y
    unfold perLam
    simp only [Fin.sum_univ_two]
    ring
  rw [heq]
  exact (h0.const_mul _).add (h1.const_mul _)

/-- Unconditional biorthogonality `<F.lam r i, compl F w r> = 0` along any `IsLinearisedFlow`
when `1 ≤ d(r)`. -/
theorem lam_pairing_compl_zero (κ : PlanarFrameKernels) {ν m b K t r : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r)
    (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2) :
    let F := periodizedFrame κ ν m b K hν hF
    (∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, F.lam r i y * compl F w r y) = 0 := by
  intro F
  have hm0 : 0 ≤ m := by linarith
  have hW_mem := memLp_movingW hm0 hν ht htr hw
  have hW_int : IntegrableOn (fun y => F.lam r i y * movingW ν w r y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    integrableOn_perLam_mul κ hm hd i hW_mem
  have hE_int : ∀ j : Fin 2, IntegrableOn (fun y => F.lam r i y * F.E r j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) := fun j =>
    integrableOn_perLam_mul κ hm hd i (memLp_frame_E F (ht.trans htr) hbr j)
  exact FrameAmplSub.lam_pairing_compl_eq_zero F (ht.trans htr) hbr w i hW_int hE_int

/-! ## Eigenvalue cancellation on the complement and Cauchy-Schwarz bound for `movH0` -/

/-- Because `compl F w r` is orthogonal to `F.lam r i = perLam κ d(r) i`, `movH0 κ tr r i (compl F w r)`
equals the cell pairing of `movLamDualSub κ lam tr r i` with `compl F w r`. -/
theorem movH0_compl_eq_sub (κ : PlanarFrameKernels) (lam : ℂ) {ν m b K t r : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r)
    (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2)
    (hSub_mem : MemLp (movLamDualSub κ lam tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    let F := periodizedFrame κ ν m b K hν hF
    movH0 κ tr r i (compl F w r) =
      ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
        movLamDualSub κ lam tr r i y * compl F w r y := by
  intro F
  have hm0 : 0 ≤ m := by linarith
  have hcompl_mem := memLp_compl F hm0 hν ht htr hbr hw
  have hSub_int : IntegrableOn (fun y => movLamDualSub κ lam tr r i y * compl F w r y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    (xNorm_pairing_bound hSub_mem hcompl_mem).1
  have hLam_int : IntegrableOn
      (fun y => seedModeEigen lam i * (F.lam r i y * compl F w r y))
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    (integrableOn_perLam_mul κ hm hd i hcompl_mem).const_mul (seedModeEigen lam i)
  have hzero := lam_pairing_compl_zero κ hm hν ht htr hbr hd hF hw i
  have heq : (fun y => movLamDual κ tr r i y * compl F w r y) =
      fun y => movLamDualSub κ lam tr r i y * compl F w r y +
        seedModeEigen lam i * (F.lam r i y * compl F w r y) := by
    funext y
    change movLamDual κ tr r i y * compl F w r y =
      (movLamDual κ tr r i y - seedModeEigen lam i * F.lam r i y) * compl F w r y +
        seedModeEigen lam i * (F.lam r i y * compl F w r y)
    ring
  rw [movH0_eq_integral_movLamDual, heq, integral_add hSub_int hLam_int,
    integral_const_mul, hzero, mul_zero, add_zero]

/-- Pointwise mode-`i` bound on `ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖` from the `X_{-m, d}`
bounds on `movLamDualHeat` and `movLamDualEulerSub`. -/
theorem ofReal_norm_movH0_compl_le (κ : PlanarFrameKernels) (lam : ℂ) {ν m b K t r : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r)
    (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ lam tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    let F := periodizedFrame κ ν m b K hν hF
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖ ≤
      (xNorm d (-m) (movLamDualHeat κ ν r i) + xNorm d (-m) (movLamDualEulerSub κ lam tr r i)) *
        xNorm d m (compl F w r) := by
  intro F d
  have hm0 : 0 ≤ m := by linarith
  have hcompl_mem := memLp_compl F hm0 hν ht htr hbr hw
  have hSub_eq : movLamDualSub κ lam tr r i =
      movLamDualHeat κ ν r i + movLamDualEulerSub κ lam tr r i := by
    funext y
    exact movLamDualSub_eq_add κ lam tr r i y
  have hSub_mem : MemLp (movLamDualSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) := by
    rw [hSub_eq]
    exact hHeat_mem.add hEuler_mem
  rw [movH0_compl_eq_sub κ lam hm hν ht htr hbr hd hF hw i hSub_mem]
  have hcs := (xNorm_pairing_bound hSub_mem hcompl_mem).2
  have htri : xNorm d (-m) (movLamDualSub κ lam tr r i) ≤
      xNorm d (-m) (movLamDualHeat κ ν r i) + xNorm d (-m) (movLamDualEulerSub κ lam tr r i) := by
    unfold xNorm
    rw [hSub_eq]
    exact eLpNorm_add_le hHeat_mem.1 hEuler_mem.1 (by norm_num)
  exact hcs.trans (mul_le_mul_of_nonneg_right htri zero_le)

end ComplCouplingSub

/-! ## Conditional assembly of `AmplComplCoupling` (`PartIII-a:T21/c5/3`) -/

open ComplCouplingSub in
/-- Conditional proof of `AmplComplCoupling κ` (`PartIII-a:T21/c5/3`) from the moving-frame dual
generator bounds `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`) and
`MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`). -/
theorem amplComplCoupling_of (κ : PlanarFrameKernels)
    (hHeat : MovLamDualHeatBound κ) (hEuler : MovLamDualEulerSubBound κ) :
    AmplComplCoupling κ := by
  intro hκ m hm K
  obtain ⟨C_h, b_h, hCh, hbh, Hb_h⟩ := hHeat hκ m hm
  obtain ⟨lam, C_e, b_e, hCe, hbe, Hb_e⟩ := hEuler hκ m hm
  refine ⟨2 * (C_h + C_e), max b_h b_e, by positivity, le_trans hbh (le_max_left _ _), ?_⟩
  intro b hb
  obtain ⟨ν_h, hν_h, Hν_h⟩ := Hb_h b (le_trans (le_max_left _ _) hb)
  obtain ⟨ν_e, hν_e, Hν_e⟩ := Hb_e b (le_trans (le_max_right _ _) hb)
  refine ⟨min (min ν_h ν_e) 1, by positivity, ?_⟩
  intro ν hν hF tr htr t s ht _hts hbs f w u hw _hcirc r hr
  have hν0 : 0 < ν := hν.1
  have hν_le_h : ν ≤ ν_h := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hν_le_e : ν ≤ ν_e := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν_le_1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hr0 : 0 ≤ r := ht.trans hr.1.le
  have hbr : b ≤ clockTheta ν r :=
    hbs.trans (theta_anti hν0 hr0 hr.2)
  have hb1 : 1 ≤ b := le_trans hbh (le_trans (le_max_left _ _) hb)
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    one_le_cellLen_of_theta hν0 hν_le_1 hr0 (hb1.trans hbr)
  have hθ_pos : 0 < clockTheta ν r := theta_pos hν0 hr0
  set F := periodizedFrame κ ν m b K hν0 hF
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  set α := ENNReal.ofReal ((C_h + C_e) * (1 / clockTheta ν r))
  have hmode : ∀ i : Fin 2,
      ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖ ≤ α * xNorm d m (compl F w r) := by
    intro i
    obtain ⟨hHm, hHb⟩ := Hν_h ν ⟨hν0, hν_le_h⟩ r hr0 hbr i
    obtain ⟨hEm, hEb⟩ := Hν_e ν ⟨hν0, hν_le_e⟩ tr htr r hr0 hbr i
    have h1 := ofReal_norm_movH0_compl_le κ lam hm hν0 ht hr.1.le hbr hd hF hw i hHm hEm
    have hsum_le : xNorm d (-m) (movLamDualHeat κ ν r i) +
        xNorm d (-m) (movLamDualEulerSub κ lam tr r i) ≤ α := by
      calc xNorm d (-m) (movLamDualHeat κ ν r i) +
            xNorm d (-m) (movLamDualEulerSub κ lam tr r i)
          ≤ ENNReal.ofReal (C_h * (1 / clockTheta ν r)) +
              ENNReal.ofReal (C_e * (1 / clockTheta ν r)) := add_le_add hHb hEb
        _ = α := by
            dsimp only [α]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    exact h1.trans (mul_le_mul_of_nonneg_right hsum_le zero_le)
  rw [Fin.sum_univ_two]
  have htwo : α + α = ENNReal.ofReal (2 * (C_h + C_e) * (1 / clockTheta ν r)) := by
    dsimp only [α]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  calc ENNReal.ofReal ‖movH0 κ tr r 0 (compl F w r)‖ +
        ENNReal.ofReal ‖movH0 κ tr r 1 (compl F w r)‖
      ≤ α * xNorm d m (compl F w r) + α * xNorm d m (compl F w r) :=
        add_le_add (hmode 0) (hmode 1)
    _ = (α + α) * xNorm d m (compl F w r) := (add_mul α α _).symm
    _ = ENNReal.ofReal (2 * (C_h + C_e) * (1 / clockTheta ν r)) * xNorm d m (compl F w r) := by
        rw [htwo]

end UnforcedLeray.Short.IIIa

end
