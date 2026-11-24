import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.CompactComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.AbsoluteStress
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.AbsoluteStress.Impulse
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Mellin
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.TestedImpulse
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2.Scale
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import UnforcedLeray.Units.B0151.OneDim

/-!
# Part III-a, `PartIII-a:T22/7`: Stress defect and anisotropy (`eq:ct-stress-defect`, `eq:ct-anisotropy`)

Source of record: `the November 2 reference manuscript` (SP), lines 3380-3404.

Proves `ctAnisotropyPair : CTStressDefect ∧ CTAnisotropy` and its projections `ctStressDefect`
and `ctAnisotropy`:
1. **Symmetrization, `sAbs` domination, right-continuity, and `IntegrableOn` on `(u_o, ∞)`**:
   Averaging any linearised flow `(w, u)` from `preparedDatum P ν` with its central reflection
   produces a centrally even linearised flow `(w_ev, u_odd)` with identical `pairEta`, `pairQ`,
   `pairC`, `quadQ`, `aPlus`, and `iA`. Right-continuity in `s` together with `ctAbsoluteStress`
   (`k = 0`) yields Bochner integrability of all weighted stress pairings on `Ioi (onsetAge ν)`.
2. **Planar angular-two cancellation**:
   On `ℝ² ≃ ℂ`, `planarMode f` transforms in angular sector `+2` under `rotation u` (`u : Circle`).
   Decomposing `v₀` and `K_∞ (planarMode f)` into `±` complex components transforms the pairwise
   products by `u²` and `u⁴`, whose integrals vanish by invariance of Lebesgue measure under
   rotations by `π/2` and `π/4`, giving `D_plan = 0` and `R_plan = 0`.
3. **Compact clock window `[s_B, s_r]` (`0 < r < B`)**:
   Replacing `tr.v s` by `Train.Vc` (`TrainComparison`), rescaling to `B0579.cell d(θ)`, replacing
   `Train.datum d` by `Train.v0` (`datum_tail_g`), replacing `U_Z` by `kerVelCx d V_d`
   (`ctCompactComparison`), and comparing cylinder vs. planar Biot-Savart velocities (`vel_compare`
   on `|y| ≤ d/8` and `canonicalGaussAndJetBound_proof` + `norm_biotSavart_le` on `|y| > d/8`)
   reduces `D_c - 3 R_c` on `[s_B, s_r]` to `o_K(𝒜_ν)` as `ν → 0⁺`.
4. **Three-way split for `CTStressDefect`**:
   Combining the core tail `(u_o, s_B]` (`O(e^{-(γ/2) B} 𝒜_ν)` uniformly in `B`), the small-clock
   impulse tail `(s_r, ∞)` (`O_B(r 𝒜_ν)` via restart + `T22Sub.ctAbsoluteImpulse` at `k = 0`),
   and the compact window `(s_B, s_r]` establishes `CTStressDefect`.
5. **Unforced quadrupole law, Fubini integration by parts, and `CTAnisotropy`**:
   Testing `hw_ev.weak` against `η² χ₀((n+1)⁻¹ η)` gives `(d/ds) Q_c(w_ev) = -(4/π) ∫(v₁ u₂ + v₂ u₁)`.
   Integrating against `(μ + 3/2) s^{-μ-5/2}` on `Ioc u_o T` via `integral_prod_symm` and passing
   to `T → ∞` by dominated convergence (`ctMellin` + `ctAbsoluteStress`) yields
   `∫_{u_o}^∞ C(s) s^{-3/2} ds = (μ + 3/2) I_A - A_+(u_o) u_o^{-3/2}`, which combines with
   `2 E_q - E_η = -(D_c - 3 R_c) + 3 i C` and `CTStressDefect` to prove `CTAnisotropy`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.Short.IIIa.AnisoSynthAux

open UnforcedLeray.Short.IIIa

lemma memLp_vol_of_cellMeasure {c m : ℝ} (hm : 0 ≤ m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    MemLp f 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨hf.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m), ?_⟩
  rw [CTE.QuadQBoundProof.eLpNorm_two_eq]
  have hle : ∫⁻ x in B0579.cell c, ‖f x‖ₑ ^ 2 ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure c m) := by
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    refine lintegral_mono fun x => ?_
    have hjb1 : 1 ≤ B0579.jb x := by
      unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hrp : 1 ≤ B0579.jb x ^ m := Real.one_le_rpow hjb1 hm
    calc ‖f x‖ₑ ^ 2 = ENNReal.ofReal 1 * ‖f x‖ₑ ^ 2 := by rw [ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (B0579.jb x ^ m) * ‖f x‖ₑ ^ 2 :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hrp) bot_le
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure c m)) ^ (1 / 2 : ℝ) < ⊤ := by
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    exact hf.2
  exact lt_of_le_of_lt (ENNReal.rpow_le_rpow hle (by positivity)) hfin

lemma integrableOn_cell_of_memX {c m : ℝ} (hm : 1 < m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    IntegrableOn f (B0579.cell c) :=
  zcCellIntegrable c m hm f hf

lemma integrable_eta_sq_of_memX (m : ℝ) (hm : 8 < m) (d : ℝ) (g : ℝ × ℝ → ℂ)
    (hg : MemLp g 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (B0579.cell d) := by
  have hm3 : 3 < m := by linarith
  have hg_aesm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)) :=
    hg.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d m)
  have hmeas_eta : Continuous (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_snd.pow 2)
  refine ⟨hmeas_eta.aestronglyMeasurable.mul hg_aesm, ?_⟩
  show ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ) * g x‖ₑ < ⊤
  simp_rw [enorm_mul]
  rw [CTE.QuadQBoundProof.lintegral_cell_eq d m]
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ *
      ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) (B0579.cellMeasure d m) := by
    apply Measurable.aemeasurable
    exact ((B0579.continuous_jb_rpow m).measurable.ennreal_ofReal.inv).mul
      hmeas_eta.measurable.enorm
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure d m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hg.aestronglyMeasurable.enorm
  simp only [ENNReal.rpow_two] at hCS
  have hstep : ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * (‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖g x‖ₑ)
      ∂(B0579.cellMeasure d m) ≤
      (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
        xNorm d m g := by
    refine (le_of_eq (lintegral_congr fun x => by simp only [Pi.mul_apply, mul_assoc])).trans
      (hCS.trans ?_)
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    refine mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) bot_le
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    exact (lintegral_mono fun x => CTE.QuadQBoundProof.density_mul_sq_le m hm3 x).trans
      (setLIntegral_le_lintegral _ _)
  refine hstep.trans_lt (ENNReal.mul_lt_top ?_ hg.2)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (CTE.QuadQBoundProof.integrable_moment m hm3).lintegral_lt_top.ne

lemma exists_isBiotSavart_of_memX {m d : ℝ} (hm : 8 < m) (hd : 1 ≤ d)
    (f : ℝ × ℝ → ℂ) (hf : MemLp f 2 (B0579.cellMeasure d m))
    (hz : HasZeroCirculation d f) (hev : IsCentrallyEven f) :
    ∃ u : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart d f u := by
  obtain ⟨C, hC⟩ := CTE.biotSavart_exists_uniform m hm
  obtain ⟨u, hu, _⟩ := hC d hd f hf hz hev
  exact ⟨u, hu⟩

/-! ## 1. `sAbs` domination, flow symmetrization, right-continuity, and `IntegrableOn` -/

def symTensorAniso {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (μ : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) (i j : Fin 2) (x : ℝ × ℝ) : ℂ :=
  ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
    ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)

lemma pairEta_eq_symTensor {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    pairEta tr μ u s = (((ν ^ (-2 : ℝ))⁻¹ : ℝ) : ℂ) *
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), symTensorAniso tr μ u s 0 0 x := by
  have _ := hν
  have hpt : (fun x => symTensorAniso tr μ u s 0 0 x) =
      fun x => (2 : ℂ) * (((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0)) := by
    funext x; unfold symTensorAniso; ring
  unfold pairEta
  rw [hpt, integral_const_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma pairQ_eq_symTensor {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    pairQ tr μ u s = (((ν ^ (-2 : ℝ))⁻¹ : ℝ) : ℂ) *
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), symTensorAniso tr μ u s 1 1 x := by
  have _ := hν
  have hpt : (fun x => symTensorAniso tr μ u s 1 1 x) =
      fun x => (2 : ℂ) * (((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1)) := by
    funext x; unfold symTensorAniso; ring
  unfold pairQ
  rw [hpt, integral_const_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma pairC_eq_symTensor {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    pairC tr μ u s = (((ν ^ (-2 : ℝ))⁻¹ : ℝ) : ℂ) *
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), symTensorAniso tr μ u s 0 1 x := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hν _).ne'
  have hpt : (fun x => symTensorAniso tr μ u s 0 1 x) =
      fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1) +
        ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0) := by
    funext x; unfold symTensorAniso; ring
  unfold pairC
  rw [hpt, Complex.ofReal_inv, one_div]

lemma norm_symTensor_le_frob {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) (i j : Fin 2) (x : ℝ × ℝ) :
    ‖symTensorAniso tr μ u s i j x‖ ≤
      Real.sqrt (∑ a : Fin 2, ∑ b : Fin 2, ‖symTensorAniso tr μ u s a b x‖ ^ 2) := by
  have h1 : ‖symTensorAniso tr μ u s i j x‖ ^ 2 ≤
      ∑ b : Fin 2, ‖symTensorAniso tr μ u s i b x‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖symTensorAniso tr μ u s i b x‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ b : Fin 2, ‖symTensorAniso tr μ u s i b x‖ ^ 2 ≤
      ∑ a : Fin 2, ∑ b : Fin 2, ‖symTensorAniso tr μ u s a b x‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b : Fin 2, ‖symTensorAniso tr μ u s a b x‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖symTensorAniso tr μ u s i j x‖
      = Real.sqrt (‖symTensorAniso tr μ u s i j x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ a : Fin 2, ∑ b : Fin 2, ‖symTensorAniso tr μ u s a b x‖ ^ 2) :=
        Real.sqrt_le_sqrt (h1.trans h2)

lemma enorm_symTensor_integral_le_sAbs {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) (i j : Fin 2) :
    ‖(((ν ^ (-2 : ℝ))⁻¹ : ℝ) : ℂ) *
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), symTensorAniso tr μ u s i j x‖ₑ ≤
      sAbs tr μ u s := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  have hcinv : ‖((c⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal c⁻¹ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hc_pos.le)]
  calc ‖((c⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell c, symTensorAniso tr μ u s i j x‖ₑ
      = ENNReal.ofReal c⁻¹ * ‖∫ x in B0579.cell c, symTensorAniso tr μ u s i j x‖ₑ := by
        rw [enorm_mul, hcinv]
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ‖symTensorAniso tr μ u s i j x‖ₑ :=
        mul_le_mul_of_nonneg_left (enorm_integral_le_lintegral_enorm _) bot_le
    _ = ∫⁻ x in B0579.cell c, ENNReal.ofReal c⁻¹ * ‖symTensorAniso tr μ u s i j x‖ₑ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ sAbs tr μ u s := by
        unfold sAbs
        refine lintegral_mono fun x => mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_symTensor_le_frob tr μ u s i j x)

lemma enorm_pairs_le_sAbs {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    ‖pairEta tr μ u s‖ₑ ≤ sAbs tr μ u s ∧
      ‖pairQ tr μ u s‖ₑ ≤ sAbs tr μ u s ∧
      ‖pairC tr μ u s‖ₑ ≤ sAbs tr μ u s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairEta_eq_symTensor hν]; exact enorm_symTensor_integral_le_sAbs hν tr μ u s 0 0
  · rw [pairQ_eq_symTensor hν]; exact enorm_symTensor_integral_le_sAbs hν tr μ u s 1 1
  · rw [pairC_eq_symTensor hν]; exact enorm_symTensor_integral_le_sAbs hν tr μ u s 0 1

lemma enorm_stressDefect_le_sAbs {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖((pairEta tr μ u s + pairQ tr μ u s) -
        3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s)) *
          ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ₑ ≤
      6 * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ u s) := by
  obtain ⟨hE, hQ, hC⟩ := enorm_pairs_le_sAbs hν tr μ u s
  have hrew : (pairEta tr μ u s + pairQ tr μ u s) -
      3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s) =
      pairEta tr μ u s - 2 * pairQ tr μ u s + 3 * (Complex.I * pairC tr μ u s) := by ring
  have htri : ‖(pairEta tr μ u s + pairQ tr μ u s) -
      3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s)‖ ≤
      ‖pairEta tr μ u s‖ + 2 * ‖pairQ tr μ u s‖ + 3 * ‖pairC tr μ u s‖ := by
    rw [hrew]
    have t1 := norm_add_le (pairEta tr μ u s - 2 * pairQ tr μ u s)
      (3 * (Complex.I * pairC tr μ u s))
    have t2 := norm_sub_le (pairEta tr μ u s) (2 * pairQ tr μ u s)
    have n2 : ‖(2 : ℂ) * pairQ tr μ u s‖ = 2 * ‖pairQ tr μ u s‖ := by simp
    have n3 : ‖(3 : ℂ) * (Complex.I * pairC tr μ u s)‖ = 3 * ‖pairC tr μ u s‖ := by
      simp
    linarith
  have hen : ‖(pairEta tr μ u s + pairQ tr μ u s) -
      3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s)‖ₑ ≤ 6 * sAbs tr μ u s := by
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖(pairEta tr μ u s + pairQ tr μ u s) -
            3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s)‖
        ≤ ENNReal.ofReal (‖pairEta tr μ u s‖ + 2 * ‖pairQ tr μ u s‖ + 3 * ‖pairC tr μ u s‖) :=
          ENNReal.ofReal_le_ofReal htri
      _ = ‖pairEta tr μ u s‖ₑ + 2 * ‖pairQ tr μ u s‖ₑ + 3 * ‖pairC tr μ u s‖ₑ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (norm_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ofReal_norm, ofReal_norm, ofReal_norm]
          norm_num
      _ ≤ sAbs tr μ u s + 2 * sAbs tr μ u s + 3 * sAbs tr μ u s :=
          add_le_add (add_le_add hE (mul_le_mul_of_nonneg_left hQ bot_le))
            (mul_le_mul_of_nonneg_left hC bot_le)
      _ = 6 * sAbs tr μ u s := by ring
  have hw_en : ‖((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs _)]
  rw [enorm_mul, hw_en]
  calc ‖(pairEta tr μ u s + pairQ tr μ u s) -
          3 * (pairQ tr μ u s - Complex.I * pairC tr μ u s)‖ₑ * ENNReal.ofReal (s ^ (-3 / 2 : ℝ))
      ≤ (6 * sAbs tr μ u s) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hen bot_le
    _ = 6 * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ u s) := by ring

lemma enorm_aniso_le_sAbs {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖(2 * pairQ tr μ u s - pairEta tr μ u s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ₑ ≤
      3 * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ u s) := by
  obtain ⟨hE, hQ, _⟩ := enorm_pairs_le_sAbs hν tr μ u s
  have htri : ‖2 * pairQ tr μ u s - pairEta tr μ u s‖ ≤
      2 * ‖pairQ tr μ u s‖ + ‖pairEta tr μ u s‖ := by
    have t1 := norm_sub_le (2 * pairQ tr μ u s) (pairEta tr μ u s)
    have n2 : ‖(2 : ℂ) * pairQ tr μ u s‖ = 2 * ‖pairQ tr μ u s‖ := by simp
    linarith
  have hen : ‖2 * pairQ tr μ u s - pairEta tr μ u s‖ₑ ≤ 3 * sAbs tr μ u s := by
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖2 * pairQ tr μ u s - pairEta tr μ u s‖
        ≤ ENNReal.ofReal (2 * ‖pairQ tr μ u s‖ + ‖pairEta tr μ u s‖) :=
          ENNReal.ofReal_le_ofReal htri
      _ = 2 * ‖pairQ tr μ u s‖ₑ + ‖pairEta tr μ u s‖ₑ := by
          rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _),
            ENNReal.ofReal_mul (by norm_num), ofReal_norm, ofReal_norm]
          norm_num
      _ ≤ 2 * sAbs tr μ u s + sAbs tr μ u s :=
          add_le_add (mul_le_mul_of_nonneg_left hQ bot_le) hE
      _ = 3 * sAbs tr μ u s := by ring
  have hw_en : ‖((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs _)]
  rw [enorm_mul, hw_en]
  calc ‖2 * pairQ tr μ u s - pairEta tr μ u s‖ₑ * ENNReal.ofReal (s ^ (-3 / 2 : ℝ))
      ≤ (3 * sAbs tr μ u s) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hen bot_le
    _ = 3 * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ u s) := by ring

/-! ### Central reflection and symmetrization of `IsLinearisedFlow` -/

lemma cell_neg_ae_eq_aniso (c : ℝ) :
    (Neg.neg ⁻¹' B0579.cell c : Set (ℝ × ℝ)) =ᵐ[volume] B0579.cell c := by
  rw [MeasureTheory.ae_eq_set]
  by_cases hc : 0 < c
  · refine ⟨?_, ?_⟩
    · have hsub : (Neg.neg ⁻¹' B0579.cell c) \ B0579.cell c ⊆ {c / 2} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = c / 2 := by
          by_contra hne
          exact h2 ⟨by linarith, lt_of_le_of_ne (by linarith) hne⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
    · have hsub : B0579.cell c \ (Neg.neg ⁻¹' B0579.cell c) ⊆ {-(c / 2)} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = -(c / 2) := by
          by_contra hne
          exact h2 ⟨by linarith, by have := lt_of_le_of_ne h1.1 (Ne.symm hne); linarith⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · have h1 : B0579.cell c = ∅ := by
      ext x; simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false,
        iff_false]
      rintro ⟨a, b⟩; linarith
    simp [h1]

lemma measurePreserving_neg_cell_aniso (c : ℝ) :
    MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
      (volume.restrict (B0579.cell c)) (volume.restrict (B0579.cell c)) := by
  refine ⟨measurable_neg, ?_⟩
  have hmp : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : volume.restrict (Neg.neg ⁻¹' B0579.cell c) = volume.restrict (B0579.cell c) :=
    Measure.restrict_congr_set (cell_neg_ae_eq_aniso c)
  calc Measure.map Neg.neg (volume.restrict (B0579.cell c))
      = Measure.map Neg.neg (volume.restrict (Neg.neg ⁻¹' B0579.cell c)) := by rw [heq]
    _ = (Measure.map Neg.neg volume).restrict (B0579.cell c) :=
        ((MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding.restrict_map volume (B0579.cell c)).symm
    _ = volume.restrict (B0579.cell c) := by rw [hmp.map_eq]

lemma ae_neg_of_ae_cell_aniso {c : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => g (-x)) :=
  (measurePreserving_neg_cell_aniso c).quasiMeasurePreserving.ae_eq_comp h

lemma integral_cell_neg_aniso {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ × ℝ → E) :
    ∫ x in B0579.cell c, f (-x) = ∫ x in B0579.cell c, f x :=
  (measurePreserving_neg_cell_aniso c).integral_comp
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding f

lemma pd_comp_neg_aniso {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (k : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd k (fun y => F (-y)) x = -B0579.pd k F (-x) := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := -ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have hfun : (fun y : ℝ × ℝ => F (-y)) = F ∘ L := rfl
  unfold B0579.pd
  have hfd : fderiv ℝ (F ∘ L) x = (fderiv ℝ F (-x)).comp L :=
    ((hF (-x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hfun, hfd, ContinuousLinearMap.comp_apply]
  simp [L]

lemma pd_neg_aniso {G : ℝ × ℝ → ℝ} (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => -G y) x = -B0579.pd k G x := by
  unfold B0579.pd
  change (fderiv ℝ (-G) x) (B0579.dir k) = -(fderiv ℝ G x) (B0579.dir k)
  rw [fderiv_neg]; rfl

lemma isCylTest_neg_aniso {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => ψ (-x)) := by
  refine ⟨hψ.smooth.comp contDiff_neg, fun x => ?_, ?_⟩
  · have hp := hψ.periodic (-x.1 - c, -x.2)
    dsimp only at hp
    have h1 : -((x.1 + c, x.2) : ℝ × ℝ) = (-x.1 - c, -x.2) := by
      ext
      · simp; ring
      · simp
    have h2 : (-x.1 - c + c, -x.2) = -x := by ext <;> simp
    rw [h1, ← hp, h2]
  · obtain ⟨B, hB⟩ := hψ.band
    refine ⟨B, fun x hx => hB (-x) ?_⟩
    simpa using hx

lemma eLpNorm_comp_neg_cellMeasure_aniso (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => F (-x)) = xNorm c m F := by
  unfold xNorm
  rw [PairContAux.eLpNorm_cellMeasure_cx, PairContAux.eLpNorm_cellMeasure_cx,
    T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
  congr 1
  have hjb : ∀ x : ℝ × ℝ, B0579.jb (-x) = B0579.jb x := fun x => by simp [B0579.jb]
  have hfn : (fun x : ℝ × ℝ => ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F (-x)‖ₑ ^ 2) =
      (fun y : ℝ × ℝ => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2) ∘ Neg.neg := by
    funext x; simp [Function.comp, hjb x]
  rw [hfn]
  exact (measurePreserving_neg_cell_aniso c).lintegral_comp_emb
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding
    (fun y => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2)

lemma memLp_comp_neg_cellMeasure_aniso {c m : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => F (-x)) 2 (B0579.cellMeasure c m) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_vol : F =ᵐ[volume.restrict (B0579.cell c)] F₀ :=
    (B0579.ac_cellMeasure c m).ae_le hF.1.ae_eq_mk
  have hae_neg : (fun x => F (-x)) =ᵐ[B0579.cellMeasure c m] (fun x => F₀ (-x)) :=
    (B0579.cellMeasure_ac c m).ae_le (ae_neg_of_ae_cell_aniso hae_vol)
  have hm : AEStronglyMeasurable (fun x => F (-x)) (B0579.cellMeasure c m) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  change xNorm c m (fun x => F (-x)) < ⊤
  rw [eLpNorm_comp_neg_cellMeasure_aniso]
  exact hF.2

lemma memLp_comp_neg_vol_aniso {c : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_neg : (fun x => F (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => F₀ (-x)) :=
    ae_neg_of_ae_cell_aniso hF.1.ae_eq_mk
  have hm : AEStronglyMeasurable (fun x => F (-x)) (volume.restrict (B0579.cell c)) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  rw [T06.eLpNorm_two_eq_lintegral]
  have hlint : ∫⁻ x, ‖F (-x)‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) =
      ∫⁻ y, ‖F y‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) :=
    (measurePreserving_neg_cell_aniso c).lintegral_comp_emb
      (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding (fun y => ‖F y‖ₑ ^ 2)
  rw [hlint, ← T06.eLpNorm_two_eq_lintegral]
  exact hF.2

def symFlowW (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * (w s x + w s (-x))

def symFlowU (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) (x : ℝ × ℝ) (j : Fin 2) : ℂ :=
  (2 : ℂ)⁻¹ * (u s x j - u s (-x) j)

lemma symFlowW_even (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) :
    IsCentrallyEven (symFlowW w s) := by
  intro x; unfold symFlowW; rw [neg_neg, add_comm]

lemma isLinearisedFlow_reflect_aniso {ν c m : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {f : ℝ × ℝ → ℂ}
    (hf_even : IsCentrallyEven f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f w u) :
    IsLinearisedFlow ν c m tr 0 f (fun τ x => w τ (-x)) (fun τ x j => -u τ (-x) j) := by
  let w' : ℝ → ℝ × ℝ → ℂ := fun τ x => w τ (-x)
  let u' : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun τ x j => -u τ (-x) j
  have hlap_neg : ∀ (ψ : ℝ × ℝ → ℝ) (_ : ContDiff ℝ ∞ ψ) (x : ℝ × ℝ),
      lapP (fun y => ψ (-y)) x = lapP ψ (-x) := by
    intro ψ hψ x; unfold lapP
    have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have hpd0 : Differentiable ℝ (B0579.pd 0 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 0).differentiable (by simp)
    have hpd1 : Differentiable ℝ (B0579.pd 1 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 1).differentiable (by simp)
    have e0 : B0579.pd 0 (fun y => ψ (-y)) = fun y => -B0579.pd 0 ψ (-y) :=
      funext (pd_comp_neg_aniso hdψ 0)
    have e1 : B0579.pd 1 (fun y => ψ (-y)) = fun y => -B0579.pd 1 ψ (-y) :=
      funext (pd_comp_neg_aniso hdψ 1)
    have d0 : B0579.pd 0 (fun y => -B0579.pd 0 ψ (-y)) x = B0579.pd 0 (B0579.pd 0 ψ) (-x) := by
      rw [pd_neg_aniso, pd_comp_neg_aniso hpd0 0 x, neg_neg]
    have d1 : B0579.pd 1 (fun y => -B0579.pd 1 ψ (-y)) x = B0579.pd 1 (B0579.pd 1 ψ) (-x) := by
      rw [pd_neg_aniso, pd_comp_neg_aniso hpd1 1 x, neg_neg]
    rw [e0, e1, d0, d1]
  have hpdE_odd : ∀ r : ℝ, 0 ≤ r → ∀ (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (UnforcedLeray.B0238.Ec tr r) (-x) =
        -B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by
    intro r hr j x
    have hdE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) :=
      (ForceMemXAux.contDiff_Ec tr hr).differentiable (by simp)
    have heven : (fun y => UnforcedLeray.B0238.Ec tr r (-y)) = UnforcedLeray.B0238.Ec tr r :=
      funext (UnforcedLeray.B0238.Ec_even tr hr)
    have h1 := pd_comp_neg_aniso hdE j x
    rw [heven] at h1; linarith
  have hfl_eq : ∀ (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) (r : ℝ), 0 ≤ r → ∀ x : ℝ × ℝ,
      flowIntegrand tr (w' r) (u' r) r ψ x =
        flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) := by
    intro ψ hψ r hr0 x
    have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
    have p0 := pd_comp_neg_aniso hdψ 0 (-x)
    have p1 := pd_comp_neg_aniso hdψ 1 (-x)
    have pl := hlap_neg ψ hψ.smooth (-x)
    rw [neg_neg] at p0 p1 pl
    have hv_odd : ∀ j : Fin 2, tr.v r (-x) j = -tr.v r x j := fun j => by
      have h := congrArg (fun v : UnforcedLeray.Train.Vec => v j) (tr.isTrain.odd r hr0 x)
      simpa using h
    have eE0 := hpdE_odd r hr0 0 x
    have eE1 := hpdE_odd r hr0 1 x
    unfold flowIntegrand; dsimp only [w', u']
    rw [p0, p1, pl, hv_odd 0, hv_odd 1, eE0, eE1, neg_neg]
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ae_neg_of_ae_cell_aniso hw.initial).trans (Eventually.of_forall hf_even)
  · exact fun s hs => memLp_comp_neg_cellMeasure_aniso (hw.memX s hs)
  · intro s hs
    refine (hw.strongCont s hs).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' _
    have heq : w' s' - w' s = fun x => (w s' - w s) (-x) := rfl
    rw [heq, eLpNorm_comp_neg_cellMeasure_aniso]
  · intro s hs
    have hbs := hw.biotSavart s hs
    refine ⟨fun j => (memLp_comp_neg_vol_aniso (hbs.1 j)).neg, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hψn := isCylTest_neg_aniso hψ
      have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
      have hpt : (fun x => u' s x 0 * (B0579.pd 0 ψ x : ℂ) + u' s x 1 * (B0579.pd 1 ψ x : ℂ)) =
          fun x => u s (-x) 0 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) +
            u s (-x) 1 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) := by
        funext x
        have p0 := pd_comp_neg_aniso hdψ 0 (-x); have p1 := pd_comp_neg_aniso hdψ 1 (-x)
        rw [neg_neg] at p0 p1; dsimp only [u']; rw [p0, p1]; push_cast; ring
      rw [hpt, integral_cell_neg_aniso c (fun y => u s y 0 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ) +
        u s y 1 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ))]
      exact hbs.2.1 _ hψn
    · have hψn := isCylTest_neg_aniso hψ
      have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
      have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
          ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
        have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
            fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
        rw [hp]; exact integral_cell_neg_aniso c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
      have hr : (fun x => u' s x 0 * (B0579.pd 1 ψ x : ℂ) - u' s x 1 * (B0579.pd 0 ψ x : ℂ)) =
          fun x => u s (-x) 0 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) -
            u s (-x) 1 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) := by
        funext x
        have p0 := pd_comp_neg_aniso hdψ 0 (-x); have p1 := pd_comp_neg_aniso hdψ 1 (-x)
        rw [neg_neg] at p0 p1; dsimp only [u']; rw [p0, p1]; push_cast; ring
      rw [hl, hr, integral_cell_neg_aniso c (fun y => u s y 0 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ) -
        u s y 1 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ))]
      exact hbs.2.2 _ hψn
  · intro ψ hψ r hr
    have hψn := isCylTest_neg_aniso hψ
    have hInt : Integrable (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))
        (volume.restrict (B0579.cell c)) := hw.integrable _ hψn r hr
    exact ((measurePreserving_neg_cell_aniso c).integrable_comp_of_integrable hInt).congr
      (Eventually.of_forall fun x => (hfl_eq ψ hψ r hr x).symm)
  · intro ψ hψ s hs
    have hψn := isCylTest_neg_aniso hψ
    refine (hw.timeIntegrable _ hψn s hs).congr fun r hr => ?_
    rw [uIoc_of_le hs] at hr
    have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
        fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
      funext (hfl_eq ψ hψ r hr.1.le)
    rw [heq_r, integral_cell_neg_aniso c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
  · intro ψ hψ s hs
    have hψn := isCylTest_neg_aniso hψ
    have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
        ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
          fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
      rw [hp]; exact integral_cell_neg_aniso c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
    have hf_int : ∫ x in B0579.cell c, f x * (ψ x : ℂ) =
        ∫ y in B0579.cell c, f y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun y : ℝ × ℝ => f y * (ψ y : ℂ)) =
          fun y => f (-y) * ((fun z => ψ (-z)) (-y) : ℂ) := by
        funext y; simp [hf_even y]
      rw [hp]; exact integral_cell_neg_aniso c (fun y => f y * ((fun z => ψ (-z)) y : ℂ))
    have hr_int : ∫ r in (0 : ℝ)..s, (∫ x in B0579.cell c, flowIntegrand tr (w' r) (u' r) r ψ x) =
        ∫ r in (0 : ℝ)..s, (∫ y in B0579.cell c,
          flowIntegrand tr (w r) (u r) r (fun z => ψ (-z)) y) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs] at hr
        have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
            fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
          funext (hfl_eq ψ hψ r hr.1)
        rw [heq_r, integral_cell_neg_aniso c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
    rw [hl, hf_int, hr_int, hw.weak _ hψn s hs]

lemma isLinearisedFlow_sym_aniso {ν c m : ℝ} (hm : 1 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {f : ℝ × ℝ → ℂ}
    (hf_mem : MemLp f 2 (B0579.cellMeasure c m)) (hf_even : IsCentrallyEven f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f w u) :
    IsLinearisedFlow ν c m tr 0 f (symFlowW w) (symFlowU u) := by
  have hw_ref := isLinearisedFlow_reflect_aniso tr hf_even hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hw.initial, hw_ref.initial] with x hx1 hx2
    unfold symFlowW; rw [hx1, hx2]; ring
  · intro s hs
    exact ((hw.memX s hs).add (hw_ref.memX s hs)).const_mul (2 : ℂ)⁻¹
  · intro s hs
    have h1 := hw.strongCont s hs
    have h2 := hw_ref.strongCont s hs
    have hsum : Tendsto (fun s' => xNorm c m (w s' - w s) +
        xNorm c m ((fun x => w s' (-x)) - (fun x => w s (-x)))) (𝓝[Ici 0] s) (𝓝 0) := by
      simpa using h1.add h2
    have hle : ∀ᶠ s' in 𝓝[Ici (0 : ℝ)] s,
        xNorm c m (symFlowW w s' - symFlowW w s) ≤
          xNorm c m (w s' - w s) + xNorm c m ((fun x => w s' (-x)) - (fun x => w s (-x))) := by
      filter_upwards [self_mem_nhdsWithin] with s' hs'0
      have hfun : symFlowW w s' - symFlowW w s =
          (2 : ℂ)⁻¹ • ((w s' - w s) + ((fun x => w s' (-x)) - (fun x => w s (-x)))) := by
        funext x; simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, symFlowW]; ring
      unfold xNorm
      rw [hfun, eLpNorm_const_smul]
      have hhalf : ‖(2 : ℂ)⁻¹‖ₑ ≤ 1 := by
        rw [← ofReal_norm]; norm_num
      calc ‖(2 : ℂ)⁻¹‖ₑ * eLpNorm ((w s' - w s) + ((fun x => w s' (-x)) - (fun x => w s (-x))))
              2 (B0579.cellMeasure c m)
          ≤ 1 * eLpNorm ((w s' - w s) + ((fun x => w s' (-x)) - (fun x => w s (-x))))
              2 (B0579.cellMeasure c m) := mul_le_mul_of_nonneg_right hhalf bot_le
        _ ≤ xNorm c m (w s' - w s) +
              xNorm c m ((fun x => w s' (-x)) - (fun x => w s (-x))) := by
            rw [one_mul]
            exact eLpNorm_add_le
              (((hw.memX s' hs'0).sub (hw.memX s hs)).1)
              (((hw_ref.memX s' hs'0).sub (hw_ref.memX s hs)).1) one_le_two
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) hle
  · intro s hs
    have b1 := hw.biotSavart s hs
    have b2 := hw_ref.biotSavart s hs
    refine ⟨fun j => ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hsub := (b1.1 j).add (b2.1 j)
      simpa [symFlowU, sub_eq_add_neg] using hsub.const_mul (2 : ℂ)⁻¹
    · have i1 : Integrable (fun x => u s x 0 * (B0579.pd 0 ψ x : ℂ) +
          u s x 1 * (B0579.pd 1 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b1.1 0)).add
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b1.1 1))
      have i2 : Integrable (fun x => (-u s (-x) 0) * (B0579.pd 0 ψ x : ℂ) +
          (-u s (-x) 1) * (B0579.pd 1 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b2.1 0)).add
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b2.1 1))
      have hpt : (fun x => symFlowU u s x 0 * (B0579.pd 0 ψ x : ℂ) +
          symFlowU u s x 1 * (B0579.pd 1 ψ x : ℂ)) =
          fun x => (2 : ℂ)⁻¹ * ((u s x 0 * (B0579.pd 0 ψ x : ℂ) +
            u s x 1 * (B0579.pd 1 ψ x : ℂ)) +
            ((-u s (-x) 0) * (B0579.pd 0 ψ x : ℂ) +
              (-u s (-x) 1) * (B0579.pd 1 ψ x : ℂ))) := by
        funext x; unfold symFlowU; ring
      rw [hpt, integral_const_mul, integral_add i1 i2, b1.2.1 ψ hψ, b2.2.1 ψ hψ,
        add_zero, mul_zero]
    · have iw1 : Integrable (fun x => w s x * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
          (memLp_vol_of_cellMeasure (by linarith) (hw.memX s hs))
      have iw2 : Integrable (fun x => w s (-x) * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
          (memLp_vol_of_cellMeasure (by linarith) (hw_ref.memX s hs))
      have iu1 : Integrable (fun x => u s x 0 * (B0579.pd 1 ψ x : ℂ) -
          u s x 1 * (B0579.pd 0 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b1.1 0)).sub
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b1.1 1))
      have iu2 : Integrable (fun x => (-u s (-x) 0) * (B0579.pd 1 ψ x : ℂ) -
          (-u s (-x) 1) * (B0579.pd 0 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b2.1 0)).sub
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b2.1 1))
      have hptL : (fun x => symFlowW w s x * (ψ x : ℂ)) =
          fun x => (2 : ℂ)⁻¹ * (w s x * (ψ x : ℂ) + w s (-x) * (ψ x : ℂ)) := by
        funext x; unfold symFlowW; ring
      have hptR : (fun x => symFlowU u s x 0 * (B0579.pd 1 ψ x : ℂ) -
          symFlowU u s x 1 * (B0579.pd 0 ψ x : ℂ)) =
          fun x => (2 : ℂ)⁻¹ * ((u s x 0 * (B0579.pd 1 ψ x : ℂ) -
            u s x 1 * (B0579.pd 0 ψ x : ℂ)) +
            ((-u s (-x) 0) * (B0579.pd 1 ψ x : ℂ) -
              (-u s (-x) 1) * (B0579.pd 0 ψ x : ℂ))) := by
        funext x; unfold symFlowU; ring
      rw [hptL, hptR, integral_const_mul, integral_const_mul,
        integral_add iw1 iw2, integral_add iu1 iu2, b1.2.2 ψ hψ, b2.2.2 ψ hψ]
  · intro ψ hψ r hr
    have hpt : flowIntegrand tr (symFlowW w r) (symFlowU u r) r ψ =
        fun x => (2 : ℂ)⁻¹ * (flowIntegrand tr (w r) (u r) r ψ x +
          flowIntegrand tr (fun y => w r (-y)) (fun y j => -u r (-y) j) r ψ x) := by
      funext x; unfold flowIntegrand symFlowW symFlowU; ring
    rw [hpt]
    exact ((hw.integrable ψ hψ r hr).add (hw_ref.integrable ψ hψ r hr)).const_mul (2 : ℂ)⁻¹
  · intro ψ hψ s hs
    have hcongr : ∀ r ∈ uIoc 0 s,
        (∫ x in B0579.cell c, flowIntegrand tr (symFlowW w r) (symFlowU u r) r ψ x) =
        (2 : ℂ)⁻¹ * ((∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r ψ x) +
          ∫ x in B0579.cell c,
            flowIntegrand tr (fun y => w r (-y)) (fun y j => -u r (-y) j) r ψ x) := by
      intro r hr
      rw [uIoc_of_le hs] at hr
      have hpt : flowIntegrand tr (symFlowW w r) (symFlowU u r) r ψ =
          fun x => (2 : ℂ)⁻¹ * (flowIntegrand tr (w r) (u r) r ψ x +
            flowIntegrand tr (fun y => w r (-y)) (fun y j => -u r (-y) j) r ψ x) := by
        funext x; unfold flowIntegrand symFlowW symFlowU; ring
      rw [hpt, integral_const_mul,
        integral_add (hw.integrable ψ hψ r hr.1.le) (hw_ref.integrable ψ hψ r hr.1.le)]
    exact (((hw.timeIntegrable ψ hψ s hs).add
      (hw_ref.timeIntegrable ψ hψ s hs)).const_mul (2 : ℂ)⁻¹).congr fun r hr => (hcongr r hr).symm
  · intro ψ hψ s hs
    have iw1 : Integrable (fun x => w s x * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
        (memLp_vol_of_cellMeasure (by linarith) (hw.memX s hs))
    have iw2 : Integrable (fun x => w s (-x) * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
        (memLp_vol_of_cellMeasure (by linarith) (hw_ref.memX s hs))
    have hptL : (fun x => symFlowW w s x * (ψ x : ℂ)) =
        fun x => (2 : ℂ)⁻¹ * (w s x * (ψ x : ℂ) + w s (-x) * (ψ x : ℂ)) := by
      funext x; unfold symFlowW; ring
    have hcongr : ∀ r ∈ uIoc 0 s,
        (∫ x in B0579.cell c, flowIntegrand tr (symFlowW w r) (symFlowU u r) r ψ x) =
        (2 : ℂ)⁻¹ * ((∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r ψ x) +
          ∫ x in B0579.cell c,
            flowIntegrand tr (fun y => w r (-y)) (fun y j => -u r (-y) j) r ψ x) := by
      intro r hr
      rw [uIoc_of_le hs] at hr
      have hpt : flowIntegrand tr (symFlowW w r) (symFlowU u r) r ψ =
          fun x => (2 : ℂ)⁻¹ * (flowIntegrand tr (w r) (u r) r ψ x +
            flowIntegrand tr (fun y => w r (-y)) (fun y j => -u r (-y) j) r ψ x) := by
        funext x; unfold flowIntegrand symFlowW symFlowU; ring
      rw [hpt, integral_const_mul,
        integral_add (hw.integrable ψ hψ r hr.1.le) (hw_ref.integrable ψ hψ r hr.1.le)]
    rw [hptL, integral_const_mul, integral_add iw1 iw2, hw.weak ψ hψ s hs, hw_ref.weak ψ hψ s hs,
      intervalIntegral.integral_congr_ae (ae_of_all _ hcongr),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hw.timeIntegrable ψ hψ s hs)
        (hw_ref.timeIntegrable ψ hψ s hs)]
    ring

lemma cyl_cellμ_eq_restrict_aniso (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

lemma memLp_train_coord_of_cellL2 {ν c s : ℝ} (hs : 0 ≤ s)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hfin : UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤) (i : Fin 2) :
    MemLp (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) ≤
        UnforcedLeray.Train.cellL2 c (tr.v s) := by
  have hcont : Continuous (fun x => tr.v s x i) :=
    ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      tr.isTrain.smooth_v.continuousOn).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, trivial⟩)
  have hle : eLpNorm (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) ≤
      UnforcedLeray.Train.cellL2 c (tr.v s) := by
    unfold UnforcedLeray.Train.cellL2
    rw [cyl_cellμ_eq_restrict_aniso]
    exact eLpNorm_mono fun x => PiLp.norm_apply_le (tr.v s x) i
  exact ⟨⟨hcont.measurable.aestronglyMeasurable, lt_of_le_of_lt hle hfin⟩, hle⟩

lemma symFlow_preserves_pairings_and_quadQ {ν c m : ℝ} (hm : 8 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    {s : ℝ} (hs : 0 ≤ s)
    (hw_mem : MemLp (w s) 2 (B0579.cellMeasure c m))
    (hu_bs : IsBiotSavart c (w s) (u s))
    (hv_fin : UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤) :
    (∀ i j : Fin 2,
      (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * symFlowU u s x j) =
        ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s x j) ∧
    quadQ c (symFlowW w s) = quadQ c (w s) := by
  constructor
  · intro i j
    have hv_mem := (memLp_train_coord_of_cellL2 hs tr hv_fin i).1
    have hu_pos : MemLp (fun x => u s x j) 2 (volume.restrict (B0579.cell c)) := hu_bs.1 j
    have hu_neg : MemLp (fun x => u s (-x) j) 2 (volume.restrict (B0579.cell c)) :=
      memLp_comp_neg_vol_aniso hu_pos
    have hi1 : IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u s x j) (B0579.cell c) :=
      hv_mem.ofReal.integrable_mul hu_pos
    have hi2 : IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u s (-x) j) (B0579.cell c) :=
      hv_mem.ofReal.integrable_mul hu_neg
    have hpt : (fun x => ((tr.v s x i : ℝ) : ℂ) * symFlowU u s x j) =
        fun x => (2 : ℂ)⁻¹ * (((tr.v s x i : ℝ) : ℂ) * u s x j -
          ((tr.v s x i : ℝ) : ℂ) * u s (-x) j) := by
      funext x; unfold symFlowU; ring
    have hneg_int : (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s (-x) j) =
        -(∫ y in B0579.cell c, ((tr.v s y i : ℝ) : ℂ) * u s y j) := by
      have hodd : ∀ x : ℝ × ℝ, ((tr.v s x i : ℝ) : ℂ) * u s (-x) j =
          -(((tr.v s (-x) i : ℝ) : ℂ) * u s (-x) j) := fun x => by
        have h := congrArg (fun v : UnforcedLeray.Train.Vec => v i) (tr.isTrain.odd s hs x)
        simp only [PiLp.neg_apply] at h
        rw [h]; push_cast; ring
      simp_rw [hodd, integral_neg]
      rw [integral_cell_neg_aniso c (fun y => ((tr.v s y i : ℝ) : ℂ) * u s y j)]
    rw [hpt, integral_const_mul, integral_sub hi1 hi2, hneg_int]
    ring
  · unfold quadQ
    congr 1
    have hm1 : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s x) (B0579.cell c) :=
      integrable_eta_sq_of_memX m hm c (w s) hw_mem
    have hm2 : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s (-x)) (B0579.cell c) :=
      integrable_eta_sq_of_memX m hm c (fun x => w s (-x))
        (memLp_comp_neg_cellMeasure_aniso hw_mem)
    have hpt : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * symFlowW w s x) =
        fun x => (2 : ℂ)⁻¹ * (((x.2 ^ 2 : ℝ) : ℂ) * w s x +
          ((x.2 ^ 2 : ℝ) : ℂ) * w s (-x)) := by
      funext x; unfold symFlowW; ring
    have hneg_q : (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s (-x)) =
        ∫ y in B0579.cell c, ((y.2 ^ 2 : ℝ) : ℂ) * w s y := by
      have hp : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * w s (-x)) =
          fun x => (((-x).2 ^ 2 : ℝ) : ℂ) * w s (-x) := by
        funext x; simp
      rw [hp]
      exact integral_cell_neg_aniso c (fun y => ((y.2 ^ 2 : ℝ) : ℂ) * w s y)
    rw [hpt, integral_const_mul, integral_add hm1 hm2, hneg_q]
    ring

/-! ### Uniform all-age `L²` train bound, right-continuity of pairings, and measurability -/

lemma train_cellL2_uniform_aniso :
    ∃ (C_L2 ν_L2 : ℝ), 0 < C_L2 ∧ 0 < ν_L2 ∧
      ∀ ν ∈ Ioc 0 ν_L2, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
          UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤ ENNReal.ofReal C_L2 := by
  obtain ⟨C_L2, ν_0, hC_L2, hν_0, hL2⟩ :=
    T22Sub.trainL2Decay_unconditional 2 (by norm_num : (1 / 2 : ℝ) < 2)
  refine ⟨C_L2, min ν_0 (1 / 2), hC_L2, lt_min hν_0 (by norm_num), fun ν hν tr htr s hs => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_le : ν ≤ ν_0 := hν.2.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν.2.trans (min_le_right _ _)
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_gt1 : 1 < c := by
    have h4 : ((1 / 2 : ℝ) ^ (-2 : ℝ)) ≤ c :=
      Real.rpow_le_rpow_of_nonpos hν_pos hν_half (by norm_num)
    have hev : ((1 / 2 : ℝ) ^ (-2 : ℝ)) = 4 := by norm_num
    linarith
  have hsc_pos : 0 < UnforcedLeray.B0146.overlapAge ν c := by
    unfold UnforcedLeray.B0146.overlapAge
    exact div_pos (by nlinarith) hν_pos
  have hL2_s := hL2 ν hν_pos hν_le tr htr s hs
  have ha_ge1 : 1 ≤ 1 + ν * s := by nlinarith
  by_cases hle : s ≤ UnforcedLeray.B0146.overlapAge ν c
  · refine (hL2_s.1 hle).trans (ENNReal.ofReal_le_ofReal ?_)
    have hw : UnforcedLeray.Train.width ν s = 1 + ν * s := rfl
    rw [hw]
    have hinv : (1 + ν * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha_ge1
    nlinarith
  · push Not at hle
    refine (hL2_s.2 hle.le).trans (ENNReal.ofReal_le_ofReal ?_)
    change C_L2 * c ^ (-2 : ℝ) * (s / UnforcedLeray.B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ C_L2
    have hc_inv : c ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc_gt1.le (by norm_num)
    have hrat : 1 ≤ s / UnforcedLeray.B0146.overlapAge ν c := (one_le_div hsc_pos).2 hle.le
    have hrpow : (s / UnforcedLeray.B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hrat (by norm_num)
    have hprod : c ^ (-2 : ℝ) * (s / UnforcedLeray.B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      mul_le_one₀ hc_inv (by positivity) hrpow
    nlinarith

lemma eLpNorm_two_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have hf_norm : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.norm.integrable_sq
  have h1 : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa using eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := f) two_ne_zero ENNReal.ofNat_ne_top
  have hlint : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) := by
    have hcongr : (fun x => ‖f x‖ₑ ^ (2 : ℝ)) =
        fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℝ)) := by
      funext x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
    have hf_rpow : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) μ := by
      simpa [Real.rpow_two] using hf_norm
    rw [hcongr, ofReal_integral_eq_lintegral_ofReal hf_rpow
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
  rw [h1, hlint, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)]

lemma norm_integral_mul_le_eLpNorm_two {c : ℝ}
    {v : ℝ × ℝ → ℝ} {u : ℝ × ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict (B0579.cell c)))
    (hu : MemLp u 2 (volume.restrict (B0579.cell c))) :
    ‖∫ x in B0579.cell c, ((v x : ℝ) : ℂ) * u x‖ ≤
      (eLpNorm v 2 (volume.restrict (B0579.cell c))).toReal *
        (eLpNorm u 2 (volume.restrict (B0579.cell c))).toReal := by
  let μ_c := volume.restrict (B0579.cell c)
  have hv' : MemLp v (ENNReal.ofReal 2) μ_c := by rw [ENNReal.ofReal_ofNat]; exact hv
  have hu' : MemLp (fun x => ‖u x‖) (ENNReal.ofReal 2) μ_c := by
    rw [ENNReal.ofReal_ofNat]; exact hu.norm
  calc ‖∫ x, ((v x : ℝ) : ℂ) * u x ∂μ_c‖
      ≤ ∫ x, ‖((v x : ℝ) : ℂ) * u x‖ ∂μ_c := norm_integral_le_integral_norm _
    _ = ∫ x, ‖v x‖ * ‖‖u x‖‖ ∂μ_c := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, norm_norm]
    _ ≤ (∫ x, ‖v x‖ ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖‖u x‖‖ ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hv' hu'
    _ = (eLpNorm v 2 μ_c).toReal * (eLpNorm u 2 μ_c).toReal := by
        simp only [norm_norm]
        rw [← eLpNorm_two_sq_eq_integral_norm_sq hv, ← eLpNorm_two_sq_eq_integral_norm_sq hu]

lemma eLpNorm_coord_le_velNorm {c : ℝ} (u : ℝ × ℝ → Fin 2 → ℂ) (j : Fin 2) :
    eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) ≤ velNorm c u := by
  unfold velNorm
  have h1 : eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) ^ 2 ≤
      ∑ k : Fin 2, eLpNorm (fun x => u x k) 2 (volume.restrict (B0579.cell c)) ^ 2 :=
    Finset.single_le_sum
      (f := fun k => eLpNorm (fun x => u x k) 2 (volume.restrict (B0579.cell c)) ^ 2)
      (fun _ _ => bot_le) (Finset.mem_univ j)
  calc eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c))
      = (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ (∑ k : Fin 2, eLpNorm (fun x => u x k) 2 (volume.restrict (B0579.cell c)) ^ 2) ^
          (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by positivity)

lemma velNorm_lt_top_aniso {c : ℝ} {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart c om u) : velNorm c u < ⊤ := by
  unfold velNorm
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  rw [Fin.sum_univ_two]
  exact (ENNReal.add_lt_top.2 ⟨ENNReal.pow_lt_top (hu.1 0).2, ENNReal.pow_lt_top (hu.1 1).2⟩).ne

lemma rightContinuous_train_vel_pairing
    {ν c m C_L2 : ℝ} (hm : 8 < m) (hc1 : 1 ≤ c) (hC_L2 : 0 < C_L2)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hv_bd : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal C_L2)
    {f : ℝ × ℝ → ℂ} (hf_zc : HasZeroCirculation c f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f w u)
    (hw_ev : ∀ s : ℝ, IsCentrallyEven (w s))
    (i j : Fin 2) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) :
    ContinuousWithinAt
      (fun s => ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s x j)
      (Ici s₀) s₀ := by
  have hc_pos : 0 < c := lt_of_lt_of_le one_pos hc1
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- First term: `∫ (tr.v s x i) * (u s x j - u s₀ x j) → 0`
  have hterm1 : Tendsto
      (fun s => ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * (u s x j - u s₀ x j))
      (𝓝[≥] s₀) (𝓝 0) := by
    have hsc : Tendsto (fun s => xNorm c m (w s - w s₀)) (𝓝[≥] s₀) (𝓝 0) :=
      (hw.strongCont s₀ hs₀).mono_left (nhdsWithin_mono s₀ (Ici_subset_Ici.2 hs₀))
    have hto0 : Tendsto (fun s => C_L2 * C_emb * (xNorm c m (w s - w s₀)).toReal)
        (𝓝[≥] s₀) (𝓝 0) := by
      have h1 : Tendsto (fun s => (xNorm c m (w s - w s₀)).toReal) (𝓝[≥] s₀) (𝓝 0) :=
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsc
      simpa using h1.const_mul (C_L2 * C_emb)
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [self_mem_nhdsWithin, (Metric.tendsto_nhds.1 hto0) ε hε] with s hs hdist
    have hs0 : 0 ≤ s := hs₀.trans hs
    have hzc_s : HasZeroCirculation c (w s) :=
      zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0 f w u hw hf_zc s hs0
    have hzc_s0 : HasZeroCirculation c (w s₀) :=
      zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0 f w u hw hf_zc s₀ hs₀
    have hzc_diff : HasZeroCirculation c (w s - w s₀) :=
      ⟨hzc_s.1.sub hzc_s0.1, by simp [Pi.sub_apply, integral_sub hzc_s.1 hzc_s0.1, hzc_s.2, hzc_s0.2]⟩
    have hev_diff : IsCentrallyEven (w s - w s₀) := fun x => by
      simp [Pi.sub_apply, hw_ev s x, hw_ev s₀ x]
    have hbs_diff : IsBiotSavart c (w s - w s₀) (fun x k => u s x k - u s₀ x k) := by
      have b1 := hw.biotSavart s hs0
      have b0 := hw.biotSavart s₀ hs₀
      refine ⟨fun k => (b1.1 k).sub (b0.1 k), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
      · have i1 : IntegrableOn (fun x => u s x 0 * (B0579.pd 0 ψ x : ℂ) +
            u s x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b1.1 0)).add
            (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b1.1 1))
        have i0 : IntegrableOn (fun x => u s₀ x 0 * (B0579.pd 0 ψ x : ℂ) +
            u s₀ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b0.1 0)).add
            (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b0.1 1))
        have hpt : (fun x => (u s x 0 - u s₀ x 0) * (B0579.pd 0 ψ x : ℂ) +
            (u s x 1 - u s₀ x 1) * (B0579.pd 1 ψ x : ℂ)) =
            fun x => (u s x 0 * (B0579.pd 0 ψ x : ℂ) + u s x 1 * (B0579.pd 1 ψ x : ℂ)) -
              (u s₀ x 0 * (B0579.pd 0 ψ x : ℂ) + u s₀ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
          funext x; ring
        rw [hpt, integral_sub i1 i0, b1.2.1 ψ hψ, b0.2.1 ψ hψ, sub_self]
      · have iw1 := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
          (memLp_vol_of_cellMeasure (by linarith) (hw.memX s hs0))
        have iw0 := CoreDuhamelRepSub.integrableOn_cylTest_mul hψ
          (memLp_vol_of_cellMeasure (by linarith) (hw.memX s₀ hs₀))
        have iu1 : IntegrableOn (fun x => u s x 0 * (B0579.pd 1 ψ x : ℂ) -
            u s x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b1.1 0)).sub
            (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b1.1 1))
        have iu0 : IntegrableOn (fun x => u s₀ x 0 * (B0579.pd 1 ψ x : ℂ) -
            u s₀ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
          (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 1) (b0.1 0)).sub
            (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ.pd 0) (b0.1 1))
        have hptL : (fun x => (w s - w s₀) x * (ψ x : ℂ)) =
            fun x => w s x * (ψ x : ℂ) - w s₀ x * (ψ x : ℂ) := by funext x; simp [ sub_mul]
        have hptR : (fun x => (u s x 0 - u s₀ x 0) * (B0579.pd 1 ψ x : ℂ) -
            (u s x 1 - u s₀ x 1) * (B0579.pd 0 ψ x : ℂ)) =
            fun x => (u s x 0 * (B0579.pd 1 ψ x : ℂ) - u s x 1 * (B0579.pd 0 ψ x : ℂ)) -
              (u s₀ x 0 * (B0579.pd 1 ψ x : ℂ) - u s₀ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
          funext x; ring
        rw [hptL, hptR, integral_sub iw1 iw0, integral_sub iu1 iu0, b1.2.2 ψ hψ, b0.2.2 ψ hψ]
    have hemb : velNorm c (fun x k => u s x k - u s₀ x k) ≤
        ENNReal.ofReal C_emb * xNorm c m (w s - w s₀) :=
      (le_add_self.trans
        (hEmb0 c hc1 (w s - w s₀) ((hw.memX s hs0).sub (hw.memX s₀ hs₀))
          hzc_diff hev_diff _ hbs_diff)).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb0 1)) bot_le)
    have hx_ne : xNorm c m (w s - w s₀) ≠ ⊤ := ((hw.memX s hs0).sub (hw.memX s₀ hs₀)).2.ne
    have hu_le : (eLpNorm (fun x => u s x j - u s₀ x j) 2 (volume.restrict (B0579.cell c))).toReal ≤
        C_emb * (xNorm c m (w s - w s₀)).toReal := by
      have h1 := (eLpNorm_coord_le_velNorm (fun x k => u s x k - u s₀ x k) j).trans hemb
      have hrhs_ne : ENNReal.ofReal C_emb * xNorm c m (w s - w s₀) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx_ne
      have h2 := ENNReal.toReal_mono hrhs_ne h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_emb.le] at h2
    have hv_s_fin : UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ :=
      lt_of_le_of_lt (hv_bd s hs0) ENNReal.ofReal_lt_top
    obtain ⟨hv_mem, hv_le⟩ := memLp_train_coord_of_cellL2 hs0 tr hv_s_fin i
    have hv_toReal : (eLpNorm (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c))).toReal ≤
        C_L2 := ENNReal.toReal_le_of_le_ofReal hC_L2.le (hv_le.trans (hv_bd s hs0))
    have hcs := norm_integral_mul_le_eLpNorm_two hv_mem (hbs_diff.1 j)
    have hbd_prod : ‖∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * (u s x j - u s₀ x j)‖ ≤
        C_L2 * (C_emb * (xNorm c m (w s - w s₀)).toReal) :=
      hcs.trans (mul_le_mul hv_toReal hu_le ENNReal.toReal_nonneg hC_L2.le)
    rw [dist_zero_right] at hdist ⊢
    rw [Real.norm_of_nonneg (by positivity)] at hdist
    linarith
  -- Second term: `∫ (tr.v s x i - tr.v s₀ x i) * u s₀ x j → 0` via vertical truncation + DCT
  have hterm2 : Tendsto
      (fun s => ∫ x in B0579.cell c, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j)
      (𝓝[≥] s₀) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    let μ_c := volume.restrict (B0579.cell c)
    have hu0 : MemLp (fun x => u s₀ x j) 2 μ_c := (hw.biotSavart s₀ hs₀).1 j
    have hg0_int : Integrable (fun x => ‖u s₀ x j‖ ^ 2) μ_c := hu0.norm.integrable_sq
    let tailSet : ℕ → Set (ℝ × ℝ) := fun n => {x : ℝ × ℝ | (n : ℝ) < |x.2|}
    have htail_meas : ∀ n : ℕ, MeasurableSet (tailSet n) := fun n =>
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd) |>.measurableSet
    have htail_lim : Tendsto
        (fun n : ℕ => ∫ x, (tailSet n).indicator (fun z => ‖u s₀ z j‖ ^ 2) x ∂μ_c)
        atTop (𝓝 0) := by
      have h0 : (0 : ℝ) = ∫ _ : ℝ × ℝ, (0 : ℝ) ∂μ_c := by simp
      rw [h0]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖u s₀ x j‖ ^ 2)
        (fun n => hg0_int.aestronglyMeasurable.indicator (htail_meas n))
        hg0_int
        (fun n => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ?_)
      · rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) x)]
        exact indicator_le_self' (fun _ _ => sq_nonneg _) x
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈|x.2|⌉₊] with n hn
        have hx_le : |x.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        have hnot : x ∉ tailSet n := not_lt.2 hx_le
        exact (indicator_of_notMem hnot _).symm
    set δ : ℝ := ε / (4 * C_L2 + 1)
    have hδ_pos : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.1 htail_lim (δ ^ 2) (sq_pos_of_pos hδ_pos)).exists
    rw [dist_zero_right, Real.norm_of_nonneg
      (integral_nonneg fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x)] at hN
    set bandSet : Set (ℝ × ℝ) := {x : ℝ × ℝ | |x.2| ≤ (N : ℝ)}
    have hband_compl : bandSetᶜ = tailSet N := by
      ext x; simp [bandSet, tailSet]
    have hband_meas : MeasurableSet bandSet :=
      isClosed_le (continuous_abs.comp continuous_snd) continuous_const |>.measurableSet
    have hu0_tail_mem : MemLp ((tailSet N).indicator (fun x => u s₀ x j)) 2 μ_c :=
      hu0.indicator (htail_meas N)
    have hu0_tail_le : (eLpNorm ((tailSet N).indicator (fun x => u s₀ x j)) 2 μ_c).toReal ≤ δ := by
      rw [eLpNorm_two_sq_eq_integral_norm_sq hu0_tail_mem]
      have heq_sq : (fun x => ‖(tailSet N).indicator (fun z => u s₀ z j) x‖ ^ (2 : ℝ)) =
          (tailSet N).indicator (fun z => ‖u s₀ z j‖ ^ 2) := by
        funext x
        by_cases hx : x ∈ tailSet N
        · simp [indicator_of_mem hx]
        · simp [indicator_of_notMem hx]
      rw [heq_sq]
      calc (∫ x, (tailSet N).indicator (fun z => ‖u s₀ z j‖ ^ 2) x ∂μ_c) ^ (1 / (2 : ℝ))
          ≤ (δ ^ 2) ^ (1 / (2 : ℝ)) :=
            Real.rpow_le_rpow
              (integral_nonneg fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x)
              hN.le (by positivity)
        _ = δ := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hδ_pos.le]
    -- Finite-measure DCT on `B0579.cell c ∩ bandSet`
    let μ_band := μ_c.restrict bandSet
    have hμ_band_fin : IsFiniteMeasure μ_band := by
      refine ⟨?_⟩
      have hsub : B0579.cell c ∩ bandSet ⊆ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(N : ℝ)) (N : ℝ) := by
        rintro ⟨x1, x2⟩ ⟨hx1, hx2⟩
        simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx1
        change |x2| ≤ (N : ℝ) at hx2; rw [abs_le] at hx2
        exact ⟨⟨hx1.1, hx1.2.le⟩, hx2⟩
      calc μ_band univ
          = volume (B0579.cell c ∩ bandSet) := by
            rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
              Measure.restrict_apply hband_meas, inter_comm]
        _ ≤ volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(N : ℝ)) (N : ℝ)) := measure_mono hsub
        _ < ⊤ := by
            rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hu0_band_int : Integrable (fun x => u s₀ x j) μ_band :=
      (hu0.restrict bandSet).integrable one_le_two
    let K_box : Set (ℝ × ℝ × ℝ) :=
      Icc s₀ (s₀ + 1) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(N : ℝ)) (N : ℝ))
    have hK_comp : IsCompact K_box :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hv_contOn : ContinuousOn (fun p : ℝ × ℝ × ℝ => tr.v p.1 p.2 i) K_box :=
      ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
        tr.isTrain.smooth_v.continuousOn).mono fun p hp => ⟨hs₀.trans hp.1.1, trivial⟩
    obtain ⟨M_box, hM_box⟩ := hK_comp.exists_bound_of_continuousOn hv_contOn
    set M_v : ℝ := max M_box 0
    have hMv_nn : 0 ≤ M_v := le_max_right _ _
    have hband_lim : Tendsto
        (fun s => ∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j ∂μ_band)
        (𝓝[≥] s₀) (𝓝 0) := by
      have h0 : (0 : ℂ) = ∫ _ : ℝ × ℝ, (0 : ℂ) ∂μ_band := by simp
      rw [h0]
      have hnhds : Icc s₀ (s₀ + 1) ∈ 𝓝[≥] s₀ :=
        Icc_mem_nhdsGE (by linarith)
      have hae_mem : ∀ᵐ x ∂μ_band, x ∈ B0579.cell c ∩ bandSet := by
        dsimp only [μ_band, μ_c]
        rw [Measure.restrict_restrict hband_meas]
        exact (ae_restrict_mem (hband_meas.inter (measurableSet_Ico.prod MeasurableSet.univ))).mono
          fun x hx => hx.symm
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x => 2 * M_v * ‖u s₀ x j‖) ?_ ?_ (hu0_band_int.norm.const_mul (2 * M_v)) ?_
      · filter_upwards [hnhds] with s hs
        have hs0 : 0 ≤ s := hs₀.trans hs.1
        have hcs : Continuous (fun x => ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp
            ((((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
              tr.isTrain.smooth_v.continuousOn).comp_continuous
                (continuous_const.prodMk continuous_id) (fun _ => ⟨hs0, trivial⟩)).sub
            (((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
              tr.isTrain.smooth_v.continuousOn).comp_continuous
                (continuous_const.prodMk continuous_id) (fun _ => ⟨hs₀, trivial⟩)))
        exact hcs.aestronglyMeasurable.mul hu0_band_int.aestronglyMeasurable
      · filter_upwards [hnhds] with s hs
        filter_upwards [hae_mem] with x hx
        have hx_box : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(N : ℝ)) (N : ℝ) :=
          ⟨⟨hx.1.1.1, hx.1.1.2.le⟩, by simpa [bandSet, abs_le] using hx.2⟩
        have hb_s : |tr.v s x i| ≤ M_v :=
          (Real.norm_eq_abs _ ▸ hM_box (s, x) ⟨hs, hx_box⟩).trans (le_max_left _ _)
        have hb_0 : |tr.v s₀ x i| ≤ M_v :=
          (Real.norm_eq_abs _ ▸ hM_box (s₀, x) ⟨⟨le_rfl, by linarith⟩, hx_box⟩).trans
            (le_max_left _ _)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hdiff_le : |tr.v s x i - tr.v s₀ x i| ≤ 2 * M_v := by
          have := abs_sub (tr.v s x i) (tr.v s₀ x i); linarith
        exact mul_le_mul_of_nonneg_right hdiff_le (norm_nonneg _)
      · filter_upwards [hae_mem] with x _
        have hcont_t : ContinuousWithinAt
            (fun s => ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) (Ici s₀) s₀ := by
          have hc1_t : ContinuousWithinAt (fun s => tr.v s x i) (Ici s₀) s₀ :=
            (((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
              tr.isTrain.smooth_v.continuousOn).comp
              (continuous_id.prodMk continuous_const).continuousOn
              (fun s hs => ⟨hs₀.trans hs, trivial⟩)) s₀ (mem_Ici.2 le_rfl)
          exact ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
            (hc1_t.sub continuousWithinAt_const)).mul continuousWithinAt_const)
        simpa using hcont_t.tendsto
    filter_upwards [self_mem_nhdsWithin,
      (Metric.tendsto_nhds.1 hband_lim) (ε / 2) (half_pos hε)] with s hs hband_s
    have hs0 : 0 ≤ s := hs₀.trans hs
    obtain ⟨hvs_mem, hvs_le⟩ := memLp_train_coord_of_cellL2 hs0 tr
      (lt_of_le_of_lt (hv_bd s hs0) ENNReal.ofReal_lt_top) i
    obtain ⟨hv0_mem, hv0_le⟩ := memLp_train_coord_of_cellL2 hs₀ tr
      (lt_of_le_of_lt (hv_bd s₀ hs₀) ENNReal.ofReal_lt_top) i
    have hvdiff_mem : MemLp (fun x => tr.v s x i - tr.v s₀ x i) 2 μ_c := hvs_mem.sub hv0_mem
    have hvdiff_le : (eLpNorm (fun x => tr.v s x i - tr.v s₀ x i) 2 μ_c).toReal ≤ 2 * C_L2 := by
      have he : eLpNorm (fun x => tr.v s x i - tr.v s₀ x i) 2 μ_c ≤
          ENNReal.ofReal (2 * C_L2) := by
        calc eLpNorm (fun x => tr.v s x i - tr.v s₀ x i) 2 μ_c
            ≤ eLpNorm (fun x => tr.v s x i) 2 μ_c + eLpNorm (fun x => tr.v s₀ x i) 2 μ_c :=
              eLpNorm_sub_le hvs_mem.1 hv0_mem.1 one_le_two
          _ ≤ ENNReal.ofReal C_L2 + ENNReal.ofReal C_L2 :=
              add_le_add (hvs_le.trans (hv_bd s hs0)) (hv0_le.trans (hv_bd s₀ hs₀))
          _ = ENNReal.ofReal (2 * C_L2) := by
              rw [← ENNReal.ofReal_add hC_L2.le hC_L2.le]; ring_nf
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) he
    have hfull_int : Integrable (fun x => ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) μ_c :=
      hvdiff_mem.ofReal.integrable_mul hu0
    have hsplit_int : ∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j ∂μ_c =
        (∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j ∂μ_band) +
          ∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) *
            (tailSet N).indicator (fun z => u s₀ z j) x ∂μ_c := by
      rw [← integral_add_compl (μ := μ_c) hband_meas hfull_int, hband_compl]
      congr 1
      rw [← integral_indicator (htail_meas N)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tailSet N <;> simp [hx]
    have htail_cs : ‖∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) *
        (tailSet N).indicator (fun z => u s₀ z j) x ∂μ_c‖ ≤ 2 * C_L2 * δ :=
      (norm_integral_mul_le_eLpNorm_two hvdiff_mem hu0_tail_mem).trans
        (mul_le_mul hvdiff_le hu0_tail_le ENNReal.toReal_nonneg (by positivity))
    have h2CL2_δ : 2 * C_L2 * δ < ε / 2 := by
      dsimp [δ]
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    rw [dist_zero_right] at hband_s ⊢
    rw [hsplit_int]
    calc ‖(∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j ∂μ_band) +
            ∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) *
              (tailSet N).indicator (fun z => u s₀ z j) x ∂μ_c‖
        ≤ ‖∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j ∂μ_band‖ +
            ‖∫ x, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) *
              (tailSet N).indicator (fun z => u s₀ z j) x ∂μ_c‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hband_s (htail_cs.trans_lt h2CL2_δ)
      _ = ε := add_halves ε
  -- Combine `hterm1` and `hterm2`
  have hsum : Tendsto
      (fun s => (∫ x in B0579.cell c, ((tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) +
        ((∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * (u s x j - u s₀ x j)) +
          ∫ x in B0579.cell c, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j))
      (𝓝[≥] s₀)
      (𝓝 (∫ x in B0579.cell c, ((tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j)) := by
    simpa using tendsto_const_nhds.add (hterm1.add hterm2)
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 ≤ s := hs₀.trans hs
  obtain ⟨hvs_mem, _⟩ := memLp_train_coord_of_cellL2 hs0 tr
    (lt_of_le_of_lt (hv_bd s hs0) ENNReal.ofReal_lt_top) i
  obtain ⟨hv0_mem, _⟩ := memLp_train_coord_of_cellL2 hs₀ tr
    (lt_of_le_of_lt (hv_bd s₀ hs₀) ENNReal.ofReal_lt_top) i
  have i_s_s : IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u s x j) (B0579.cell c) :=
    hvs_mem.ofReal.integrable_mul ((hw.biotSavart s hs0).1 j)
  have i_s_0 : IntegrableOn (fun x => ((tr.v s x i : ℝ) : ℂ) * u s₀ x j) (B0579.cell c) :=
    hvs_mem.ofReal.integrable_mul ((hw.biotSavart s₀ hs₀).1 j)
  have i_0_0 : IntegrableOn (fun x => ((tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) (B0579.cell c) :=
    hv0_mem.ofReal.integrable_mul ((hw.biotSavart s₀ hs₀).1 j)
  have eq1 : (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * (u s x j - u s₀ x j)) =
      (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s x j) -
        ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s₀ x j := by
    have hp : (fun x => ((tr.v s x i : ℝ) : ℂ) * (u s x j - u s₀ x j)) =
        fun x => ((tr.v s x i : ℝ) : ℂ) * u s x j - ((tr.v s x i : ℝ) : ℂ) * u s₀ x j := by
      funext x; ring
    rw [hp, integral_sub i_s_s i_s_0]
  have eq2 : (∫ x in B0579.cell c, ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) =
      (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u s₀ x j) -
        ∫ x in B0579.cell c, ((tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j := by
    have hp : (fun x => ((tr.v s x i - tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j) =
        fun x => ((tr.v s x i : ℝ) : ℂ) * u s₀ x j - ((tr.v s₀ x i : ℝ) : ℂ) * u s₀ x j := by
      funext x; push_cast; ring
    rw [hp, integral_sub i_s_0 i_0_0]
  rw [eq1, eq2]; ring

/-- Any function `g : ℝ → ℂ` that is right-continuous at every `s > 0` equals a globally
`StronglyMeasurable` function on `Ioi 0` (via dyadic ceiling step approximations). -/
lemma stronglyMeasurable_posIndicator_of_rightContinuous {g : ℝ → ℂ}
    (hrc : ∀ s : ℝ, 0 < s → ContinuousWithinAt g (Ici s) s) :
    StronglyMeasurable (fun s : ℝ => if 0 < s then g s else 0) := by
  let approx : ℕ → ℝ → ℂ := fun n s =>
    if 0 < s then g ((⌈(2 : ℝ) ^ n * s⌉₊ : ℝ) / (2 : ℝ) ^ n) else 0
  have hmeas_n : ∀ n : ℕ, StronglyMeasurable (approx n) := fun n => by
    have hm_ceil : Measurable (fun s : ℝ => ⌈(2 : ℝ) ^ n * s⌉₊) :=
      Nat.measurable_ceil.comp (measurable_const.mul measurable_id)
    have hm_eval : Measurable (fun k : ℕ => g ((k : ℝ) / (2 : ℝ) ^ n)) :=
      measurable_of_countable _
    exact ((hm_eval.comp hm_ceil).piecewise (measurableSet_Ioi) measurable_const).stronglyMeasurable
  refine stronglyMeasurable_of_tendsto atTop hmeas_n (tendsto_pi_nhds.2 fun s => ?_)
  by_cases hs : 0 < s
  · simp only [approx, hs, ↓reduceIte]
    have htn : Tendsto (fun n : ℕ => (⌈(2 : ℝ) ^ n * s⌉₊ : ℝ) / (2 : ℝ) ^ n) atTop (𝓝[≥] s) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have hsq : Tendsto (fun n : ℕ => s + (1 / 2 : ℝ) ^ n) atTop (𝓝 (s + 0)) :=
          tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
        rw [add_zero] at hsq
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
          (fun n => ?_) (fun n => ?_)
        · have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          rw [le_div_iff₀ h2n, mul_comm]
          exact Nat.le_ceil _
        · have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
          have hlt := (Nat.ceil_lt_add_one (mul_pos h2n hs).le).le
          rw [div_le_iff₀ h2n]
          have h12 : (s + (1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n = (2 : ℝ) ^ n * s + 1 := by
            have hmul : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
              rw [← mul_pow]; norm_num
            calc (s + (1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n
                = s * (2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n := add_mul _ _ _
              _ = (2 : ℝ) ^ n * s + 1 := by rw [hmul, mul_comm]
          linarith
      · have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        rw [mem_Ici, le_div_iff₀ h2n, mul_comm]
        exact Nat.le_ceil _
    exact (hrc s hs).tendsto.comp htn
  · simp only [approx, hs, ↓reduceIte]
    exact tendsto_const_nhds

lemma aestronglyMeasurable_on_subset_Ioi_of_rightContinuous
    {g : ℝ → ℂ} {A : Set ℝ} (hA : A ⊆ Ioi 0) (hmA : MeasurableSet A)
    (hrc : ∀ s : ℝ, 0 < s → ContinuousWithinAt g (Ici s) s) :
    AEStronglyMeasurable g (volume.restrict A) := by
  have hsm := (stronglyMeasurable_posIndicator_of_rightContinuous hrc).aestronglyMeasurable
    (μ := volume.restrict A)
  refine hsm.congr ?_
  filter_upwards [ae_restrict_mem hmA] with s hs
  have hpos : 0 < s := hA hs
  simp [hpos]

/-! ## 2. Planar angular-two symmetry and exact vanishing of `D_plan` and `R_plan` -/

lemma planarMode_toPlane_rotation (f : Profile) (u : Circle) (z : ℂ) :
    planarMode f (UnforcedLeray.B0009.toPlane (rotation u z)) =
      (u : ℂ) ^ 2 * planarMode f (UnforcedLeray.B0009.toPlane z) := by
  have hrot_eq : rotation u z = (u : ℂ) * z := rotation_apply u z
  have hsq_z : (UnforcedLeray.B0009.toPlane z).1 ^ 2 + (UnforcedLeray.B0009.toPlane z).2 ^ 2 =
      ‖z‖ ^ 2 := by
    dsimp only [UnforcedLeray.B0009.toPlane]
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq_uz : (UnforcedLeray.B0009.toPlane (rotation u z)).1 ^ 2 +
      (UnforcedLeray.B0009.toPlane (rotation u z)).2 ^ 2 = ‖z‖ ^ 2 := by
    dsimp only [UnforcedLeray.B0009.toPlane]
    have hnsq : (rotation u z).re ^ 2 + (rotation u z).im ^ 2 = ‖rotation u z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hnsq, (rotation u).norm_map z]
  have hre_im : ∀ w : ℂ, ((UnforcedLeray.B0009.toPlane w).1 : ℂ) +
      ((UnforcedLeray.B0009.toPlane w).2 : ℂ) * Complex.I = w := fun w => by
    apply Complex.ext <;> simp [UnforcedLeray.B0009.toPlane]
  unfold planarMode angTwo
  rw [hsq_uz, hsq_z, hre_im (rotation u z), hre_im z, hrot_eq]
  ring

lemma kernel_pm_eq (w : ℂ) :
    UnforcedLeray.B0009.kernel 0 w + Complex.I * UnforcedLeray.B0009.kernel 1 w =
      (((2 * Real.pi * ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * (Complex.I * w) ∧
    UnforcedLeray.B0009.kernel 0 w - Complex.I * UnforcedLeray.B0009.kernel 1 w =
      (((2 * Real.pi * ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * (-Complex.I * conj w) := by
  have hp : ((-w.im : ℝ) : ℂ) + Complex.I * ((w.re : ℝ) : ℂ) = Complex.I * w := by
    apply Complex.ext <;> simp
  have hm : ((-w.im : ℝ) : ℂ) - Complex.I * ((w.re : ℝ) : ℂ) = -Complex.I * conj w := by
    apply Complex.ext <;> simp
  constructor
  · simp only [UnforcedLeray.B0009.kernel, UnforcedLeray.B0009.perpComp, div_eq_mul_inv,
      Complex.ofReal_mul]
    linear_combination (((2 * Real.pi * ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * hp
  · simp only [UnforcedLeray.B0009.kernel, UnforcedLeray.B0009.perpComp, div_eq_mul_inv,
      Complex.ofReal_mul]
    linear_combination (((2 * Real.pi * ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * hm

lemma biotSavart_pm_rotation {g : ℂ → ℂ} (hgc : Continuous g) {K : ℝ}
    (hgK : ∀ z, ‖g z‖ ≤ K) (hgi : Integrable g) (u : Circle)
    (hg_rot : ∀ z : ℂ, g (rotation u z) = (u : ℂ) ^ 2 * g z) (y : ℂ) :
    (UnforcedLeray.B0009.biotSavart g 0 (rotation u y) +
        Complex.I * UnforcedLeray.B0009.biotSavart g 1 (rotation u y) =
      (u : ℂ) ^ 3 * (UnforcedLeray.B0009.biotSavart g 0 y +
        Complex.I * UnforcedLeray.B0009.biotSavart g 1 y)) ∧
    (UnforcedLeray.B0009.biotSavart g 0 (rotation u y) -
        Complex.I * UnforcedLeray.B0009.biotSavart g 1 (rotation u y) =
      (u : ℂ) * (UnforcedLeray.B0009.biotSavart g 0 y -
        Complex.I * UnforcedLeray.B0009.biotSavart g 1 y)) := by
  have hi0_uy := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := 0) (rotation u y) hgc hgK hgi
  have hi1_uy := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := 1) (rotation u y) hgc hgK hgi
  have hi0_y := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := 0) y hgc hgK hgi
  have hi1_y := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := 1) y hgc hgK hgi
  have hmp := (rotation u).measurePreserving
  have hme := (rotation u).toHomeomorph.measurableEmbedding
  have hu_conj : conj (u : ℂ) * (u : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe u, one_pow,
      Complex.ofReal_one]
  constructor
  · rw [UnforcedLeray.B0009.biotSavart_apply, UnforcedLeray.B0009.biotSavart_apply,
      UnforcedLeray.B0009.biotSavart_apply, UnforcedLeray.B0009.biotSavart_apply,
      ← integral_const_mul, ← integral_add hi0_uy (hi1_uy.const_mul Complex.I),
      ← integral_const_mul Complex.I, ← integral_add hi0_y (hi1_y.const_mul Complex.I),
      ← integral_const_mul ((u : ℂ) ^ 3)]
    rw [← hmp.integral_comp hme]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only [Function.comp_apply]
    have hsub : rotation u y - rotation u z = rotation u (y - z) :=
      ((rotation u).map_sub y z).symm
    have hnrm : ‖rotation u (y - z)‖ = ‖y - z‖ := (rotation u).norm_map (y - z)
    have hrot_app : rotation u (y - z) = (u : ℂ) * (y - z) := rotation_apply u (y - z)
    have hk_uy := (kernel_pm_eq (rotation u (y - z))).1
    have hk_y := (kernel_pm_eq (y - z)).1
    have h1 : UnforcedLeray.B0009.kernel 0 (rotation u (y - z)) * g (rotation u z) +
          Complex.I * (UnforcedLeray.B0009.kernel 1 (rotation u (y - z)) * g (rotation u z)) =
        (UnforcedLeray.B0009.kernel 0 (rotation u (y - z)) +
          Complex.I * UnforcedLeray.B0009.kernel 1 (rotation u (y - z))) * g (rotation u z) := by
      ring
    have h2 : UnforcedLeray.B0009.kernel 0 (y - z) * g z +
          Complex.I * (UnforcedLeray.B0009.kernel 1 (y - z) * g z) =
        (UnforcedLeray.B0009.kernel 0 (y - z) +
          Complex.I * UnforcedLeray.B0009.kernel 1 (y - z)) * g z := by
      ring
    rw [hsub, h1, h2, hk_uy, hk_y, hnrm, hrot_app, hg_rot z]
    ring
  · rw [UnforcedLeray.B0009.biotSavart_apply, UnforcedLeray.B0009.biotSavart_apply,
      UnforcedLeray.B0009.biotSavart_apply, UnforcedLeray.B0009.biotSavart_apply,
      ← integral_const_mul Complex.I, ← integral_sub hi0_uy (hi1_uy.const_mul Complex.I),
      ← integral_const_mul Complex.I, ← integral_sub hi0_y (hi1_y.const_mul Complex.I),
      ← integral_const_mul (u : ℂ)]
    rw [← hmp.integral_comp hme]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only [Function.comp_apply]
    have hsub : rotation u y - rotation u z = rotation u (y - z) :=
      ((rotation u).map_sub y z).symm
    have hnrm : ‖rotation u (y - z)‖ = ‖y - z‖ := (rotation u).norm_map (y - z)
    have hrot_app : rotation u (y - z) = (u : ℂ) * (y - z) := rotation_apply u (y - z)
    have hk_uy := (kernel_pm_eq (rotation u (y - z))).2
    have hk_y := (kernel_pm_eq (y - z)).2
    have h1 : UnforcedLeray.B0009.kernel 0 (rotation u (y - z)) * g (rotation u z) -
          Complex.I * (UnforcedLeray.B0009.kernel 1 (rotation u (y - z)) * g (rotation u z)) =
        (UnforcedLeray.B0009.kernel 0 (rotation u (y - z)) -
          Complex.I * UnforcedLeray.B0009.kernel 1 (rotation u (y - z))) * g (rotation u z) := by
      ring
    have h2 : UnforcedLeray.B0009.kernel 0 (y - z) * g z -
          Complex.I * (UnforcedLeray.B0009.kernel 1 (y - z) * g z) =
        (UnforcedLeray.B0009.kernel 0 (y - z) -
          Complex.I * UnforcedLeray.B0009.kernel 1 (y - z)) * g z := by
      ring
    rw [hsub, h1, h2, hk_uy, hk_y, hnrm, hrot_app, map_mul, hg_rot z]
    linear_combination (((2 * Real.pi * ‖y - z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (-Complex.I * conj (y - z) * ((u : ℂ) * g z)) * hu_conj

lemma v0_pm_toPlane_eq (y : ℂ) :
    ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 0 : ℝ) : ℂ) +
        Complex.I * ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 1 : ℝ) : ℂ) =
      ((UnforcedLeray.GaussianVortex.radialOmega ‖y‖ : ℝ) : ℂ) * (Complex.I * y) ∧
    ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 0 : ℝ) : ℂ) -
        Complex.I * ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 1 : ℝ) : ℂ) =
      ((UnforcedLeray.GaussianVortex.radialOmega ‖y‖ : ℝ) : ℂ) * (-Complex.I * conj y) := by
  have hg : UnforcedLeray.Train.gauss0 (UnforcedLeray.B0009.toPlane y) =
      UnforcedLeray.GaussianVortex.radialOmega ‖y‖ := by
    rw [EulerErrorEig.gauss0_eq_radialOmega, EulerErrorEig.planeToC_toPlane]
  have hv0 : UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 0 =
      UnforcedLeray.GaussianVortex.radialOmega ‖y‖ * (-y.im) := by
    rw [UnforcedLeray.Train.v0, PiLp.smul_apply, smul_eq_mul, hg]
    rfl
  have hv1 : UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 1 =
      UnforcedLeray.GaussianVortex.radialOmega ‖y‖ * y.re := by
    rw [UnforcedLeray.Train.v0, PiLp.smul_apply, smul_eq_mul, hg]
    rfl
  have hp : -((y.im : ℝ) : ℂ) + Complex.I * ((y.re : ℝ) : ℂ) = Complex.I * y := by
    apply Complex.ext <;> simp
  have hm : -((y.im : ℝ) : ℂ) - Complex.I * ((y.re : ℝ) : ℂ) = -Complex.I * conj y := by
    apply Complex.ext <;> simp
  rw [hv0, hv1]
  push_cast
  exact ⟨by linear_combination ((UnforcedLeray.GaussianVortex.radialOmega ‖y‖ : ℝ) : ℂ) * hp,
    by linear_combination ((UnforcedLeray.GaussianVortex.radialOmega ‖y‖ : ℝ) : ℂ) * hm⟩

lemma integral_zero_of_rotation_neg {F : ℂ → ℂ} (u : Circle)
    (hrot : ∀ y : ℂ, F (rotation u y) = -F y) :
    ∫ y : ℂ, F y = 0 := by
  have h1 : ∫ y : ℂ, F y = ∫ y : ℂ, F (rotation u y) :=
    ((rotation u).measurePreserving.integral_comp (rotation u).toHomeomorph.measurableEmbedding F).symm
  simp_rw [hrot, integral_neg] at h1
  linear_combination (2 : ℂ)⁻¹ * h1

/-- For any continuous Gaussian-decaying angular-two planar vorticity `e = planarMode f`,
all planar stress defect integrals `D_plan` and `R_plan` against `Train.v0` vanish identically. -/
lemma planar_stressDefect_integral_eq_zero {f : Profile}
    (he_cont : Continuous (planarMode f)) {C_e : ℝ} (hCe : 0 ≤ C_e)
    (he_bd : ∀ z : ℝ × ℝ, ‖planarMode f z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :
    ∫ x : ℝ × ℝ,
      ((2 * (((UnforcedLeray.Train.v0 x 0 : ℝ) : ℂ) * kerVelPlanarCx (planarMode f) x 0) +
          2 * (((UnforcedLeray.Train.v0 x 1 : ℝ) : ℂ) * kerVelPlanarCx (planarMode f) x 1)) -
        3 * (2 * (((UnforcedLeray.Train.v0 x 1 : ℝ) : ℂ) * kerVelPlanarCx (planarMode f) x 1) -
          Complex.I * ((((UnforcedLeray.Train.v0 x 0 : ℝ) : ℂ) *
              kerVelPlanarCx (planarMode f) x 1) +
            (((UnforcedLeray.Train.v0 x 1 : ℝ) : ℂ) *
              kerVelPlanarCx (planarMode f) x 0)))) = 0 := by
  set g : ℂ → ℂ := fun z => planarMode f (UnforcedLeray.B0009.toPlane z)
  have hgc : Continuous g :=
    he_cont.comp (Complex.continuous_re.prodMk Complex.continuous_im)
  have he_sup : ∀ z : ℝ × ℝ, ‖planarMode f z‖ ≤ C_e := fun z =>
    (he_bd z).trans (mul_le_of_le_one_right hCe
      (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])))
  have he_int : Integrable (planarMode f) :=
    Integrable.mono' ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul C_e)
      he_cont.aestronglyMeasurable (Eventually.of_forall he_bd)
  have hgi : Integrable g := EulerErrorTail.integrable_toPlane he_int
  have hgK : ∀ z : ℂ, ‖g z‖ ≤ C_e := fun z => he_sup _
  -- Uniform bound and measurability of `B0009.biotSavart g i`
  set C_bs : ℝ := C_e * ((∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖) +
      (∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖)) +
    (2 * Real.pi)⁻¹ * ∫ t : ℂ, ‖g t‖
  have hCbs_nn : 0 ≤ C_bs := by
    dsimp [C_bs]
    have i0 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have i1 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have ig : 0 ≤ ∫ t : ℂ, ‖g t‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  have hbs_bd : ∀ (i : Fin 2) (y : ℂ), ‖UnforcedLeray.B0009.biotSavart g i y‖ ≤ C_bs := by
    intro i y
    refine (EulerErrorTail.norm_biotSavart_le hgc hgK hgi i y).trans ?_
    dsimp [C_bs]
    have i0 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 0 t‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have i1 : 0 ≤ ∫ t in Metric.ball (0 : ℂ) 1, ‖UnforcedLeray.B0009.kernel 1 t‖ :=
      integral_nonneg fun _ => norm_nonneg _
    fin_cases i
    · simp only [Fin.zero_eta]; nlinarith
    · simp only [Fin.mk_one]; nlinarith
  have hbs_meas : ∀ i : Fin 2, StronglyMeasurable (UnforcedLeray.B0009.biotSavart g i) := by
    intro i
    have hfun : UnforcedLeray.B0009.biotSavart g i =
        fun y : ℂ => ∫ z : ℂ, UnforcedLeray.B0009.kernel i (y - z) * g z := by
      funext y; exact UnforcedLeray.B0009.biotSavart_apply g i y
    rw [hfun]
    exact StronglyMeasurable.integral_prod_right'
      (((UnforcedLeray.B0009.measurable_kernel i).comp
        (measurable_fst.sub measurable_snd)).mul (hgc.measurable.comp measurable_snd)
        |>.stronglyMeasurable)
  --Integrability of `V_a * U_b` on `ℂ`
  obtain ⟨A_v0, hAv0, hbv0⟩ := EulerErrorTail.v0_gauss
  let V0 : ℂ → ℂ := fun y => ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 0 : ℝ) : ℂ)
  let V1 : ℂ → ℂ := fun y => ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) 1 : ℝ) : ℂ)
  let U0 : ℂ → ℂ := UnforcedLeray.B0009.biotSavart g 0
  let U1 : ℂ → ℂ := UnforcedLeray.B0009.biotSavart g 1
  have hVi : ∀ i : Fin 2, Integrable (fun y : ℂ =>
      ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) i : ℝ) : ℂ)) := by
    intro i
    have hcont_i : Continuous (fun x : ℝ × ℝ => ((UnforcedLeray.Train.v0 x i : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
          (UnforcedLeray.Train.contDiff_v0 (n := 1)).continuous)
    have hint_plane : Integrable (fun x : ℝ × ℝ => ((UnforcedLeray.Train.v0 x i : ℝ) : ℂ)) :=
      Integrable.mono' ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul A_v0)
        hcont_i.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Complex.norm_real]
          exact (PiLp.norm_apply_le (UnforcedLeray.Train.v0 z) i).trans (hbv0 z))
    exact EulerErrorTail.integrable_toPlane hint_plane
  have hVUi : ∀ (i j : Fin 2), Integrable (fun y : ℂ =>
      ((UnforcedLeray.Train.v0 (UnforcedLeray.B0009.toPlane y) i : ℝ) : ℂ) *
        UnforcedLeray.B0009.biotSavart g j y) := by
    intro i j
    refine Integrable.mono' ((hVi i).norm.const_mul C_bs)
      ((hVi i).aestronglyMeasurable.mul (hbs_meas j).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbs_bd j y) (norm_nonneg _)
  let Vplus : ℂ → ℂ := fun y => V0 y + Complex.I * V1 y
  let Vminus : ℂ → ℂ := fun y => V0 y - Complex.I * V1 y
  let Uplus : ℂ → ℂ := fun y => U0 y + Complex.I * U1 y
  let Uminus : ℂ → ℂ := fun y => U0 y - Complex.I * U1 y
  let P1 : ℂ → ℂ := fun y => Vminus y * Uplus y
  let P2 : ℂ → ℂ := fun y => Vplus y * Uminus y
  let P3 : ℂ → ℂ := fun y => Vplus y * Uplus y
  have hP1_int : Integrable P1 := by
    have hrew : P1 = fun y => (V0 y * U0 y + V1 y * U1 y) +
        Complex.I * (V0 y * U1 y - V1 y * U0 y) := by
      funext y; dsimp [P1, Vminus, Uplus]; ring_nf; rw [Complex.I_sq]; ring
    rw [hrew]
    exact ((hVUi 0 0).add (hVUi 1 1)).add (((hVUi 0 1).sub (hVUi 1 0)).const_mul Complex.I)
  have hP2_int : Integrable P2 := by
    have hrew : P2 = fun y => (V0 y * U0 y + V1 y * U1 y) -
        Complex.I * (V0 y * U1 y - V1 y * U0 y) := by
      funext y; dsimp [P2, Vplus, Uminus]; ring_nf; rw [Complex.I_sq]; ring
    rw [hrew]
    exact ((hVUi 0 0).add (hVUi 1 1)).sub (((hVUi 0 1).sub (hVUi 1 0)).const_mul Complex.I)
  have hP3_int : Integrable P3 := by
    have hrew : P3 = fun y => (V0 y * U0 y - V1 y * U1 y) +
        Complex.I * (V0 y * U1 y + V1 y * U0 y) := by
      funext y; dsimp [P3, Vplus, Uplus]; ring_nf; rw [Complex.I_sq]; ring
    rw [hrew]
    exact ((hVUi 0 0).sub (hVUi 1 1)).add (((hVUi 0 1).add (hVUi 1 0)).const_mul Complex.I)
  -- Rotation laws of `P1`, `P2`, `P3` under any `u : Circle`
  have hP_rot : ∀ (u : Circle) (y : ℂ),
      P1 (rotation u y) = (u : ℂ) ^ 2 * P1 y ∧
      P2 (rotation u y) = (u : ℂ) ^ 2 * P2 y ∧
      P3 (rotation u y) = (u : ℂ) ^ 4 * P3 y := by
    intro u y
    have hg_u : ∀ z : ℂ, g (rotation u z) = (u : ℂ) ^ 2 * g z :=
      planarMode_toPlane_rotation f u
    obtain ⟨hUp, hUm⟩ := biotSavart_pm_rotation hgc hgK hgi u hg_u y
    have hVp : Vplus (rotation u y) = (u : ℂ) * Vplus y := by
      dsimp only [Vplus, V0, V1]
      rw [(v0_pm_toPlane_eq (rotation u y)).1, (v0_pm_toPlane_eq y).1,
        (rotation u).norm_map y, rotation_apply]
      ring
    have hVm : Vminus (rotation u y) = conj (u : ℂ) * Vminus y := by
      dsimp only [Vminus, V0, V1]
      rw [(v0_pm_toPlane_eq (rotation u y)).2, (v0_pm_toPlane_eq y).2,
        (rotation u).norm_map y, rotation_apply, map_mul]
      ring
    have hu_conj : conj (u : ℂ) * (u : ℂ) = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe u, one_pow,
        Complex.ofReal_one]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [P1]
      rw [hVm, show Uplus (rotation u y) = (u : ℂ) ^ 3 * Uplus y from hUp]
      linear_combination (u : ℂ) ^ 2 * Vminus y * Uplus y * hu_conj
    · dsimp only [P2]
      rw [hVp, show Uminus (rotation u y) = (u : ℂ) * Uminus y from hUm]
      ring
    · dsimp only [P3]
      rw [hVp, show Uplus (rotation u y) = (u : ℂ) ^ 3 * Uplus y from hUp]
      ring
  -- `u4 = Circle.exp (π / 2)` (`u4 ^ 2 = -1`) and `u8 = Circle.exp (π / 4)` (`u8 ^ 4 = -1`)
  let u4 : Circle := Circle.exp (Real.pi / 2)
  have hu4_sq : (u4 : ℂ) ^ 2 = -1 := by
    rw [Circle.coe_exp, ← Complex.exp_nat_mul]
    have heq : (2 : ℕ) * ((Real.pi / 2 : ℝ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.exp_pi_mul_I]
  let u8 : Circle := Circle.exp (Real.pi / 4)
  have hu8_pow4 : (u8 : ℂ) ^ 4 = -1 := by
    rw [Circle.coe_exp, ← Complex.exp_nat_mul]
    have heq : (4 : ℕ) * ((Real.pi / 4 : ℝ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.exp_pi_mul_I]
  have hI1 : ∫ y : ℂ, P1 y = 0 :=
    integral_zero_of_rotation_neg u4 fun y => by rw [(hP_rot u4 y).1, hu4_sq, neg_one_mul]
  have hI2 : ∫ y : ℂ, P2 y = 0 :=
    integral_zero_of_rotation_neg u4 fun y => by rw [(hP_rot u4 y).2.1, hu4_sq, neg_one_mul]
  have hI3 : ∫ y : ℂ, P3 y = 0 :=
    integral_zero_of_rotation_neg u8 fun y => by rw [(hP_rot u8 y).2.2, hu8_pow4, neg_one_mul]
  -- Transfer from `ℝ × ℝ` to `ℂ` via `EulerErrorTail.integral_planeToC`
  have htoPlane_planeToC : ∀ x : ℝ × ℝ, UnforcedLeray.B0009.toPlane (planeToC x) = x := fun x => by
    ext <;> simp [UnforcedLeray.B0009.toPlane, planeToC]
  let G_c : ℂ → ℂ := fun y =>
    -(2 : ℂ)⁻¹ * (P1 y + P2 y) + 3 * P3 y
  have hGc_zero : ∫ y : ℂ, G_c y = 0 := by
    have h12 : Integrable (fun y : ℂ => P1 y + P2 y) := hP1_int.add hP2_int
    dsimp only [G_c]
    rw [integral_add (h12.const_mul _) (hP3_int.const_mul _),
      integral_const_mul, integral_add hP1_int hP2_int, integral_const_mul,
      hI1, hI2, hI3]
    ring
  rw [← hGc_zero, ← EulerErrorTail.integral_planeToC G_c]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [G_c, P1, P2, P3, Vplus, Vminus, Uplus, Uminus, V0, V1, U0, U1, g, kerVelPlanarCx]
  rw [htoPlane_planeToC x]
  ring_nf; rw [Complex.I_sq]; ring


/-! ## 3. `m = 0` Hermite synthesis and compact clock window `[s_B, s_r]` -/

section HermiteSynth

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0121

theorem norm_J_sq_eq_integral (ψ : S2) :
    ‖J ψ‖ ^ 2 = ∫ z : ℝ × ℝ, ‖ψ z‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_J]
  have h : pairS ψ ψ = ((∫ z : ℝ × ℝ, ‖ψ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [pairS, ← integral_complex_ofReal]
    congr 1; funext z; rw [Complex.conj_mul']; norm_cast
  simp [h]

theorem norm_J_dop_sq_le_Aop (i : Fin 2) (φ : S2) :
    ‖J (dop i φ)‖ ^ 2 ≤ ‖J (Aop i φ)‖ ^ 2 := by
  have hre_norm : ∀ ψ : S2, (⟪J ψ, J ψ⟫_ℂ).re = ‖J ψ‖ ^ 2 := fun ψ => by
    simpa using (@norm_sq_eq_re_inner ℂ _ _ _ _ (J ψ)).symm
  have hexp : ‖J (Aop i φ)‖ ^ 2 =
      ‖J (dop i φ)‖ ^ 2 + 4⁻¹ * ‖J φ‖ ^ 2 + 16⁻¹ * ‖J (B0121.X i φ)‖ ^ 2 := by
    rw [← hre_norm (Aop i φ), inner_Aop, Bop_Aop, map_add, map_add, map_neg,
      map_smul, map_smul, inner_add_right, inner_add_right, inner_neg_right,
      inner_smul_right, inner_smul_right]
    have h1 : (⟪J φ, J (dop i (dop i φ))⟫_ℂ).re = -‖J (dop i φ)‖ ^ 2 := by
      have hp : pairS φ (dop i (dop i φ)) = -pairS (dop i φ) (dop i φ) := by
        linear_combination pairS_dop i φ (dop i φ)
      rw [inner_J, hp, Complex.neg_re, ← inner_J, hre_norm]
    have h2 : (⟪J φ, J φ⟫_ℂ).re = ‖J φ‖ ^ 2 := hre_norm φ
    have h3 : (⟪J φ, J (B0121.X i (B0121.X i φ))⟫_ℂ).re = ‖J (B0121.X i φ)‖ ^ 2 := by
      rw [inner_J, ← pairS_X i φ (B0121.X i φ), ← inner_J, hre_norm]
    have hc4 : (4⁻¹ : ℂ) = ((4⁻¹ : ℝ) : ℂ) := by norm_num
    have hc16 : (16⁻¹ : ℂ) = ((16⁻¹ : ℝ) : ℂ) := by norm_num
    rw [hc4, hc16]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1, h2, h3]; ring
  rw [hexp]
  have hnn : 0 ≤ 4⁻¹ * ‖J φ‖ ^ 2 + 16⁻¹ * ‖J (B0121.X i φ)‖ ^ 2 := by positivity
  linarith

theorem Aop_zero_dop_one (φ : S2) :
    Aop 0 (dop 1 φ) = dop 1 (Aop 0 φ) := by
  rw [Aop_apply, Aop_apply, map_sub, map_smul, dop_comm 0 1 φ, dop_X 1 0 φ,
    crdL_zero_ev_one, Complex.ofReal_zero, zero_smul, zero_add]

theorem norm_J_dop_dop_sq_le (φ : S2) :
    ‖J (dop 0 (dop 1 φ))‖ ^ 2 ≤ ‖J (Aop 1 (Aop 0 φ))‖ ^ 2 := by
  calc ‖J (dop 0 (dop 1 φ))‖ ^ 2
      ≤ ‖J (Aop 0 (dop 1 φ))‖ ^ 2 := norm_J_dop_sq_le_Aop 0 (dop 1 φ)
    _ = ‖J (dop 1 (Aop 0 φ))‖ ^ 2 := by rw [Aop_zero_dop_one]
    _ ≤ ‖J (Aop 1 (Aop 0 φ))‖ ^ 2 := norm_J_dop_sq_le_Aop 1 (Aop 0 φ)

theorem schwartz_norm_bound (ψ : S2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ, (1 + ‖z‖ ^ 2) * ‖ψ z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := ψ.decay' 0 0
  obtain ⟨C₂, hC₂⟩ := ψ.decay' 2 0
  refine ⟨max C₀ 0 + max C₂ 0, by positivity, fun z => ?_⟩
  have b0 := hC₀ z
  have b2 := hC₂ z
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at b0
  rw [norm_iteratedFDeriv_zero] at b2
  change ‖ψ z‖ ≤ C₀ at b0
  change ‖z‖ ^ 2 * ‖ψ z‖ ≤ C₂ at b2
  have m0 : C₀ ≤ max C₀ 0 := le_max_left _ _
  have m2 : C₂ ≤ max C₂ 0 := le_max_left _ _
  calc (1 + ‖z‖ ^ 2) * ‖ψ z‖ = ‖ψ z‖ + ‖z‖ ^ 2 * ‖ψ z‖ := by ring
    _ ≤ max C₀ 0 + max C₂ 0 := by linarith

theorem integrable_slice_fst (ψ : S2) (y : ℝ) :
    Integrable (fun s : ℝ => ‖ψ (s, y)‖) := by
  obtain ⟨C, _, hb⟩ := schwartz_norm_bound ψ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_norm.comp (ψ.continuous.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hs : s ^ 2 ≤ ‖(s, y)‖ ^ 2 := by
    have hle : |s| ≤ ‖(s, y)‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
    nlinarith [sq_abs s, abs_nonneg s]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s ^ 2)]
  calc ‖ψ (s, y)‖ * (1 + s ^ 2)
      = (1 + s ^ 2) * ‖ψ (s, y)‖ := mul_comm _ _
    _ ≤ (1 + ‖(s, y)‖ ^ 2) * ‖ψ (s, y)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ C := hb (s, y)

theorem integrable_slice_snd (ψ : S2) (x : ℝ) :
    Integrable (fun t : ℝ => ‖ψ (x, t)‖) := by
  obtain ⟨C, _, hb⟩ := schwartz_norm_bound ψ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_norm.comp (ψ.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have ht : t ^ 2 ≤ ‖(x, t)‖ ^ 2 := by
    have hle : |t| ≤ ‖(x, t)‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
    nlinarith [sq_abs t, abs_nonneg t]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  calc ‖ψ (x, t)‖ * (1 + t ^ 2)
      = (1 + t ^ 2) * ‖ψ (x, t)‖ := mul_comm _ _
    _ ≤ (1 + ‖(x, t)‖ ^ 2) * ‖ψ (x, t)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ C := hb (x, t)

theorem integrable_re_mul_slice_fst (ψ₁ ψ₂ : S2) (y : ℝ) :
    Integrable (fun s : ℝ => (ψ₁ (s, y)).re * (ψ₂ (s, y)).re) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ₁
  have hsup : ∀ z, ‖ψ₁ z‖ ≤ C := fun z =>
    (le_mul_of_one_le_left (norm_nonneg _) (by linarith [sq_nonneg ‖z‖])).trans (hb z)
  refine Integrable.mono' ((integrable_slice_fst ψ₂ y).const_mul C)
    (((Complex.continuous_re.comp (ψ₁.continuous.comp (continuous_id.prodMk continuous_const))).mul
      (Complex.continuous_re.comp (ψ₂.continuous.comp (continuous_id.prodMk continuous_const))))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((Complex.abs_re_le_norm _).trans (hsup _))
    (Complex.abs_re_le_norm _) (abs_nonneg _) hC

theorem integrable_re_mul_slice_snd (ψ₁ ψ₂ : S2) (x : ℝ) :
    Integrable (fun t : ℝ => (ψ₁ (x, t)).re * (ψ₂ (x, t)).re) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ₁
  have hsup : ∀ z, ‖ψ₁ z‖ ≤ C := fun z =>
    (le_mul_of_one_le_left (norm_nonneg _) (by linarith [sq_nonneg ‖z‖])).trans (hb z)
  refine Integrable.mono' ((integrable_slice_snd ψ₂ x).const_mul C)
    (((Complex.continuous_re.comp (ψ₁.continuous.comp (continuous_const.prodMk continuous_id))).mul
      (Complex.continuous_re.comp (ψ₂.continuous.comp (continuous_const.prodMk continuous_id))))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((Complex.abs_re_le_norm _).trans (hsup _))
    (Complex.abs_re_le_norm _) (abs_nonneg _) hC

theorem integrable_re_sq (ψ : S2) :
    Integrable (fun z : ℝ × ℝ => (ψ z).re ^ 2) := by
  refine Integrable.mono' (integrable_conj_mul ψ ψ).norm
    ((Complex.continuous_re.comp ψ.continuous).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_conj, ← sq, ← sq_abs ((ψ z).re)]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (ψ z)) 2

theorem hasDerivAt_re_fst (ψ : S2) (s y : ℝ) :
    HasDerivAt (fun x : ℝ => (ψ (x, y)).re) ((dop 0 ψ (s, y)).re) s := by
  have hp : HasDerivAt (fun x : ℝ => (x, y)) (ev 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((ψ.hasFDerivAt (s, y)).comp_hasDerivAt s hp)

theorem hasDerivAt_re_snd (ψ : S2) (x t : ℝ) :
    HasDerivAt (fun y : ℝ => (ψ (x, y)).re) ((dop 1 ψ (x, t)).re) t := by
  have hp : HasDerivAt (fun y : ℝ => (x, y)) (ev 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((ψ.hasFDerivAt (x, t)).comp_hasDerivAt t hp)

theorem re_sq_le_slice_snd (ψ : S2) (x y : ℝ) :
    (ψ (x, y)).re ^ 2 ≤ ∫ t : ℝ, ((ψ (x, t)).re ^ 2 + (dop 1 ψ (x, t)).re ^ 2) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (ψ (x, u)).re ^ 2)
      (2 * (ψ (x, t)).re * (dop 1 ψ (x, t)).re) t := fun t => by
    simpa [pow_one, mul_assoc] using! (hasDerivAt_re_snd ψ x t).fun_pow 2
  have hi0 : Integrable (fun u : ℝ => (ψ (x, u)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd ψ ψ x
  have hi1 : Integrable (fun u : ℝ => 2 * (ψ (x, u)).re * (dop 1 ψ (x, u)).re) := by
    simpa [mul_assoc] using (integrable_re_mul_slice_snd ψ (dop 1 ψ) x).const_mul 2
  have hi_rhs : Integrable (fun t : ℝ => (ψ (x, t)).re ^ 2 + (dop 1 ψ (x, t)).re ^ 2) :=
    hi0.add (by simpa [sq] using integrable_re_mul_slice_snd (dop 1 ψ) (dop 1 ψ) x)
  have h1 := UnforcedLeray.B0151.abs_le_integral_deriv hd hi1 hi0 y
  rw [abs_of_nonneg (sq_nonneg _)] at h1
  refine h1.trans (integral_mono hi1.abs hi_rhs fun t => ?_)
  dsimp only
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (|(ψ (x, t)).re| - |(dop 1 ψ (x, t)).re|),
    sq_abs (ψ (x, t)).re, sq_abs (dop 1 ψ (x, t)).re]

theorem re_sq_le_integral_2d (ψ : S2) (z : ℝ × ℝ) :
    (ψ z).re ^ 2 ≤ ∫ w : ℝ × ℝ,
      ((ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2) := by
  rcases z with ⟨x, y⟩
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => (ψ (u, y)).re ^ 2)
      (2 * (ψ (s, y)).re * (dop 0 ψ (s, y)).re) s := fun s => by
    simpa [pow_one, mul_assoc] using! (hasDerivAt_re_fst ψ s y).fun_pow 2
  have hi0 : Integrable (fun s : ℝ => (ψ (s, y)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_fst ψ ψ y
  have hi1 : Integrable (fun s : ℝ => 2 * (ψ (s, y)).re * (dop 0 ψ (s, y)).re) := by
    simpa [mul_assoc] using (integrable_re_mul_slice_fst ψ (dop 0 ψ) y).const_mul 2
  have hi_mid : Integrable (fun s : ℝ => (ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2) :=
    hi0.add (by simpa [sq] using integrable_re_mul_slice_fst (dop 0 ψ) (dop 0 ψ) y)
  have hstep1 : (ψ (x, y)).re ^ 2 ≤ ∫ s : ℝ, ((ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2) := by
    have h1 := UnforcedLeray.B0151.abs_le_integral_deriv hd hi1 hi0 x
    rw [abs_of_nonneg (sq_nonneg _)] at h1
    refine h1.trans (integral_mono hi1.abs hi_mid fun s => ?_)
    dsimp only
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (|(ψ (s, y)).re| - |(dop 0 ψ (s, y)).re|),
      sq_abs (ψ (s, y)).re, sq_abs (dop 0 ψ (s, y)).re]
  set G : ℝ × ℝ → ℝ := fun w =>
    (ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2
  have hG_int : Integrable G :=
    (((integrable_re_sq ψ).add (integrable_re_sq (dop 1 ψ))).add
      (integrable_re_sq (dop 0 ψ))).add (integrable_re_sq (dop 1 (dop 0 ψ)))
  have hslice_int : Integrable (fun s : ℝ => ∫ t : ℝ, G (s, t)) := hG_int.integral_prod_left
  refine hstep1.trans ?_
  change _ ≤ ∫ z : ℝ × ℝ, G z ∂(volume.prod volume)
  rw [integral_prod G hG_int]
  refine integral_mono hi_mid hslice_int fun s => ?_
  have ha := re_sq_le_slice_snd ψ s y
  have hb := re_sq_le_slice_snd (dop 0 ψ) s y
  have ia1 : Integrable (fun t : ℝ => (ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd ψ ψ s
  have ia2 : Integrable (fun t : ℝ => (dop 1 ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 1 ψ) (dop 1 ψ) s
  have ia : Integrable (fun t : ℝ => (ψ (s, t)).re ^ 2 + (dop 1 ψ (s, t)).re ^ 2) := ia1.add ia2
  have ib1 : Integrable (fun t : ℝ => (dop 0 ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 0 ψ) (dop 0 ψ) s
  have ib2 : Integrable (fun t : ℝ => (dop 1 (dop 0 ψ) (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 1 (dop 0 ψ)) (dop 1 (dop 0 ψ)) s
  have ib : Integrable (fun t : ℝ => (dop 0 ψ (s, t)).re ^ 2 + (dop 1 (dop 0 ψ) (s, t)).re ^ 2) :=
    ib1.add ib2
  calc (ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2
      ≤ (∫ t : ℝ, ((ψ (s, t)).re ^ 2 + (dop 1 ψ (s, t)).re ^ 2)) +
          ∫ t : ℝ, ((dop 0 ψ (s, t)).re ^ 2 + (dop 1 (dop 0 ψ) (s, t)).re ^ 2) := add_le_add ha hb
    _ = ∫ t : ℝ, G (s, t) := by rw [← integral_add ia ib]; congr 1; funext t; dsimp [G]; ring

theorem norm_sq_schwartz_le_Aop (ψ : S2) (z : ℝ × ℝ) :
    ‖ψ z‖ ^ 2 ≤ ‖J ψ‖ ^ 2 + ‖J (Aop 1 ψ)‖ ^ 2 + ‖J (Aop 0 ψ)‖ ^ 2 +
      ‖J (Aop 1 (Aop 0 ψ))‖ ^ 2 := by
  have hre := re_sq_le_integral_2d ψ z
  have him := re_sq_le_integral_2d ((-Complex.I) • ψ) z
  have hI_re : ∀ (φ : S2) (w : ℝ × ℝ), (((-Complex.I) • φ) w).re = (φ w).im := fun φ w => by
    simp [smul_eq_mul]
  have hdop_smul : ∀ (i : Fin 2) (φ : S2), dop i ((-Complex.I) • φ) = (-Complex.I) • dop i φ :=
    fun i φ => map_smul (dop i) (-Complex.I) φ
  simp only [hdop_smul, hI_re] at him
  set G_re : ℝ × ℝ → ℝ := fun w =>
    (ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2
  set G_im : ℝ × ℝ → ℝ := fun w =>
    (ψ w).im ^ 2 + (dop 1 ψ w).im ^ 2 + (dop 0 ψ w).im ^ 2 + (dop 1 (dop 0 ψ) w).im ^ 2
  have hi_re : Integrable G_re :=
    (((integrable_re_sq ψ).add (integrable_re_sq (dop 1 ψ))).add
      (integrable_re_sq (dop 0 ψ))).add (integrable_re_sq (dop 1 (dop 0 ψ)))
  have hi_im : Integrable G_im := by
    have eqf : G_im = fun w => (((-Complex.I) • ψ) w).re ^ 2 +
        (dop 1 ((-Complex.I) • ψ) w).re ^ 2 + (dop 0 ((-Complex.I) • ψ) w).re ^ 2 +
        (dop 1 (dop 0 ((-Complex.I) • ψ)) w).re ^ 2 := by
      funext w; simp only [G_im, hdop_smul, hI_re]
    rw [eqf]
    exact (((integrable_re_sq _).add (integrable_re_sq _)).add (integrable_re_sq _)).add
      (integrable_re_sq _)
  have hnorm_sq : ∀ ζ : ℂ, ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := fun ζ => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hint_norm : ∀ φ : S2, Integrable (fun w : ℝ × ℝ => ‖φ w‖ ^ 2) := fun φ =>
    Integrable.mono' (integrable_conj_mul φ φ).norm
      ((continuous_norm.comp φ.continuous).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_conj, ← sq])
  have hsum_z : ‖ψ z‖ ^ 2 ≤ ∫ w : ℝ × ℝ,
      (‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2 + ‖dop 1 (dop 0 ψ) w‖ ^ 2) := by
    rw [← hnorm_sq (ψ z)]
    refine (add_le_add hre him).trans ?_
    rw [← integral_add hi_re hi_im]
    refine le_of_eq (congrArg (integral volume) (funext fun w => ?_))
    simp only [G_re, G_im, ← hnorm_sq]; ring
  have i12 : Integrable (fun w : ℝ × ℝ => ‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2) :=
    (hint_norm ψ).add (hint_norm (dop 1 ψ))
  have i123 : Integrable (fun w : ℝ × ℝ => ‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2) :=
    i12.add (hint_norm (dop 0 ψ))
  have hsplit : (∫ w : ℝ × ℝ,
      (‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2 + ‖dop 1 (dop 0 ψ) w‖ ^ 2)) =
      ‖J ψ‖ ^ 2 + ‖J (dop 1 ψ)‖ ^ 2 + ‖J (dop 0 ψ)‖ ^ 2 + ‖J (dop 0 (dop 1 ψ))‖ ^ 2 := by
    rw [integral_add i123 (hint_norm _), integral_add i12 (hint_norm _),
      integral_add (hint_norm ψ) (hint_norm _),
      ← norm_J_sq_eq_integral, ← norm_J_sq_eq_integral,
      ← norm_J_sq_eq_integral, ← norm_J_sq_eq_integral, dop_comm 1 0 ψ]
  refine hsum_z.trans ?_
  rw [hsplit]
  linarith [norm_J_dop_sq_le_Aop 1 ψ, norm_J_dop_sq_le_Aop 0 ψ, norm_J_dop_dop_sq_le ψ]

theorem norm_J_Aw_φS_sq_le {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 2) (ℓ : ℕ) :
    ‖J (Aw k w (φS ℓ))‖ ^ 2 ≤ 2592 * Real.pi * (1 + (ℓ : ℝ)) ^ 4 := by
  have hchi : chi {ℓ} (fun _ => 1) = φS ℓ := by simp [chi]
  have h1 : ‖J (Aw k w (φS ℓ))‖ ^ 2 ≤ ∑ w' : Fin k → Fin 2, ‖J (Aw k w' (φS ℓ))‖ ^ 2 :=
    Finset.single_le_sum (f := fun w' => ‖J (Aw k w' (φS ℓ))‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
  have h2 := sum_norm_sq_Aw_chi k {ℓ} (fun _ => 1)
  simp only [hchi, Finset.sum_singleton, norm_one, one_pow, mul_one] at h2
  have h3 := qpoly_le (by omega : k ≤ 4) ℓ
  norm_num at h3
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  nlinarith

theorem norm_gS_φS_le (ℓ : ℕ) (z : ℝ × ℝ) :
    ‖gS (φS ℓ) z‖ ≤
      (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  have hφ_bd : ‖φS ℓ z‖ ≤ 204 * (1 + (ℓ : ℝ)) ^ 2 := by
    set ψ := φS ℓ
    have h0 : ψ = Aw 0 ![] (φS ℓ) := rfl
    have e1 : Aop 1 ψ = Aw 1 (Fin.cons 1 ![]) (φS ℓ) := by rw [h0]; simp [Aw_succ]
    have e0 : Aop 0 ψ = Aw 1 (Fin.cons 0 ![]) (φS ℓ) := by rw [h0]; simp [Aw_succ]
    have e10 : Aop 1 (Aop 0 ψ) = Aw 2 (Fin.cons 1 (Fin.cons 0 ![])) (φS ℓ) := by
      rw [e0]; simp [Aw_succ]
    have b0 := norm_J_Aw_φS_sq_le (by omega) ![] ℓ
    have b1 := norm_J_Aw_φS_sq_le (by omega) (Fin.cons 1 ![]) ℓ
    have b2 := norm_J_Aw_φS_sq_le (by omega) (Fin.cons 0 ![]) ℓ
    have b3 := norm_J_Aw_φS_sq_le (by omega) (Fin.cons 1 (Fin.cons 0 ![])) ℓ
    have hsup := norm_sq_schwartz_le_Aop ψ z
    rw [e10, e1, e0, h0] at hsup
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hℓ4 : 0 ≤ (1 + (ℓ : ℝ)) ^ 4 := by positivity
    have hsq : ‖Aw 0 ![] (φS ℓ) z‖ ^ 2 ≤ (204 * (1 + (ℓ : ℝ)) ^ 2) ^ 2 := by
      calc ‖Aw 0 ![] (φS ℓ) z‖ ^ 2 ≤ 4 * (2592 * Real.pi * (1 + (ℓ : ℝ)) ^ 4) := by linarith
        _ ≤ 4 * (2592 * 4 * (1 + (ℓ : ℝ)) ^ 4) := by nlinarith
        _ ≤ (204 * (1 + (ℓ : ℝ)) ^ 2) ^ 2 := by nlinarith
    rw [← h0] at hsq
    nlinarith [norm_nonneg (ψ z), (by positivity : (0 : ℝ) ≤ 204 * (1 + (ℓ : ℝ)) ^ 2)]
  rw [gS_apply, norm_mul, sqGc, Complex.norm_real, Real.norm_of_nonneg (sqG_pos z).le,
    sqG_eq, gaussS_apply]
  have hc := B0093.sqrtConst_pos.le
  have he := (Real.exp_pos (-((z.1 ^ 2 + z.2 ^ 2) / 8))).le
  rw [show -((z.1 ^ 2 + z.2 ^ 2) / 8) = -(z.1 ^ 2 + z.2 ^ 2) / 8 by ring] at he ⊢
  calc B0093.sqrtConst * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) * ‖φS ℓ z‖
      ≤ B0093.sqrtConst * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) * (204 * (1 + (ℓ : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hφ_bd (mul_nonneg hc he)
    _ = (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        ring

theorem summable_inv_one_add_pow_four :
    Summable (fun ℓ : ℕ => ((1 + (ℓ : ℝ)) ^ 2)⁻¹ ^ 2) := by
  have hs : Summable (fun ℓ : ℕ => (((ℓ + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hs
  have h1 : (1 : ℝ) ≤ 1 + (ℓ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hpos : (0 : ℝ) < (1 + (ℓ : ℝ)) ^ 2 := by positivity
  have hcast : ((ℓ + 1 : ℕ) : ℝ) = 1 + (ℓ : ℝ) := by push_cast; ring
  rw [hcast, inv_pow, ← pow_mul]
  exact inv_anti₀ hpos (pow_le_pow_right₀ h1 (by norm_num : 2 ≤ 2 * 2))

def sumInvFour : ℝ := ∑' ℓ : ℕ, ((1 + (ℓ : ℝ)) ^ 2)⁻¹ ^ 2

theorem sumInvFour_pos : 0 < sumInvFour :=
  summable_inv_one_add_pow_four.tsum_pos (fun _ => by positivity) 0 (by norm_num)

theorem coef_weighted_summable_and_le (u : XG) (hu : u ∈ (fracPow 8).domain) :
    Summable (fun ℓ : ℕ => ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ∧
      (∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ≤
        Real.sqrt sumInvFour * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) := by
  set G₈ := Real.sqrt (graphNormSq 8 ⟨u, hu⟩)
  have hG_nn : 0 ≤ graphNormSq 8 ⟨u, hu⟩ := by unfold graphNormSq; positivity
  have hG_sq : G₈ ^ 2 = ∑' ℓ : ℕ, (1 + (1 + (ℓ : ℝ)) ^ 8) * ‖⟪oscBasis ℓ, u⟫_ℂ‖ ^ 2 := by
    rw [Real.sq_sqrt hG_nn, graphNormSq_eq 8 ⟨u, hu⟩]
  have hsum8 : Summable (fun ℓ : ℕ => (1 + (1 + (ℓ : ℝ)) ^ 8) * ‖⟪oscBasis ℓ, u⟫_ℂ‖ ^ 2) :=
    (summable_coef_sq u).add ((mem_XGj_iff 8 u).1 hu) |>.congr fun ℓ => by ring
  have hN : ∀ N : ℕ, ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 ≤
      Real.sqrt sumInvFour * G₈ := by
    intro N
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun ℓ => ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4)
      (fun ℓ => ((1 + (ℓ : ℝ)) ^ 2)⁻¹)
    have hrew : ∑ ℓ ∈ Finset.range N,
        (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4) * ((1 + (ℓ : ℝ)) ^ 2)⁻¹ =
        ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have hpos : (1 + (ℓ : ℝ)) ≠ 0 := by positivity
      field_simp
    rw [hrew] at hcs
    have hA : ∑ ℓ ∈ Finset.range N, (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4) ^ 2 ≤ G₈ ^ 2 := by
      rw [hG_sq]
      refine (Finset.sum_le_sum fun ℓ _ => ?_).trans
        (hsum8.sum_le_tsum (Finset.range N) fun _ _ => by positivity)
      nlinarith [sq_nonneg ‖⟪oscBasis ℓ, u⟫_ℂ‖]
    have hB : ∑ ℓ ∈ Finset.range N, (((1 + (ℓ : ℝ)) ^ 2)⁻¹) ^ 2 ≤ sumInvFour :=
      summable_inv_one_add_pow_four.sum_le_tsum (Finset.range N) fun _ _ => by positivity
    have hsq : (∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ^ 2 ≤
        (Real.sqrt sumInvFour * G₈) ^ 2 := by
      calc (∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ^ 2
          ≤ G₈ ^ 2 * sumInvFour := hcs.trans (mul_le_mul hA hB
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg G₈))
        _ = (Real.sqrt sumInvFour * G₈) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt sumInvFour_pos.le, mul_comm]
    have hS_nn : 0 ≤ ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hR_nn : 0 ≤ Real.sqrt sumInvFour * G₈ := by positivity
    nlinarith
  have hs := summable_of_sum_range_le (fun _ => by positivity) hN
  exact ⟨hs, hs.tsum_le_of_sum_range_le hN⟩

def synthPlanar (u : XG) (z : ℝ × ℝ) : ℂ :=
  ∑' ℓ : ℕ, ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z

def synthZeroConst : ℝ := (204 * B0093.sqrtConst) * Real.sqrt sumInvFour

theorem synthZeroConst_pos : 0 < synthZeroConst :=
  mul_pos (mul_pos (by norm_num) B0093.sqrtConst_pos) (Real.sqrt_pos.2 sumInvFour_pos)

theorem continuous_and_gauss_synthPlanar (u : XG) (hu : u ∈ (fracPow 8).domain) :
    Continuous (synthPlanar u) ∧
      ∀ z : ℝ × ℝ, ‖synthPlanar u z‖ ≤
        synthZeroConst * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  obtain ⟨hsum_w, hle_w⟩ := coef_weighted_summable_and_le u hu
  set c0 : ℝ := 204 * B0093.sqrtConst
  have hc0_pos : 0 < c0 := mul_pos (by norm_num) B0093.sqrtConst_pos
  have hbd_gauss : ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z‖ ≤
        (c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2)) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro ℓ z
    rw [norm_mul]
    calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖gS (φS ℓ) z‖
        ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (c0 * (1 + (ℓ : ℝ)) ^ 2 *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left (norm_gS_φS_le ℓ z) (norm_nonneg _)
      _ = (c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2)) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by ring
  have hbd_unif : ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z‖ ≤
        c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) := by
    intro ℓ z
    have hexp1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    exact (hbd_gauss ℓ z).trans (mul_le_of_le_one_right (by positivity) hexp1)
  have hcont : Continuous (synthPlanar u) :=
    continuous_tsum (fun ℓ => continuous_const.mul (gS (φS ℓ)).continuous)
      (hsum_w.mul_left c0) hbd_unif
  refine ⟨hcont, fun z => ?_⟩
  have hsum_norm : Summable (fun ℓ : ℕ => ‖⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hbd_unif ℓ z) (hsum_w.mul_left c0)
  have hsum_rhs : Summable (fun ℓ : ℕ =>
      (c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2)) *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
    (hsum_w.mul_left c0).mul_right _
  calc ‖synthPlanar u z‖
      ≤ ∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' ℓ : ℕ, (c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2)) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
        hsum_norm.tsum_le_tsum (fun ℓ => hbd_gauss ℓ z) hsum_rhs
    _ = c0 * (∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ synthZeroConst * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        calc c0 * ∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2
            ≤ c0 * (Real.sqrt sumInvFour * Real.sqrt (graphNormSq 8 ⟨u, hu⟩)) :=
              mul_le_mul_of_nonneg_left hle_w hc0_pos.le
          _ = synthZeroConst * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) := by
              unfold synthZeroConst; dsimp [c0]; ring

theorem gS_φS_eq_angF (ℓ : ℕ) (z : ℝ × ℝ) :
    gS (φS ℓ) z = angF (qp (lev ℓ)) z := by
  rw [gS_apply, φS, coe_coreS, sqGc_mul_conjG, angularTwoField_profFun]

theorem gS_φS_zero (ℓ : ℕ) : gS (φS ℓ) (0, 0) = 0 := by
  rw [gS_φS_eq_angF]; simp [angF, wz]

theorem gS_φS_eq_axis_mul_angTwo (ℓ : ℕ) {z : ℝ × ℝ} (hz : z ≠ (0, 0)) :
    gS (φS ℓ) z = gS (φS ℓ) (Real.sqrt (z.1 ^ 2 + z.2 ^ 2), 0) * angTwo z := by
  have hs_pos : 0 < z.1 ^ 2 + z.2 ^ 2 := by
    by_contra hle
    exact hz (Prod.ext (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
      (by nlinarith [sq_nonneg z.1, sq_nonneg z.2]))
  have hsq : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 = z.1 ^ 2 + z.2 ^ 2 := Real.sq_sqrt hs_pos.le
  rw [gS_φS_eq_angF, gS_φS_eq_angF]
  unfold angF angTwo wz sz
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Complex.ofReal_zero, zero_mul]
  rw [← Complex.ofReal_pow, hsq]
  have hne : ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs_pos.ne'
  field_simp [hne]

theorem oscBasis_ae_eq_gS_axis (ℓ : ℕ) :
    (oscBasis ℓ : ℝ → ℂ) =ᵐ[xGMeasure] fun r : ℝ => gS (φS ℓ) (r, 0) := by
  have h1 : (oscBasis ℓ : ℝ → ℂ) =ᵐ[xGMeasure] schProf (φS ℓ) := by
    rw [← toXG_φS ℓ, toXG]
    exact (memLp_schProf (φS ℓ)).coeFn_toLp
  filter_upwards [h1, UnforcedLeray.B0012.ae_xG_pos] with r hr1 hr_pos
  rw [hr1]
  have h2 := congrFun (angularTwoField_schProf_eq_gS (isAngularTwo_φS ℓ)) (r, 0)
  rw [← h2]
  unfold angularTwoField
  simp only [polarCoord_apply, zero_pow (by norm_num : 2 ≠ 0), add_zero,
    Real.sqrt_sq hr_pos.le]
  have harg : Complex.arg (Complex.equivRealProd.symm (r, 0)) = 0 := by
    have heq : Complex.equivRealProd.symm (r, 0) = (r : ℂ) := by apply Complex.ext <;> simp
    rw [heq]
    exact Complex.arg_ofReal_of_nonneg hr_pos.le
  rw [harg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

theorem planarMode_eq_synthPlanar {f : Profile}
    (hfc : ContDiffOn ℝ ∞ f (Ioi 0)) {u : XG}
    (hfu : f =ᵐ[xGMeasure] (u : ℝ → ℂ)) (hu : u ∈ (fracPow 8).domain) :
    planarMode f = synthPlanar u := by
  obtain ⟨hcont_F, _⟩ := continuous_and_gauss_synthPlanar u hu
  obtain ⟨hsum_w, _⟩ := coef_weighted_summable_and_le u hu
  set c0 : ℝ := 204 * B0093.sqrtConst
  have hc0_pos : 0 < c0 := mul_pos (by norm_num) B0093.sqrtConst_pos
  have hsum_pt : ∀ z : ℝ × ℝ, Summable (fun ℓ : ℕ => ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z) := by
    intro z
    refine Summable.of_norm_bounded (hsum_w.mul_left c0) fun ℓ => ?_
    rw [norm_mul]
    have hb := norm_gS_φS_le ℓ z
    have hexp1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖gS (φS ℓ) z‖
        ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (c0 * (1 + (ℓ : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (hb.trans (mul_le_of_le_one_right (by positivity) hexp1)) (norm_nonneg _)
      _ = c0 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) := by ring
  have hS : HasSum (fun ℓ : ℕ => ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ) u := by
    simpa only [HilbertBasis.repr_apply_apply] using oscBasis.hasSum_repr u
  have hcoe : ∀ N : ℕ,
      (⇑(∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ) : ℝ → ℂ) =ᵐ[xGMeasure]
        fun r : ℝ => ∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) (r, 0) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 xGMeasure
    | succ N ih =>
      filter_upwards [ih,
        Lp.coeFn_add (∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ)
          (⟪oscBasis N, u⟫_ℂ • oscBasis N),
        Lp.coeFn_smul ⟪oscBasis N, u⟫_ℂ (oscBasis N),
        oscBasis_ae_eq_gS_axis N] with r h1 h2 h3 h4
      simp only [Finset.sum_range_succ]
      rw [h2, Pi.add_apply, h1, h3, Pi.smul_apply, smul_eq_mul, h4]
  obtain ⟨ns, hns, hae_sub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hS.tendsto_sum_nat).exists_seq_tendsto_ae
  have hae_u : (u : ℝ → ℂ) =ᵐ[xGMeasure] fun r : ℝ => synthPlanar u (r, 0) := by
    filter_upwards [hae_sub, ae_all_iff.2 hcoe] with r hr1 hr2
    exact tendsto_nhds_unique (Tendsto.congr (fun i => hr2 (ns i)) hr1)
      ((hsum_pt (r, 0)).hasSum.tendsto_sum_nat.comp hns.tendsto_atTop)
  have hae_vol : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r : ℝ => synthPlanar u (r, 0) :=
    UnforcedLeray.B0012.restrict_ac.ae_le (hfu.trans hae_u)
  have hcont_axis : ContinuousOn (fun r : ℝ => synthPlanar u (r, 0)) (Ioi 0) :=
    (hcont_F.comp (continuous_id.prodMk continuous_const)).continuousOn
  have heq_on : EqOn f (fun r : ℝ => synthPlanar u (r, 0)) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae_vol isOpen_Ioi hfc.continuousOn hcont_axis
  funext z
  by_cases hz : z = (0, 0)
  · subst hz; simp [planarMode, angTwo, synthPlanar, gS_φS_zero]
  · have hs_pos : 0 < z.1 ^ 2 + z.2 ^ 2 := by
      by_contra hle
      exact hz (Prod.ext (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
        (by nlinarith [sq_nonneg z.1, sq_nonneg z.2]))
    have hr_pos : 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := Real.sqrt_pos.2 hs_pos
    unfold planarMode
    rw [heq_on hr_pos]
    unfold synthPlanar
    rw [← tsum_mul_right]
    congr 1; funext ℓ
    rw [mul_assoc, ← gS_φS_eq_axis_mul_angTwo ℓ hz]

theorem planarMode_and_periodizeC_gauss {f : Profile}
    (hfc : ContDiffOn ℝ ∞ f (Ioi 0)) {u : XG}
    (hfu : f =ᵐ[xGMeasure] (u : ℝ → ℂ)) (hu : u ∈ (fracPow 8).domain)
    {M₈ : ℝ} (hM₈ : 0 ≤ M₈) (hG₈ : Real.sqrt (graphNormSq 8 ⟨u, hu⟩) ≤ M₈)
    {d : ℝ} (hd : 1 ≤ d) :
    Continuous (planarMode f) ∧
    (∀ z : ℝ × ℝ, ‖planarMode f z‖ ≤
      (synthZeroConst * M₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) ∧
    Continuous (periodizeC d (planarMode f)) ∧
    (∀ y ∈ B0579.cell d,
      ‖periodizeC d (planarMode f) y - planarMode f y‖ ≤
        (256 * (synthZeroConst * M₈) * EulerErrorTail.sZ) / d ^ 2 *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by
  have heq := planarMode_eq_synthPlanar hfc hfu hu
  obtain ⟨hcont_F, hbd_F⟩ := continuous_and_gauss_synthPlanar u hu
  have he_cont : Continuous (planarMode f) := heq ▸ hcont_F
  set C_e : ℝ := synthZeroConst * M₈
  have hCe_nn : 0 ≤ C_e := mul_nonneg synthZeroConst_pos.le hM₈
  have he_bd : ∀ z : ℝ × ℝ, ‖planarMode f z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro z
    rw [heq]
    refine (hbd_F z).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact mul_le_mul_of_nonneg_left hG₈ synthZeroConst_pos.le
  have hd_ne : d ≠ 0 := by linarith
  have hper_eq : periodizeC d (planarMode f) =
      fun y => ∑' n : ℤ, planarMode f (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext y
    change UnforcedLeray.Gaussian.periodize d (planarMode f) y = _
    exact UnforcedLeray.Gaussian.periodize_eq d (planarMode f) y
  have hW_cont : Continuous (periodizeC d (planarMode f)) := by
    rw [hper_eq]
    refine UnforcedLeray.Gaussian.continuous_tsum_translates he_cont (s := 2) (c := d)
      one_lt_two hd_ne (C := 16 * C_e) fun z => ?_
    calc ‖planarMode f z‖
        ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := he_bd z
      _ ≤ C_e * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (perCont_exp_le_translate_weight z.1 z.2) hCe_nn
      _ = (16 * C_e) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
  refine ⟨he_cont, he_bd, hW_cont, fun y hy => ?_⟩
  have hshift_eq : periodizeC d (planarMode f) y =
      ∑' n : ℤ, planarMode f (y.1 - n * d, y.2) := by
    rw [hper_eq]
    dsimp only
    refine tsum_congr fun n => ?_
    congr 1
    ext <;> simp [UnforcedLeray.Gaussian.shiftVec]
  rw [hshift_eq]
  exact EulerErrorTail.tail_gauss' hCe_nn he_bd hd (EulerErrorTail.abs_fst_le_of_mem_cell hy)

end HermiteSynth

end UnforcedLeray.Short.IIIa.AnisoSynthAux

