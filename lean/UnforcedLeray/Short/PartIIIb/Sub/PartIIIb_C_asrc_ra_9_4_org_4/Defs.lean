import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3.PsiASum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3.GpsiAEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.EnvL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.AffMBdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1` : the leaves of `PsiADerivCell`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 4966-4968 (`p_j = -a⁻³e^{-|x_j|²/(2a)}`, `a = 1+νs`, `x_j = (q-jc, η)`),
4978 ("the sums and their required derivatives converge by Gaussian decay"), 5024
(`Ψ_A = Σ_j (A^y_mer x_j)·∇p_j`), 5063-5071 and 5076-5079 (Gaussian cell norms, derivative budget).

`Ψ_A(s,x) = Σ_j psiT(s, A^y(s), x_j)` with the explicit lattice term
`psiT = a⁻⁴ ⟨A^y_mer y, y⟩ e^{-|y|²/(2a)}` (`pdc_PsiA_eq`, from `psiASum_proof`, `gpsiA_eq_proof`).
Its `η`- and `s`-derivatives are the explicit `psiTEta`, `psiTS`.  The leaves:

* (a) termwise differentiation: `PsiTEtaDeriv`, `PsiTSDeriv` (one term), `PsiAEtaTsum`,
  `PsiASTsum` (the lattice sums);
* (b) Gaussian envelope of one term, with the weights `|η|` and `s` of `𝒦`:
  `PsiTValBound`, `PsiTEtaBound`, `PsiTSBound`, against `genvT y = (1+‖y‖)⁴e^{-‖y‖²/9}`, the
  summand of the lattice envelope `gEnv` of `PartIII-b_C_asrc_ra_8_3_2`;
* (c) continuity in `x` of the lattice sums (`PsiASliceCont`, for a.e. measurability); the cell
  `L²` bound itself is proved here from `gEnvL2` (`P_ν`), `affMBdd` and `fac_frob_Ay_le`
  (`|A^y(s)| + |s∂_sA^y(s)| ≤ s^{5/2}M(A)`): `psiADerivCell_of`.

Helper lemmas for the leaves (`pdc_*`) are proved here as well.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The lattice term of `Ψ_A` and its derivatives (source 4966-4968, 5024) -/

/-- `Q_M(y) = ⟨M_mer y, y⟩`. -/
def qM (M : Mat3) (y : ℝ × ℝ) : ℝ := y.1 * (merApply M y).1 + y.2 * (merApply M y).2

/-- The lattice term of `Ψ_A` at `y = x_j`, `M = A^y(s)`:
`(M_mer y)·∇p_0(y) = a⁻⁴ ⟨M_mer y, y⟩ e^{-|y|²/(2a)}`, `a = 1+νs` (source 4966, 5024). -/
def psiT (ν s : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  Real.exp (-(sq2 y) / (2 * ageA ν s)) * ((ageA ν s ^ 4)⁻¹ * qM M y)

/-- `∂_η psiT = a⁻⁴ e^{-|y|²/(2a)} [(M_rz + M_zr) y₁ + 2M_zz y₂ - (y₂/a) Q_M(y)]`. -/
def psiTEta (ν s : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ *
    ((M 0 2 + M 2 0) * y.1 + 2 * M 2 2 * y.2 - y.2 / ageA ν s * qM M y)

/-- `∂_s psiT(s, M(s), y)` with `D = M'(s)`:
`a⁻⁴ e^{-|y|²/(2a)} [Q_D(y) - (4ν/a) Q_M(y) + (ν|y|²/(2a²)) Q_M(y)]`. -/
def psiTS (ν s : ℝ) (M D : Mat3) (y : ℝ × ℝ) : ℝ :=
  Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ *
    (qM D y - 4 * ν / ageA ν s * qM M y + ν * sq2 y / (2 * ageA ν s ^ 2) * qM M y)

/-- The summand of the lattice envelope `gEnv ν x = Σ_j genvT (x_j)`. -/
def genvT (y : ℝ × ℝ) : ℝ := (1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9)

/-- `Ψ_A` as the lattice sum of `psiT` (source 5024; `psiASum_proof`, `gpsiA_eq_proof`). -/
theorem pdc_PsiA_eq (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    PsiA ν χ A s x = ∑' j : ℤ, psiT ν s (Ay ν χ A s) (xj ν j x) := by
  have h : PsiA ν χ A s x = ∑' j : ℤ, GpsiA ν χ A (s, (x.1 - j * cOf ν, x.2)) :=
    congrFun (psiASum_proof ν χ A) (s, x)
  rw [h]
  refine tsum_congr fun j => ?_
  rw [gpsiA_eq_proof ν χ A]
  rfl

/-! ## 2. Elementary helpers for the leaves -/

theorem pdc_abs_le_frob (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  unfold frob
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact Real.abs_le_sqrt (h1.trans h2)

theorem pdc_frob_nonneg (M : Mat3) : 0 ≤ frob M := Real.sqrt_nonneg _

theorem pdc_abs_fst_le (y : ℝ × ℝ) : |y.1| ≤ ‖y‖ := by
  have h := norm_fst_le y
  rwa [Real.norm_eq_abs] at h

theorem pdc_abs_snd_le (y : ℝ × ℝ) : |y.2| ≤ ‖y‖ := by
  have h := norm_snd_le y
  rwa [Real.norm_eq_abs] at h

theorem pdc_norm_sq_le_sq2 (y : ℝ × ℝ) : ‖y‖ ^ 2 ≤ sq2 y := by
  have hn : ‖y‖ = max |y.1| |y.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold sq2
  rcases max_choice |y.1| |y.2| with h | h <;> rw [hn, h] <;>
    nlinarith [sq_abs y.1, sq_abs y.2, sq_nonneg y.1, sq_nonneg y.2]

theorem pdc_sq2_le (y : ℝ × ℝ) : sq2 y ≤ 2 * ‖y‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (pdc_abs_fst_le y) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (pdc_abs_snd_le y) 2
  rw [sq_abs] at h1 h2
  unfold sq2
  linarith

theorem pdc_sq2_nonneg (y : ℝ × ℝ) : 0 ≤ sq2 y := by unfold sq2; positivity

/-- `|c u v| ≤ F n²` from `|c| ≤ F`, `|u|, |v| ≤ n`. -/
theorem pdc_abs_mul3_le {c u v F n : ℝ} (hc : |c| ≤ F) (hu : |u| ≤ n) (hv : |v| ≤ n) :
    |c * (u * v)| ≤ F * n ^ 2 := by
  have hn : 0 ≤ n := (abs_nonneg u).trans hu
  rw [abs_mul, abs_mul, sq]
  exact mul_le_mul hc (mul_le_mul hu hv (abs_nonneg _) hn) (by positivity) ((abs_nonneg c).trans hc)

/-- `|Q_M(y)| ≤ 4 |M| ‖y‖²`. -/
theorem pdc_qM_le (M : Mat3) (y : ℝ × ℝ) : |qM M y| ≤ 4 * frob M * ‖y‖ ^ 2 := by
  have e : qM M y = M 0 0 * (y.1 * y.1) + M 0 2 * (y.1 * y.2) + M 2 0 * (y.2 * y.1)
      + M 2 2 * (y.2 * y.2) := by
    simp only [qM, merApply]; ring
  have h1 := pdc_abs_fst_le y
  have h2 := pdc_abs_snd_le y
  have a1 := pdc_abs_mul3_le (pdc_abs_le_frob M 0 0) h1 h1
  have a2 := pdc_abs_mul3_le (pdc_abs_le_frob M 0 2) h1 h2
  have a3 := pdc_abs_mul3_le (pdc_abs_le_frob M 2 0) h2 h1
  have a4 := pdc_abs_mul3_le (pdc_abs_le_frob M 2 2) h2 h2
  rw [e]
  have t1 := abs_add_le (M 0 0 * (y.1 * y.1) + M 0 2 * (y.1 * y.2) + M 2 0 * (y.2 * y.1))
    (M 2 2 * (y.2 * y.2))
  have t2 := abs_add_le (M 0 0 * (y.1 * y.1) + M 0 2 * (y.1 * y.2)) (M 2 0 * (y.2 * y.1))
  have t3 := abs_add_le (M 0 0 * (y.1 * y.1)) (M 0 2 * (y.1 * y.2))
  linarith

/-- `Q` is linear in the matrix: `Q_{r M}(y) = r Q_M(y)`. -/
theorem pdc_qM_smul (r : ℝ) (M : Mat3) (y : ℝ × ℝ) : qM (r • M) y = r * qM M y := by
  simp only [qM, merApply, Pi.smul_apply, smul_eq_mul]; ring

theorem pdc_ageA_ge_one {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) : 1 ≤ ageA ν s := by
  unfold ageA; nlinarith [mul_nonneg hν hs]

theorem pdc_ageA_le {ν s : ℝ} (hνs : ν * s ≤ 5 / 2) : ageA ν s ≤ 7 / 2 := by
  unfold ageA; linarith

/-- The Gaussian factor of the lattice term is below the envelope Gaussian for `1 ≤ a ≤ 7/2`. -/
theorem pdc_exp_le {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (hνs : ν * s ≤ 5 / 2) (y : ℝ × ℝ) :
    Real.exp (-(sq2 y) / (2 * ageA ν s)) ≤ Real.exp (-(‖y‖ ^ 2) / 9) := by
  have ha1 := pdc_ageA_ge_one hν hs
  have ha2 := pdc_ageA_le hνs
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div, neg_le_neg_iff]
  have hq := pdc_norm_sq_le_sq2 y
  have hq0 := pdc_sq2_nonneg y
  calc ‖y‖ ^ 2 / 9 ≤ sq2 y / 9 := by gcongr
    _ ≤ sq2 y / (2 * ageA ν s) := div_le_div_of_nonneg_left hq0 (by linarith) (by linarith)

theorem pdc_genvT_nonneg (y : ℝ × ℝ) : 0 ≤ genvT y := by unfold genvT; positivity

theorem pdc_gEnv_eq (ν : ℝ) (x : ℝ × ℝ) : gEnv ν x = ∑' j : ℤ, genvT (xj ν j x) := rfl

/-- The envelope summand at `x_j` is dominated by a Gaussian in `q - jc` alone. -/
theorem pdc_genvT_le (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    genvT (xj ν j x) ≤ 5200 * Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
  have h := gEnv_summand_le (norm_nonneg (xj ν j x))
  have h1 : |(xj ν j x).1| ≤ ‖xj ν j x‖ := pdc_abs_fst_le _
  have hsq : (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ ‖xj ν j x‖ ^ 2 := by
    have e : (x.1 - (j : ℝ) * cOf ν) ^ 2 = |(xj ν j x).1| ^ 2 := by
      rw [sq_abs]; rfl
    rw [e]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hexp : Real.exp (-(‖xj ν j x‖ ^ 2) / 18) ≤
      Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  unfold genvT
  exact h.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

/-- Summability of the envelope summands at a point. -/
theorem pdc_genv_summable {ν : ℝ} (hν : 0 < ν) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => genvT (xj ν j x)) := by
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  exact Summable.of_nonneg_of_le (fun j => pdc_genvT_nonneg _) (fun j => pdc_genvT_le ν j x)
    ((gp_gauss_summable x.1 (1 / 18) (cOf ν) (by norm_num) hc).mul_left 5200)

/-- A summable majorant of the envelope summands, uniform for `|q| ≤ R` (and all `η`). -/
theorem pdc_genv_unif {ν : ℝ} (hν : 0 < ν) (R : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ x : ℝ × ℝ, |x.1| ≤ R → ∀ j : ℤ, genvT (xj ν j x) ≤ u j := by
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hα0 : (0 : ℝ) < 1 / 18 := by norm_num
  have hT : 0 < (1 / 18) * cOf ν ^ 2 / Real.pi :=
    div_pos (mul_pos hα0 (pow_pos hc 2)) Real.pi_pos
  refine ⟨fun j => 5200 * Real.exp (-Real.pi * (((1 / 18) * cOf ν ^ 2 / Real.pi) * (j : ℝ) ^ 2
      - 2 * ((1 / 18) * R * cOf ν / Real.pi) * |(j : ℝ)|)), ?_, ?_⟩
  · have h := summable_pow_mul_jacobiTheta₂_term_bound ((1 / 18) * R * cOf ν / Real.pi) hT 0
    refine (h.mul_left 5200).congr (fun j => ?_)
    simp only [pow_zero, one_mul, Int.cast_abs]
  · intro x hx j
    refine (pdc_genvT_le ν j x).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    refine (gp_gauss_dom x.1 (1 / 18) (cOf ν) hα0 hc.le j).trans ?_
    apply Real.exp_le_exp.mpr
    have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
    have h1 : (1 / 18) * |x.1| * cOf ν / Real.pi ≤ (1 / 18) * R * cOf ν / Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hα0.le) hc.le
    nlinarith [mul_le_mul_of_nonneg_right h1 hz, Real.pi_pos]

/-- `A^y = χ_f A` is `C¹` on `s > 0` (source 4741-4745, 4955). -/
theorem pdc_Ay_contDiffOn {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {as : ℝ} {A : ℝ → Mat3}
    (hA : IsAffElem as A) (ν : ℝ) : ContDiffOn ℝ 1 (Ay ν χf A) (Ioi 0) := by
  intro t ht
  have h1 : ContDiffAt ℝ 1 (fun t => χf (ν * t)) t :=
    ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffAt).of_le (by norm_num)
  have h2 : ContDiffAt ℝ 1 A t :=
    (hA.smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by norm_num)
  exact (h1.smul h2).contDiffWithinAt

/-! ## 3. The leaves -/

/-- **(a1) `η`-derivative of one lattice term** (source 4966, 5024; calculus): for `a > 0`,
`∂_η psiT(s, M, (q, η)) = psiTEta(s, M, (q, η))`. -/
def PsiTEtaDeriv : Prop :=
  ∀ (ν s : ℝ), 0 < ageA ν s → ∀ (M : Mat3) (q η : ℝ),
    HasDerivAt (fun η' => psiT ν s M (q, η')) (psiTEta ν s M (q, η)) η

/-- **(a2) `s`-derivative of one lattice term** along a matrix path `M(s)` with `M'(s) = D`
(source 4966, 5024; calculus): `∂_s psiT(s, M(s), y) = psiTS(s, M(s), D, y)`. -/
def PsiTSDeriv : Prop :=
  ∀ (ν : ℝ) (Mf : ℝ → Mat3) (D : Mat3) (s : ℝ), 0 < ageA ν s → HasDerivAt Mf D s →
    ∀ y : ℝ × ℝ, HasDerivAt (fun t => psiT ν t (Mf t) y) (psiTS ν s (Mf s) D y) s

/-- **(b1) Gaussian envelope of one lattice term** (source 4978, 5063-5071): for
`0 ≤ νs ≤ 5/2` (so `1 ≤ a ≤ 7/2`), `|psiT| ≤ K|M| (1+‖y‖)⁴ e^{-‖y‖²/9}`. -/
def PsiTValBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → 0 ≤ s → ν * s ≤ 5 / 2 → ∀ (M : Mat3) (y : ℝ × ℝ),
    |psiT ν s M y| ≤ K * frob M * genvT y

/-- **(b2) Gaussian envelope of the `η`-derivative, with and without the weight `|η|` of `𝒦`**
(source 4978, 5039-5043, 5063-5071, 5076-5079). -/
def PsiTEtaBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → 0 ≤ s → ν * s ≤ 5 / 2 → ∀ (M : Mat3) (y : ℝ × ℝ),
    |psiTEta ν s M y| ≤ K * frob M * genvT y ∧ |y.2| * |psiTEta ν s M y| ≤ K * frob M * genvT y

/-- **(b3) Gaussian envelope of the `s`-derivative with the weight `s` of `𝒦`** (source 4978,
5039-5043, 5063-5071, 5076-5079): `s|∂_s psiT| ≤ K(|M| + |sD|)(1+‖y‖)⁴e^{-‖y‖²/9}`, using
`νs ≤ 5/2` for the `ν`-factors produced by `∂_s a = ν`. -/
def PsiTSBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → 0 ≤ s → ν * s ≤ 5 / 2 → ∀ (M D : Mat3) (y : ℝ × ℝ),
    s * |psiTS ν s M D y| ≤ K * (frob M + frob (s • D)) * genvT y

/-- **(a3) Termwise `η`-differentiation of the lattice sum** (source 4978): the `η`-derivative
of `η ↦ Σ_j psiT(s, M, x_j(q, η))` is `Σ_j psiTEta(s, M, x_j)`, the envelope being uniform in
`η` (`pdc_genvT_le`). -/
def PsiAEtaTsum : Prop :=
  PsiTEtaDeriv → PsiTValBound → PsiTEtaBound →
    ∀ (ν s : ℝ), 0 < ν → 0 < s → ν * s ≤ 11 / 10 → ∀ (M : Mat3) (x : ℝ × ℝ),
      HasDerivAt (fun η => ∑' j : ℤ, psiT ν s M (xj ν j (x.1, η)))
        (∑' j : ℤ, psiTEta ν s M (xj ν j x)) x.2

/-- **(a4) Termwise `s`-differentiation of the lattice sum** (source 4978) along a `C¹` matrix
path (`M = A^y`, `C¹` on `s > 0` by `pdc_Ay_contDiffOn`). -/
def PsiASTsum : Prop :=
  PsiTSDeriv → PsiTValBound → PsiTSBound →
    ∀ (ν s : ℝ), 0 < ν → 0 < s → ν * s ≤ 11 / 10 → ∀ (Mf : ℝ → Mat3),
      ContDiffOn ℝ 1 Mf (Ioi 0) → ∀ x : ℝ × ℝ,
        HasDerivAt (fun t => ∑' j : ℤ, psiT ν t (Mf t) (xj ν j x))
          (∑' j : ℤ, psiTS ν s (Mf s) (deriv Mf s) (xj ν j x)) s

/-- **(c) Continuity in `x` of the lattice sums** of the term and of its `s`-derivative
(source 4978; locally uniform Gaussian majorant `pdc_genv_unif`), giving the a.e. measurability
in the cell norms. -/
def PsiASliceCont : Prop :=
  PsiTValBound → PsiTSBound →
    ∀ (ν s : ℝ), 0 < ν → 0 < s → ν * s ≤ 11 / 10 → ∀ (M D : Mat3),
      Continuous (fun x : ℝ × ℝ => ∑' j : ℤ, psiT ν s M (xj ν j x)) ∧
        Continuous (fun x : ℝ × ℝ => ∑' j : ℤ, psiTS ν s M D (xj ν j x))

/-! ## 4. The cell bound from the leaves -/

/-- From a pointwise bound `f ≤ P gEnv` and the envelope bound `GEnvL2`, the normalized cell
`L²` bound. -/
theorem pdc_cell_le {ν : ℝ} (C : ℝ) (k : ℕ)
    (hC : ∫⁻ x, ENNReal.ofReal (gEnv ν x ^ 2) ∂(UnforcedLeray.Cyl.avgμ ((ν ^ 2)⁻¹))
      ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k) ^ 2))
    (f : ℝ × ℝ → ℝ) (P B : ℝ) (hP : 0 ≤ P) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ P * gEnv ν x) (hPB : P * |C| * |ν⁻¹ ^ k| ≤ B) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal (B ^ 2) := by
  have hpt : ∀ x, ENNReal.ofReal (f x ^ 2) ≤
      ENNReal.ofReal (P ^ 2) * ENNReal.ofReal (gEnv ν x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc f x ^ 2 ≤ (P * gEnv ν x) ^ 2 := pow_le_pow_left₀ (hf0 x) (hf x) 2
      _ = P ^ 2 * gEnv ν x ^ 2 := by ring
  calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal (P ^ 2) * ENNReal.ofReal (gEnv ν x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_mono hpt
    _ = ENNReal.ofReal (P ^ 2) * ∫⁻ x, ENNReal.ofReal (gEnv ν x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (P ^ 2) * ENNReal.ofReal ((C * ν⁻¹ ^ k) ^ 2) := by
        gcongr
        exact hC
    _ = ENNReal.ofReal ((P * |C| * |ν⁻¹ ^ k|) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
        ring
    _ ≤ ENNReal.ofReal (B ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hPB 2)

/-- **`PsiADerivCell` from the eight leaves** (source 5063-5079, 4978, 5024).  Constant
`K₃ + K₄ + 2K₅` times the envelope constant of `gEnvL2`, `ν₀ = 1`. -/
theorem psiADerivCell_of (as : ℝ) (χf : ℝ → ℝ) (h1 : PsiTEtaDeriv) (h2 : PsiTSDeriv)
    (h3 : PsiTValBound) (h4 : PsiTEtaBound) (h5 : PsiTSBound) (h6 : PsiAEtaTsum)
    (h7 : PsiASTsum) (h8 : PsiASliceCont) : PsiADerivCell as χf := by
  intro hχ
  have H6 := h6 h1 h3 h4
  have H7 := h7 h2 h3 h5
  have H8 := h8 h3 h5
  obtain ⟨K3, hK3, B3⟩ := h3
  obtain ⟨K4, hK4, B4⟩ := h4
  obtain ⟨K5, hK5, B5⟩ := h5
  obtain ⟨C, k, hC⟩ := gEnvL2
  have hKt0 : 0 ≤ K3 + K4 + 2 * K5 := by positivity
  refine ⟨(K3 + K4 + 2 * K5) * |C|, k, 1, one_pos, fun ν hν hν1 A hA s hs hs1 => ?_⟩
  dsimp only
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hs1; linarith
  have hνs' : ν * s ≤ 5 / 2 := by linarith
  have hFM : 0 ≤ frob (Ay ν χf A s) := pdc_frob_nonneg _
  have hFD : 0 ≤ frob (s • deriv (Ay ν χf A) s) := pdc_frob_nonneg _
  have hMx0 : 0 ≤ frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s) := add_nonneg hFM hFD
  have hMxA : frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)
      ≤ s ^ (5 / 2 : ℝ) * affM ν χf A :=
    fac_frob_Ay_le ν χf A (affMBdd as χf hχ ν hν A hA) s hs hs1
  have hAC1 := pdc_Ay_contDiffOn hχ hA ν
  -- the comparison `K' F g ≤ Kt Mx g`
  have hmono : ∀ (K' F y : ℝ), 0 ≤ F → K' ≤ K3 + K4 + 2 * K5 →
      F ≤ frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s) → 0 ≤ y →
      K' * F * y ≤ (K3 + K4 + 2 * K5) *
        (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * y := by
    intro K' F y hF hK' hFM' hy
    exact mul_le_mul_of_nonneg_right (mul_le_mul hK' hFM' hF hKt0) hy
  -- (c) the value
  have hcb : ∀ x : ℝ × ℝ, |PsiA ν χf A s x| ≤ (K3 + K4 + 2 * K5) *
      (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * gEnv ν x := by
    intro x
    rw [pdc_PsiA_eq ν χf A s x]
    have hs' := (pdc_genv_summable hν x).hasSum.mul_left (K3 * frob (Ay ν χf A s))
    have hb := tsum_of_norm_bounded (f := fun j : ℤ => psiT ν s (Ay ν χf A s) (xj ν j x)) hs'
      (fun j => by
        rw [Real.norm_eq_abs]
        exact B3 ν s hν hs.le hνs' (Ay ν χf A s) (xj ν j x))
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [← pdc_gEnv_eq]
    exact hmono K3 _ _ hFM (by linarith) (by linarith) (gEnv_nonneg ν x)
  -- (a) the `η`-weighted `η`-derivative
  have hab : ∀ x : ℝ × ℝ, |x.2| * |fderiv ℝ (PsiA ν χf A s) x (ei 1)| ≤ (K3 + K4 + 2 * K5) *
      (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * gEnv ν x := by
    intro x
    have hg0 : 0 ≤ gEnv ν x := gEnv_nonneg ν x
    by_cases hd : DifferentiableAt ℝ (PsiA ν χf A s) x
    · have hl : HasDerivAt (fun η : ℝ => ((x.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x.2 :=
        (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
      have hd' : HasFDerivAt (PsiA ν χf A s) (fderiv ℝ (PsiA ν χf A s) x) (x.1, x.2) :=
        hd.hasFDerivAt
      have hc1 : HasDerivAt (fun η : ℝ => PsiA ν χf A s (x.1, η))
          (fderiv ℝ (PsiA ν χf A s) x ((0 : ℝ), (1 : ℝ))) x.2 :=
        hd'.comp_hasDerivAt x.2 hl
      have hc2 : HasDerivAt (fun η : ℝ => PsiA ν χf A s (x.1, η))
          (∑' j : ℤ, psiTEta ν s (Ay ν χf A s) (xj ν j x)) x.2 := by
        have e : (fun η : ℝ => PsiA ν χf A s (x.1, η)) =
            fun η => ∑' j : ℤ, psiT ν s (Ay ν χf A s) (xj ν j (x.1, η)) :=
          funext fun η => pdc_PsiA_eq ν χf A s (x.1, η)
        rw [e]
        exact H6 ν s hν hs hνs (Ay ν χf A s) x
      have hei : ei 1 = ((0 : ℝ), (1 : ℝ)) := by simp [ei]
      rw [hei, hc1.unique hc2, ← abs_mul, ← tsum_mul_left]
      have hs' := (pdc_genv_summable hν x).hasSum.mul_left (K4 * frob (Ay ν χf A s))
      have hb := tsum_of_norm_bounded
        (f := fun j : ℤ => x.2 * psiTEta ν s (Ay ν χf A s) (xj ν j x)) hs'
        (fun j => by
          rw [Real.norm_eq_abs, abs_mul]
          exact (B4 ν s hν hs.le hνs' (Ay ν χf A s) (xj ν j x)).2)
      rw [Real.norm_eq_abs] at hb
      refine hb.trans ?_
      rw [← pdc_gEnv_eq]
      exact hmono K4 _ _ hFM (by linarith) (by linarith) hg0
    · rw [fderiv_zero_of_not_differentiableAt hd]
      simp only [ContinuousLinearMap.zero_apply, abs_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hKt0 hMx0) hg0
  -- (b) the `s`-weighted `s`-derivative
  have hderS : ∀ x : ℝ × ℝ, deriv (fun s' => PsiA ν χf A s' x) s =
      ∑' j : ℤ, psiTS ν s (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x) := by
    intro x
    have e : (fun s' => PsiA ν χf A s' x) =
        fun t => ∑' j : ℤ, psiT ν t (Ay ν χf A t) (xj ν j x) :=
      funext fun t => pdc_PsiA_eq ν χf A t x
    rw [e]
    exact (H7 ν s hν hs hνs (Ay ν χf A) hAC1 x).deriv
  have hbb : ∀ x : ℝ × ℝ, 2 * s * |deriv (fun s' => PsiA ν χf A s' x) s| ≤ (K3 + K4 + 2 * K5) *
      (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * gEnv ν x := by
    intro x
    have hg0 : 0 ≤ gEnv ν x := gEnv_nonneg ν x
    rw [hderS x]
    have hs' := (pdc_genv_summable hν x).hasSum.mul_left
      (K5 * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)))
    have hb := tsum_of_norm_bounded
      (f := fun j : ℤ => s * psiTS ν s (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x)) hs'
      (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs]
        exact B5 ν s hν hs.le hνs' (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x))
    rw [tsum_mul_left, Real.norm_eq_abs, abs_mul, abs_of_pos hs, ← pdc_gEnv_eq] at hb
    calc 2 * s * |∑' j : ℤ, psiTS ν s (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x)|
        = 2 * (s * |∑' j : ℤ, psiTS ν s (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x)|) := by
          ring
      _ ≤ 2 * (K5 * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * gEnv ν x) := by
          gcongr
      _ = (2 * K5) * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * gEnv ν x := by
          ring
      _ ≤ _ := hmono (2 * K5) _ _ hMx0 (by linarith) le_rfl hg0
  -- measurability
  have hcont := H8 ν s hν hs hνs (Ay ν χf A s) (deriv (Ay ν χf A) s)
  have hcm : Measurable (fun x : ℝ × ℝ => |PsiA ν χf A s x|) := by
    have e : (fun x : ℝ × ℝ => |PsiA ν χf A s x|) =
        fun x => |∑' j : ℤ, psiT ν s (Ay ν χf A s) (xj ν j x)| :=
      funext fun x => by rw [pdc_PsiA_eq ν χf A s x]
    rw [e]
    exact (continuous_abs.comp hcont.1).measurable
  have hbm : Measurable (fun x : ℝ × ℝ => 2 * s * |deriv (fun s' => PsiA ν χf A s' x) s|) := by
    have e : (fun x : ℝ × ℝ => 2 * s * |deriv (fun s' => PsiA ν χf A s' x) s|) =
        fun x => 2 * s * |∑' j : ℤ, psiTS ν s (Ay ν χf A s) (deriv (Ay ν χf A) s) (xj ν j x)| :=
      funext fun x => by rw [hderS x]
    rw [e]
    exact (continuous_const.mul (continuous_abs.comp hcont.2)).measurable
  have ham : Measurable (fun x : ℝ × ℝ => |x.2| * |fderiv ℝ (PsiA ν χf A s) x (ei 1)|) :=
    (continuous_abs.comp continuous_snd).measurable.mul
      (continuous_abs.measurable.comp (measurable_fderiv_apply_const ℝ (PsiA ν χf A s) (ei 1)))
  -- the cell bound
  have hB : (K3 + K4 + 2 * K5) * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * |C| *
      |ν⁻¹ ^ k| ≤ (K3 + K4 + 2 * K5) * |C| * ν⁻¹ ^ k * affM ν χf A *
        (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) := by
    rw [abs_of_pos (pow_pos (inv_pos.2 hν) k)]
    have hA0 : 0 ≤ affM ν χf A := affM_nonneg ν χf A
    have h32 : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    have hle : frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)
        ≤ affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) := by
      calc _ ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := hMxA
        _ ≤ affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) := by
          nlinarith [mul_nonneg hA0 h32]
    have hK : 0 ≤ (K3 + K4 + 2 * K5) * |C| * ν⁻¹ ^ k := by
      have := pow_pos (inv_pos.2 hν) k
      positivity
    calc (K3 + K4 + 2 * K5) * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) * |C| *
          ν⁻¹ ^ k
        = ((K3 + K4 + 2 * K5) * |C| * ν⁻¹ ^ k) *
          (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) := by ring
      _ ≤ ((K3 + K4 + 2 * K5) * |C| * ν⁻¹ ^ k) *
          (affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hle hK
      _ = _ := by ring
  have hP : 0 ≤ (K3 + K4 + 2 * K5) * (frob (Ay ν χf A s) + frob (s • deriv (Ay ν χf A) s)) :=
    mul_nonneg hKt0 hMx0
  refine ⟨ham.aemeasurable, hbm.aemeasurable, hcm.aemeasurable, ?_, ?_, ?_⟩
  · exact pdc_cell_le C k (hC ν hν hν1) _ _ _ hP (fun x => by positivity) hab hB
  · exact pdc_cell_le C k (hC ν hν hν1) _ _ _ hP (fun x => by positivity) hbb hB
  · exact pdc_cell_le C k (hC ν hν hν1) _ _ _ hP (fun x => abs_nonneg _) hcb hB

end UnforcedLeray.Short.PartIIIb.Concrete
