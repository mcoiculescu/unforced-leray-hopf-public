import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PairInt

/-!
# `PartIII-a:T21/2/7/2/1/1/3/2`: domination of the adjoint multiplier (`AdjMDominated`)

Source: `the November 2 reference manuscript` lines 3052-3061.
The dominating function is `ν|Δψ| + C(|∂₀ψ| + |∂₁ψ|) + C jb^{-(m+2)/2}(|uψ₀| + |uψ₁|)`
(written with norms), with `C` the time-local bound of the train at `s`.
Square integrability on the cell of `jb^{-1}`, and of `jb^{-1}|uψ_j|` through the bounded
mean shear (`meanShear`), gives membership in `X_m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- `jb^{-1}` is square integrable on the whole plane, hence on the cell. -/
theorem amd_jb_inv_memLp (c : ℝ) :
    MemLp (fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ (-1 : ℝ)) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  have hcont : Continuous fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ (-1 : ℝ) :=
    UnforcedLeray.B0579.continuous_jb_rpow _
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hI : Integrable (fun z : ℝ × ℝ => (1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹)
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq
  refine Integrable.mono' hI.restrict ((hcont.pow 2).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  have hj : 0 < UnforcedLeray.B0579.jb x := UnforcedLeray.B0579.jb_pos x
  have hsq : (UnforcedLeray.B0579.jb x ^ (-1 : ℝ)) ^ 2 = (UnforcedLeray.B0579.jb x ^ 2)⁻¹ := by
    rw [Real.rpow_neg_one, inv_pow]
  rw [Real.norm_of_nonneg (sq_nonneg _), hsq, ← mul_inv]
  apply inv_anti₀ (by positivity)
  unfold UnforcedLeray.B0579.jb
  nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_nonneg (sq_nonneg x.1) (sq_nonneg x.2)]

/-- A bounded-mean-shear weighted piece: `jb^{-1}|U|` is in `L²(cell)` when `U - S ∈ L²(cell)`,
`S` measurable and bounded by `K`. -/
theorem amd_jbinv_abs_memLp {c : ℝ} {U S : ℝ × ℝ → ℝ} {K : ℝ}
    (hU : MemLp (fun x => U x - S x) 2 (volume.restrict (UnforcedLeray.B0579.cell c)))
    (hS : Measurable S) (hSK : ∀ x, |S x| ≤ K) :
    MemLp (fun x => UnforcedLeray.B0579.jb x ^ (-1 : ℝ) * ‖U x‖) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  have hcont : Continuous fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ (-1 : ℝ) :=
    UnforcedLeray.B0579.continuous_jb_rpow _
  have hUm : AEStronglyMeasurable U (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have h1 := hU.aestronglyMeasurable.add hS.aestronglyMeasurable
    refine h1.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  have hA : MemLp (fun x => ‖U x - S x‖) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hU.norm
  have hK : MemLp (fun x => K * UnforcedLeray.B0579.jb x ^ (-1 : ℝ)) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := (amd_jb_inv_memLp c).const_mul K
  refine MemLp.of_le (hA.add hK) (hcont.aestronglyMeasurable.mul hUm.norm) ?_
  refine Eventually.of_forall fun x => ?_
  have hjb1 : 1 ≤ UnforcedLeray.B0579.jb x := by
    unfold UnforcedLeray.B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hinv : UnforcedLeray.B0579.jb x ^ (-1 : ℝ) = (UnforcedLeray.B0579.jb x)⁻¹ :=
    Real.rpow_neg_one _
  have hinv_nn : 0 ≤ (UnforcedLeray.B0579.jb x)⁻¹ := by positivity
  have hinv_le : (UnforcedLeray.B0579.jb x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hjb1
  have hUS : |U x| ≤ |U x - S x| + K := by
    have h := abs_add_le (U x - S x) (S x)
    rw [sub_add_cancel] at h
    linarith [hSK x]
  have hmain : (UnforcedLeray.B0579.jb x)⁻¹ * |U x| ≤
      |U x - S x| + K * (UnforcedLeray.B0579.jb x)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left hUS hinv_nn
    have h2 : (UnforcedLeray.B0579.jb x)⁻¹ * |U x - S x| ≤ |U x - S x| :=
      mul_le_of_le_one_left (abs_nonneg _) hinv_le
    nlinarith [h1, h2]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hSK x)
  have hnn : 0 ≤ ‖U x - S x‖ + K * UnforcedLeray.B0579.jb x ^ (-1 : ℝ) := by
    rw [hinv]; exact add_nonneg (norm_nonneg _) (mul_nonneg hK0 hinv_nn)
  show ‖UnforcedLeray.B0579.jb x ^ (-1 : ℝ) * ‖U x‖‖ ≤
    ‖‖U x - S x‖ + K * UnforcedLeray.B0579.jb x ^ (-1 : ℝ)‖
  rw [Real.norm_of_nonneg hnn, hinv, Real.norm_of_nonneg (mul_nonneg hinv_nn (norm_nonneg _))]
  simp only [Real.norm_eq_abs]
  linarith [hmain]

/-- The weighted cell pieces of the adjoint multiplier with the weight `jb^{-(m+2)/2}`. -/
theorem amd_piece_memLp {c m : ℝ} (C' : ℝ) {U S : ℝ × ℝ → ℝ} {K : ℝ}
    (hU : MemLp (fun x => U x - S x) 2 (volume.restrict (UnforcedLeray.B0579.cell c)))
    (hS : Measurable S) (hSK : ∀ x, |S x| ≤ K) :
    MemLp (fun x => C' * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * ‖U x‖) 2
      (UnforcedLeray.B0579.cellMeasure c m) := by
  refine (UnforcedLeray.B0579.memLp_cellMeasure_iff c m).2 ?_
  have h := (amd_jbinv_abs_memLp hU hS hSK).const_mul C'
  convert h using 1
  funext x
  have hpos := UnforcedLeray.B0579.jb_pos x
  have e : UnforcedLeray.B0579.jb x ^ (m / 2) * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) =
      UnforcedLeray.B0579.jb x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [UnforcedLeray.B0579.bracket_rpow]
  calc UnforcedLeray.B0579.jb x ^ (m / 2) * (C' * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) *
        ‖U x‖)
      = C' * (UnforcedLeray.B0579.jb x ^ (m / 2) * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2))) *
        ‖U x‖ := by ring
    _ = C' * (UnforcedLeray.B0579.jb x ^ (-1 : ℝ) * ‖U x‖) := by rw [e]; ring

/-- **Leaf 2** (SP 3052-3061): the domination `|adjM r| ≤ B` on the cell for `r ∈ [t, s]`, with
`B ∈ X_m`. -/
theorem adjMDominated (m : ℝ) : UnforcedLeray.Short.IIIa.AdjMDominated m := by
  unfold UnforcedLeray.Short.IIIa.AdjMDominated
  intro ν hν hν1 tr hbdd t s ht hts ψ uψ hψ hu
  obtain ⟨C, hC⟩ := hbdd s (le_of_lt (lt_of_le_of_lt ht hts))
  have hlap : MemLp (UnforcedLeray.Short.IIIa.lapP ψ) 2
      (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
    unfold UnforcedLeray.Short.IIIa.lapP
    exact (((hψ.pd 0).pd 0).memLp m).add (((hψ.pd 1).pd 1).memLp m)
  have hpsi1 : MemLp (fun x => ν * ‖UnforcedLeray.Short.IIIa.lapP ψ x‖) 2
      (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hlap.norm.const_mul ν
  have hpsi2 : MemLp (fun x => C * ‖UnforcedLeray.B0579.pd 0 ψ x‖) 2
      (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    ((hψ.pd 0).memLp m).norm.const_mul C
  have hpsi3 : MemLp (fun x => C * ‖UnforcedLeray.B0579.pd 1 ψ x‖) 2
      (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    ((hψ.pd 1).memLp m).norm.const_mul C
  have hu0 := amd_piece_memLp (c := ν ^ (-2 : ℝ)) (m := m) C (U := fun x => uψ x 0)
    (S := fun x => UnforcedLeray.Short.IIIa.meanShear (ν ^ (-2 : ℝ))
      (∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y) x 0)
    (K := |(∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y) / (2 * ν ^ (-2 : ℝ))|)
    (hu.1 0) (UnforcedLeray.Short.IIIa.PairIntAux.ms_measurable _ _ 0)
    (fun x => UnforcedLeray.Short.IIIa.PairIntAux.ms_abs_le _ _ 0 x)
  have hu1 := amd_piece_memLp (c := ν ^ (-2 : ℝ)) (m := m) C (U := fun x => uψ x 1)
    (S := fun x => UnforcedLeray.Short.IIIa.meanShear (ν ^ (-2 : ℝ))
      (∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y) x 1)
    (K := |(∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y) / (2 * ν ^ (-2 : ℝ))|)
    (hu.1 1) (UnforcedLeray.Short.IIIa.PairIntAux.ms_measurable _ _ 1)
    (fun x => UnforcedLeray.Short.IIIa.PairIntAux.ms_abs_le _ _ 1 x)
  refine ⟨fun x => ν * ‖UnforcedLeray.Short.IIIa.lapP ψ x‖ + C * ‖UnforcedLeray.B0579.pd 0 ψ x‖ +
    C * ‖UnforcedLeray.B0579.pd 1 ψ x‖ +
    C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * ‖uψ x 0‖ +
    C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * ‖uψ x 1‖, ?_, ?_⟩
  · exact (((hpsi1.add hpsi2).add hpsi3).add hu0).add hu1
  · intro r hr x hx
    have hrs : r ∈ Icc (0 : ℝ) s := ⟨le_trans ht hr.1, hr.2⟩
    obtain ⟨hv, hE⟩ := hC r hrs x hx
    have hkey : ∀ j : Fin 2, |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r) x| ≤
        C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) := by
      intro j
      have hp : 0 < UnforcedLeray.B0579.jb x ^ ((m + 2) / 2) :=
        Real.rpow_pos_of_pos (UnforcedLeray.B0579.jb_pos x) _
      rw [Real.rpow_neg (UnforcedLeray.B0579.jb_pos x).le]
      calc |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r) x|
          = (UnforcedLeray.B0579.jb x ^ ((m + 2) / 2))⁻¹ *
              (UnforcedLeray.B0579.jb x ^ ((m + 2) / 2) *
                |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r) x|) := by
            rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
        _ ≤ (UnforcedLeray.B0579.jb x ^ ((m + 2) / 2))⁻¹ * C :=
            mul_le_mul_of_nonneg_left (hE j) (inv_nonneg.2 hp.le)
        _ = C * (UnforcedLeray.B0579.jb x ^ ((m + 2) / 2))⁻¹ := mul_comm _ _
    have hx0 : |tr.v r x 0 * UnforcedLeray.B0579.pd 0 ψ x| ≤
        C * |UnforcedLeray.B0579.pd 0 ψ x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hv 0) (abs_nonneg _)
    have hx1 : |tr.v r x 1 * UnforcedLeray.B0579.pd 1 ψ x| ≤
        C * |UnforcedLeray.B0579.pd 1 ψ x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hv 1) (abs_nonneg _)
    have hy0 : |uψ x 0 * UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x| ≤
        C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * |uψ x 0| := by
      rw [abs_mul]
      calc |uψ x 0| * |UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x|
          ≤ |uψ x 0| * (C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2))) :=
            mul_le_mul_of_nonneg_left (hkey 0) (abs_nonneg _)
        _ = C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * |uψ x 0| := by ring
    have hy1 : |uψ x 1 * UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x| ≤
        C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * |uψ x 1| := by
      rw [abs_mul]
      calc |uψ x 1| * |UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x|
          ≤ |uψ x 1| * (C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2))) :=
            mul_le_mul_of_nonneg_left (hkey 1) (abs_nonneg _)
        _ = C * UnforcedLeray.B0579.jb x ^ (-((m + 2) / 2)) * |uψ x 1| := by ring
    have hl1 : ν * UnforcedLeray.Short.IIIa.lapP ψ x ≤
        ν * |UnforcedLeray.Short.IIIa.lapP ψ x| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hν.le
    have hl2 : -(ν * |UnforcedLeray.Short.IIIa.lapP ψ x|) ≤
        ν * UnforcedLeray.Short.IIIa.lapP ψ x := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (UnforcedLeray.Short.IIIa.lapP ψ x)) hν.le
      linarith
    have a0 := abs_le.1 hx0
    have a1 := abs_le.1 hx1
    have b0 := abs_le.1 hy0
    have b1 := abs_le.1 hy1
    unfold UnforcedLeray.Short.IIIa.adjM
    simp only [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, b0.1, b0.2, b1.1, b1.2, hl1, hl2]
