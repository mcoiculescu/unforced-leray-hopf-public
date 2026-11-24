import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerBounds.Calc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerShifted
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# Bounds on the contracted kernel gradient `gradKCon` (`PointDom/KerBounds`)

For `t > 0`, `F_t(x) = gradKCon t x M` is `C²`; its `n`-th derivative (`n ≤ 2`) is bounded by
`27 B ‖M‖_F` whenever the `(n+1)`-st derivatives of all components of `K_t` are bounded by `B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KB

theorem kb_contDiff_fderiv_apply {f : Space → ℝ} (hf : ContDiff ℝ 3 f) (v : Space) :
    ContDiff ℝ 2 (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

/-- Finite sums: the `n`-th derivative of a finite sum is bounded by the sum of the bounds. -/
theorem kb_sum_iter {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ) (n : ℕ) (x : Space)
    (B : ι → ℝ) (hf : ∀ a ∈ s, ContDiff ℝ n (f a))
    (hB : ∀ a ∈ s, ‖iteratedFDeriv ℝ n (f a) x‖ ≤ B a) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ a ∈ s, f a y) x‖ ≤ ∑ a ∈ s, B a := by
  rw [iteratedFDeriv_sum hf, Finset.sum_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => hB a ha)

theorem kb_contDiff_gradKCon {t : ℝ} (ht : 0 < t) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ 2 (fun y => gradKCon t y M) := by
  have hK : ∀ i j : Fin 3, ContDiff ℝ 3 (fun x => IIIa.heatLerayK t i j x) :=
    fun i j => heatLerayKSmooth t ht i j
  unfold gradKCon
  refine PiLp.contDiff_toLp.comp ?_
  refine contDiff_pi.2 fun i => ?_
  refine ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_
  exact ((kb_contDiff_fderiv_apply (hK i j) (coordinateVector k)).mul contDiff_const)

theorem kb_abs_le_tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm
  have h1 : M j k ^ 2 ≤ ∑ i, ∑ j', M i j' ^ 2 := by
    calc M j k ^ 2 ≤ ∑ j', M j j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => M j j' ^ 2)
            (fun j' _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ i, ∑ j', M i j' ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j', M i j' ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  calc |M j k| = Real.sqrt (M j k ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ∑ j', M i j' ^ 2) := Real.sqrt_le_sqrt h1

/-- The `n`-th derivative of `∇K_t : M` for `n ≤ 2`. -/
theorem kb_gradKCon_iter {t : ℝ} (ht : 0 < t) (M : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (hn : n ≤ 2)
    (x : Space) (B : ℝ)
    (hB : ∀ i j : Fin 3, ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK t i j y) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => gradKCon t y M) x‖ ≤ 27 * B * IIIa.tensorNorm M := by
  have hK : ∀ i j : Fin 3, ContDiff ℝ 3 (fun x => IIIa.heatLerayK t i j x) :=
    fun i j => heatLerayKSmooth t ht i j
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hnN : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  have hG : ContDiffAt ℝ 2 (fun y => gradKCon t y M) x :=
    (kb_contDiff_gradKCon ht M).contDiffAt
  have hbr := kb_norm_iteratedFDeriv_vec hG hnN
  have hi : ∀ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => gradKCon t y M i) x‖ ≤
      9 * (IIIa.tensorNorm M * B) := by
    intro i
    have hfun : (fun y => gradKCon t y M i) =
        fun y => ∑ j : Fin 3, ∑ k : Fin 3, M j k • fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y
          (coordinateVector k) := by
      funext y
      simp only [gradKCon, PiLp.toLp_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hfun]
    have hΦ : ∀ j k : Fin 3, ContDiff ℝ n
        (fun y => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y (coordinateVector k)) :=
      fun j k => (kb_contDiff_fderiv_apply (hK i j) (coordinateVector k)).of_le hnN
    have hΦb : ∀ j k : Fin 3, ‖iteratedFDeriv ℝ n
        (fun y => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y (coordinateVector k)) x‖ ≤ B := by
      intro j k
      have hKa : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x' => IIIa.heatLerayK t i j x') x :=
        (hK i j).contDiffAt.of_le (by exact_mod_cast (show n + 1 ≤ 3 by omega))
      have h1 := kb_fderiv_apply_norm (f := fun x' => IIIa.heatLerayK t i j x') hKa
        (coordinateVector k)
      have hnorm : ‖coordinateVector k‖ = 1 := by
        unfold coordinateVector
        simp
      rw [hnorm, one_mul] at h1
      exact h1.trans (hB i j)
    have hin : ∀ j : Fin 3, ‖iteratedFDeriv ℝ n
        (fun y => ∑ k : Fin 3, M j k • fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y
          (coordinateVector k)) x‖ ≤ ∑ k : Fin 3, |M j k| * B := by
      intro j
      refine kb_sum_iter Finset.univ (fun k y => M j k • fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y
          (coordinateVector k)) n x (fun k => |M j k| * B)
        (fun k _ => (hΦ j k).const_smul (M j k)) ?_
      intro k _
      rw [iteratedFDeriv_const_smul_apply' (hΦ j k).contDiffAt, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hΦb j k) (abs_nonneg _)
    have hout := kb_sum_iter Finset.univ (fun j y => ∑ k : Fin 3, M j k • fderiv ℝ
        (fun x' => IIIa.heatLerayK t i j x') y (coordinateVector k)) n x
        (fun j => ∑ k : Fin 3, |M j k| * B)
        (fun j _ => ContDiff.sum fun k _ => (hΦ j k).const_smul (M j k)) (fun j _ => hin j)
    refine hout.trans ?_
    calc ∑ j : Fin 3, ∑ k : Fin 3, |M j k| * B
        ≤ ∑ j : Fin 3, ∑ k : Fin 3, IIIa.tensorNorm M * B :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (kb_abs_le_tensorNorm M j k) hB0
      _ = 9 * (IIIa.tensorNorm M * B) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  calc ‖iteratedFDeriv ℝ n (fun y => gradKCon t y M) x‖
      ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => gradKCon t y M i) x‖ := hbr
    _ ≤ ∑ i : Fin 3, 9 * (IIIa.tensorNorm M * B) := Finset.sum_le_sum fun i _ => hi i
    _ = 27 * B * IIIa.tensorNorm M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

/-- `|Δ G| ≤ 3 ‖D²G‖` for a `C²` vector field. -/
theorem kb_physLap_norm_le {G : Space → Space} (hG : ContDiff ℝ 2 G) (x : Space) :
    ‖physLap G x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 G x‖ := by
  have hnorm : ∀ j : Fin 3, ‖coordinateVector j‖ = 1 := by
    intro j
    unfold coordinateVector
    simp
  have hterm : ∀ j : Fin 3, ‖physPd2 G j j x‖ ≤ ‖iteratedFDeriv ℝ 2 G x‖ := by
    intro j
    have hcd : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) G x :=
      hG.contDiffAt.of_le (by norm_num)
    have h1 := kb_fderiv_apply_norm (f := G) (x := x) (n := 1) hcd (coordinateVector j)
    rw [norm_iteratedFDeriv_one, hnorm j, one_mul] at h1
    have hpd : physPd2 G j j x =
        (fderiv ℝ (fun y => fderiv ℝ G y (coordinateVector j)) x) (coordinateVector j) := rfl
    rw [hpd]
    calc _ ≤ ‖fderiv ℝ (fun y => fderiv ℝ G y (coordinateVector j)) x‖ *
          ‖coordinateVector j‖ := (fderiv ℝ (fun y => fderiv ℝ G y (coordinateVector j)) x).le_opNorm _
      _ = ‖fderiv ℝ (fun y => fderiv ℝ G y (coordinateVector j)) x‖ := by rw [hnorm j, mul_one]
      _ ≤ ‖iteratedFDeriv ℝ 2 G x‖ := h1
  calc ‖physLap G x‖ = ‖∑ j : Fin 3, physPd2 G j j x‖ := rfl
    _ ≤ ∑ j : Fin 3, ‖physPd2 G j j x‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 2 G x‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 3 * ‖iteratedFDeriv ℝ 2 G x‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

end UnforcedLeray.Short.PartIIIb.Concrete.KB

end
