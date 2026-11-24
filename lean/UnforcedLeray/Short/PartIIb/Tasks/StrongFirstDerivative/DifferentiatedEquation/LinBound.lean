import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldLp
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `PartII-b:S1/1/1`: `DiffEqLinBound` (SP 2525-2534, 2388-2394, 1217-1220)

Source of record `the November 2 reference manuscript`.

The linear term is represented by the field `GELinField p z g h j` (`gELinIBP`), a combination of
`rep g, rep h, rep w` with coefficients `raw, ∂raw, ∂²raw`.  The polynomial-in-`ν⁻¹` bounds on these
coefficients come from `ringBoundedDerivs` (SP 1217-1219), the bounds on `g, h` from
`grad_and_hess_bound_of_geData`.  The `Y_{q₀}` norm of the representing element is computed on
the period cell: for `IsRep a Λ` the cell `L^{q₀}` norm of `Λ` is `P^{1/q₀} ‖a‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Short.PartIIIb.Concrete (GELinField GELinRawOK gELinFieldMeas gELinFieldPer
  gELinFieldLp gELinIBP rawSmoothBdd rawSmoothBdd_ok rawD rawDD gAdj_rawD_bound gAdj_rawDD_bound
  gAdj_norm_le_sum_coord raw_eq_of R_ge_two)
open UnforcedLeray.B0412 (q0E q0E_ne_top)

namespace LinBoundSub

/-- The cell `L^q` integral of a representative. -/
theorem cell_lintegral {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {a : Yq P q} {Λ : ℝ × Space → CVec3} (hΛ : IsRep a Λ) :
    ∫⁻ x in Ioc (0 : ℝ) P ×ˢ (univ : Set Space), ‖Λ x‖ₑ ^ q.toReal =
      ENNReal.ofReal P * ‖a‖ₑ ^ q.toReal := by
  have hprod : (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) =
      ((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc 0 P)).symm
  have hmeas : AEMeasurable (fun x : ℝ × Space => ‖Λ x‖ₑ ^ q.toReal)
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space)) :=
    (hΛ.meas.measurable.enorm.pow_const _).aemeasurable
  rw [hprod, lintegral_prod _ hmeas]
  have h1 : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ q.toReal =
      ∫⁻ τ in Ioc (0 : ℝ) P, ‖a (τ : AddCircle P)‖ₑ ^ q.toReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hΛ.slice] with τ hτ
    rw [← UnforcedLeray.PhaseSpace.lintegral_enorm_rpow_Lp _ hq]
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    rw [hy]
  rw [h1]
  have h2 := UnforcedLeray.PhaseSpace.lintegral_Ioc_period (P := P)
    (fun θ : AddCircle P => ‖a θ‖ₑ ^ q.toReal) 0 0
  simp only [zero_add] at h2
  rw [h2, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
    UnforcedLeray.PhaseSpace.lintegral_enorm_rpow_Yq a hq]
  rfl

/-- The cell `L^q` norm of a representative. -/
theorem eLpNorm_cell {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {a : Yq P q} {Λ : ℝ × Space → CVec3} (hΛ : IsRep a Λ) :
    eLpNorm Λ q (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) =
      ENNReal.ofReal P ^ (1 / q.toReal) * ‖a‖ₑ := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have ht : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq, cell_lintegral hq hΛ,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  rw [mul_one_div_cancel ht.ne', ENNReal.rpow_one]

/-- Norm bound from a pointwise bound by a sum of representatives. -/
theorem norm_le_of_pointwise {P : ℝ} [Fact (0 < P)] {ι : Type*} [Fintype ι] {F : Yq P q0E}
    {Λ : ℝ × Space → CVec3}
    (hF : IsRep F Λ) (us : ι → Yq P q0E) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ x : ℝ × Space, ‖Λ x‖ ≤ K * ∑ i, ‖rep (us i) x.1 x.2‖) :
    ‖F‖ ≤ K * ∑ i, ‖us i‖ := by
  have hrep : ∀ u : Yq P q0E, IsRep u (fun x : ℝ × Space => rep u x.1 x.2) := fun u =>
    ⟨stronglyMeasurable_rep u, ae_of_all _ (fun τ => rep_slice u τ)⟩
  set μ : Measure (ℝ × Space) := volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal P ^ (1 / q0E.toReal) with hc
  have hP : 0 < P := Fact.out
  have hc0 : c ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hP) ENNReal.ofReal_ne_top).ne'
  have hctop : c ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h1 : eLpNorm Λ q0E μ ≤ eLpNorm (fun x : ℝ × Space =>
      K * ∑ i, ‖rep (us i) x.1 x.2‖) q0E μ := eLpNorm_mono_real hle
  have hmeas : ∀ i ∈ (Finset.univ : Finset ι), AEStronglyMeasurable
      (fun x : ℝ × Space => ‖rep (us i) x.1 x.2‖) μ := fun i _ =>
    (stronglyMeasurable_rep (us i)).norm.aestronglyMeasurable
  have hfun : (fun x : ℝ × Space => K * ∑ i, ‖rep (us i) x.1 x.2‖) =
      K • (∑ i ∈ (Finset.univ : Finset ι), fun x : ℝ × Space => ‖rep (us i) x.1 x.2‖) := by
    funext x; simp [Finset.sum_apply]
  have h2 : eLpNorm (fun x : ℝ × Space => K * ∑ i, ‖rep (us i) x.1 x.2‖) q0E μ ≤
      ‖K‖ₑ * ∑ i, eLpNorm (fun x : ℝ × Space => ‖rep (us i) x.1 x.2‖) q0E μ := by
    rw [hfun]
    refine (eLpNorm_const_smul_le).trans ?_
    gcongr
    exact eLpNorm_sum_le (f := fun i (x : ℝ × Space) => ‖rep (us i) x.1 x.2‖)
      (s := (Finset.univ : Finset ι)) (p := q0E) (μ := μ) hmeas (Fact.out : 1 ≤ q0E)
  have hu : ∀ i, eLpNorm (fun x : ℝ × Space => ‖rep (us i) x.1 x.2‖) q0E μ = c * ‖us i‖ₑ := by
    intro i
    rw [eLpNorm_norm (fun x : ℝ × Space => rep (us i) x.1 x.2)]
    exact eLpNorm_cell q0E_ne_top (hrep (us i))
  have hFn : eLpNorm Λ q0E μ = c * ‖F‖ₑ := eLpNorm_cell q0E_ne_top hF
  have h3 : c * ‖F‖ₑ ≤ c * (‖K‖ₑ * ∑ i, ‖us i‖ₑ) := by
    rw [← hFn]
    refine h1.trans (h2.trans (le_of_eq ?_))
    simp only [hu, ← Finset.mul_sum]
    ring
  have h4 : ‖F‖ₑ ≤ ‖K‖ₑ * ∑ i, ‖us i‖ₑ := (ENNReal.mul_le_mul_iff_right hc0 hctop).1 h3
  have hKe : ‖K‖ₑ = ENNReal.ofReal K := by
    rw [← ofReal_norm, Real.norm_of_nonneg hK]
  have h5 : ENNReal.ofReal ‖F‖ ≤ ENNReal.ofReal (K * ∑ i, ‖us i‖) := by
    rw [ofReal_norm, ENNReal.ofReal_mul hK,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
    simp only [ofReal_norm]
    rwa [hKe] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5

/-- A field with periodic `Y`-representative and the phase pairing. -/
theorem gELinField_rep (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period q0E)
    (h : Fin 3 → Fin 3 → Yq p.period q0E) (j : Fin 3) (hraw : GELinRawOK p) :
    ∃ F : Yq p.period q0E, IsRep F (GELinField p z g h j) ∧
      ∀ Φ, IsPhaseTest p.period Φ →
        phasePair p.period q0E Φ F = pairF p.period Φ (GELinField p z g h j) := by
  have hΛm : StronglyMeasurable (GELinField p z g h j) :=
    gELinFieldMeas p z g h j hraw.1
  have hper : ∀ᵐ τ : ℝ, (fun y => GELinField p z g h j (τ + p.period, y)) =ᵐ[volume]
      (fun y => GELinField p z g h j (τ, y)) :=
    ae_of_all _ (fun τ => ae_of_all _ (fun y =>
      UnforcedLeray.Short.PartIIIb.Concrete.gELinFieldPer p z g h j hraw.1 τ y))
  have hfin := UnforcedLeray.Short.PartIIIb.Concrete.gELinFieldLp p z g h j hraw
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    q0E q0E_ne_top p.period (GELinField p z g h j) hΛm hper hfin
  refine ⟨F, hF, fun Φ hΦ => ?_⟩
  have hae : ∀ᵐ τ : ℝ, (fun y => GELinField p z g h j (τ, y)) =ᵐ[volume]
      (fun y => rep F τ y) := by
    filter_upwards [hF.slice] with τ hτ
    exact hτ.trans (rep_slice F τ).symm
  have hint : ∀ᵐ τ : ℝ, ∫ y, dotL (Φ (τ, y)) (rep F τ y) =
      ∫ y, dotL (Φ (τ, y)) (GELinField p z g h j (τ, y)) := by
    filter_upwards [hae] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ] with y hy
    exact congrArg (dotL (Φ (τ, y))) hy.symm
  rw [phasePair_eq_pairF_rep hΦ F]
  unfold pairF phaseInt
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hint] with τ hτ _
  exact hτ

/-- Pointwise bound of the field `GELinField` by a sum of representatives. -/
theorem field_pointwise (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period q0E)
    (h : Fin 3 → Fin 3 → Yq p.period q0E) (j : Fin 3) {B : ℝ} (hB : 0 ≤ B)
    (hC : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (h0 : ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ ≤ B)
    (h1 : ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ ≤ B)
    (h2 : ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖ ≤ B)
    (x : ℝ × Space) :
    ‖GELinField p z g h j x‖ ≤ (18 * B) *
      (‖rep (g j) x.1 x.2‖ + ‖rep (p.wOf z) x.1 x.2‖ + ∑ m, ‖rep (h j m) x.1 x.2‖ +
        ∑ m, ‖rep (g m) x.1 x.2‖) := by
  have hcoord : ∀ (v : CVec3) (i : Fin 3), ‖v i‖ ≤ ‖v‖ := fun v i => PiLp.norm_apply_le v i
  have hraw0 : ∀ m : Fin 3, ‖((p.raw x.1 x.2 m : ℝ) : ℂ)‖ ≤ B := by
    intro m
    rw [Complex.norm_real]
    calc ‖p.raw x.1 x.2 m‖ ≤ ‖p.raw x.1 x.2‖ := PiLp.norm_apply_le _ _
      _ = ‖iteratedFDeriv ℝ 0 (p.raw x.1) x.2‖ := (norm_iteratedFDeriv_zero (𝕜 := ℝ)).symm
      _ ≤ B := h0 _ _
  set aG := ‖rep (g j) x.1 x.2‖ with haG
  set aW := ‖rep (p.wOf z) x.1 x.2‖ with haW
  have hper : ∀ i : Fin 3, ‖GELinField p z g h j x i‖ ≤ B * (6 * aG + 6 * aW +
      ∑ m, ‖rep (h j m) x.1 x.2‖ + ∑ m, ‖rep (g m) x.1 x.2‖) := by
    intro i
    have hfi : GELinField p z g h j x i =
        -((∑ k : Fin 3, ((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k +
          ∑ m : Fin 3, (((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
            ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i)) +
        (∑ k : Fin 3, ((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k +
          ∑ m : Fin 3, (((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
            ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i))) := rfl
    rw [hfi, norm_neg]
    have b1 : ∀ k, ‖((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k‖ ≤ B * aG := fun k => by
      rw [norm_mul]
      exact mul_le_mul (gAdj_rawD_bound h1 x k i) (hcoord _ k) (norm_nonneg _) hB
    have b2 : ∀ m, ‖((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i‖ ≤ B * aG := fun m => by
      rw [norm_mul]
      exact mul_le_mul (gAdj_rawD_bound h1 x m m) (hcoord _ i) (norm_nonneg _) hB
    have b3 : ∀ m, ‖((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i‖ ≤
        B * ‖rep (h j m) x.1 x.2‖ := fun m => by
      rw [norm_mul]
      exact mul_le_mul (hraw0 m) (hcoord _ i) (norm_nonneg _) hB
    have b4 : ∀ k, ‖((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k‖ ≤ B * aW := fun k => by
      rw [norm_mul]
      exact mul_le_mul (gAdj_rawDD_bound hC h2 x k j i) (hcoord _ k) (norm_nonneg _) hB
    have b5 : ∀ m, ‖((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i‖ ≤ B * aW := fun m => by
      rw [norm_mul]
      exact mul_le_mul (gAdj_rawDD_bound hC h2 x m j m) (hcoord _ i) (norm_nonneg _) hB
    have b6 : ∀ m, ‖((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i‖ ≤
        B * ‖rep (g m) x.1 x.2‖ := fun m => by
      rw [norm_mul]
      exact mul_le_mul (gAdj_rawD_bound h1 x j m) (hcoord _ i) (norm_nonneg _) hB
    have s1 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun k => ((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k)
    have s2 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun m => ((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
            ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i)
    have s3 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun k => ((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k)
    have s4 := norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun m => ((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
            ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i)
    have t2 : ∀ m, ‖((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
            ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i‖ ≤
        B * aG + B * ‖rep (h j m) x.1 x.2‖ := fun m => (norm_add_le _ _).trans (add_le_add (b2 m) (b3 m))
    have t4 : ∀ m, ‖((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
            ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i‖ ≤
        B * aW + B * ‖rep (g m) x.1 x.2‖ := fun m => (norm_add_le _ _).trans (add_le_add (b5 m) (b6 m))
    have u1 := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => b1 k)
    have u2 := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => t2 m)
    have u3 := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => b4 k)
    have u4 := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => t4 m)
    have e := norm_add_le (∑ k : Fin 3, ((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k +
          ∑ m : Fin 3, (((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
            ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i))
        (∑ k : Fin 3, ((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k +
          ∑ m : Fin 3, (((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
            ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i))
    have e1 := norm_add_le (∑ k : Fin 3, ((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k)
          (∑ m : Fin 3, (((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
            ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i))
    have e2 := norm_add_le (∑ k : Fin 3, ((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k)
          (∑ m : Fin 3, (((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
            ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at u1 u2 u3 u4
    push_cast at u1 u2 u3 u4
    nlinarith [u1, u2, u3, u4, e, e1, e2, s1, s2, s3, s4]
  have hsum := gAdj_norm_le_sum_coord (GELinField p z g h j x)
  simp only [Fin.sum_univ_three] at hsum
  have hnn : 0 ≤ ∑ m, ‖rep (h j m) x.1 x.2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnn2 : 0 ≤ ∑ m, ‖rep (g m) x.1 x.2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have haG0 : 0 ≤ aG := norm_nonneg _
  have haW0 : 0 ≤ aW := norm_nonneg _
  nlinarith [hper 0, hper 1, hper 2, mul_nonneg hB haG0, mul_nonneg hB haW0,
    mul_nonneg hB hnn, mul_nonneg hB hnn2]

/-- `‖w‖ ≤ ‖z‖` for the correction of a state (`‖z‖ = ‖w‖_X + |A|`, `ℓ¹` norm). -/
theorem norm_wOf_le (p : Params) (z : p.Z) : ‖p.wOf z‖ ≤ ‖z‖ := by
  have h := norm_amb (P := p.period) (z : Amb p.period)
  have h2 : ‖z‖ = ‖(z : Amb p.period)‖ := (Submodule.coe_norm z).symm
  have h3 : p.wOf z = cw p.period (z : Amb p.period) := rfl
  rw [h2, h3, h]
  linarith [norm_nonneg (cΔ p.period (z : Amb p.period)), norm_nonneg (cT p.period (z : Amb p.period)),
    norm_nonneg (cA p.period (z : Amb p.period))]

/-- Polynomial-in-`ν⁻¹` bounds of the derivatives of orders `≤ 2` of `raw` (SP 1217-1219). -/
theorem raw_poly_bound (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C : ℝ) (d : ℕ) (ν₁ : ℝ), 0 < ν₁ ∧ ∀ (p : Params) (dd : ℝ), BgRegime p dd dm dp →
      p.ν ≤ ν₁ → ∀ m ≤ 2, ∀ (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ m (p.raw τ) y‖ ≤
          Short.PartIIa.polyConst C d p.ν (p.ν ^ (-(2 : ℝ))) := by
  obtain ⟨ν₀, hν₀, C, d, H⟩ := UnforcedLeray.Short.PartIIa.ringBoundedDerivs 2 2 (by norm_num)
  refine ⟨C, d, min (ν₀ / 2) dm, lt_min (by linarith) hdm, fun p dd hreg hν m hm τ y => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans (min_le_right _ _)
  obtain ⟨U, hU, hoff, hB⟩ := H p.ν ⟨p.ν_pos, by linarith⟩ _ _
    (isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R (R_ge_two hreg hν2)
  have hcont : ∀ τ, Continuous (fun y => (fun x : ℝ × Space => U x.1 x.2) (τ, y)) :=
    fun τ => (hU τ).continuous
  have hraw := raw_eq_of hb (fun x : ℝ × Space => U x.1 x.2) hcont
    (fun x hx => hoff x.1 x.2 hx) τ
  rw [hraw]
  exact hB m hm τ y

end LinBoundSub

/-- **Quantitative differentiated linear raw-convection bound** (`PartII-b:S1/1/1`). -/
theorem diffEqLinBound_proof : UnforcedLeray.Short.IIb.DiffEqLinBound := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C₁, d₁, ν₁, hν₁, HP⟩ := LinBoundSub.raw_poly_bound dm dp hdm
  obtain ⟨ν₂, hν₂, hok⟩ := rawSmoothBdd_ok (dp := dp) rawSmoothBdd hdm
  obtain ⟨C_GH, hC_GH, HGH⟩ := DiffEqSub.grad_and_hess_bound_of_geData
  have hC₁ : 0 < max C₁ 1 := lt_max_of_lt_right one_pos
  set C₁' : ℝ := max C₁ 1 * 3 ^ d₁ with hC₁'def
  have hC₁' : 0 < C₁' := by positivity
  refine ⟨18 * C₁' * (7 * C_GH + 1), 2 * d₁ + 1, min (min ν₁ ν₂) (min 1 (dm ^ 3 / 12)),
    by positivity, lt_min (lt_min hν₁ hν₂) (lt_min one_pos (by positivity)), ?_⟩
  intro p dd hreg hν _hSg _hmode z g₀ h hgd hh j
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν4 : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp1 : p.period ≤ 1 := UnforcedLeray.Short.PartIIIb.Concrete.bgCorr_period_le_one hreg hν4
  have hraw : GELinRawOK p := hok p dd hreg hν2'
  obtain ⟨F, hFrep, hFpair⟩ := LinBoundSub.gELinField_rep p z g₀ h j hraw
  refine ⟨F, fun Φ hΦ => ?_, ?_⟩
  · rw [hFpair Φ hΦ.1]
    exact gELinIBP p z g₀ h j hraw.1 hgd.2 (fun m => hh j m) Φ hΦ.1
  · set B : ℝ := C₁' * (p.ν ^ (2 * d₁))⁻¹ with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hpc : Short.PartIIa.polyConst C₁ d₁ p.ν (p.ν ^ (-(2 : ℝ))) ≤ B := by
      have hX : (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by
        calc (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ (3 * (p.ν ^ 2)⁻¹) ^ d₁ :=
              pow_le_pow_left₀ (by positivity) (one_add_inv_le hνpos hν3) d₁
          _ = 3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹) := by rw [mul_pow, inv_pow, ← pow_mul]
      have hXn : 0 ≤ (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ := by positivity
      dsimp only [Short.PartIIa.polyConst]
      calc C₁ * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁
          ≤ max C₁ 1 * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hXn
        _ ≤ max C₁ 1 * (3 ^ d₁ * ((p.ν ^ (2 * d₁))⁻¹)) :=
            mul_le_mul_of_nonneg_left hX hC₁.le
        _ = B := by rw [hBdef, hC₁'def]; ring
    have hbd : ∀ m ≤ 2, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ m (p.raw τ) y‖ ≤ B :=
      fun m hm τ y => (HP p dd hreg hν1 m hm τ y).trans hpc
    have hpt : ∀ x : ℝ × Space, ‖GELinField p z g₀ h j x‖ ≤ (18 * B) *
        ∑ i, ‖rep ((Sum.elim ![g₀ j, p.wOf z] (Sum.elim (h j) g₀) :
          Fin 2 ⊕ Fin 3 ⊕ Fin 3 → Yq p.period q0E) i) x.1 x.2‖ := by
      intro x
      refine (LinBoundSub.field_pointwise p z g₀ h j hB0 hraw.1.1
        (hbd 0 (by norm_num)) (hbd 1 (by norm_num)) (hbd 2 le_rfl) x).trans (le_of_eq ?_)
      simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hF := LinBoundSub.norm_le_of_pointwise hFrep _ (by positivity) hpt
    obtain ⟨hg, hhh⟩ := HGH p hp1 hν3 z g₀ h hgd hh
    have hw := LinBoundSub.norm_wOf_le p z
    have hinv1 : 1 ≤ (p.ν ^ 1)⁻¹ := by
      rw [pow_one]; exact (one_le_inv₀ hνpos).2 hν3
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have hzz : ‖z‖ ≤ (p.ν ^ 1)⁻¹ * ‖z‖ := by nlinarith
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at hF
    have hS : ‖g₀ j‖ + ‖p.wOf z‖ + ((‖h j 0‖ + ‖h j 1‖ + ‖h j 2‖) +
        (‖g₀ 0‖ + ‖g₀ 1‖ + ‖g₀ 2‖)) ≤ (7 * C_GH + 1) * ((p.ν ^ 1)⁻¹ * ‖z‖) := by
      nlinarith [hg j, hhh j 0, hhh j 1, hhh j 2, hg 0, hg 1, hg 2, hw, hzz]
    have hfin : 18 * B * ((7 * C_GH + 1) * ((p.ν ^ 1)⁻¹ * ‖z‖)) =
        18 * C₁' * (7 * C_GH + 1) * (p.ν ^ (2 * d₁ + 1))⁻¹ * ‖z‖ := by
      have e : p.ν ^ (2 * d₁ + 1) = p.ν ^ (2 * d₁) * p.ν := pow_succ _ _
      rw [e, pow_one, mul_inv, hBdef]
      ring
    calc ‖F‖ ≤ _ := hF
      _ ≤ 18 * B * ((7 * C_GH + 1) * ((p.ν ^ 1)⁻¹ * ‖z‖)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := hfin

end UnforcedLeray.Short.IIb
