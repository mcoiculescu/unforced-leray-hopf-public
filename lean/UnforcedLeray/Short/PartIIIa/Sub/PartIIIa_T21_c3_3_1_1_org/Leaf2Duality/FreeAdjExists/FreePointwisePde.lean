import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.RegularOfSmooth
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Leaf 2 (`PartIII-a:T21/c3/3/1/1/2/2/2/1/2`): `FreePointwisePde`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958,
3060.

Proves that a spatially `C^∞` `c`-periodic version `φ'` (`c = ν⁻²`) of `IsFreeAdjointWeak` whose
spatial partials are jointly continuous on `[t, s) × ℝ²` satisfies the backward free PDE
`-∂_r φ' = ν Δ φ' + v · ∇ φ'` pointwise within `[t, b]` for every `b ∈ (t, s)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

namespace FreePointwisePdeAux

/-- Right-hand side of `∂_r φ' = -(ν Δ φ' + v · ∇ φ')`. -/
private def freeRhs {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ' : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  -((ν : ℂ) * stLap (φ' r) x +
    (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
      ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x))

/-- Product rule for `pdCx` on `ℂ`-valued differentiable functions. -/
private theorem pdCx_mul {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) (x : ℝ × ℝ) :
    pdCx j (fun y => f y * g y) x = pdCx j f x * g x + f x * pdCx j g x := by
  unfold pdCx
  change (fderiv ℝ (f * g) x) (B0579.dir j) = _
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- `pdCx` commutes with `Complex.ofReal`. -/
private theorem pdCx_ofReal {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (j : Fin 2) (x : ℝ × ℝ) :
    pdCx j (fun y => ((f y : ℝ) : ℂ)) x = ((B0579.pd j f x : ℝ) : ℂ) := by
  unfold pdCx B0579.pd
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (B0579.dir j) =
    Complex.ofRealCLM (fderiv ℝ f x (B0579.dir j))
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv]
  rfl

/-- Classical integration by parts on `B0579.cell c` for `freeAdjIntegrand` against a cylinder test,
using `cellIBP`, `ibp_pdpd_mrt`, and `tr.isTrain.solenoidal`. -/
private theorem cell_ibp_freeAdj {ν c : ℝ} (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {φ' : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hsm : ContDiff ℝ ∞ (φ' r)) (hper : ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, freeAdjIntegrand tr (φ' r) r ψ x =
      -∫ x in B0579.cell c, freeRhs tr φ' r x * (ψ x : ℂ) := by
  have hvC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v r x) :=
    tr.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨hr0, mem_univ x⟩)
  have hvr : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v r x j) := fun j =>
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).comp hvC
  have hvc : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v r x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp (hvr j)
  have hvper : ∀ x : ℝ × ℝ, tr.v r (x.1 + c, x.2) = tr.v r x :=
    fun x => tr.isTrain.periodic_v r hr0 x
  have hφd : Differentiable ℝ (φ' r) := hsm.differentiable (by simp)
  have hdiv : ∀ x : ℝ × ℝ, pdCx 0 (fun y => ((tr.v r y 0 : ℝ) : ℂ)) x +
      pdCx 1 (fun y => ((tr.v r y 1 : ℝ) : ℂ)) x = 0 := by
    intro x
    rw [pdCx_ofReal ((hvr 0).differentiable (by simp)) 0 x,
      pdCx_ofReal ((hvr 1).differentiable (by simp)) 1 x, ← Complex.ofReal_add]
    have hd := tr.isTrain.solenoidal r hr0 x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv ((hvr 0).differentiable (by simp)) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv ((hvr 1).differentiable (by simp)) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v r y 0) x + B0579.pd 1 (fun y => tr.v r y 1) x = 0 := hd
    rw [hd', Complex.ofReal_zero]
  obtain ⟨R₀, hR₀⟩ := hψ.band
  obtain ⟨R₁, hR₁⟩ := (hψ.pd 0).band
  obtain ⟨R₂, hR₂⟩ := (hψ.pd 1).band
  obtain ⟨R₃, hR₃⟩ := ((hψ.pd 0).pd 0).band
  obtain ⟨R₄, hR₄⟩ := ((hψ.pd 1).pd 1).band
  have hILapL : ∀ l : Fin 2,
      IntegrableOn (fun x => adjSpatial [l, l] (φ' r) x * (ψ x : ℂ)) (B0579.cell c) := by
    intro l
    exact integrableOn_cell_cplx (R := R₀)
      ((st_contDiff_adjSpatial hsm [l, l]).continuous.mul
        (Complex.continuous_ofReal.comp hψ.continuous))
      (fun x hx => by simp [hR₀ x hx])
  have hILapR0 : IntegrableOn (fun x => φ' r x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ))
      (B0579.cell c) :=
    integrableOn_cell_cplx (R := R₃)
      (hsm.continuous.mul (Complex.continuous_ofReal.comp ((hψ.pd 0).pd 0).continuous))
      (fun x hx => by simp [hR₃ x hx])
  have hILapR1 : IntegrableOn (fun x => φ' r x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ))
      (B0579.cell c) :=
    integrableOn_cell_cplx (R := R₄)
      (hsm.continuous.mul (Complex.continuous_ofReal.comp ((hψ.pd 1).pd 1).continuous))
      (fun x hx => by simp [hR₄ x hx])
  have hLap : ∫ x in B0579.cell c, φ' r x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ) =
      ∫ x in B0579.cell c, stLap (φ' r) x * (ψ x : ℂ) := by
    have hpt1 : (fun x => φ' r x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) = fun x =>
        φ' r x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
          φ' r x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x; unfold UnforcedLeray.Short.IIb.lapP; push_cast; ring
    have hpt2 : (fun x => stLap (φ' r) x * (ψ x : ℂ)) = fun x =>
        adjSpatial [0, 0] (φ' r) x * (ψ x : ℂ) + adjSpatial [1, 1] (φ' r) x * (ψ x : ℂ) := by
      funext x; unfold stLap; ring
    rw [hpt1, integral_add hILapR0 hILapR1,
      ← ibp_pdpd_mrt cellIBP c hc (φ' r) hsm hper ψ hψ 0,
      ← ibp_pdpd_mrt cellIBP c hc (φ' r) hsm hper ψ hψ 1,
      ← integral_add (hILapL 0) (hILapL 1), ← hpt2]
  have hGsm : ∀ l : Fin 2, ContDiff ℝ ∞ (fun y => φ' r y * ((tr.v r y l : ℝ) : ℂ)) :=
    fun l => hsm.mul (hvc l)
  have hGper : ∀ l : Fin 2, ∀ x : ℝ × ℝ,
      φ' r (x.1 + c, x.2) * ((tr.v r (x.1 + c, x.2) l : ℝ) : ℂ) =
        φ' r x * ((tr.v r x l : ℝ) : ℂ) :=
    fun l x => by rw [hper x, hvper x]
  have hIT0 : IntegrableOn (fun x => φ' r x * ((tr.v r x 0 : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ))
      (B0579.cell c) :=
    integrableOn_cell_cplx (R := R₁)
      ((hGsm 0).continuous.mul (Complex.continuous_ofReal.comp (hψ.pd 0).continuous))
      (fun x hx => by simp [hR₁ x hx])
  have hIT1 : IntegrableOn (fun x => φ' r x * ((tr.v r x 1 : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ))
      (B0579.cell c) :=
    integrableOn_cell_cplx (R := R₂)
      ((hGsm 1).continuous.mul (Complex.continuous_ofReal.comp (hψ.pd 1).continuous))
      (fun x hx => by simp [hR₂ x hx])
  have hIDG : ∀ l : Fin 2, IntegrableOn
      (fun x => pdCx l (fun y => φ' r y * ((tr.v r y l : ℝ) : ℂ)) x * (ψ x : ℂ))
      (B0579.cell c) := fun l =>
    integrableOn_cell_cplx (R := R₀)
      ((st_contDiff_adjSpatial (hGsm l) [l]).continuous.mul
        (Complex.continuous_ofReal.comp hψ.continuous))
      (fun x hx => by simp [hR₀ x hx])
  have hTpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => φ' r y * ((tr.v r y 0 : ℝ) : ℂ)) x * (ψ x : ℂ) +
        pdCx 1 (fun y => φ' r y * ((tr.v r y 1 : ℝ) : ℂ)) x * (ψ x : ℂ) =
      (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
        ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x) * (ψ x : ℂ) := by
    intro x
    rw [pdCx_mul hφd ((hvc 0).differentiable (by simp)) 0 x,
      pdCx_mul hφd ((hvc 1).differentiable (by simp)) 1 x]
    linear_combination (φ' r x * (ψ x : ℂ)) * hdiv x
  have hTrans : ∫ x in B0579.cell c,
      φ' r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c,
        (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
          ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x) * (ψ x : ℂ) := by
    have hpt : (fun x => φ' r x *
        ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) = fun x =>
        φ' r x * ((tr.v r x 0 : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ) +
          φ' r x * ((tr.v r x 1 : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ) := by
      funext x; push_cast; ring
    rw [hpt, integral_add hIT0 hIT1,
      cellIBP c _ ψ hc (hGsm 0) (hGper 0) hψ 0,
      cellIBP c _ ψ hc (hGsm 1) (hGper 1) hψ 1,
      ← neg_add, ← integral_add (hIDG 0) (hIDG 1)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hTpt)
  have hILapFull : IntegrableOn (fun x => φ' r x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ))
      (B0579.cell c) := by
    refine (hILapR0.add hILapR1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply, UnforcedLeray.Short.IIb.lapP]; push_cast; ring
  have hITFull : IntegrableOn
      (fun x => φ' r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ))
      (B0579.cell c) := by
    refine (hIT0.add hIT1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply]; push_cast; ring
  have hILapSt : IntegrableOn (fun x => stLap (φ' r) x * (ψ x : ℂ)) (B0579.cell c) := by
    refine ((hILapL 0).add (hILapL 1)).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply, stLap]; ring
  have hITSt : IntegrableOn
      (fun x => (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
        ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x) * (ψ x : ℂ)) (B0579.cell c) := by
    refine ((hIDG 0).add (hIDG 1)).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply]; exact hTpt x
  have hLHS : ∫ x in B0579.cell c, freeAdjIntegrand tr (φ' r) r ψ x =
      (ν : ℂ) * (∫ x in B0579.cell c, φ' r x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
        ∫ x in B0579.cell c,
          φ' r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
    have hpt : freeAdjIntegrand tr (φ' r) r ψ = fun x =>
        (ν : ℂ) * (φ' r x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
          φ' r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
      funext x; unfold freeAdjIntegrand; push_cast; ring
    rw [hpt, integral_sub (hILapFull.const_mul (ν : ℂ)) hITFull, integral_const_mul]
  have hRHS : -∫ x in B0579.cell c, freeRhs tr φ' r x * (ψ x : ℂ) =
      (ν : ℂ) * (∫ x in B0579.cell c, stLap (φ' r) x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c,
          (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
            ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x) * (ψ x : ℂ) := by
    rw [← integral_const_mul, ← integral_add (hILapSt.const_mul (ν : ℂ)) hITSt, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [freeRhs]; ring
  rw [hLHS, hRHS, hLap, hTrans]
  ring

/-- Joint continuity of `freeRhs tr φ'` on `Ico t s ×ˢ univ`. -/
private theorem continuousOn_freeRhs {ν c t s : ℝ} (ht : 0 ≤ t)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {φ' : ℝ → ℝ × ℝ → ℂ}
    (hcont : ∀ w : List (Fin 2),
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ' p.1) p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => freeRhs tr φ' p.1 p.2) (Ico t s ×ˢ univ) := by
  have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ico t s ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn.mono
      (prod_mono (fun r hr => ht.trans hr.1) subset_rfl)
  have hv : ∀ j : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ((tr.v p.1 p.2 j : ℝ) : ℂ))
      (Ico t s ×ˢ univ) := fun j =>
    Complex.continuous_ofReal.comp_continuousOn
      (((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn hv0)
  have hlap : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => stLap (φ' p.1) p.2) (Ico t s ×ˢ univ) :=
    (hcont [0, 0]).add (hcont [1, 1])
  unfold freeRhs
  exact ((continuousOn_const.mul hlap).add
    (((hv 0).mul (hcont [0])).add ((hv 1).mul (hcont [1])))).neg

/-- Continuity in `x` of `x ↦ ∫ τ in u..b, R_fn τ x` for jointly continuous `R_fn` on `[u, b] × ℝ²`. -/
private theorem continuous_interval_rhs {R_fn : ℝ → ℝ × ℝ → ℂ} {u b : ℝ} (hub : u ≤ b)
    (hR : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => R_fn p.1 p.2) (Icc u b ×ˢ univ)) :
    Continuous (fun x : ℝ × ℝ => ∫ τ in u..b, R_fn τ x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have heq_set : (fun x : ℝ × ℝ => ∫ τ in u..b, R_fn τ x) =
      fun x : ℝ × ℝ => ∫ τ in Ioc u b, R_fn τ x :=
    funext fun x => intervalIntegral.integral_of_le hub
  rw [heq_set]
  have hK : IsCompact (Icc u b ×ˢ Metric.closedBall x₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hKsub : Icc u b ×ˢ Metric.closedBall x₀ 1 ⊆ Icc u b ×ˢ univ :=
    prod_mono subset_rfl (subset_univ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hR.mono hKsub)
  set C₀ : ℝ := max M 0
  have hfin : (volume.restrict (Ioc u b)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hbound_int : Integrable (fun _ : ℝ => C₀) (volume.restrict (Ioc u b)) :=
    integrable_const C₀
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C₀) ?_ ?_ hbound_int ?_
  · refine Eventually.of_forall fun x => ?_
    have emb_τ : Continuous (fun τ : ℝ => (τ, x)) :=
      continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)
    have hslice : ContinuousOn (fun τ : ℝ => R_fn τ x) (Icc u b) :=
      hR.comp emb_τ.continuousOn (fun τ hτ => ⟨hτ, mem_univ x⟩)
    exact (hslice.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
    exact (hM (τ, x) ⟨Ioc_subset_Icc_self hτ, Metric.ball_subset_closedBall hx⟩).trans
      (le_max_left _ _)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
    have emb_x : Continuous (fun x : ℝ × ℝ => (τ, x)) :=
      (continuous_const : Continuous fun _ : ℝ × ℝ => τ).prodMk continuous_id
    have hslice_x : Continuous (fun x : ℝ × ℝ => R_fn τ x) :=
      continuousOn_univ.1
        (hR.comp emb_x.continuousOn (fun x _ => ⟨Ioc_subset_Icc_self hτ, mem_univ x⟩))
    exact hslice_x.continuousAt

/-- Fubini swap between `∫ τ in u..b` and `∫ x in B0579.cell c` against a cylinder test `ψ`. -/
private theorem fubini_interval_cell {c : ℝ} {R_fn : ℝ → ℝ × ℝ → ℂ} {u b : ℝ} (hub : u ≤ b)
    (hR : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => R_fn p.1 p.2) (Icc u b ×ˢ univ))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    (∫ τ in u..b, ∫ x in B0579.cell c, R_fn τ x * (ψ x : ℂ)) =
      ∫ x in B0579.cell c, (∫ τ in u..b, R_fn τ x) * (ψ x : ℂ) := by
  obtain ⟨R₀, hR₀⟩ := hψ.band
  let H : ℝ → ℝ × ℝ → ℂ := fun τ x => R_fn τ x * (ψ x : ℂ)
  have hH_prod : Integrable (Function.uncurry H)
      ((volume.restrict (Set.uIoc u b)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), ← IntegrableOn,
      Set.uIoc_of_le hub]
    have hψc : Continuous (fun p : ℝ × (ℝ × ℝ) => (ψ p.2 : ℂ)) :=
      (Complex.continuous_ofReal.comp hψ.continuous).comp continuous_snd
    have hHcpt_cont : ContinuousOn (Function.uncurry H) (Icc u b ×ˢ B0579.box c R₀) :=
      (hR.mono (prod_mono subset_rfl (subset_univ _))).mul hψc.continuousOn
    have hHcpt_int : IntegrableOn (Function.uncurry H) (Ioc u b ×ˢ B0579.box c R₀) :=
      (hHcpt_cont.integrableOn_compact
        (isCompact_Icc.prod (B0579.isCompact_box c R₀))).mono_set
        (prod_mono Ioc_subset_Icc_self subset_rfl)
    exact hHcpt_int.of_forall_sdiff_eq_zero
      (measurableSet_Ioc.prod (B0579.measurableSet_cell c))
      (fun p hp => by
        have hx_not : p.2 ∉ B0579.box c R₀ := fun hxB => hp.2 ⟨hp.1.1, hxB⟩
        have hgt : R₀ < |p.2.2| := by
          by_contra hle
          exact hx_not (B0579.mem_box_of_mem_cell hp.1.2 (not_lt.1 hle))
        simp [Function.uncurry, H, hR₀ p.2 hgt])
  rw [MeasureTheory.intervalIntegral_integral_swap hH_prod]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact intervalIntegral.integral_mul_const (ψ x : ℂ) (fun τ => R_fn τ x)

/-- A continuous `c`-periodic field whose cell integral against every cylinder test vanishes is
identically `0` on `ℝ²`. -/
private theorem eq_zero_of_cell_pairing {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (hFc : Continuous F) (hFp : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x)
    (hF0 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, F x * (ψ x : ℂ) = 0) :
    ∀ x : ℝ × ℝ, F x = 0 := by
  have htest : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ wuStrip c →
      ∫ x, g x • F x ∂(volume : Measure (ℝ × ℝ)) = 0 := by
    intro g hg hcpt hsub
    obtain ⟨A, R, hA, hbd⟩ := wkBounds hc hcpt.isCompact hsub
    have hv : ∀ y : ℝ × ℝ, (A < |y.1| ∨ R < |y.2|) → g y = 0 := by
      intro y hy
      by_contra hne
      obtain ⟨b1, b2⟩ := hbd y (subset_tsupport g (Function.mem_support.2 hne))
      rcases hy with h | h <;> linarith
    obtain ⟨Θ, hΘ, hΘeq⟩ := wkPeriodize hc hg hA hv
    have hout : ∀ x ∉ B0579.cell c, g x • F x = 0 := by
      intro x hx
      have hxn : x ∉ tsupport g := fun h => hx (wuStrip_subset_cell c (hsub h))
      rw [image_eq_zero_of_notMem_tsupport hxn, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B0579.cell c) hout]
    have e1 : ∫ x in B0579.cell c, g x • F x =
        ∫ x in B0579.cell c, F x * ((Θ x : ℝ) : ℂ) :=
      setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => by
        simp only [hΘeq x hx, Complex.real_smul]
        ring)
    rw [e1]
    exact hF0 Θ hΘ
  have hopen : IsOpen (wuStrip c) := isOpen_Ioo.prod isOpen_univ
  have hfund : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∈ wuStrip c → F x = 0 :=
    hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hFc.continuousOn.locallyIntegrableOn hopen.measurableSet) htest
  have hline : volume {x : ℝ × ℝ | x.1 = -(c / 2)} = 0 := by
    have e : {x : ℝ × ℝ | x.1 = -(c / 2)} = ({-(c / 2)} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext x; simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x.1 ≠ -(c / 2) := by
    rw [ae_iff]; simpa using hline
  have hcell0 : F =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    rw [EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell c)]
    filter_upwards [hfund, hnull] with x hx1 hx2 hxc
    exact hx1 ⟨⟨lt_of_le_of_ne hxc.1.1 (Ne.symm hx2), hxc.1.2⟩, mem_univ _⟩
  have hae0 : F =ᵐ[volume] (0 : ℝ × ℝ → ℂ) :=
    periodicAeOfCell c hc F 0 hFp (fun _ => rfl) hcell0
  exact congrFun ((Continuous.ae_eq_iff_eq volume hFc continuous_const).1 hae0)

private theorem cplx_sub_adj {G₀ Au Ab Iub Ibs Ius : ℂ}
    (hu : Au = G₀ + Ius) (hb : Ab = G₀ + Ibs) (hadj : Iub + Ibs = Ius) :
    Au - Ab = Iub := by
  linear_combination hu - hb - hadj

private theorem cplx_cand_zero {Au Ab J K : ℂ}
    (h1 : Au - Ab = K) (h2 : K = -J) :
    Au - (Ab - J) = 0 := by
  linear_combination h1 + h2

/-- Differentiate `u ↦ φ' u x` within `Icc t b` from the integral identity
`φ' u x = φ' b x - ∫ τ in u..b, R_fn τ x`. -/
private theorem hasDerivWithinAt_of_cand {R_fn φ' : ℝ → ℝ × ℝ → ℂ} {t s b r : ℝ}
    (hb : b ∈ Ioo t s) (hr : r ∈ Icc t b) (x : ℝ × ℝ)
    (hR_joint : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => R_fn p.1 p.2) (Ico t s ×ˢ univ))
    (h_cand : ∀ u ∈ Icc t b, φ' u x = φ' b x - ∫ τ in u..b, R_fn τ x) :
    HasDerivWithinAt (fun r' => φ' r' x) (R_fn r x) (Icc t b) r := by
  have emb : Continuous (fun τ : ℝ => (τ, x)) :=
    continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)
  have hI_cont : ContinuousOn (fun τ => R_fn τ x) (Icc t b) :=
    hR_joint.comp emb.continuousOn (fun τ hτ => ⟨⟨hτ.1, hτ.2.trans_lt hb.2⟩, mem_univ x⟩)
  let I : ℝ → ℂ := fun τ => R_fn τ x
  have hIt : ∀ u ∈ Icc t b, IntervalIntegrable I volume t u := fun u hu =>
    (hI_cont.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  have hF : ∀ u ∈ Icc t b,
      φ' u x = φ' b x - ((∫ τ in t..b, I τ) - ∫ τ in t..u, I τ) := by
    intro u hu
    rw [intervalIntegral.integral_interval_sub_left (hIt b ⟨hb.1.le, le_rfl⟩) (hIt u hu)]
    exact h_cand u hu
  have h1 : HasDerivWithinAt (fun u => ∫ τ in t..u, I τ) (I r) (Icc t b) r := by
    have : Fact (r ∈ Icc t b) := ⟨hr⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hIt r hr)
      (hI_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc r)
      (hI_cont.continuousWithinAt hr)
  have hderiv : HasDerivWithinAt
      (fun u => φ' b x - ((∫ τ in t..b, I τ) - ∫ τ in t..u, I τ))
      (I r) (Icc t b) r :=
    ((h1.const_sub (∫ τ in t..b, I τ)).const_sub (φ' b x)).congr_deriv (neg_neg (I r))
  exact hderiv.congr (fun u hu => hF u hu) (hF r hr)

/-- Integral representation `φ' u y = φ' b y - ∫ τ in u..b, freeRhs tr φ' τ y` on `Icc t b`. -/
private theorem phi_eq_cand_of_weak {ν c m t s : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hts : t < s)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {g : ℝ × ℝ → ℂ} {φ φ' : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν c m tr t s g φ)
    (hφ'ae : ∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r)
    (hφ'sm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r))
    (hφ'per : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x)
    (hR_joint : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => freeRhs tr φ' p.1 p.2) (Ico t s ×ˢ univ))
    {b u : ℝ} (hb : b ∈ Ioo t s) (hu : u ∈ Icc t b) (y : ℝ × ℝ) :
    φ' u y = φ' b y - ∫ τ in u..b, freeRhs tr φ' τ y := by
  have hb_Ico : b ∈ Ico t s := ⟨hb.1.le, hb.2⟩
  have hb_Icc : b ∈ Icc t s := ⟨hb.1.le, hb.2.le⟩
  have hu_Ico : u ∈ Ico t s := ⟨hu.1, hu.2.trans_lt hb.2⟩
  have hu_Icc : u ∈ Icc t s := ⟨hu.1, hu.2.trans hb.2.le⟩
  have hR_per : ∀ τ ∈ Ico t s, ∀ z : ℝ × ℝ,
      freeRhs tr φ' τ (z.1 + c, z.2) = freeRhs tr φ' τ z := by
    intro τ hτ z
    have hv := tr.isTrain.periodic_v τ (ht.trans hτ.1) z
    have hp00 := st_adjSpatial_periodic (hφ'per τ hτ) [0, 0] z
    have hp11 := st_adjSpatial_periodic (hφ'per τ hτ) [1, 1] z
    have hp0 := st_adjSpatial_periodic (hφ'per τ hτ) [0] z
    have hp1 := st_adjSpatial_periodic (hφ'per τ hτ) [1] z
    unfold freeRhs stLap
    simp only [adjSpatial] at hp0 hp1
    rw [hp00, hp11, hp0, hp1, hv]
  have hR_ub : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => freeRhs tr φ' p.1 p.2) (Icc u b ×ˢ univ) :=
    hR_joint.mono (prod_mono (fun τ hτ => ⟨hu.1.trans hτ.1, hτ.2.trans_lt hb.2⟩) subset_rfl)
  have hint_cont : Continuous (fun z : ℝ × ℝ => ∫ τ in u..b, freeRhs tr φ' τ z) :=
    continuous_interval_rhs hu.2 hR_ub
  let ψ_cand : ℝ × ℝ → ℂ := fun z => φ' b z - ∫ τ in u..b, freeRhs tr φ' τ z
  have hFc : Continuous (fun z : ℝ × ℝ => φ' u z - ψ_cand z) :=
    (hφ'sm u hu_Ico).continuous.sub ((hφ'sm b hb_Ico).continuous.sub hint_cont)
  have hFp : ∀ z : ℝ × ℝ,
      (φ' u (z.1 + c, z.2) - ψ_cand (z.1 + c, z.2)) = (φ' u z - ψ_cand z) := by
    intro z
    have heq_int : (∫ τ in u..b, freeRhs tr φ' τ (z.1 + c, z.2)) =
        ∫ τ in u..b, freeRhs tr φ' τ z := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hu.2] at hτ
      exact hR_per τ ⟨hu.1.trans hτ.1, hτ.2.trans_lt hb.2⟩ z
    simp only [ψ_cand, hφ'per u hu_Ico z, hφ'per b hb_Ico z, heq_int]
  have hF0 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ z in B0579.cell c, (φ' u z - ψ_cand z) * (ψ z : ℂ) = 0 := by
    intro ψ hψ
    obtain ⟨R₀, hR₀⟩ := hψ.band
    have hwu := hφ.weak ψ hψ u hu_Icc
    have hwb := hφ.weak ψ hψ b hb_Icc
    have hint_ub : IntervalIntegrable
        (fun τ => ∫ z in B0579.cell c, freeAdjIntegrand tr (φ τ) τ ψ z) volume u b :=
      (hφ.timeIntegrable ψ hψ).mono_set (by
        rw [Set.uIcc_of_le hu.2, Set.uIcc_of_le hts.le]
        exact Icc_subset_Icc hu.1 hb.2.le)
    have hint_bs : IntervalIntegrable
        (fun τ => ∫ z in B0579.cell c, freeAdjIntegrand tr (φ τ) τ ψ z) volume b s :=
      (hφ.timeIntegrable ψ hψ).mono_set (by
        rw [Set.uIcc_of_le hb.2.le, Set.uIcc_of_le hts.le]
        exact Icc_subset_Icc hb.1.le le_rfl)
    have hadj := intervalIntegral.integral_add_adjacent_intervals hint_ub hint_bs
    have hsub_φ : (∫ z in B0579.cell c, φ u z * (ψ z : ℂ)) -
        (∫ z in B0579.cell c, φ b z * (ψ z : ℂ)) =
        ∫ τ in u..b, ∫ z in B0579.cell c, freeAdjIntegrand tr (φ τ) τ ψ z :=
      cplx_sub_adj hwu hwb hadj
    have hae_u : (fun z => φ' u z * (ψ z : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun z => φ u z * (ψ z : ℂ) :=
      (ae_restrict_of_ae (hφ'ae u hu_Ico)).mono fun z hz => by simp only [hz]
    have hae_b : (fun z => φ' b z * (ψ z : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun z => φ b z * (ψ z : ℂ) :=
      (ae_restrict_of_ae (hφ'ae b hb_Ico)).mono fun z hz => by simp only [hz]
    have hibp_congr : (∫ τ in u..b, ∫ z in B0579.cell c, freeAdjIntegrand tr (φ τ) τ ψ z) =
        -∫ τ in u..b, ∫ z in B0579.cell c, freeRhs tr φ' τ z * (ψ z : ℂ) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hu.2] at hτ
      have hτ_Ico : τ ∈ Ico t s := ⟨hu.1.trans hτ.1, hτ.2.trans_lt hb.2⟩
      have hae_τ : freeAdjIntegrand tr (φ τ) τ ψ =ᵐ[volume.restrict (B0579.cell c)]
          freeAdjIntegrand tr (φ' τ) τ ψ :=
        (ae_restrict_of_ae (hφ'ae τ hτ_Ico).symm).mono fun z hz => by
          simp only [freeAdjIntegrand, hz]
      rw [integral_congr_ae hae_τ]
      exact cell_ibp_freeAdj hc tr (ht.trans hτ_Ico.1)
        (hφ'sm τ hτ_Ico) (hφ'per τ hτ_Ico) hψ
    have hswap := fubini_interval_cell hu.2 hR_ub hψ
    have hIu : IntegrableOn (fun z => φ' u z * (ψ z : ℂ)) (B0579.cell c) :=
      integrableOn_cell_cplx (R := R₀)
        ((hφ'sm u hu_Ico).continuous.mul (Complex.continuous_ofReal.comp hψ.continuous))
        (fun z hz => by simp [hR₀ z hz])
    have hIb : IntegrableOn (fun z => φ' b z * (ψ z : ℂ)) (B0579.cell c) :=
      integrableOn_cell_cplx (R := R₀)
        ((hφ'sm b hb_Ico).continuous.mul (Complex.continuous_ofReal.comp hψ.continuous))
        (fun z hz => by simp [hR₀ z hz])
    have hIint : IntegrableOn
        (fun z => (∫ τ in u..b, freeRhs tr φ' τ z) * (ψ z : ℂ)) (B0579.cell c) :=
      integrableOn_cell_cplx (R := R₀)
        (hint_cont.mul (Complex.continuous_ofReal.comp hψ.continuous))
        (fun z hz => by simp [hR₀ z hz])
    have hIcand : IntegrableOn (fun z => ψ_cand z * (ψ z : ℂ)) (B0579.cell c) := by
      refine (hIb.sub hIint).congr_fun (fun z _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.sub_apply, ψ_cand]; ring
    have hsplit : (∫ z in B0579.cell c, (φ' u z - ψ_cand z) * (ψ z : ℂ)) =
        (∫ z in B0579.cell c, φ' u z * (ψ z : ℂ)) -
          ((∫ z in B0579.cell c, φ' b z * (ψ z : ℂ)) -
            ∫ z in B0579.cell c,
              (∫ τ in u..b, freeRhs tr φ' τ z) * (ψ z : ℂ)) := by
      have h1 : (fun z => (φ' u z - ψ_cand z) * (ψ z : ℂ)) =
          fun z => φ' u z * (ψ z : ℂ) - ψ_cand z * (ψ z : ℂ) := by
        funext z; ring
      have h2 : (fun z => ψ_cand z * (ψ z : ℂ)) = fun z =>
          φ' b z * (ψ z : ℂ) -
            (∫ τ in u..b, freeRhs tr φ' τ z) * (ψ z : ℂ) := by
        funext z; simp only [ψ_cand]; ring
      rw [h1, integral_sub hIu hIcand, h2, integral_sub hIb hIint]
    rw [hsplit, integral_congr_ae hae_u, integral_congr_ae hae_b, ← hswap]
    exact cplx_cand_zero hsub_φ hibp_congr
  exact sub_eq_zero.1 (eq_zero_of_cell_pairing hc hFc hFp hF0 y)

/-- General-period `c > 0` pointwise backward PDE for a spatially `C^∞` representative `φ'`. -/
private theorem freePointwisePde_gen {ν c m t s : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hts : t < s)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {g : ℝ × ℝ → ℂ} {φ φ' : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν c m tr t s g φ)
    (hφ'ae : ∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r)
    (hφ'sm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r))
    (hφ'per : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x)
    (hφ'cont : ∀ w : List (Fin 2),
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ' p.1) p.2) (Ico t s ×ˢ univ))
    {b : ℝ} (hb : b ∈ Ioo t s) {r : ℝ} (hr : r ∈ Icc t b) (x : ℝ × ℝ) :
    HasDerivWithinAt (fun r' => φ' r' x) (freeRhs tr φ' r x) (Icc t b) r := by
  have hR_joint : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => freeRhs tr φ' p.1 p.2) (Ico t s ×ˢ univ) :=
    continuousOn_freeRhs ht tr hφ'cont
  exact hasDerivWithinAt_of_cand (R_fn := freeRhs tr φ') (φ' := φ') hb hr x hR_joint fun u hu =>
    phi_eq_cand_of_weak hc ht hts tr hφ hφ'ae hφ'sm hφ'per hR_joint hb hu x

end FreePointwisePdeAux

namespace Leaf2DualityNeeded

/-- **Proof of Leaf 2 (`FreePointwisePde`)** (`PartIII-a:T21/c3/3/1/1/2/2/2/1/2`, SP 2937-2958,
3060). -/
theorem freePointwisePde (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t s : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.FreePointwisePde ν m tr t s :=
  fun hν ht hts _ _ _ hφ _ hφ'ae hφ'sm hφ'per hφ'cont _ hb _ hr x =>
    FreePointwisePdeAux.freePointwisePde_gen (Real.rpow_pos_of_pos hν _) ht hts tr hφ
      hφ'ae hφ'sm hφ'per hφ'cont hb hr x

end Leaf2DualityNeeded

end UnforcedLeray.Short.IIIa.ComplFreeRateSub

export UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded (freePointwisePde)
