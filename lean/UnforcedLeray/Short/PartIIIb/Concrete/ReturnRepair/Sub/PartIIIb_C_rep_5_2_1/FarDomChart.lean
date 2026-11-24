import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# Proof of `FarDomChart` (`PartIII-b:C/rep/5/2/1/1`, source 3604-3623, 3905-3912, 5585-5590)

Apply `IIIa.sepWDominated` (j = 0) to the masked source `T'` (the cut `e^δ s < R²/|z'|²` of
`sepWfar`), which is `IsSepSource` with `rOut = R e^{-δ/2}/√s`; the receiver gap `rIn - rOut =
(1-e^{-δ/2})R/√s` dominates `(1-e^{-δ/2})R/√S`, and `sepDom` is antitone in the gap and monotone in
the source. `merRe` costs `√2`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fd_floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

theorem fd_chartOf_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
  have hR' : R ≠ 0 := hR.ne'
  have hX : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  unfold NearInst.chartOf
  rw [hX, fd_floor_shift _ c hc]

theorem fd_cartLift_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3) (τ : ℝ)
    (z : Space) :
    NearInst.cartLift R c f (τ + 2 * c / R) z = NearInst.cartLift R c f τ z := by
  unfold NearInst.cartLift
  rw [fd_chartOf_period R c hR hc z τ]

/-- The masked-out region: if `|z'| > R e^{-δ/2}/√s` then `e^δ s < R²/|z'|²` fails. -/
theorem fd_cond_false (R s δ : ℝ) (hR : 0 < R) (hs : 0 < s) (z : Space)
    (hz : R * Real.exp (-(δ / 2)) / Real.sqrt s < Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) :
    ¬ (Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) := by
  intro hc
  set r := R * Real.exp (-(δ / 2)) / Real.sqrt s with hr
  set Q := z 0 ^ 2 + z 1 ^ 2 with hQ
  have hr0 : 0 ≤ r := by
    rw [hr]; positivity
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt (by positivity)
  have hQpos : 0 < Q := by
    have : 0 < Real.sqrt Q := lt_of_le_of_lt hr0 hz
    have := Real.sqrt_pos.mp this
    exact this
  have h1 : r ^ 2 < Q := by
    have := pow_lt_pow_left₀ hz hr0 (two_ne_zero)
    rw [hsq] at this
    exact this
  have hr2 : r ^ 2 = R ^ 2 * Real.exp (-(δ / 2)) ^ 2 / s := by
    rw [hr, div_pow, mul_pow, Real.sq_sqrt hs.le]
  have he : Real.exp (-(δ / 2)) ^ 2 * Real.exp δ = 1 := by
    rw [sq, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have : -(δ / 2) + (-(δ / 2) + δ) = 0 := by ring
    rw [this, Real.exp_zero]
  have hb : 0 < Real.exp (-(δ / 2)) ^ 2 := by positivity
  have hdiv : Real.exp δ * s * Q < R ^ 2 := by
    rw [lt_div_iff₀ hQpos] at hc
    linarith
  -- R² b < s Q, where b = e^{-δ}
  have h2 : R ^ 2 * Real.exp (-(δ / 2)) ^ 2 < s * Q := by
    rw [hr2, div_lt_iff₀ hs] at h1
    linarith
  -- multiply the first by b, use b e^δ = 1
  have h3 : Real.exp (-(δ / 2)) ^ 2 * (Real.exp δ * s * Q) <
      Real.exp (-(δ / 2)) ^ 2 * R ^ 2 :=
    mul_lt_mul_of_pos_left hdiv hb
  have h4 : Real.exp (-(δ / 2)) ^ 2 * (Real.exp δ * s * Q) = s * Q := by
    have : Real.exp (-(δ / 2)) ^ 2 * (Real.exp δ * s * Q) =
        (Real.exp (-(δ / 2)) ^ 2 * Real.exp δ) * (s * Q) := by ring
    rw [this, he, one_mul]
  nlinarith

theorem fd_sepDom_anti (a : ℝ) (j : ℕ) (D1 D2 : ℝ) (h : D2 ≤ D1)
    (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) :
    UnforcedLeray.Short.IIIa.sepDom a j D1 g τ y ≤
      UnforcedLeray.Short.IIIa.sepDom a j D2 g τ y := by
  unfold UnforcedLeray.Short.IIIa.sepDom
  refine lintegral_mono (fun l => mul_le_mul' le_rfl ?_)
  refine lintegral_mono (fun z => mul_le_mul' ?_ le_rfl)
  by_cases h1 : D1 ≤ ‖y - l • z‖
  · have h2 : D2 ≤ ‖y - l • z‖ := le_trans h h1
    simp only [UnforcedLeray.Short.IIIa.sepKd, if_pos h1, if_pos h2, le_refl]
  · simp [UnforcedLeray.Short.IIIa.sepKd, if_neg h1]

theorem fd_sepDom_mono (a : ℝ) (j : ℕ) (D : ℝ) (g1 g2 : ℝ → Space → ℝ≥0∞)
    (h : ∀ τ z, g1 τ z ≤ g2 τ z) (τ : ℝ) (y : Space) :
    UnforcedLeray.Short.IIIa.sepDom a j D g1 τ y ≤
      UnforcedLeray.Short.IIIa.sepDom a j D g2 τ y := by
  unfold UnforcedLeray.Short.IIIa.sepDom
  refine lintegral_mono (fun l => ?_)
  refine mul_le_mul' le_rfl ?_
  refine lintegral_mono (fun z => ?_)
  exact mul_le_mul' le_rfl (h _ _)

theorem fd_srcNorm_mask_le (R c s δ : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space) :
    UnforcedLeray.Short.IIIa.srcNorm
        (fun τ' z' => if Real.exp δ * s < R ^ 2 / (z' 0 ^ 2 + z' 1 ^ 2) then
          NearInst.cartLift R c f τ' z' else 0) τ z ≤
      UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) τ z := by
  unfold UnforcedLeray.Short.IIIa.srcNorm
  apply ENNReal.ofReal_le_ofReal
  dsimp only
  split_ifs
  · exact le_rfl
  · have h0 : UnforcedLeray.Short.IIIa.tensorNorm 0 = 0 := by
      simp [UnforcedLeray.Short.IIIa.tensorNorm]
    rw [h0]
    exact Real.sqrt_nonneg _

theorem fd_mask_source_meas (R c s δ : ℝ) (f : Chart → Ten3) (hf : Measurable f) (i j : Fin 3) :
    Measurable fun p : ℝ × Space => (fun τ' z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          NearInst.cartLift R c f τ' z else 0) p.1 p.2 i j := by
  have hcoord : ∀ k : Fin 3, Measurable fun p : ℝ × Space => p.2 k :=
    fun k => (T8_1.measurable_coord k).comp measurable_snd
  have hcond : MeasurableSet {p : ℝ × Space | Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2)} :=
    measurableSet_lt measurable_const
      (measurable_const.div (((hcoord 0).pow_const 2).add ((hcoord 1).pow_const 2)))
  have hc := T8_1.measurable_cartLift_entry R c f hf i j
  have key : ∀ p : ℝ × Space, (fun τ' z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          NearInst.cartLift R c f τ' z else 0) p.1 p.2 i j =
        if Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2) then
          NearInst.cartLift R c f p.1 p.2 i j else 0 := by
    intro p
    dsimp only
    split_ifs <;> rfl
  have hm : Measurable fun p : ℝ × Space =>
      if Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2) then
        NearInst.cartLift R c f p.1 p.2 i j else 0 :=
    Measurable.ite hcond hc measurable_const
  exact (funext key : _) ▸ hm

theorem fd_isSepSource (R c δ s : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3)
    (hf : Measurable f) (hs : 0 < s) :
    UnforcedLeray.Short.IIIa.IsSepSource (2 * c / R)
      (R * Real.exp (-(δ / 2)) / Real.sqrt s)
      (fun τ' z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          NearInst.cartLift R c f τ' z else 0) where
  measurable := fun i j => fd_mask_source_meas R c s δ f hf i j
  periodic := by
    intro τ z
    dsimp only
    rw [fd_cartLift_period R c hR hc f τ z]
  support := by
    intro τ z hz
    dsimp only
    rw [if_neg (fd_cond_false R s δ hR hs z hz)]

theorem fd_merRe_bound (w : Fin 3 → ℂ) :
    ‖NearInst.merRe (-w)‖ₑ ≤ ENNReal.ofReal (Real.sqrt 2) * ‖w‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  apply ENNReal.ofReal_le_ofReal
  have h0 := norm_le_pi_norm w 0
  have h2 := norm_le_pi_norm w 2
  have a0 : |(w 0).re| ≤ ‖w‖ := le_trans (Complex.abs_re_le_norm _) h0
  have a2 : |(w 2).re| ≤ ‖w‖ := le_trans (Complex.abs_re_le_norm _) h2
  have b0 : (w 0).re ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a0 2
  have b2 : (w 2).re ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a2 2
  unfold NearInst.merRe
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  simp
  calc Real.sqrt ((w 0).re ^ 2 + (w 2).re ^ 2)
      ≤ Real.sqrt ((Real.sqrt 2 * ‖w‖) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        linarith
    _ = Real.sqrt 2 * ‖w‖ := Real.sqrt_sq (by positivity)

theorem farDomChart : FarDomChart := by
  obtain ⟨C0, hC0, hD⟩ := UnforcedLeray.Short.IIIa.sepWDominated
    UnforcedLeray.Short.IIIa.sepKernelBounds 0
  refine ⟨Real.sqrt 2 * max C0 1, by positivity, ?_⟩
  intro ν hν μ hμ R c δ S hR hc hδ hS f hf p hp0 hpS
  have hfm : Measurable f := hf.measurable
  have hsqrt_pos : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hsqrtS : Real.sqrt p.1 ≤ Real.sqrt S := Real.sqrt_le_sqrt hpS.le
  have he1 : Real.exp (-(δ / 2)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(δ / 2) < 0 by linarith)
    simpa using this
  have he0 : 0 < Real.exp (-(δ / 2)) := Real.exp_pos _
  have hrOut0 : 0 ≤ R * Real.exp (-(δ / 2)) / Real.sqrt p.1 := by positivity
  have hrlt : R * Real.exp (-(δ / 2)) / Real.sqrt p.1 < R / Real.sqrt p.1 := by
    apply div_lt_div_of_pos_right _ hsqrt_pos
    nlinarith
  have hrIn_rOut : R / Real.sqrt p.1 - R * Real.exp (-(δ / 2)) / Real.sqrt p.1 =
      (1 - Real.exp (-(δ / 2))) * R / Real.sqrt p.1 := by ring
  have h1e : 0 ≤ (1 - Real.exp (-(δ / 2))) * R := mul_nonneg (by linarith) hR.le
  have hD2le : (1 - Real.exp (-(δ / 2))) * R / Real.sqrt S ≤
      R / Real.sqrt p.1 - R * Real.exp (-(δ / 2)) / Real.sqrt p.1 := by
    rw [hrIn_rOut]
    gcongr
  have hy0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  have hy1 : (NearInst.chartY R p) 1 = 0 := by
    simp [NearInst.chartY]
  have hyle : R / Real.sqrt p.1 ≤ Real.sqrt ((NearInst.chartY R p) 0 ^ 2 + (NearInst.chartY R p) 1 ^ 2) := by
    rw [hy0, hy1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [Real.sqrt_sq (by positivity)]
  have hsep := fd_isSepSource R c δ p.1 hR hc f hfm hp0
  set Tm : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ := fun τ' z => if Real.exp δ * p.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          NearInst.cartLift R c f τ' z else 0 with hTm
  set G : ℝ → Space → ℝ≥0∞ := UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) with hG
  have hW : ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f) (NearInst.chartY R p)
        (NearInst.chartTau R p)‖ₑ ≤
      ENNReal.ofReal (max C0 1) * UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
        ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) G (NearInst.chartTau R p) (NearInst.chartY R p) := by
    have hWeq : ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f) (NearInst.chartY R p)
        (NearInst.chartTau R p)‖ₑ =
        UnforcedLeray.Short.IIIa.wDerivNorm ν (μ : ℂ) Tm 0 (NearInst.chartTau R p) (NearInst.chartY R p) := by
      unfold UnforcedLeray.Short.IIIa.wDerivNorm
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
      rfl
    have hchain : UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 (R / Real.sqrt p.1 - R * Real.exp (-(δ / 2)) / Real.sqrt p.1)
        (UnforcedLeray.Short.IIIa.srcNorm Tm) (NearInst.chartTau R p) (NearInst.chartY R p) ≤
        UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) G
          (NearInst.chartTau R p) (NearInst.chartY R p) := by
      have e1 := fd_sepDom_anti (2 * (μ : ℂ).re + 2) 0 _ _ hD2le (UnforcedLeray.Short.IIIa.srcNorm Tm)
        (NearInst.chartTau R p) (NearInst.chartY R p)
      have e2 := fd_sepDom_mono (2 * (μ : ℂ).re + 2) 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S)
        (UnforcedLeray.Short.IIIa.srcNorm Tm) G (fd_srcNorm_mask_le R c p.1 δ f)
        (NearInst.chartTau R p) (NearInst.chartY R p)
      simpa using le_trans e1 e2
    by_cases hTop : UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
        ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) G (NearInst.chartTau R p) (NearInst.chartY R p) = ⊤
    · rw [hTop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))).ne']
      exact le_top
    · have hfin : UnforcedLeray.Short.IIIa.sepDom (2 * (μ : ℂ).re + 2) 0
          (R / Real.sqrt p.1 - R * Real.exp (-(δ / 2)) / Real.sqrt p.1)
          (UnforcedLeray.Short.IIIa.srcNorm Tm) (NearInst.chartTau R p) (NearInst.chartY R p) < ⊤ := by
        refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hTop)
        simpa using hchain
      have hD' := hD ν hν (μ : ℂ) (by simpa using hμ)
        (R * Real.exp (-(δ / 2)) / Real.sqrt p.1) (R / Real.sqrt p.1) (2 * c / R) hrOut0 hrlt
        (by positivity) Tm hsep (NearInst.chartTau R p) (NearInst.chartY R p) hyle hfin
      simp only [Complex.ofReal_re] at hD'
      rw [hWeq]
      refine le_trans hD' ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) ?_
      exact hchain
  calc ‖NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
          (NearInst.chartY R p) (NearInst.chartTau R p))‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt 2) * ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
          (NearInst.chartY R p) (NearInst.chartTau R p)‖ₑ := fd_merRe_bound _
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * (ENNReal.ofReal (max C0 1) * UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
        ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) G (NearInst.chartTau R p) (NearInst.chartY R p)) :=
          mul_le_mul' le_rfl hW
    _ = ENNReal.ofReal (Real.sqrt 2 * max C0 1) * UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
        ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) G (NearInst.chartTau R p) (NearInst.chartY R p) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]


end UnforcedLeray.Short.PartIIIb.Concrete
