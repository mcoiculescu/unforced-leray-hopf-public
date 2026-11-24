import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.CylMemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Lemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.RawSmoothBdd3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Drift

/-!
# `PartIII-b:C/ward/12/3/2/2/2` (decomposition): `GEInletIBP2`

Source of record:
`the November 2 reference manuscript`,
lines 2542-2551 (inlet complete source in `W^{2,Y_p}`, vanishing of the inlet cutoff near the axis,
uniform in phase), 2381-2387, 2563-2569, 1206-1222.

With `inletFn2 p i j l = -∂_j(inletFn p i l) = ∂_j∂_l(inletSrc p i)`:
* **Identity**: `h2 : InletIBPIdentity` at `(i, l)` (discharging its `MemLp` hypothesis by
  `h1 : InletFnMemLp` at `(i, l)`) applied to the solenoidal test `∂_jΦ` (`gEW_isSolTest_dy`) gives
  `⟪L₀ᵗ∂_l∂_jΦ, Eᵢ⟫ + ⟪conv_raw ∂_l∂_jΦ, Eᵢ⟫ = ⟪∂_jΦ, inletFn p i l⟫`;
  integration by parts in `y_j` on each slice (`pairF_dy_of_smooth`, unconditionally proved here
  for any smooth field `G` and phase test `Φ`) turns the right side into
  `⟪Φ, inletFn2 p i j l⟫` once `inletSrc p i` is smooth (`inletSrc_contDiff`, from `RawJointSmooth`).
* **Integrability**: order-2 analogue of `inletFnMemLp_of` (`PartIII-b_C_ward_12_3_1_2_5_1_1.lean`):
  a.e. strong measurability `inletFn2Meas_of` (proved here from `RawJointSmooth`), the cylindrical
  envelope `inletFn2Envelope_of` (proved here from `InletFn2FarDecay` and `InletFn2NearBound`), and
  the proved `cylProfile_memLp` (`CylMemLp.lean`) give `InletFn2MemLp`.
* **Near-axis and far-field reductions**:
  - `inletFn2NearBound_of_jets` proves `InletFn2NearBound` from `RawJointSmooth`, `RawDerivBdd3`,
    `InletENearJets4` (order-4 near-axis axial decay of `E_i` and order-2 of `∂_τE_i`), and
    `InletSrcDeriv2Bound` (generic product-rule bound for `inletFn2`).
  - `inletFn2FarDecay_of_hom` proves `InletFn2FarDecay` from `InletEFarHom4` (order-4 far-field
    homogeneous jets of `E_i`), `InletFn2FarOfHom`, and the proved `inletDriftFar : InletDriftFar`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseInt)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The order-2 integrated-by-parts inlet field
`F_n = -∂_j(inletFn p i l) = ∂_j∂_l(L₀E_i + B_raw E_i)` (source 2542-2551). -/
def inletFn2 (p : Params) (i : Fin 2) (j l : Fin 3) : ℝ × UnforcedLeray.Space → CVec3 :=
  -(dy j (inletFn p i l))

/-- Slice-by-slice integration by parts in `y_j` for a scalar smooth function against a scalar
phase test on `ℝ³` (from `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, as in
`weakDyS_of_smooth`). -/
theorem slice_ibp_dy_smooth {P : ℝ} (j : Fin 3) {φ f : ℝ × UnforcedLeray.Space → ℂ}
    (hφ : IsPhaseTest P φ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    ∫ y, dy j φ (t, y) * f (t, y) = -∫ y, φ (t, y) * dy j f (t, y) := by
  obtain ⟨R, hR⟩ := hφ.bounded_support
  obtain ⟨R', hR'⟩ := (hφ.dy j).bounded_support
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdf := contDiff_dy' hf j
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hdφ := contDiff_dy' hφ.smooth j
  have hc : ∀ {g : ℝ × UnforcedLeray.Space → ℂ},
      Continuous g → Continuous fun y : UnforcedLeray.Space => g (t, y) :=
    fun hg => hg.comp (continuous_const.prodMk continuous_id)
  have hfs : Differentiable ℝ (fun y : UnforcedLeray.Space => f (t, y)) :=
    hfd.comp ((differentiable_const t).prodMk differentiable_id)
  have hφs : Differentiable ℝ (fun y : UnforcedLeray.Space => φ (t, y)) :=
    hφd.comp ((differentiable_const t).prodMk differentiable_id)
  have e1 : ∀ y, fderiv ℝ (fun y' => f (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j f (t, y) := fun y => slice_fderiv hfd t y _
  have e2 : ∀ y, fderiv ℝ (fun y' => φ (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j φ (t, y) := fun y => slice_fderiv hφd t y _
  have I1 := integrable_mul_of_vanish (hc hdf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have I2 := integrable_mul_of_vanish (hc hf.continuous) (hc hdφ.continuous) R'
    (fun y hy => hR' t y hy)
  have I3 := integrable_mul_of_vanish (hc hf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y : UnforcedLeray.Space => f (t, y))
    (g := fun y : UnforcedLeray.Space => φ (t, y))
    (v := UnforcedLeray.coordinateVector j)
    (by simpa only [e1] using I1.1) (by simpa only [e2] using I2.1) I3.1
    (fun x _ => hfs x) (fun x _ => hφs x)
  simp only [e1, e2] at key
  have a1 : (fun y => dy j φ (t, y) * f (t, y)) = fun y => f (t, y) * dy j φ (t, y) := by
    funext y; ring
  have a2 : (fun y => φ (t, y) * dy j f (t, y)) = fun y => dy j f (t, y) * φ (t, y) := by
    funext y; ring
  rw [a1, a2]
  exact key

/-- **Integration by parts in `y_j` for `pairF` against any smooth field `G`** (source 2385-2387,
2542-2551): for any phase test `Φ` and smooth vector field `G`,
`pairF P (dy j Φ) G = pairF P Φ (-(dy j G))`. -/
theorem pairF_dy_of_smooth (P : ℝ) (j : Fin 3)
    {Φ G : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ) (hG : ContDiff ℝ ∞ G) :
    pairF P (dy j Φ) G = pairF P Φ (-(dy j G)) := by
  unfold pairF phaseInt
  congr 1
  congr 1
  funext t
  have hφk : ∀ k : Fin 3, IsPhaseTest P (fun x => Φ x k) :=
    fun k => isPhaseTest_comp_coord hΦ k
  have hGk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => G x k) :=
    fun k => (contDiff_piLp_apply (p := 2) (i := k)).comp hG
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨R', hR'⟩ := (hΦ.dy j).bounded_support
  have hintL : ∀ k : Fin 3, Integrable (fun y : UnforcedLeray.Space =>
      dy j Φ (t, y) k * G (t, y) k) volume := by
    intro k
    have hcG : Continuous (fun y : UnforcedLeray.Space => G (t, y) k) :=
      (hGk k).continuous.comp (continuous_const.prodMk continuous_id)
    have hcΦ : Continuous (fun y : UnforcedLeray.Space => dy j Φ (t, y) k) :=
      ((contDiff_piLp_apply (p := 2) (i := k)).comp (hΦ.dy j).smooth).continuous.comp
        (continuous_const.prodMk continuous_id)
    exact (integrable_mul_of_vanish hcG hcΦ R' (fun y hy => by
      rw [hR' t y hy]; simp)).2
  have hintR : ∀ k : Fin 3, Integrable (fun y : UnforcedLeray.Space =>
      Φ (t, y) k * (-dy j G (t, y) k)) volume := by
    intro k
    have hcG : Continuous (fun y : UnforcedLeray.Space => -dy j G (t, y) k) :=
      (((contDiff_piLp_apply (p := 2) (i := k)).comp (contDiff_dy' hG j)).continuous.comp
        (continuous_const.prodMk continuous_id)).neg
    have hcΦ : Continuous (fun y : UnforcedLeray.Space => Φ (t, y) k) :=
      (hφk k).smooth.continuous.comp (continuous_const.prodMk continuous_id)
    exact (integrable_mul_of_vanish hcG hcΦ R (fun y hy => by
      rw [hR t y hy]; simp)).2
  simp only [dotL_apply, Pi.neg_apply, PiLp.neg_apply]
  rw [integral_finset_sum _ (fun k _ => hintL k),
    integral_finset_sum _ (fun k _ => hintR k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := slice_ibp_dy_smooth j (hφk k) (hGk k) t
  have eΦ : ∀ y, dy j (fun x => Φ x k) (t, y) = dy j Φ (t, y) k :=
    fun y => dy_comp_coord hΦ.smooth j k (t, y)
  have eG : ∀ y, dy j (fun x => G x k) (t, y) = dy j G (t, y) k :=
    fun y => dy_comp_coord hG j k (t, y)
  simp only [eΦ, eG] at h1
  have hneg : (fun y : UnforcedLeray.Space => Φ (t, y) k * (-dy j G (t, y) k)) =
      fun y => -(Φ (t, y) k * dy j G (t, y) k) := by
    funext y; ring
  rw [hneg, integral_neg, h1]

/-- `InletYIBP` from `RawJointSmooth` via `pairF_dy_of_smooth`. -/
theorem inletYIBP_of_raw (hraw : RawJointSmooth) : InletYIBP := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H⟩ := hraw dm dp hdm
  refine ⟨min ν1 1, lt_min hν1 one_pos, fun p d hreg hν hm z g hg i j Φ hΦ => ?_⟩
  have hR := H p d hreg (hν.trans (min_le_left _ _))
  have hI := inlet_contDiff_joint lam q hq hreg (hν.trans (min_le_right _ _)) hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  exact pairF_dy_of_smooth p.period j hΦ (inletSrc_contDiff hE hR)

/-- Smoothness of `inletFn2 p i j l` when `E_i` and `raw` are jointly smooth. -/
theorem inletFn2_contDiff {p : Params} {i : Fin 2} (j l : Fin 3)
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)) :
    ContDiff ℝ ∞ (inletFn2 p i j l) := by
  unfold inletFn2 inletFn
  exact (UnforcedLeray.PhaseSpace.contDiff_dy
    (UnforcedLeray.PhaseSpace.contDiff_dy (inletSrc_contDiff hE hR) l).neg j).neg

/-- **Order-2 measurability** (`InletFn2Meas`, order-2 analogue of `InletFnMeas`,
`PartIII-b_C_ward_12_3_1_2_5_1_1.lean:40`): `inletFn2 p i j l` is a.e. strongly measurable on the
phase cell. -/
def InletFn2Meas : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3),
    AEStronglyMeasurable (inletFn2 p i j l)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)

/-- `InletFn2Meas` from `RawJointSmooth` (order-2 analogue of `inletFnMeas_of`). -/
theorem inletFn2Meas_of (hraw : RawJointSmooth) : InletFn2Meas := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H⟩ := hraw dm dp hdm
  refine ⟨min ν1 1, lt_min hν1 one_pos, fun p d hreg hν hm z g hg i j l => ?_⟩
  have hR := H p d hreg (hν.trans (min_le_left _ _))
  have hI := inlet_contDiff_joint lam q hq hreg (hν.trans (min_le_right _ _)) hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  exact (inletFn2_contDiff j l hE hR).continuous.aestronglyMeasurable

/-- **Order-2 far-field decay** (source 2542-2548 at `k = 2`, order-2 analogue of
`InletFnFarDecay`, `PartIII-b_C_ward_12_3_1_2_5_1_1_3.lean:26`). -/
def InletFn2FarDecay : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
      ‖inletFn2 p i j l (τ, y)‖ ≤ C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ))

/-- **Order-2 near-axis bound** (source 2545-2551 at `k = 2`, order-2 analogue of
`InletFnNearBound`, `PartIII-b_C_ward_12_3_1_2_5_1_1_3.lean:36`). -/
def InletFn2NearBound : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      ‖inletFn2 p i j l (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)

/-- **Order-2 pointwise cylindrical envelope** (source 2542-2551, 2563-2569, 1206-1222; order-2
analogue of `InletFnEnvelope`, `PartIII-b_C_ward_12_3_1_2_5_1_1.lean:50`). -/
def InletFn2Envelope : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      ‖inletFn2 p i j l (τ, y)‖ ≤ C * cylProfile R0 y

/-- `InletFn2Envelope` from `InletFn2FarDecay` and `InletFn2NearBound` (order-2 analogue of
`inletFnEnvelope_of`). -/
theorem inletFn2Envelope_of (h1 : InletFn2FarDecay) (h2 : InletFn2NearBound) :
    InletFn2Envelope := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hm z g hg i j l => ?_⟩
  obtain ⟨Cf, R0, hR0, hf⟩ := H1 p d hreg (hν.trans (min_le_left _ _)) hm z g hg i j l
  obtain ⟨Cn, hn⟩ := H2 p d hreg (hν.trans (min_le_right _ _)) hm z g hg i j l R0 hR0
  refine ⟨max Cf Cn, R0, hR0, fun τ hτ y => ?_⟩
  unfold cylProfile
  by_cases hy : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0
  · rw [if_pos hy]
    have hpos : 0 < (1 + |y 2|) ^ (-2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    exact (hn τ hτ y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)
  · rw [if_neg hy]
    have hy' : R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := not_le.mp hy
    have hρ : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hR0.trans hy'
    have hpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos (by positivity) _)
    exact (hf τ hτ y hy').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)

/-- **Order-2 `L^{q0E}` integrability of the inlet source** (source 2542-2551, 2563-2569,
1206-1222; order-2 analogue of `InletFnMemLp`, `PartIII-b_C_ward_12_3_1_2_5_1.lean:42`). -/
def InletFn2MemLp : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3), MemLp (inletFn2 p i j l) UnforcedLeray.B0412.q0E
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)

/-- `InletFn2MemLp` from `CylProfileMemLp`, `InletFn2Meas`, and `InletFn2Envelope` (order-2
analogue of `inletFnMemLp_of`). -/
theorem inletFn2MemLp_of (h1 : CylProfileMemLp) (h2 : InletFn2Meas) (h3 : InletFn2Envelope) :
    InletFn2MemLp := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨ν₃, hν₃, H3⟩ := h3 lam q hq dm dp hdm
  refine ⟨min ν₂ ν₃, lt_min hν₂ hν₃, fun p d hreg hν hm z g hg i j l => ?_⟩
  have hm2 := H2 p d hreg (hν.trans (min_le_left _ _)) hm z g hg i j l
  obtain ⟨C, R0, hR0, hb⟩ := H3 p d hreg (hν.trans (min_le_right _ _)) hm z g hg i j l
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) := ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × UnforcedLeray.Space => C * cylProfile R0 x.2)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((h1 R0 hR0).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  refine hg1.mono' hm2 ?_
  have hae : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume : Measure UnforcedLeray.Space)), x.1 ∈ Ioc (0 : ℝ) p.period :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with x hx
  exact hb x.1 hx x.2

/-- `InletFn2MemLp` from `RawJointSmooth` and `InletFn2Envelope` (discharging `CylProfileMemLp` by
`cylProfile_memLp` and `InletFn2Meas` by `inletFn2Meas_of`). -/
theorem inletFn2MemLp_of_raw_env (hraw : RawJointSmooth) (henv : InletFn2Envelope) :
    InletFn2MemLp :=
  inletFn2MemLp_of cylProfile_memLp (inletFn2Meas_of hraw) henv

/-- **Second-step `y_j`-integration by parts for `inletFn`** (source 2385-2387, 2542-2551):
`⟪∂_jΦ, inletFn p i l⟫ = ⟪Φ, inletFn2 p i j l⟫` for every phase test `Φ`. -/
def InletFn2YIBP : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3) (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest p.period Φ →
    pairF p.period (dy j Φ) (inletFn p i l) = pairF p.period Φ (inletFn2 p i j l)

/-- `InletFn2YIBP` from `RawJointSmooth` via `pairF_dy_of_smooth`. -/
theorem inletFn2YIBP_of (hraw : RawJointSmooth) : InletFn2YIBP := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H⟩ := hraw dm dp hdm
  refine ⟨min ν1 1, lt_min hν1 one_pos, fun p d hreg hν hm z g hg i j l Φ hΦ => ?_⟩
  have hR := H p d hreg (hν.trans (min_le_left _ _))
  have hI := inlet_contDiff_joint lam q hq hreg (hν.trans (min_le_right _ _)) hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  have hF : ContDiff ℝ ∞ (inletFn p i l) :=
    (UnforcedLeray.PhaseSpace.contDiff_dy (inletSrc_contDiff hE hR) l).neg
  exact pairF_dy_of_smooth p.period j hΦ hF

/-- `GEInletIBP2` from `InletFn2MemLp`, `InletFn2YIBP`, `h1 : InletFnMemLp`, and
`h2 : InletIBPIdentity` (source 2542-2551). -/
theorem gEInletIBP2_of_memLp_yibp (hM : InletFn2MemLp) (hY : InletFn2YIBP)
    (h1 : InletFnMemLp) (h2 : InletIBPIdentity) : GEInletIBP2 := by
  intro lam q hq dm dp hdm
  obtain ⟨νM, hνM, HM⟩ := hM lam q hq dm dp hdm
  obtain ⟨νY, hνY, HY⟩ := hY lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min (min νM νY) (min ν1 ν2),
    lt_min (lt_min hνM hνY) (lt_min hν1 hν2), fun p d hreg hν hm z g hg i j l => ?_⟩
  have eM : p.ν ≤ νM := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have eY : p.ν ≤ νY := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e1 : p.ν ≤ ν1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e2 : p.ν ≤ ν2 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm1 := H1 p d hreg e1 hm z g hg i l
  have hm2 := HM p d hreg eM hm z g hg i j l
  refine ⟨inletFn2 p i j l, hm2, fun Φ hΦ => ?_⟩
  have hΨ : IsSolTest p.period (dy j Φ) := gEW_isSolTest_dy hΦ j
  rw [H2 p d hreg e2 hm z g hg i l hm1 (dy j Φ) hΨ,
    HY p d hreg eY hm z g hg i j l Φ hΦ.1]

/-- `GEInletIBP2` from `RawJointSmooth`, `InletFn2Envelope`, `h1 : InletFnMemLp`, and
`h2 : InletIBPIdentity`. -/
theorem gEInletIBP2_of_raw_env (hraw : RawJointSmooth) (henv : InletFn2Envelope)
    (h1 : InletFnMemLp) (h2 : InletIBPIdentity) : GEInletIBP2 :=
  gEInletIBP2_of_memLp_yibp (inletFn2MemLp_of_raw_env hraw henv) (inletFn2YIBP_of hraw) h1 h2

/-! ## Decomposition leaves for `InletFn2NearBound` and `InletFn2FarDecay` -/

/-- **(Leaf 1) Order-4 near-axis axial decay of the inlet jets**
(source `the November 2 reference manuscript`
lines 2545-2551, 2385-2387; order-4 analogue of `InletENearJets`,
`PartIII-b_C_ward_12_3_1_2_5_1_1_3_2.lean:24`): on the disc `ϱ ≤ R₀`, spatial derivatives of
order `≤ 4` of `E_i = realC (inlet)` and spatial derivatives of order `≤ 2` of `∂_τ E_i` are
bounded by `C (1 + |y₃|)^{-N}`, uniformly in `τ ∈ (0, P]`. -/
def InletENearJets4 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (N : ℕ) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      (∀ k : ℕ, k ≤ 4 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
      (∀ k : ℕ, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
            UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ)))

/-- **(Leaf 2) Order-2 generic product-rule bound for `inletFn2`**
(source `the November 2 reference manuscript`
lines 2545-2551, 2563-2569; order-2 analogue of `InletSrcDerivBound`,
`PartIII-b_C_ward_12_3_1_2_5_1_1_3_2_2.lean:32`): there is a universal constant `K ≥ 0` such that
for `ν ≤ 1` and jointly smooth `E_i`, `raw`, at every `(τ, y)`,
`‖inletFn2 p i j l (τ, y)‖ ≤ K (1 + ‖y‖) (1 + B) A`, where `A` is the sum of the slice jets of
`E_i` of order `≤ 4` and of `∂_τ E_i` of order `≤ 2` at `y`, and `B` is the sum of the slice jets
of `raw τ` of order `≤ 3` at `y`. -/
def InletSrcDeriv2Bound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : Params) (i : Fin 2) (j l : Fin 3), p.ν ≤ 1 →
    ContDiff ℝ ∞ (p.Efun i) → ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) →
    ∀ (τ : ℝ) (y : UnforcedLeray.Space),
      ‖inletFn2 p i j l (τ, y)‖ ≤ K * (1 + ‖y‖) *
        (1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) *
        ((∑ k ∈ Finset.range 5,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖)

/-- `InletFn2NearBound` from `RawJointSmooth`, `RawDerivBdd3`, `InletENearJets4`, and
`InletSrcDeriv2Bound` (order-2 analogue of `inletFnNearOfJets_of`,
`PartIII-b_C_ward_12_3_1_2_5_1_1_3_2_2.lean:44`). -/
theorem inletFn2NearBound_of_jets (hraw : RawJointSmooth) (hbdd : RawDerivBdd3)
    (hE : InletENearJets4) (hK : InletSrcDeriv2Bound) : InletFn2NearBound := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := hE lam q hq dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := hbdd dm dp hdm
  obtain ⟨ν3, hν3, H3⟩ := hraw dm dp hdm
  obtain ⟨K, hK0, HK⟩ := hK
  refine ⟨min (min ν1 ν2) (min ν3 1), lt_min (lt_min hν1 hν2) (lt_min hν3 one_pos),
    fun p d hreg hν hm z g hg i j l R0 hR0 => ?_⟩
  have h1 : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : p.ν ≤ ν3 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR := H3 p d hreg h3
  have hI := inlet_contDiff_joint lam q hq hreg h4 hm i
  have hEs : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  obtain ⟨CE, hCE⟩ := H1 p d hreg h1 hm z g hg i 3 R0 hR0
  obtain ⟨c0, hc0⟩ := H2 p d hreg h2 0
  obtain ⟨c1, hc1⟩ := H2 p d hreg h2 1
  obtain ⟨c2, hc2⟩ := H2 p d hreg h2 2
  obtain ⟨c3, hc3⟩ := H2 p d hreg h2 3
  refine ⟨K * (1 + R0) * (1 + (c0 + c1 + c2 + c3)) * (8 * CE), fun τ hτ y hy => ?_⟩
  obtain ⟨hA, hA'⟩ := hCE τ hτ y hy
  set t : ℝ := (1 + |y 2|) ^ (-((3 : ℕ) : ℝ)) with ht
  have hpos : 0 < 1 + |y 2| := by positivity
  have htpos : 0 < t := Real.rpow_pos_of_pos hpos _
  have hsumE : ∑ k ∈ Finset.range 5,
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤ 5 * (CE * t) := by
    calc _ ≤ ∑ k ∈ Finset.range 5, CE * t := by
          apply Finset.sum_le_sum
          intro k hk
          exact hA k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk)
      _ = 5 * (CE * t) := by simp
  have hsumD : ∑ k ∈ Finset.range 3,
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
        UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤ 3 * (CE * t) := by
    calc _ ≤ ∑ k ∈ Finset.range 3, CE * t := by
          apply Finset.sum_le_sum
          intro k hk
          exact hA' k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk)
      _ = 3 * (CE * t) := by simp
  have hsumB : ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ c0 + c1 + c2 + c3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact add_le_add (add_le_add (add_le_add (hc0 τ y) (hc1 τ y)) (hc2 τ y)) (hc3 τ y)
  have hnorm : ‖y‖ ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    have : Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≤
        Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + Real.sqrt (y 2 ^ 2) := by
      rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))),
        Real.sq_sqrt (sq_nonneg (y 2)), Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2),
        Real.sqrt_nonneg (y 2 ^ 2)]
    simpa [Real.sqrt_sq_eq_abs] using this
  have hy1 : 1 + ‖y‖ ≤ (1 + R0) * (1 + |y 2|) := by
    nlinarith [abs_nonneg (y 2)]
  have hbound := HK p i j l h4 hEs hR τ y
  have hB0 : 0 ≤ 1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ := by positivity
  have hA0 : 0 ≤ (∑ k ∈ Finset.range 5,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ := by positivity
  have hKy : K * (1 + ‖y‖) ≤ K * ((1 + R0) * (1 + |y 2|)) := mul_le_mul_of_nonneg_left hy1 hK0
  have hBle : 1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
      1 + (c0 + c1 + c2 + c3) := by
    linarith
  have hstep : K * (1 + ‖y‖) *
        (1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) *
        ((∑ k ∈ Finset.range 5,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖) ≤
      K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2 + c3)) * (8 * (CE * t)) := by
    have e1 : K * (1 + ‖y‖) * (1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) ≤
        K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2 + c3)) :=
      mul_le_mul hKy hBle hB0 (by positivity)
    have hAle' : (∑ k ∈ Finset.range 5,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤ 8 * (CE * t) := by linarith
    have hb0 : 0 ≤ K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2 + c3)) :=
      mul_nonneg (mul_nonneg hK0 (by positivity)) (hB0.trans hBle)
    exact mul_le_mul e1 hAle' hA0 hb0
  refine hbound.trans (hstep.trans (le_of_eq ?_))
  have hmul : (1 + |y 2|) * t = (1 + |y 2|) ^ (-2 : ℝ) := by
    rw [ht, show (-((3 : ℕ) : ℝ)) = (-2 : ℝ) + (-1 : ℝ) by norm_num,
      Real.rpow_add hpos, Real.rpow_neg_one]
    field_simp
  calc K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2 + c3)) * (8 * (CE * t))
      = K * (1 + R0) * (1 + (c0 + c1 + c2 + c3)) * (8 * CE) * ((1 + |y 2|) * t) := by ring
    _ = _ := by rw [hmul]

/-- **(Leaf 3) Order-4 far-field jets of the inlet, homogeneity `-1`**
(source `the November 2 reference manuscript`
lines 2542-2549, 1206-1222; order-4 analogue of `InletEFarHom`, `FarOrg.lean:138`): spatial
derivatives of order `k ≤ 4` of `E = p.Efun i` are bounded by
`C ϱ^{-1-k}(1+|y₃|/ϱ)^{-N}` for `ϱ > R₀`, for every phase `τ`. -/
def InletEFarHom4 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (N : ℕ), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y → ∀ k : ℕ, k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
        C * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)))

/-- **(Leaf 4) Order-2 far product rule**
(source `the November 2 reference manuscript`
lines 2542-2549, 2563-2569, 1206-1222; order-2 analogue of `InletFnFarOfHom`, `FarOrg.lean:203`):
on `ϱ > R₀`, `inletFn2 p i j l = ∂_j∂_l(L₀E_i + (raw·∇)E_i + (E_i·∇)raw)` with
`∂_j∂_l L₀E_i = -ν∂_j∂_lΔE_i` (`InletDriftFar`, the drift vanishes on an open far set), and every
term is `O(ϱ^{-5}(1+|y₃|/ϱ)^{M-N}) ≤ O(ϱ^{-3}(1+|y₃|/ϱ)^{-2})` (take `N = M + 2`, `R₀ ≥ 1`). -/
def InletFn2FarOfHom : Prop := InletEFarHom4 → InletDriftFar → InletFn2FarDecay

/-- `InletFn2FarDecay` from `InletEFarHom4` and `InletFn2FarOfHom` (discharging `InletDriftFar`
by the proved `inletDriftFar`). -/
theorem inletFn2FarDecay_of_hom (hE : InletEFarHom4) (hF : InletFn2FarOfHom) :
    InletFn2FarDecay :=
  hF hE inletDriftFar

/-- **`GEInletIBP2` from the decomposed leaves** (`RawJointSmooth`, `RawDerivBdd3`,
`InletENearJets4`, `InletSrcDeriv2Bound`, `InletEFarHom4`, `InletFn2FarOfHom`, and the
target hypotheses `h1 : InletFnMemLp`, `h2 : InletIBPIdentity`). -/
theorem gEInletIBP2_of_sub (hraw : RawJointSmooth) (hbdd : RawDerivBdd3)
    (hENear : InletENearJets4) (hK : InletSrcDeriv2Bound)
    (hEFar : InletEFarHom4) (hFar : InletFn2FarOfHom)
    (h1 : InletFnMemLp) (h2 : InletIBPIdentity) : GEInletIBP2 :=
  gEInletIBP2_of_raw_env hraw
    (inletFn2Envelope_of (inletFn2FarDecay_of_hom hEFar hFar)
      (inletFn2NearBound_of_jets hraw hbdd hENear hK)) h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.pairF_dy_of_smooth
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.inletYIBP_of_raw
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.inletFn2MemLp_of_raw_env
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.inletFn2YIBP_of
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.inletFn2NearBound_of_jets
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.inletFn2FarDecay_of_hom
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.gEInletIBP2_of_sub
