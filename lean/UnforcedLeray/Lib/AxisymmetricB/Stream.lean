import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.PhaseSpace.PointSingularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# AX06: Stokes stream functions, the ring stream lift and stream cutoffs


§5 Layer 3, target AX06 (`Axi/Stream.lean`); Wave 2 block 2J AXI1 of `scoping/README.md`.
Blueprint units served: B0185 (`eq:st18-t00188/189`, tex 2851–2865: `𝒫 = rψ`,
`u_r = −r⁻¹𝒫_z`, `u_z = r⁻¹𝒫_r`, exactly solenoidal), B0298 (`background:eq:2.27`,
tex 5282–5303: the exact physical stream lift and its normalized components), B0303
(tex 5143–5159: axial completion `ε[(χ − 2sχ')Ψ − χηΨ_η]`), B0555 (tex 8893–8948),
B0780 (tex 11201–11213) and B0961 (`eq:st18-t00618`, tex 10589–10604:
`C_χ W − χ W = (Ψ_W/ρ) ∂_ρ χ e_z`).

* `streamProfile Ψ = (−ρ⁻¹ ∂_z Ψ, ρ⁻¹ ∂_ρ Ψ)` and `streamLift Ψ = liftMer (streamProfile Ψ)`:
  the field `curl(Ψ e_φ/ρ)` of a Stokes stream function `Ψ(ρ, z)`.
* `div_streamLift_eq_zero`: off the axis the stream lift of a `C²` stream is divergence free
  (symmetry of second derivatives).
* `isSolenoidal_streamLift`: a `C²` stream with compact support in `{ρ > 0}` (the annular core
  of bypass BP5) lifts to a field that is distributionally solenoidal on all of `ℝ³`
  (`Statement.IsSolenoidal`), through `PhaseSpace.isSolenoidal_of_punctured`.
* `streamLift_mul`, `streamCutoff_eq`: the stream cutoff `C_χ W := streamLift (χΨ_W)` of
  `W = streamLift Ψ_W` differs from `χ W` by `(Ψ_W/ρ)(−∂_zχ e_r + ∂_ρχ e_z)`; for a radial
  cutoff this is `(Ψ_W/ρ) ∂_ρχ e_z` (B0961, B0780).
* `ringStreamLift_components`: the physical stream `ρ φ(s, ξ, η)` at the chart point lifts to
  `N_v e`, `e = (−φ_η, φ_ξ + ε(φ − 2sφ_s − ηφ_η))`, `ε = R⁻¹`; with `φ = χ(s) ψ(ξ, η)` this is
  B0298's `e_ε = (−χψ_η, χψ_q + ε[(χ − 2sχ')ψ − χηψ_η])` (`ringStreamProfile_cutoff`), and at
  `τ = 0` with `φ = ψ(ξ, η)` it is the datum `background:eq:2.27` (`streamLift_datum`).

Junk values. `ρ⁻¹` is Lean's `0⁻¹ = 0` at `ρ = 0`; all differential identities are stated off
the axis, or for profiles differentiable at the point used. The stream `Ψ` is a function on all of
`ℝ × ℝ`; only its germ at points with `ρ > 0` enters.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Axi

/-! ### The meridional basis -/

/-- The meridional basis vector `e_r` of `Merid`. -/
def m0 : Merid := EuclideanSpace.single 0 1
/-- The meridional basis vector `e_z` of `Merid`. -/
def m1 : Merid := EuclideanSpace.single 1 1

@[simp] theorem m0_zero : m0 0 = 1 := by simp [m0]
@[simp] theorem m0_one : m0 1 = 0 := by simp [m0]
@[simp] theorem m1_zero : m1 0 = 0 := by simp [m1]
@[simp] theorem m1_one : m1 1 = 1 := by simp [m1]

theorem frameL_m0 (y : Space) : frameL y m0 = eR y := by simp [frameL_apply]
theorem frameL_m1 (y : Space) : frameL y m1 = e3 := by simp [frameL_apply]

/-! ### Partial derivatives on `ℝ × ℝ` -/

section Partials

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_line_fst {f : ℝ × ℝ → F} {p : ℝ × ℝ} (h : DifferentiableAt ℝ f p) :
    HasDerivAt (fun r => f (r, p.2)) (dρ f p) p.1 := by
  have hc : HasDerivAt (fun r : ℝ => (r, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 : HasFDerivAt f (fderiv ℝ f p) (p.1, p.2) := h.hasFDerivAt
  exact h2.comp_hasDerivAt p.1 hc

theorem hasDerivAt_line_snd {f : ℝ × ℝ → F} {p : ℝ × ℝ} (h : DifferentiableAt ℝ f p) :
    HasDerivAt (fun z => f (p.1, z)) (dz f p) p.2 := by
  have hc : HasDerivAt (fun z : ℝ => (p.1, z)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasFDerivAt f (fderiv ℝ f p) (p.1, p.2) := h.hasFDerivAt
  exact h2.comp_hasDerivAt p.2 hc

theorem fderiv_apply_fderiv {Ψ : ℝ × ℝ → F} {p : ℝ × ℝ}
    (hd : DifferentiableAt ℝ (fderiv ℝ Ψ) p) (v w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ Ψ q v) p w = fderiv ℝ (fderiv ℝ Ψ) p w v := by
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).fderiv]
  simp

end Partials

/-- Mixed partials commute for a `C²` function: `∂_z ∂_ρ Ψ = ∂_ρ ∂_z Ψ`. -/
theorem dz_dρ_eq_dρ_dz {Ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hΨ : ContDiffAt ℝ 2 Ψ p) :
    dz (dρ Ψ) p = dρ (dz Ψ) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) p :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsym := hΨ.isSymmSndFDerivAt (by simp)
  have e1 : dz (dρ Ψ) p = fderiv ℝ (fun q => fderiv ℝ Ψ q (1, 0)) p (0, 1) := rfl
  have e2 : dρ (dz Ψ) p = fderiv ℝ (fun q => fderiv ℝ Ψ q (0, 1)) p (1, 0) := rfl
  rw [e1, e2, fderiv_apply_fderiv hd, fderiv_apply_fderiv hd]
  exact hsym _ _

/-- The derivative of a meridional vector field `f e_r + g e_z`. -/
theorem fderiv_pair_apply {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : ℝ × ℝ) :
    fderiv ℝ (fun q => f q • m0 + g q • m1) p v = fderiv ℝ f p v • m0 + fderiv ℝ g p v • m1 := by
  rw [((hf.hasFDerivAt.smul_const m0).fun_add (hg.hasFDerivAt.smul_const m1)).fderiv]
  simp

theorem hasFDerivAt_inv_fst {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1)⁻¹) ((-(p.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  (hasDerivAt_inv hp).comp_hasFDerivAt p hasFDerivAt_fst

/-! ### The stream lift -/

/-- The meridional field `(−ρ⁻¹ ∂_z Ψ, ρ⁻¹ ∂_ρ Ψ)` of a Stokes stream function (tex 2855:
`u_r = −r⁻¹𝒫_z`, `u_z = r⁻¹𝒫_r`). -/
def streamProfile (Ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Merid :=
  (-(p.1)⁻¹ * dz Ψ p) • m0 + ((p.1)⁻¹ * dρ Ψ p) • m1

/-- **AX06 `streamLift`.** The axisymmetric field `curl(Ψ e_φ/ρ) = −ρ⁻¹Ψ_z e_r + ρ⁻¹Ψ_ρ e_z`
of a Stokes stream `Ψ(ρ, z)`. -/
def streamLift (Ψ : ℝ × ℝ → ℝ) : Space → Space := liftMer (streamProfile Ψ)

theorem streamLift_apply (Ψ : ℝ × ℝ → ℝ) (y : Space) :
    streamLift Ψ y = (-(ϱ y)⁻¹ * dz Ψ (mer y)) • eR y + ((ϱ y)⁻¹ * dρ Ψ (mer y)) • e3 := by
  rw [streamLift, liftMer_eq_frameL, streamProfile, map_add, map_smul, map_smul, frameL_m0,
    frameL_m1]
  rfl

theorem isAxisymmetricNoSwirl_streamLift (Ψ : ℝ × ℝ → ℝ) :
    IsAxisymmetricNoSwirl (streamLift Ψ) :=
  isAxisymmetricNoSwirl_liftMer _

theorem contDiffOn_streamProfile {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiffOn ℝ 2 Ψ (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ 1 (streamProfile Ψ) (Ioi 0 ×ˢ univ) := by
  have hinv : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.1)⁻¹) (Ioi 0 ×ˢ univ) :=
    contDiffOn_fst.inv fun p hp => (ne_of_gt hp.1)
  have h0 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -(p.1)⁻¹ * dz Ψ p) (Ioi 0 ×ˢ univ) :=
    hinv.neg.mul (contDiffOn_dz hΨ)
  have h1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.1)⁻¹ * dρ Ψ p) (Ioi 0 ×ˢ univ) :=
    hinv.mul (contDiffOn_dρ hΨ)
  exact (h0.smul contDiffOn_const).add (h1.smul contDiffOn_const)

/-- **AX06 `div_streamLift_eq_zero`** (B0185, tex 2855–2858: "hence exactly solenoidal").
Off the axis, the stream lift of a stream of class `C²` on `{ρ > 0}` is divergence free. -/
theorem div_streamLift_eq_zero {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiffOn ℝ 2 Ψ (Ioi 0 ×ˢ univ))
    {y : Space} (hy : y ∉ axis) : divergence (streamLift Ψ) y = 0 := by
  set p := mer y with hp_def
  have hpm : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := mapsTo_mer hy
  have hp0 : p.1 ≠ 0 := ne_of_gt hpm.1
  have hnhds : Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 p := isOpen_halfPlane.mem_nhds hpm
  have hΨp : ContDiffAt ℝ 2 Ψ p := hΨ.contDiffAt hnhds
  have hdz : DifferentiableAt ℝ (dz Ψ) p :=
    ((contDiffOn_dz hΨ).contDiffAt hnhds).differentiableAt one_ne_zero
  have hdρ : DifferentiableAt ℝ (dρ Ψ) p :=
    ((contDiffOn_dρ hΨ).contDiffAt hnhds).differentiableAt one_ne_zero
  have hf : HasFDerivAt (fun q : ℝ × ℝ => -(q.1)⁻¹ * dz Ψ q) _ p :=
    ((hasFDerivAt_inv_fst hp0).fun_neg).fun_mul hdz.hasFDerivAt
  have hg : HasFDerivAt (fun q : ℝ × ℝ => (q.1)⁻¹ * dρ Ψ q) _ p :=
    (hasFDerivAt_inv_fst hp0).fun_mul hdρ.hasFDerivAt
  have hsp : streamProfile Ψ = fun q => (-(q.1)⁻¹ * dz Ψ q) • m0 + ((q.1)⁻¹ * dρ Ψ q) • m1 := rfl
  have hb : DifferentiableAt ℝ (streamProfile Ψ) p := by
    rw [hsp]
    exact (hf.differentiableAt.smul_const m0).add (hg.differentiableAt.smul_const m1)
  rw [streamLift, divergence_liftMer hy hb]
  have e1 : dρ (streamProfile Ψ) p 0 = -(p.1)⁻¹ * dρ (dz Ψ) p + dz Ψ p * (p.1 ^ 2)⁻¹ := by
    have h := fderiv_pair_apply hf.differentiableAt hg.differentiableAt (1, 0)
    rw [← hsp] at h
    rw [dρ, h, hf.fderiv]
    simp [dρ]
  have e2 : dz (streamProfile Ψ) p 1 = (p.1)⁻¹ * dz (dρ Ψ) p := by
    have h := fderiv_pair_apply hf.differentiableAt hg.differentiableAt (0, 1)
    rw [← hsp] at h
    rw [dz, h, hg.fderiv]
    simp [dz]
  have e3' : streamProfile Ψ p 0 = -(p.1)⁻¹ * dz Ψ p := by simp [streamProfile]
  rw [← hp_def, e1, e2, e3', dz_dρ_eq_dρ_dz hΨp]
  have hρ : ϱ y = p.1 := rfl
  rw [hρ]
  field_simp
  ring

/-- Away from the support of `Ψ`, the stream profile vanishes. -/
theorem streamProfile_of_notMem_tsupport {Ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∉ tsupport Ψ) :
    streamProfile Ψ p = 0 := by
  have h := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
  simp [streamProfile, dz, dρ, h]

/-- **AX06 `isSolenoidal_streamLift`** (B0185 on the annular core of bypass BP5; B0494's
"lifts to a globally solenoidal Cartesian field"). A stream of class `C²` on `{ρ > 0}` with
compact support inside `{ρ > 0}` lifts to a field that is distributionally divergence free on
all of `ℝ³` (`Statement.IsSolenoidal`). -/
theorem isSolenoidal_streamLift {Ψ : ℝ × ℝ → ℝ} (hΨ : ContDiffOn ℝ 2 Ψ (Ioi 0 ×ˢ univ))
    (hc : HasCompactSupport Ψ) (hsub : tsupport Ψ ⊆ Ioi 0 ×ˢ univ) :
    IsSolenoidal (streamLift Ψ) := by
  -- a positive lower bound of `ρ` on the support
  obtain ⟨ρ0, hρ0, hmin⟩ : ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ p ∈ tsupport Ψ, ρ0 ≤ p.1 := by
    by_cases hne : (tsupport Ψ).Nonempty
    · obtain ⟨p0, hp0, hm⟩ := hc.isCompact.exists_isMinOn hne continuous_fst.continuousOn
      exact ⟨p0.1, (hsub hp0).1, fun p hp => hm hp⟩
    · exact ⟨1, one_pos, fun p hp => (hne ⟨p, hp⟩).elim⟩
  set f := streamLift Ψ with hf_def
  have hzero : ∀ y : Space, mer y ∉ tsupport Ψ → f y = 0 := by
    intro y hy
    rw [hf_def, streamLift, liftMer_eq_frameL, streamProfile_of_notMem_tsupport hy, map_zero]
  have hnear : ∀ y : Space, ϱ y < ρ0 → f =ᶠ[𝓝 y] fun _ => 0 := by
    intro y hy
    have hopen : IsOpen {x : Space | ϱ x < ρ0} := isOpen_lt continuous_ϱ continuous_const
    filter_upwards [hopen.mem_nhds hy] with x hx
    exact hzero x fun hm => absurd (hmin _ hm) (not_le.2 hx)
  have hcd : ContDiff ℝ 1 f := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ axis
    · have hy0 : ϱ y < ρ0 := by rw [(mem_axis_iff y).1 hy]; exact hρ0
      exact contDiffAt_const.congr_of_eventuallyEq (hnear y hy0)
    · exact (contDiffOn_liftMer (contDiffOn_streamProfile hΨ)).contDiffAt
        (isOpen_compl_axis.mem_nhds hy)
  have hdiv : ∀ x : Space, PhaseSpace.pointDivergence f x = 0 := by
    intro x
    by_cases hx : x ∈ axis
    · have hx0 : ϱ x < ρ0 := by rw [(mem_axis_iff x).1 hx]; exact hρ0
      have hfd : fderiv ℝ f x = 0 := by
        rw [(hnear x hx0).fderiv_eq]
        exact fderiv_const_apply _
      simp [PhaseSpace.pointDivergence, hfd]
    · exact div_streamLift_eq_zero hΨ hx
  -- compact support of the field
  have hmer : Continuous mer :=
    continuous_ϱ.prodMk (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous
  have hKc : IsCompact (mer ⁻¹' tsupport Ψ) := by
    obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
    refine Metric.isCompact_of_isClosed_isBounded
      ((isClosed_tsupport Ψ).preimage hmer) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := 2 * |r|)).subset fun y hy => ?_
    have hy' := hr hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy' ⊢
    have h1 : ϱ y ≤ |r| := by
      have h := (norm_fst_le (mer y)).trans hy'
      have e : ‖(mer y).1‖ = ϱ y := Real.norm_of_nonneg (ϱ_nonneg y)
      rw [e] at h
      exact h.trans (le_abs_self r)
    have h2 : |y 2| ≤ |r| := by
      have h := (norm_snd_le (mer y)).trans hy'
      have e : ‖(mer y).2‖ = |y 2| := Real.norm_eq_abs _
      rw [e] at h
      exact h.trans (le_abs_self r)
    have h3 : ‖y‖ ^ 2 ≤ (2 * |r|) ^ 2 := by
      rw [norm_sq_eq_ϱ_sq_add]
      nlinarith [ϱ_nonneg y, abs_nonneg (y 2), sq_abs (y 2), abs_nonneg r]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro hKc fun y hy => hzero y hy
  obtain ⟨M, hM⟩ := hcd.continuous.bounded_above_of_compact_support hfc
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Space)
  have hbd : ∀ x ≠ (0 : Space), ‖f x‖ ≤ (max M 0 * max r 0) * ‖x‖⁻¹ := by
    intro x hx
    by_cases hfx : f x = 0
    · rw [hfx, norm_zero]; positivity
    have hxs : x ∈ tsupport f := subset_tsupport _ (Function.mem_support.2 hfx)
    have hxr : ‖x‖ ≤ max r 0 := by
      have := hr hxs
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    calc ‖f x‖ ≤ max M 0 := (hM x).trans (le_max_left _ _)
      _ = max M 0 * ‖x‖ * ‖x‖⁻¹ := by field_simp
      _ ≤ max M 0 * max r 0 * ‖x‖⁻¹ := by gcongr
  exact PhaseSpace.isSolenoidal_of_punctured (hcd.contDiffOn) (fun x _ => hdiv x) hbd

/-! ### Stream cutoffs -/

theorem dρ_mul {χ Ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hχ : DifferentiableAt ℝ χ p)
    (hΨ : DifferentiableAt ℝ Ψ p) :
    dρ (fun q => χ q * Ψ q) p = χ p * dρ Ψ p + Ψ p * dρ χ p := by
  simp only [dρ]
  rw [(hχ.hasFDerivAt.fun_mul hΨ.hasFDerivAt).fderiv]
  simp

theorem dz_mul {χ Ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hχ : DifferentiableAt ℝ χ p)
    (hΨ : DifferentiableAt ℝ Ψ p) :
    dz (fun q => χ q * Ψ q) p = χ p * dz Ψ p + Ψ p * dz χ p := by
  simp only [dz]
  rw [(hχ.hasFDerivAt.fun_mul hΨ.hasFDerivAt).fderiv]
  simp

/-- **AX06 `streamLift_mul`** (B0555, tex 8893–8948; B0780, tex 11201–11213). The stream lift of
`χΨ` is `χ` times the stream lift of `Ψ`, plus `(Ψ/ρ)(−∂_zχ e_r + ∂_ρχ e_z)`. -/
theorem streamLift_mul {χ Ψ : ℝ × ℝ → ℝ} {y : Space} (hχ : DifferentiableAt ℝ χ (mer y))
    (hΨ : DifferentiableAt ℝ Ψ (mer y)) :
    streamLift (fun p => χ p * Ψ p) y = χ (mer y) • streamLift Ψ y +
      (Ψ (mer y) / ϱ y) • (-(dz χ (mer y)) • eR y + dρ χ (mer y) • e3) := by
  rw [streamLift_apply, streamLift_apply, dz_mul hχ hΨ, dρ_mul hχ hΨ]
  simp only [smul_add, smul_smul, neg_smul]
  have hρ : (mer y).1 = ϱ y := rfl
  module

/-- **AX06 `streamCutoff_eq`** (B0961, `eq:st18-t00618`, tex 10589–10604; B0780,
`eq:st18-t00646`). For a radial cutoff (`∂_zχ = 0` at the point), the stream cutoff
`C_χ W := streamLift (χΨ_W)` of `W = streamLift Ψ_W` satisfies
`C_χ W − χ W = (Ψ_W/ρ) ∂_ρχ e_z`. -/
theorem streamCutoff_eq {χ Ψ : ℝ × ℝ → ℝ} {y : Space} (hχ : DifferentiableAt ℝ χ (mer y))
    (hΨ : DifferentiableAt ℝ Ψ (mer y)) (hrad : dz χ (mer y) = 0) :
    streamLift (fun p => χ p * Ψ p) y - χ (mer y) • streamLift Ψ y =
      (Ψ (mer y) / ϱ y * dρ χ (mer y)) • e3 := by
  rw [streamLift_mul hχ hΨ, hrad, add_sub_cancel_left, neg_zero, zero_smul, zero_add, smul_smul]

/-! ### The ring stream lift -/

/-- The meridional form of the similarity chart:
`(ρ, z) ↦ (R²/ρ², Rτ/2 − (R/2) log(R²/ρ²), Rz/ρ)`, so that `chart R τ y = merChart R τ (ϱ, y₃)`. -/
def merChart (R τ : ℝ) (p : ℝ × ℝ) : ℝ × (ℝ × ℝ) :=
  (R ^ 2 / p.1 ^ 2, (R * τ / 2 - (R / 2) * Real.log (R ^ 2 / p.1 ^ 2), R * p.2 / p.1))

theorem chart_eq_merChart (R τ : ℝ) (y : Space) : chart R τ y = merChart R τ (mer y) := rfl

theorem hasDerivAt_merChart_fst {R : ℝ} (hR : R ≠ 0) (τ z : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun ρ => merChart R τ (ρ, z))
      (-(2 * R ^ 2 / r ^ 3), (R / r, -(R * z / r ^ 2))) r := by
  have hs := hasDerivAt_sq_div R hr
  have hne : R ^ 2 / r ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 hr)
  have hξ : HasDerivAt (fun ρ : ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / ρ ^ 2)) (R / r) r := by
    have h := (hasDerivAt_const r (R * τ / 2)).sub ((hs.log hne).const_mul (R / 2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hη : HasDerivAt (fun ρ : ℝ => R * z / ρ) (-(R * z / r ^ 2)) r := by
    have h := (hasDerivAt_const r (R * z)).div (hasDerivAt_id r) hr
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  exact hs.prodMk (hξ.prodMk hη)

theorem hasDerivAt_merChart_snd (R τ : ℝ) {r : ℝ} (z : ℝ) :
    HasDerivAt (fun ζ => merChart R τ (r, ζ)) ((0 : ℝ), ((0 : ℝ), R / r)) z := by
  have hη : HasDerivAt (fun ζ : ℝ => R * ζ / r) (R / r) z := by
    have h := ((hasDerivAt_id z).const_mul R).div_const r
    simpa using h
  exact (hasDerivAt_const z (R ^ 2 / r ^ 2)).prodMk
    ((hasDerivAt_const z (R * τ / 2 - (R / 2) * Real.log (R ^ 2 / r ^ 2))).prodMk hη)

theorem differentiableAt_merChart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    DifferentiableAt ℝ (merChart R τ) p := by
  have hsq : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1 ^ 2)⁻¹) p :=
    (differentiableAt_fst.pow 2).fun_inv (pow_ne_zero 2 hp)
  have hs : DifferentiableAt ℝ (fun q : ℝ × ℝ => R ^ 2 / q.1 ^ 2) p := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_const (R ^ 2)).fun_mul hsq
  have hne : R ^ 2 / p.1 ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 hp)
  have hξ : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / q.1 ^ 2)) p :=
    (differentiableAt_const _).fun_sub ((differentiableAt_const _).fun_mul (hs.log hne))
  have hη : DifferentiableAt ℝ (fun q : ℝ × ℝ => R * q.2 / q.1) p := by
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const R).fun_mul differentiableAt_snd).fun_mul
      (differentiableAt_fst.fun_inv hp)
  exact hs.prodMk (hξ.prodMk hη)

/-- The physical Stokes stream `ρ φ(s, ξ, η)` of a ring profile `φ`, at phase time `τ`
(B0185: `𝒫 = rψ`). -/
def ringStream (R τ : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ := p.1 * φ (merChart R τ p)

/-- The normalized components `(−φ_η, φ_ξ + ε(φ − 2sφ_s − ηφ_η))`, `ε = R⁻¹`, of the stream lift
of `ρ φ` (B0298, tex 5288–5295). -/
def ringStreamProfile (R : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ) (m : ℝ × (ℝ × ℝ)) : Merid :=
  (-(dEta φ m)) • m0 + (dQ φ m + R⁻¹ * (φ m - 2 * m.1 * dS φ m - m.2.2 * dEta φ m)) • m1

theorem differentiableAt_ringStream {R τ : ℝ} (hR : R ≠ 0) {φ : ℝ × (ℝ × ℝ) → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ≠ 0) (hφ : DifferentiableAt ℝ φ (merChart R τ p)) :
    DifferentiableAt ℝ (ringStream R τ φ) p :=
  differentiableAt_fst.mul (hφ.comp p (differentiableAt_merChart hR τ hp))

theorem dz_ringStream {R τ : ℝ} (hR : R ≠ 0) {φ : ℝ × (ℝ × ℝ) → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ≠ 0) (hφ : DifferentiableAt ℝ φ (merChart R τ p)) :
    dz (ringStream R τ φ) p = R * dEta φ (merChart R τ p) := by
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (merChart R τ p)) (merChart R τ (p.1, p.2)) :=
    hφ.hasFDerivAt
  have hline : HasDerivAt (fun ζ => ringStream R τ φ (p.1, ζ))
      (p.1 * fderiv ℝ φ (merChart R τ p) ((0 : ℝ), ((0 : ℝ), R / p.1))) p.2 := by
    have h := (hφ'.comp_hasDerivAt p.2 (hasDerivAt_merChart_snd R τ (r := p.1) p.2)).const_mul p.1
    simpa [ringStream] using h
  rw [(hasDerivAt_line_snd (differentiableAt_ringStream hR hp hφ)).unique hline, clm_triple, dEta]
  simp only [smul_eq_mul, zero_mul, zero_add]
  field_simp

theorem dρ_ringStream {R τ : ℝ} (hR : R ≠ 0) {φ : ℝ × (ℝ × ℝ) → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ≠ 0) (hφ : DifferentiableAt ℝ φ (merChart R τ p)) :
    dρ (ringStream R τ φ) p = φ (merChart R τ p) - 2 * (R ^ 2 / p.1 ^ 2) * dS φ (merChart R τ p) +
      R * dQ φ (merChart R τ p) - R * p.2 / p.1 * dEta φ (merChart R τ p) := by
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (merChart R τ p)) (merChart R τ (p.1, p.2)) :=
    hφ.hasFDerivAt
  have hline : HasDerivAt (fun r => ringStream R τ φ (r, p.2))
      (1 * φ (merChart R τ p) + p.1 * fderiv ℝ φ (merChart R τ p)
        (-(2 * R ^ 2 / p.1 ^ 3), (R / p.1, -(R * p.2 / p.1 ^ 2)))) p.1 := by
    have h := (hasDerivAt_id' p.1).fun_mul
      (hφ'.comp_hasDerivAt p.1 (hasDerivAt_merChart_fst hR τ p.2 hp))
    exact h
  rw [(hasDerivAt_line_fst (differentiableAt_ringStream hR hp hφ)).unique hline, clm_triple]
  simp only [dS, dQ, dEta, smul_eq_mul]
  field_simp
  ring

/-- The stream profile of the ring stream: `streamProfile (ρ φ) = (R/ρ) e(merChart)`. -/
theorem streamProfile_ringStream {R τ : ℝ} (hR : R ≠ 0) {φ : ℝ × (ℝ × ℝ) → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ≠ 0) (hφ : DifferentiableAt ℝ φ (merChart R τ p)) :
    streamProfile (ringStream R τ φ) p =
      (R / p.1) • ringStreamProfile R φ (merChart R τ p) := by
  rw [streamProfile, dz_ringStream hR hp hφ, dρ_ringStream hR hp hφ, ringStreamProfile]
  ext i
  fin_cases i
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, m0_zero, m1_zero]
    field_simp
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, m0_one, m1_one,
      merChart]
    field_simp
    ring

/-- **AX06 `ringStreamLift_components`** (B0298, tex 5282–5295; B0185). Off the axis, the stream
lift of the physical stream `ρ φ(s, ξ, η)` is the ring lift `N_v e` of the normalized
components `e = (−φ_η, φ_ξ + ε(φ − 2sφ_s − ηφ_η))`, `ε = R⁻¹`. -/
theorem ringStreamLift_components {R τ : ℝ} (hR : 0 < R) {φ : ℝ × (ℝ × ℝ) → ℝ} {y : Space}
    (hy : y ∉ axis) (hφ : DifferentiableAt ℝ φ (chart R τ y)) :
    streamLift (ringStream R τ φ) y = Nv R (ringStreamProfile R φ) τ y := by
  rw [streamLift, liftMer_eq_frameL, streamProfile_ringStream hR.ne' (ϱ_ne_zero hy) hφ, Nv,
    sqrt_age hR hy, map_smul, chart_eq_merChart]
  rfl

/-- The components of B0298 for an age cutoff times an entrance stream, `φ = χ(s) ψ(ξ, η)`:
`e_ε = (−χψ_η, χψ_ξ + ε[(χ − 2sχ')ψ − χηψ_η])` (tex 5288–5295, tex 5150–5155). -/
theorem ringStreamProfile_cutoff (R : ℝ) {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} {m : ℝ × (ℝ × ℝ)}
    (hχ : DifferentiableAt ℝ χ m.1) (hψ : DifferentiableAt ℝ ψ m.2) :
    ringStreamProfile R (fun n => χ n.1 * ψ n.2) m =
      (-(χ m.1 * fderiv ℝ ψ m.2 (0, 1))) • m0 +
        (χ m.1 * fderiv ℝ ψ m.2 (1, 0) + R⁻¹ * ((χ m.1 - 2 * m.1 * deriv χ m.1) * ψ m.2 -
          χ m.1 * m.2.2 * fderiv ℝ ψ m.2 (0, 1))) • m1 := by
  have h1 : HasFDerivAt (fun n : ℝ × (ℝ × ℝ) => χ n.1)
      (deriv χ m.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) m :=
    hχ.hasDerivAt.comp_hasFDerivAt m hasFDerivAt_fst
  have h2 : HasFDerivAt (fun n : ℝ × (ℝ × ℝ) => ψ n.2)
      ((fderiv ℝ ψ m.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) m :=
    hψ.hasFDerivAt.comp m hasFDerivAt_snd
  have hd := (h1.fun_mul h2).fderiv
  simp only [ringStreamProfile, dS, dQ, dEta, hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, Prod.mk_zero_zero, map_zero, mul_zero, mul_one, zero_add, add_zero]
  congr 2
  ring_nf

theorem merChart_zero_snd {R : ℝ} (hR : 0 < R) {p : ℝ × ℝ} (hp : 0 < p.1) :
    (merChart R 0 p).2 = (R * Real.log (p.1 / R), R * p.2 / p.1) := by
  rw [merChart]
  rw [Real.log_div (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 hp.ne'), Real.log_pow, Real.log_pow,
    Real.log_div hp.ne' hR.ne']
  push_cast
  ring_nf

/-- The datum stream at `τ = 0`: for `ρ, R > 0`,
`ringStream R 0 (ψ ∘ snd) (ρ, z) = ρ ψ(R log(ρ/R), Rz/ρ)` (B0185: `𝒫 = rψ`, tex 5297). -/
theorem ringStream_datum {R : ℝ} (hR : 0 < R) (ψ : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ringStream R 0 (fun n => ψ n.2) p = p.1 * ψ (R * Real.log (p.1 / R), R * p.2 / p.1) := by
  rw [ringStream, merChart_zero_snd hR hp]

/-- **The datum of `background:eq:2.27`** (B0298, tex 5288–5297). Off the axis, the stream lift of
the physical stream `ρ ψ(R log(ρ/R), Rz/ρ)` is
`(R/ϱ)[−ψ_η e_r + (ψ_q + ε(ψ − ηψ_η)) e_z]` at `q = R log(ϱ/R)`, `η = R y₃/ϱ`. -/
theorem streamLift_datum {R : ℝ} (hR : 0 < R) {ψ : ℝ × ℝ → ℝ} {y : Space} (hy : y ∉ axis)
    (hψ : DifferentiableAt ℝ ψ (R * Real.log (ϱ y / R), R * y 2 / ϱ y)) :
    streamLift (ringStream R 0 fun n => ψ n.2) y =
      (R / ϱ y) • ((-(fderiv ℝ ψ (R * Real.log (ϱ y / R), R * y 2 / ϱ y) (0, 1))) • eR y +
        (fderiv ℝ ψ (R * Real.log (ϱ y / R), R * y 2 / ϱ y) (1, 0) +
          R⁻¹ * (ψ (R * Real.log (ϱ y / R), R * y 2 / ϱ y) - R * y 2 / ϱ y *
            fderiv ℝ ψ (R * Real.log (ϱ y / R), R * y 2 / ϱ y) (0, 1))) • e3) := by
  have hρ := ϱ_pos hy
  have hm2 : (chart R 0 y).2 = (R * Real.log (ϱ y / R), R * y 2 / ϱ y) := by
    rw [chart_eq_merChart]
    exact merChart_zero_snd hR (p := mer y) hρ
  have hm22 : (chart R 0 y).2.2 = R * y 2 / ϱ y := by rw [hm2]
  have hψ' : DifferentiableAt ℝ ψ (chart R 0 y).2 := by rw [hm2]; exact hψ
  have hφ : DifferentiableAt ℝ (fun n : ℝ × (ℝ × ℝ) => ψ n.2) (chart R 0 y) :=
    hψ'.comp _ differentiableAt_snd
  rw [ringStreamLift_components hR hy hφ]
  have hcut := ringStreamProfile_cutoff R (χ := fun _ => (1 : ℝ)) (ψ := ψ)
    (m := chart R 0 y) (differentiableAt_const _) hψ'
  simp only [one_mul, deriv_const', mul_zero, sub_zero] at hcut
  rw [Nv, hcut, sqrt_age hR hy, hm22, hm2, map_add, map_smul, map_smul, frameL_m0, frameL_m1]

end UnforcedLeray.Axi
