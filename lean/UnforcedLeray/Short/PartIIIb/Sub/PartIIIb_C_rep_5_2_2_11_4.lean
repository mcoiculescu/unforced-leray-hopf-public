import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# `PartIII-b:C/rep/5/2/2/11/4` : decomposition of `TCGrad`

Source `the November 2 reference manuscript`
4176-4214 (`Ψ_{AZ} = AΨ_Z + Ψ_Z`, `A = -y·∇/2`), 3603-3647 (kernel bounds for `X₀`), 3700-3712.

`tcg_generic` (proved here): for an abstract field `Z` which is `C²`, divergence free and
axisymmetric swirl-free on the young region, with `StreamDecay` and with `ρ (y·∇Z)_z`
integrable on `(ϱ y, ∞)`, one has `Ψ_{y·∇Z} = (y·∇)Ψ_Z - 2Ψ_Z` at `y`.  Proof: `∂_rΨ = rZ_z`,
`∂_zΨ = -rZ_r` (`outPrimDerivR`, `outPrimDerivZ`), `Ψ` is `C²` (`t9_outPrim_c2`), `(y·∇)Ψ = ϱ∂_rΨ +
y₃∂_zΨ`; and `-∫ρ²∂_ρZ_z = ϱ²Z_z - 2Ψ` (integration by parts, the boundary term at infinity
vanishes because `ρ Z_z` is integrable and `ρ²Z_z` has a limit), `-z∫ρ∂_zZ_z = -zϱZ_r` (divergence).

The single leaf `TCGradX0Facts` is the analysis of `X₀ = sepX0` (the five hypotheses of
`tcg_generic`); `tcGrad_of` proves `TCGrad` from it.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Structure of `X₀`** (source 4176-4214, 3603-3647): for separated old data in the context of
`TransCommPoint`, `Z = X₀ = sepX0 ν μ T` is `C²` in `y` on the young region `ϱ > R√(5ν/6)` (old data
is supported in `ϱ ≤ R√(5ν/6)`, so the kernels are smooth there), divergence free there (the Leray
kernel `K_t` satisfies `∂_iK_{ij} = 0`) and axisymmetric swirl-free (`IsAxiSource`). -/
def TCGradX0Struct : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) ∧
      (∀ y' ∈ youngOpen ν R, ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y' j = 0) ∧
      AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)

/-- **Decay of `X₀`** (source 4177-4179, 4181-4192, from `SepKernelBounds`
`|D^jW| ≤ C r^{-4-j+3/b}` and the finite `L²_τL²` moment): `X₀` obeys `StreamDecay` on the young
region, and `ρ (y·∇X₀)_z(ρ,0,y₃)` is integrable on `(ϱ y, ∞)` (one more derivative and the weight
`|y|`; this is the third integrability of `TCInt`). -/
def TCGradX0Decay : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      StreamDecay ν R (sepX0 ν μ T) τ ∧
      IntegrableOn (fun ρ : ℝ => ρ *
        (fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y))

/-- Integration by parts on `(r₀,∞)` for `x² f'`, with vanishing boundary term at infinity. -/
theorem tcg_ibp {r0 : ℝ} {f A : ℝ → ℝ}
    (hd : ∀ x ∈ Ici r0, HasDerivAt f (A x) x)
    (hf : IntegrableOn (fun x => x * f x) (Ioi r0))
    (hA : IntegrableOn (fun x => x ^ 2 * A x) (Ioi r0)) :
    ∫ x in Ioi r0, x ^ 2 * A x = -(r0 ^ 2 * f r0) - 2 * ∫ x in Ioi r0, x * f x := by
  have hg : ∀ x ∈ Ici r0, HasDerivAt (fun x => x ^ 2 * f x) (2 * (x * f x) + x ^ 2 * A x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 * f x) (((2 : ℕ) : ℝ) * x ^ (2 - 1) * f x + x ^ 2 * A x) x :=
      (hasDerivAt_pow 2 x).mul (hd x hx)
    exact h1.congr_deriv (by norm_num <;> ring)
  have hint : IntegrableOn (fun x => 2 * (x * f x) + x ^ 2 * A x) (Ioi r0) :=
    (hf.const_mul 2).add hA
  have hlim := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (fun x hx => hg x (Set.mem_Ici.2 hx.le)) hint
  set L := limUnder atTop (fun x : ℝ => x ^ 2 * f x) with hL
  have hL0 : L = 0 := by
    by_contra hne
    have hLa : 0 < |L| := abs_pos.2 hne
    have habs : Tendsto (fun x : ℝ => |x ^ 2 * f x|) atTop (𝓝 |L|) :=
      (continuous_abs.tendsto L).comp hlim
    have hev : ∀ᶠ x in atTop, |L| / 2 < |x ^ 2 * f x| :=
      habs.eventually (lt_mem_nhds (by linarith))
    obtain ⟨M, hM⟩ := eventually_atTop.1
      (hev.and ((eventually_gt_atTop r0).and (eventually_gt_atTop (1 : ℝ))))
    set N := max M r0 with hN
    have hsub : IntegrableOn (fun x => x * f x) (Ioi N) :=
      hf.mono_set (Ioi_subset_Ioi (le_max_right _ _))
    have hx : ∀ x ∈ Ioi N, |L| / 2 < |x ^ 2 * f x| ∧ 1 < x := fun x hx =>
      ⟨(hM x (le_trans (le_max_left _ _) hx.le)).1, (hM x (le_trans (le_max_left _ _) hx.le)).2.2⟩
    have hcomp : IntegrableOn (fun x : ℝ => (|L| / 2) * x⁻¹) (Ioi N) := by
      refine Integrable.mono' hsub.norm ?_ ?_
      · exact (measurable_inv.const_mul _).aestronglyMeasurable
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hxm => ?_
        obtain ⟨h1, h2⟩ := hx x hxm
        have hx0 : 0 < x := by linarith
        have e : |x ^ 2 * f x| = x * ‖x * f x‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0, abs_of_pos (pow_pos hx0 2)]
          ring
        rw [e] at h1
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [← div_eq_mul_inv, div_le_iff₀ hx0]
        linarith
    have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi N) := by
      have := hcomp.const_mul (2 / |L|)
      refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
      field_simp
    exact not_integrableOn_Ioi_inv hinv
  have hcont : ContinuousWithinAt (fun x => x ^ 2 * f x) (Ici r0) r0 :=
    (hg r0 (Set.mem_Ici.2 le_rfl)).continuousAt.continuousWithinAt
  have hT : Tendsto (fun x : ℝ => x ^ 2 * f x) atTop (𝓝 0) := hL0 ▸ hlim
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx => hg x (Set.mem_Ici.2 hx.le))
    hint hT
  rw [integral_add (hf.const_mul 2) hA, integral_const_mul] at key
  try simp only at key
  linarith

/-- Integrability of `ρ Z_z` and `ρ ∂_zZ_z` on `(r,∞)` from `StreamDecay`. -/
theorem tcg_int {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R)) (hS : StreamDecay ν R Z τ) (r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    IntegrableOn (fun x : ℝ => x * Z τ !₂[x, 0, z] 2) (Ioi r) ∧
    IntegrableOn (fun x : ℝ => x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2) (Ioi r) := by
  obtain ⟨⟨B, hBi, hB⟩, -⟩ := hS r z hr
  have hcontF : ContinuousOn (fun x : ℝ => x * Z τ !₂[x, 0, z] 2) (Ioi r) :=
    (continuousOn_id.mul (t3c_contZ hZc z 2)).mono (fun x hx => lt_trans hr hx)
  have hD2 : ContinuousOn (fun x : ℝ => x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2)
      (Ioi r) :=
    (continuousOn_id.mul (t3c_contD hZc z (coordinateVector 2) 2)).mono
      (fun x hx => lt_trans hr hx)
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hBi (hcontF.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact (hB x hx z (Metric.mem_ball_self one_pos)).1
  · refine Integrable.mono' hBi (hD2.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact (hB x hx z (Metric.mem_ball_self one_pos)).2

/-- `∫_r^∞ ρ ∂_zZ_z = r Z_r(r)` (divergence-free, axisymmetric, decay). -/
theorem tcg_vert {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdiv : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0)
    (hAx : AxiNoSwirlOn (youngOpen ν R) Z) (hS : StreamDecay ν R Z τ) (r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    ∫ x in Ioi r, x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2 =
      r * Z τ !₂[r, 0, z] 0 := by
  obtain ⟨-, hTend⟩ := hS r z hr
  have hgInt := (tcg_int hZc hS r z hr).2
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with x hx
    simpa using hx
  have hae : (fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
      =ᵐ[volume.restrict (Ioi r)]
      (fun x : ℝ => -(x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae h0] with x hx hx0
    exact t3c_key hZc hdiv hAx z x (lt_trans hr hx) hx0
  have hf'Int : IntegrableOn
      (fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
      (Ioi r) :=
    hgInt.neg.congr_fun_ae hae.symm
  have hcont : ContinuousWithinAt (fun x : ℝ => x * Z τ !₂[x, 0, z] 0) (Ici r) r :=
    (t3c_hGd hZc z r hr).continuousAt.continuousWithinAt
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x : ℝ => x * Z τ !₂[x, 0, z] 0)
    (f' := fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
    hcont (fun x hx => t3c_hGd hZc z x (lt_trans hr hx)) hf'Int hTend
  have hc := integral_congr_ae hae
  rw [integral_neg] at hc
  try simp only at hFTC
  linarith

theorem tcg_rho_rad {y : Space} (h : 0 < ϱ y) {t : ℝ} (ht : -ϱ y < t) :
    ϱ (y + t • radialUnit y) = ϱ y + t := by
  have h2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold ϱ; rw [Real.sq_sqrt (by positivity)]
  have hne : ϱ y ≠ 0 := h.ne'
  have e : (y 0 + t * ((ϱ y)⁻¹ * y 0)) ^ 2 + (y 1 + t * ((ϱ y)⁻¹ * y 1)) ^ 2 = (ϱ y + t) ^ 2 := by
    have e1 : (y 0 + t * ((ϱ y)⁻¹ * y 0)) ^ 2 + (y 1 + t * ((ϱ y)⁻¹ * y 1)) ^ 2 =
        (y 0 ^ 2 + y 1 ^ 2) * (1 + t * (ϱ y)⁻¹) ^ 2 := by ring
    rw [e1, ← h2]
    field_simp
  have : ϱ (y + t • radialUnit y) = Real.sqrt ((y 0 + t * ((ϱ y)⁻¹ * y 0)) ^ 2 +
      (y 1 + t * ((ϱ y)⁻¹ * y 1)) ^ 2) := by
    simp [ϱ, radialUnit]
  rw [this, e, Real.sqrt_sq (by linarith)]

theorem tcg_y_decomp {y : Space} (h : 0 < ϱ y) :
    y = ϱ y • radialUnit y + y 2 • (coordinateVector 2 : Space) := by
  have hne : ϱ y ≠ 0 := h.ne'
  ext i
  fin_cases i <;> simp [radialUnit, coordinateVector] <;> field_simp

/-- `(y·∇)` of the primitive: `ϱ ∂_rΨ + y₃ ∂_zΨ`. -/
theorem tcg_fderiv_Phi {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    {y : Space} (hy : y ∈ youngOpen ν R)
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdiv : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0)
    (hAx : AxiNoSwirlOn (youngOpen ν R) Z) (hS : StreamDecay ν R Z τ) :
    DifferentiableAt ℝ (fun y : Space => outPrim Z τ (ϱ y) (y 2)) y ∧
    fderiv ℝ (fun y : Space => outPrim Z τ (ϱ y) (y 2)) y y =
      ϱ y * (ϱ y * Z τ !₂[ϱ y, 0, y 2] 2) + y 2 * (-(ϱ y * Z τ !₂[ϱ y, 0, y 2] 0)) := by
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hr : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  have hpos : 0 < ϱ y := lt_of_le_of_lt (by positivity) hr
  have hΦ := t9_outPrim_c2 hν hR hZc (fun r z hr =>
    ⟨outPrimDerivR ν R Z τ hZc hS r z hr, outPrimDerivZ ν R Z τ hZc hdiv hAx hS r z hr⟩)
  have hdiff : DifferentiableAt ℝ (fun y : Space => outPrim Z τ (ϱ y) (y 2)) y :=
    (hΦ.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
  refine ⟨hdiff, ?_⟩
  set Φ := fun y : Space => outPrim Z τ (ϱ y) (y 2) with hΦdef
  -- radial direction
  have hrad : fderiv ℝ Φ y (radialUnit y) = ϱ y * Z τ !₂[ϱ y, 0, y 2] 2 := by
    have hc : HasDerivAt (fun t : ℝ => y + t • radialUnit y) (radialUnit y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (radialUnit y)).const_add y
    have hF : HasFDerivAt Φ (fderiv ℝ Φ y) ((fun t : ℝ => y + t • radialUnit y) 0) := by
      simpa using hdiff.hasFDerivAt
    have h1 := hF.comp_hasDerivAt (0 : ℝ) hc
    have h2 : HasDerivAt (fun t : ℝ => outPrim Z τ (ϱ y + t) (y 2))
        (ϱ y * Z τ !₂[ϱ y, 0, y 2] 2) 0 :=
      (show HasDerivAt _ _ (ϱ y + 0) by simpa using outPrimDerivR ν R Z τ hZc hS (ϱ y) (y 2) hr
        ).comp_const_add (ϱ y) 0
    have heq : (Φ ∘ fun t : ℝ => y + t • radialUnit y) =ᶠ[𝓝 0] fun t : ℝ => outPrim Z τ (ϱ y + t) (y 2) := by
      have : Metric.ball (0 : ℝ) (ϱ y) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hpos
      filter_upwards [this] with t ht
      have ht' : -ϱ y < t := by
        have := (Metric.mem_ball.1 ht); rw [Real.dist_eq, sub_zero] at this
        linarith [neg_abs_le t, abs_lt.1 this]
      have hz : (y + t • radialUnit y) 2 = y 2 := by simp [radialUnit]
      simp only [Function.comp, hΦdef, tcg_rho_rad hpos ht', hz]
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hvert : fderiv ℝ Φ y (coordinateVector 2) = -(ϱ y * Z τ !₂[ϱ y, 0, y 2] 0) := by
    have hc : HasDerivAt (fun t : ℝ => y + t • (coordinateVector 2 : Space)) (coordinateVector 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 : Space)).const_add y
    have hF : HasFDerivAt Φ (fderiv ℝ Φ y) ((fun t : ℝ => y + t • (coordinateVector 2 : Space)) 0) := by
      simpa using hdiff.hasFDerivAt
    have h1 := hF.comp_hasDerivAt (0 : ℝ) hc
    have h2 : HasDerivAt (fun t : ℝ => outPrim Z τ (ϱ y) (y 2 + t))
        (-(ϱ y * Z τ !₂[ϱ y, 0, y 2] 0)) 0 :=
      (show HasDerivAt _ _ (y 2 + 0) by
        simpa using outPrimDerivZ ν R Z τ hZc hdiv hAx hS (ϱ y) (y 2) hr).comp_const_add (y 2) 0
    have heq : (Φ ∘ fun t : ℝ => y + t • (coordinateVector 2 : Space)) = fun t : ℝ => outPrim Z τ (ϱ y) (y 2 + t) := by
      funext t
      have h0 : (y + t • (coordinateVector 2 : Space)) 0 = y 0 := by simp [coordinateVector]
      have h1' : (y + t • (coordinateVector 2 : Space)) 1 = y 1 := by simp [coordinateVector]
      have h2' : (y + t • (coordinateVector 2 : Space)) 2 = y 2 + t := by simp [coordinateVector]
      simp only [Function.comp, hΦdef, ϱ, h0, h1', h2']
    exact h1.unique (h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq))
  have e : fderiv ℝ Φ y y = fderiv ℝ Φ y (ϱ y • radialUnit y + y 2 • (coordinateVector 2 : Space)) := by
    rw [← tcg_y_decomp hpos]
  rw [e, map_add, map_smul, map_smul, hrad, hvert, smul_eq_mul, smul_eq_mul]

/-- **`Ψ_{y·∇Z} = (y·∇)Ψ_Z - 2Ψ_Z`** for an abstract field with the stated structure. -/
theorem tcg_generic {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space} {τ : ℝ}
    {y : Space} (hy : y ∈ youngOpen ν R)
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdiv : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0)
    (hAx : AxiNoSwirlOn (youngOpen ν R) Z) (hS : StreamDecay ν R Z τ)
    (hI : IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2)
      (Ioi (ϱ y))) :
    psiFld (fun t y' => fderiv ℝ (Z t) y' y') τ y =
      fderiv ℝ (psiFld Z τ) y y - (2 : ℝ) • psiFld Z τ y := by
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hr : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  obtain ⟨hdiff, hfd⟩ := tcg_fderiv_Phi hν hR hy hZc hdiv hAx hS
  have hps : fderiv ℝ (psiFld Z τ) y y =
      (fderiv ℝ (fun y : Space => outPrim Z τ (ϱ y) (y 2)) y y) • (coordinateVector 2 : Space) := by
    have : psiFld Z τ = fun y : Space => outPrim Z τ (ϱ y) (y 2) • (coordinateVector 2 : Space) :=
      rfl
    rw [this, fderiv_smul_const hdiff]
    rfl
  obtain ⟨hfI, hBI⟩ := tcg_int hZc hS (ϱ y) (y 2) hr
  have hvert := tcg_vert hZc hdiv hAx hS (ϱ y) (y 2) hr
  -- decomposition of the integrand
  have hdec : ∀ ρ : ℝ, (!₂[ρ, 0, y 2] : Space) = ρ • (coordinateVector 0 : Space) +
      y 2 • (coordinateVector 2 : Space) := by
    intro ρ; ext i; fin_cases i <;> simp [coordinateVector]
  have hpt : ∀ ρ : ℝ, ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2 =
      ρ ^ 2 * fderiv ℝ (Z τ) !₂[ρ, 0, y 2] (coordinateVector 0) 2 +
        y 2 * (ρ * fderiv ℝ (Z τ) !₂[ρ, 0, y 2] (coordinateVector 2) 2) := by
    intro ρ
    have e : fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2] = fderiv ℝ (Z τ) !₂[ρ, 0, y 2]
        (ρ • (coordinateVector 0 : Space) + y 2 • (coordinateVector 2 : Space)) := by
      rw [← hdec ρ]
    rw [e]
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hA : IntegrableOn (fun ρ : ℝ => ρ ^ 2 * fderiv ℝ (Z τ) !₂[ρ, 0, y 2] (coordinateVector 0) 2)
      (Ioi (ϱ y)) := by
    have := hI.sub (hBI.const_mul (y 2))
    refine this.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [hpt ρ]; ring
  have hd : ∀ x ∈ Ici (ϱ y), HasDerivAt (fun x : ℝ => Z τ !₂[x, 0, y 2] 2)
      (fderiv ℝ (Z τ) !₂[x, 0, y 2] (coordinateVector 0) 2) x := by
    intro x hx
    have hxr : R * Real.sqrt (5 * ν / 6) < x := lt_of_lt_of_le hr hx
    have hdA : DifferentiableAt ℝ (Z τ) !₂[x, 0, y 2] :=
      (hZc.contDiffAt (hopen.mem_nhds (t3c_mem (y 2) x hxr))).differentiableAt (by norm_num)
    exact t3c_proj 2 (t3c_chain hdA (t3c_c0 x (y 2)) rfl)
  have hibp := tcg_ibp hd hfI hA
  have hsplit : ∫ ρ in Ioi (ϱ y), ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2 =
      (∫ ρ in Ioi (ϱ y), ρ ^ 2 * fderiv ℝ (Z τ) !₂[ρ, 0, y 2] (coordinateVector 0) 2) +
        y 2 * ∫ ρ in Ioi (ϱ y), ρ * fderiv ℝ (Z τ) !₂[ρ, 0, y 2] (coordinateVector 2) 2 := by
    rw [← integral_const_mul, ← integral_add hA (hBI.const_mul (y 2))]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hps, hfd]
  show (-∫ ρ in Ioi (ϱ y), ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2) •
      (coordinateVector 2 : Space) = _
  show _ = _ - (2 : ℝ) • (outPrim Z τ (ϱ y) (y 2) • (coordinateVector 2 : Space))
  rw [smul_smul, ← sub_smul]
  congr 1
  unfold outPrim
  rw [hsplit, hibp, hvert]
  ring

/-- **`TCGrad` from the structure and decay of `X₀`.** -/
theorem tcGrad_of_parts (hS : TCGradX0Struct) (hD : TCGradX0Decay) : TCGrad := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := hctx
  have hctx : TCCtx σ₁ σ₂ ν μ R P T y := ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩
  have hR : 0 < R := by linarith
  have hyy : y ∈ youngOpen ν R := by
    show R * Real.sqrt (5 * ν / 6) < ϱ y
    refine lt_of_lt_of_le ?_ hy.1
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  obtain ⟨h1, h2, h3⟩ := hS σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨h4, h5⟩ := hD σ₁ σ₂ ν μ R P T τ y hctx
  exact tcg_generic hν hR hyy h1 h2 h3 h4 h5

end UnforcedLeray.Short.PartIIIb.Concrete
