import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileOfNoSwirl.Real

/-!
# Part II-b, task `PartII-b:T10/6/2`: no-swirl phase fields are lifts of `H_r` profiles

Source of record: `the November 2 reference manuscript`, lines 1902-1906.

Target `profileOfNoSwirl_proof : ProfileOfNoSwirl`: a `P`-periodic, measurable, no-swirl `Y_r`
field (`P = 2εc`, `R = ε⁻¹`) is a.e. the ring lift `N_v p` of a `c`-periodic measurable profile `p`.

Proof. Real and imaginary parts give real no-swirl fields for each `g ∈ 𝒪`; the rotation averaging
`avgLift` (per-`g` version in `ProfileOfNoSwirl/AvgPG.lean`) writes them as `A_r e_r + A_z e_z`;
the inverse chart `invLift` (with the constant `(√π R)⁻¹`, matching `liftFun`) gives the profile
`p`; `N_v` of `p` is the field on one period, and periodicity extends it to `ℝ × ℝ³`
(`ProfileOfNoSwirl/Ext.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.B0412 UnforcedLeray.PhaseSpace UnforcedLeray.Axi

/-- A complex meridional vector with real part `K • u` and imaginary part `K • v`. -/
def meridC (u v : Merid) (K : ℝ) : CMerid :=
  WithLp.toLp 2 fun i => ((K * u i : ℝ) : ℂ) + Complex.I * ((K * v i : ℝ) : ℂ)

theorem reM_meridC (u v : Merid) (K : ℝ) : reM (meridC u v K) = K • u := by
  ext i
  simp [reM, meridC]

theorem imM_meridC (u v : Merid) (K : ℝ) : imM (meridC u v K) = K • v := by
  ext i
  simp [imM, meridC]

theorem NvC_meridC (R K : ℝ) (B1 B2 : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × Space) :
    NvC R (fun z => meridC (B1 z) (B2 z) K) x =
      realC (K • Nv R B1 x.1 x.2) + Complex.I • realC (K • Nv R B2 x.1 x.2) := by
  have h1 : (fun z => reM (meridC (B1 z) (B2 z) K)) = K • B1 :=
    funext fun z => reM_meridC _ _ _
  have h2 : (fun z => imM (meridC (B1 z) (B2 z) K)) = K • B2 :=
    funext fun z => imM_meridC _ _ _
  simp only [NvC]
  rw [h1, h2, Nv_smul, Nv_smul]

/-- Integer shifts in `q` of the inverse chart: `perRep` is `P`-periodic. -/
theorem perRep_add_int_mul {P : ℝ} (hP : P ≠ 0) (t : ℝ) (k : ℤ) :
    perRep P (t + (k : ℝ) * P) = perRep P t := by
  unfold perRep
  have h1 : (t + (k : ℝ) * P) / P = t / P + (k : ℝ) := by
    rw [add_div, mul_div_cancel_right₀ _ hP]
  rw [h1, Int.ceil_add_intCast]
  push_cast
  ring

theorem invLift_int_shift {R c P : ℝ} (hc : 0 < c) (hR : 0 < R) (hP : P = 2 * c / R)
    (A : ℝ × (ℝ × ℝ) → Merid) (k : ℤ) (s ξ η : ℝ) :
    invLift R P A (s, (ξ + (k : ℝ) * c, η)) = invLift R P A (s, (ξ, η)) := by
  have hPne : P ≠ 0 := by
    rw [hP]
    positivity
  have e : 2 / R * (ξ + (k : ℝ) * c) + Real.log s = (2 / R * ξ + Real.log s) + (k : ℝ) * P := by
    rw [hP]
    ring
  unfold invLift
  dsimp only
  rw [e, perRep_add_int_mul hPne]


theorem invLift_perExt {R c P : ℝ} (hc : 0 < c) (hR : 0 < R) (hP : P = 2 * c / R)
    (A : ℝ × (ℝ × ℝ) → Merid) : perExt c (invLift R P A) = invLift R P A := by
  funext p
  unfold perExt
  have e : cellRep c p.2.1 = p.2.1 + ((-(⌊(p.2.1 + c / 2) / c⌋) : ℤ) : ℝ) * c := by
    unfold cellRep
    push_cast
    ring
  rw [e]
  exact invLift_int_shift hc hR hP A _ _ _ _

theorem invLift_c_shift {R c P : ℝ} (hc : 0 < c) (hR : 0 < R) (hP : P = 2 * c / R)
    (A : ℝ × (ℝ × ℝ) → Merid) (s ξ η : ℝ) :
    invLift R P A (s, (ξ + c, η)) = invLift R P A (s, (ξ, η)) := by
  have h := invLift_int_shift hc hR hP A 1 s ξ η
  simpa using h

/-- The frame identity for the inverse chart, with the constant `(√π R)⁻¹` of `liftFun`. -/
theorem frame_invLift {R c P : ℝ} (hc : 0 < c) (hR : 0 < R) (hP : P = 2 * c / R)
    (A : ℝ × (ℝ × ℝ) → Merid) {τ : ℝ} (hτ : τ ∈ Ioc 0 P) {y : Space} (hy : y ∉ axis) :
    (√π * R)⁻¹ • Nv R (invLift R P A) τ y = frameL y (A (τ, mer y)) := by
  have h := liftFun_invLift hR hc hP A hτ hy
  unfold liftFun at h
  rw [invLift_perExt hc hR hP A] at h
  exact h

theorem frameL_avgMer (W : ℝ × Space → Space) (τ : ℝ) (y : Space) :
    frameL y (avgMer W (τ, mer y)) = avgR W (τ, mer y) • eR y + avgZ W (τ, mer y) • e3 := by
  rw [frameL_apply]
  simp [avgMer]

/-- Periodicity of the lifted complex field in `τ`. -/
theorem NvC_meridC_periodic {R c P K : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R)
    (B1 B2 : ℝ × (ℝ × ℝ) → Merid)
    (h1 : ∀ s ξ η, B1 (s, (ξ + c, η)) = B1 (s, (ξ, η)))
    (h2 : ∀ s ξ η, B2 (s, (ξ + c, η)) = B2 (s, (ξ, η))) (τ : ℝ) (y : Space) :
    NvC R (fun z => meridC (B1 z) (B2 z) K) (τ + P, y) =
      NvC R (fun z => meridC (B1 z) (B2 z) K) (τ, y) := by
  rw [NvC_meridC, NvC_meridC]
  dsimp only
  rw [Nv_dss hR hP h1, Nv_dss hR hP h2]

theorem continuous_meridC (K : ℝ) : Continuous fun q : Merid × Merid => meridC q.1 q.2 K := by
  unfold meridC
  fun_prop


theorem measurable_reV : Measurable reV := by
  unfold reV
  fun_prop

theorem measurable_imV : Measurable imV := by
  unfold imV
  fun_prop

/-- **Target** `PartII-b:T10/6/2` (`ProfileOfNoSwirl`). -/
theorem profileOfNoSwirl_proof : ProfileOfNoSwirl := by
  intro c ε r d hc hε hr hd hns
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hP0 : 0 < 2 * ε * c := by positivity
  obtain ⟨d', hd'm, hdd⟩ : ∃ d' : ℝ × Space → CVec3, Measurable d' ∧ d' =ᵐ[volume] d :=
    ⟨hd.meas.mk d, hd.meas.stronglyMeasurable_mk.measurable, hd.meas.ae_eq_mk.symm⟩
  set W : ℝ × Space → Space := fun x => reV (d' x) with hWdef
  set W' : ℝ × Space → Space := fun x => imV (d' x) with hW'def
  have hW : Measurable W := measurable_reV.comp hd'm
  have hW' : Measurable W' := measurable_imV.comp hd'm
  have hgW : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ x ∂phaseμ (2 * ε * c), W (x.1, g x.2) = g (W x) :=
    fun g hg => ae_phase_of_ae_volume
      (ae_equiv_of_phaseNoSwirl (Φ := reV) (fun g v => reV_gC g v) hns hdd g hg)
  have hgW' : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ x ∂phaseμ (2 * ε * c), W' (x.1, g x.2) = g (W' x) :=
    fun g hg => ae_phase_of_ae_volume
      (ae_equiv_of_phaseNoSwirl (Φ := imV) (fun g v => imV_gC g v) hns hdd g hg)
  have hWeq : ∀ᵐ x ∂phaseμ (2 * ε * c),
      W x = avgR W (x.1, mer x.2) • eR x.2 + avgZ W (x.1, mer x.2) • e3 :=
    ae_eq_avgLift_pg (μ := (ENNReal.ofReal (2 * ε * c))⁻¹ • volume.restrict (Ioc (0 : ℝ) (2 * ε * c)))
      hW hgW
  have hWeq' : ∀ᵐ x ∂phaseμ (2 * ε * c),
      W' x = avgR W' (x.1, mer x.2) • eR x.2 + avgZ W' (x.1, mer x.2) • e3 :=
    ae_eq_avgLift_pg (μ := (ENNReal.ofReal (2 * ε * c))⁻¹ • volume.restrict (Ioc (0 : ℝ) (2 * ε * c)))
      hW' hgW'
  have hτ : ∀ᵐ x ∂phaseμ (2 * ε * c), x.1 ∈ Ioc 0 (2 * ε * c) :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _)
  have hy : ∀ᵐ x ∂phaseμ (2 * ε * c), x.2 ∉ axis :=
    Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis
  have hBRm : Measurable (invLift ε⁻¹ (2 * ε * c) (avgMer W)) :=
    measurable_invLift _ _ (measurable_avgMer hW)
  have hBIm : Measurable (invLift ε⁻¹ (2 * ε * c) (avgMer W')) :=
    measurable_invLift _ _ (measurable_avgMer hW')
  have hBRper : ∀ s ξ η, invLift ε⁻¹ (2 * ε * c) (avgMer W) (s, (ξ + c, η)) =
      invLift ε⁻¹ (2 * ε * c) (avgMer W) (s, (ξ, η)) :=
    fun s ξ η => invLift_c_shift hc hR hP _ s ξ η
  have hBIper : ∀ s ξ η, invLift ε⁻¹ (2 * ε * c) (avgMer W') (s, (ξ + c, η)) =
      invLift ε⁻¹ (2 * ε * c) (avgMer W') (s, (ξ, η)) :=
    fun s ξ η => invLift_c_shift hc hR hP _ s ξ η
  refine ⟨fun z => meridC (invLift ε⁻¹ (2 * ε * c) (avgMer W) z)
    (invLift ε⁻¹ (2 * ε * c) (avgMer W') z) (√π * ε⁻¹)⁻¹, ?_, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    show meridC (invLift ε⁻¹ (2 * ε * c) (avgMer W) (x.1, (x.2.1 + c, x.2.2)))
        (invLift ε⁻¹ (2 * ε * c) (avgMer W') (x.1, (x.2.1 + c, x.2.2))) (√π * ε⁻¹)⁻¹ =
      meridC (invLift ε⁻¹ (2 * ε * c) (avgMer W) x)
        (invLift ε⁻¹ (2 * ε * c) (avgMer W') x) (√π * ε⁻¹)⁻¹
    rw [hBRper, hBIper]
  · have hmeas : Measurable (fun z : ℝ × (ℝ × ℝ) =>
        meridC (invLift ε⁻¹ (2 * ε * c) (avgMer W) z)
          (invLift ε⁻¹ (2 * ε * c) (avgMer W') z) (√π * ε⁻¹)⁻¹) :=
      (continuous_meridC _).measurable.comp (hBRm.prodMk hBIm)
    exact hmeas.aestronglyMeasurable
  · have hae : ∀ᵐ x ∂phaseμ (2 * ε * c), NvC ε⁻¹
        (fun z => meridC (invLift ε⁻¹ (2 * ε * c) (avgMer W) z)
          (invLift ε⁻¹ (2 * ε * c) (avgMer W') z) (√π * ε⁻¹)⁻¹) x = d x := by
      have hdP : ∀ᵐ x ∂phaseμ (2 * ε * c), d' x = d x := ae_phase_of_ae_volume hdd
      filter_upwards [hWeq, hWeq', hτ, hy, hdP] with x h1 h1' h2 h3 h4
      rw [NvC_meridC, frame_invLift hc hR hP (avgMer W) h2 h3,
        frame_invLift hc hR hP (avgMer W') h2 h3, frameL_avgMer, frameL_avgMer, ← h1, ← h1']
      show realC (reV (d' x)) + Complex.I • realC (imV (d' x)) = d x
      rw [← realC_decomp]
      exact h4
    exact ae_volume_of_periodic hP0
      (fun τ y => NvC_meridC_periodic hR.ne' hP _ _ hBRper hBIper τ y) hd.periodic hae

end UnforcedLeray.Short.IIb
