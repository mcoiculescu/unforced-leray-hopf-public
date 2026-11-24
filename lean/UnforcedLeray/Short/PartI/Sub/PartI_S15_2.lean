import UnforcedLeray.Short.PartI.Sub.PartI_S15
import UnforcedLeray.Short.PartI.Tasks.XgEmbGeneral
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof
import UnforcedLeray.Lib.PlanarSpectralB.Complement
import UnforcedLeray.Lib.PlanarSpectralB.SimpleProj
import UnforcedLeray.Lib.OperatorInputs.SimpleSpectralDual

/-!
# Part I, task `PartI:S15/2` (decomposition): `SeedGrowProjAgree`

Source of record: `the November 2 reference manuscript`
lines 603-609 (`P = qℓ`, eq. `short-seed-functional`) and 841-889 ("Resolvents, hence Riesz
projections, agree on intersections of weighted spaces"; the sector-two adjoint functional).

Route.  Two leaves are the only analytic input:

* `SeedDualBounded`: the explicit functional `f ↦ seedEll h f` extends to a bounded functional
  `Λ` on the weighted profile space `L²(2π r ⟨r⟩^{2M} dr)` (the integrand `h r / k r · r` is in the
  dual weighted `L²`);
* `XgEmbDense`: the embedding `X_G → L²_M` of `PartI:S01` has dense range (the compactly supported
  radial profiles lie in `X_G`).

Proved here: with those, `Λ ∘ Lsec 2 = λ Λ` (it holds on the range of the embedding by `ℓ ∘ L_0 = λ ℓ`
and `SeedFunctional`, hence everywhere by density), so by uniqueness of the left eigenfunctional of
the simple Riesz projection `Λ = ℓ₂`; sector `-2` is the conjugate functional.  Then
`growingProjW_rankOne_apply` and the sector profile formula `secProf M n f = angularSector f n`
(`coeFn_secProf`, proved here) give the agreement with `seedProjFun`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-- Leaf `PartI:S15/2/1` (source 603-609 and 841-889).  For a seed triple, the explicit functional
`f ↦ ℓ(f) = J_q⁻¹ ∫₀^∞ h f /k · r dr` is a bounded functional on `L²(2π r⟨r⟩^{2M} dr)`:
`Λ f = seedEll h f` for every `f` in the profile space (integrand a.e. defined; `h/k` is smooth on
`(0,∞)`, `O(r⁻²)` at infinity by `SeedFunctional`, and `O(1)` near `0` since `h = O(r²)`, so
`h r/k r · r` lies in the dual weighted space `L²(dr/(r⟨r⟩^{2M}))`, `M > 1`). -/
def SeedDualBounded : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (_ : 1 < M),
      ∃ Λ : Planar.ProfL2 M →L[ℂ] ℂ, ∀ f : Planar.ProfL2 M, Λ f = seedEll h ⇑f

/-- Leaf `PartI:S15/2/2` (source 841-889; `PartI:S01`).  The embedding `xgEmbM : X_G → L²_M`
(identity on profiles) has dense range: `X_G` contains every compactly supported measurable
profile with finite `L²` norm, and these are dense in `L²(2π r⟨r⟩^{2M} dr)`. -/
def XgEmbDense : Prop := ∀ (M : ℝ) (hM : 1 < M), DenseRange (xgEmbM hM)

/-! ### Sector profile formula -/

theorem coeFn_secProf (M : ℝ) (n : ℤ) (f : Planar.L2w M) :
    ⇑(Planar.secProf M n f) =ᵐ[Planar.profileMeasure M]
      Planar.NUE.Polar.angularSector (⇑f) n := by
  set u : Planar.ProfL2 M := Planar.secProf M n f with hu
  set A : ℝ → ℂ := Planar.NUE.Polar.angularSector (⇑f) n with hA
  have h1 : Planar.NUE.Ang.ofProfile n (⇑u) =ᵐ[Planar.wMeasure M]
      Planar.NUE.Ang.ofProfile n A := by
    filter_upwards [Planar.coeFn_secEmb M n u, Planar.sectorProjW_ae_eq_ofProfile M n f]
      with x hx1 hx2
    rw [← hx1, hu, Planar.secEmb_secProf, hx2]
  have hfm : AEStronglyMeasurable (⇑f) volume :=
    (Lp.aestronglyMeasurable f).mono_ac (Planar.volume_ac M)
  have hAm : AEStronglyMeasurable A (Planar.profileMeasure M) :=
    (Planar.NUE.Ang.ParsevalH.aestronglyMeasurable_angularSector hfm n).mono_ac
      (Planar.profileMeasure_ac M)
  have hum : AEStronglyMeasurable (⇑u) (Planar.profileMeasure M) := Lp.aestronglyMeasurable u
  have hdm : AEStronglyMeasurable (fun r => u r - A r) (volume.restrict (Ioi 0)) :=
    (hum.sub hAm).mono_ac (Planar.ac_profileMeasure M)
  have h0 : ∫⁻ r, ‖u r - A r‖ₑ ^ 2 ∂Planar.profileMeasure M = 0 := by
    rw [← Planar.lintegral_ofProfile M n hdm]
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))]
    · simp
    · filter_upwards [h1] with x hx
      have : Planar.NUE.Ang.ofProfile n (fun r => u r - A r) x = 0 := by
        simp only [Planar.NUE.Ang.ofProfile, sub_mul] at hx ⊢
        rw [hx, sub_self]
      rw [this]
      simp
  have hmeas : AEMeasurable (fun r => ‖u r - A r‖ₑ ^ 2) (Planar.profileMeasure M) :=
    ((hum.sub hAm).enorm).pow_const 2
  have := (lintegral_eq_zero_iff' hmeas).1 h0
  filter_upwards [this] with r hr
  have : ‖u r - A r‖ₑ = 0 := by
    simpa using hr
  exact sub_eq_zero.1 (by simpa using this)

/-! ### Elementary lemmas -/

theorem seedEll_congr {h f f' : ℝ → ℂ} (hff : f =ᵐ[volume.restrict (Ioi 0)] f') :
    seedEll h f = seedEll h f' := by
  unfold seedEll
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hff] with r hr
  rw [hr]

theorem seedEll_congr_prof (M : ℝ) {h f f' : ℝ → ℂ}
    (hff : f =ᵐ[Planar.profileMeasure M] f') : seedEll h f = seedEll h f' :=
  seedEll_congr ((Planar.ac_profileMeasure M).ae_le hff)

/-- A left eigenfunctional read off a rank-one projection with `P A = z₀ P`. -/
theorem eigenfunctional_of_rankOne {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {A : X →L[ℂ] X} {ℓ : X →L[ℂ] ℂ} {q : X} {z₀ : ℂ} (hq : q ≠ 0)
    (hP : rankOneProj ℓ q * A = z₀ • rankOneProj ℓ q) (f : X) : ℓ (A f) = z₀ * ℓ f := by
  have h := congrArg (fun T : X →L[ℂ] X => T f) hP
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    Infra.Dunford.rankOneProj_apply, smul_smul] at h
  have h2 : (ℓ (A f) - z₀ * ℓ f) • q = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hq

theorem star_add_prof {M : ℝ} (f g : Planar.ProfL2 M) : star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Planar.coeFn_star_prof (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g),
    Planar.coeFn_star_prof f, Planar.coeFn_star_prof g] with r h1 h2 h3 h4 h5
  rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, map_add]

theorem norm_star_prof {M : ℝ} (f : Planar.ProfL2 M) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (Lp.coeFn_star f)]
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun r => by simp)

/-- The conjugate functional `f ↦ conj (Λ (star f))`. -/
def starFunctional {M : ℝ} (Λ : Planar.ProfL2 M →L[ℂ] ℂ) : Planar.ProfL2 M →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (starRingEnd ℂ) (Λ (star f))
      map_add' := fun f g => by simp only [star_add_prof, map_add]
      map_smul' := fun a f => by
        simp only [Planar.star_smul_prof, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    ‖Λ‖ (fun f => by
      show ‖(starRingEnd ℂ) (Λ (star f))‖ ≤ ‖Λ‖ * ‖f‖
      rw [RCLike.norm_conj]
      calc ‖Λ (star f)‖ ≤ ‖Λ‖ * ‖star f‖ := Λ.le_opNorm _
        _ = ‖Λ‖ * ‖f‖ := by rw [norm_star_prof])

theorem starFunctional_apply {M : ℝ} (Λ : Planar.ProfL2 M →L[ℂ] ℂ) (f : Planar.ProfL2 M) :
    starFunctional Λ f = (starRingEnd ℂ) (Λ (star f)) := rfl

theorem angPhase_neg_two (y : ℂ) (hy : y ≠ 0) :
    Planar.NUE.Ang.angPhase (-2) y = (starRingEnd ℂ) (Planar.NUE.Ang.angPhase 2 y) := by
  unfold Planar.NUE.Ang.angPhase
  set u : ℂ := y / (‖y‖ : ℂ) with hu
  have hn : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hy)]
  have h1 : (starRingEnd ℂ) u * u = 1 := by
    rw [Complex.conj_mul', hn]; simp
  have h2 : u ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn
  have h3 : (starRingEnd ℂ) u = u⁻¹ := by
    field_simp
    simpa [mul_comm] using h1
  rw [map_zpow₀, h3]
  simp [zpow_neg]

theorem ofProfile_two_conj (h : ℝ → ℂ) :
    (fun y => Planar.NUE.Ang.ofProfile (-2) (fun r => (starRingEnd ℂ) (h r)) y) =ᵐ[volume]
      fun y => (starRingEnd ℂ) (Planar.NUE.Ang.ofProfile 2 h y) := by
  have hy : ∀ᵐ y : ℂ ∂volume, y ≠ 0 := Planar.NUE.Ang.SectorL2Aux.ae_ne_zero
  filter_upwards [hy] with y hy
  simp only [Planar.NUE.Ang.ofProfile, map_mul]
  rw [angPhase_neg_two y hy]

/-! ### The assembly -/

theorem seedGrowProjAgree_of (h2 : SeedDualBounded) (h3 : XgEmbDense) : SeedGrowProjAgree := by
  intro lam h hh ℓ hs M hM
  set q : B0010.XG := hh.toLp h with hq
  set e := xgEmbM hM with he
  have heL : ∀ f, e (Planar.L0 f) = Planar.Lsec hM 2 (e f) := fun f => xgEmbM_L0 hM f
  set q' : Planar.ProfL2 M := e q with hq'def
  have hq'0 : q' ≠ 0 := fun h0 => hs.ne_zero (xgEmbM_injective hM h0)
  have hq' : Planar.Lsec hM 2 q' = lam • q' := by
    rw [hq'def, ← heL, hs.eigen, map_smul]
  refine ⟨q', hq'0, hq', ?_⟩
  intro ℓ₂ ℓm h2q hmq hP2 hPm f F hF
  obtain ⟨Λ, hΛ⟩ := h2 lam h hh ℓ hs M hM
  have hSF := seedFunctional_proof lam h hh ℓ hs
  have hΛe : ∀ f, Λ (e f) = ℓ f := by
    intro f
    rw [hΛ, hSF.2.2.2.1 f]
    exact seedEll_congr_prof M (coeFn_xgEmbM hM f)
  have hℓL : ∀ f, ℓ (Planar.L0 f) = lam * ℓ f :=
    eigenfunctional_of_rankOne hs.ne_zero hs.proj.proj_mul
  have hΛL : ∀ f, Λ (Planar.Lsec hM 2 f) = lam * Λ f := by
    have hF1 : ⇑(Λ.comp (Planar.Lsec hM 2)) = ⇑(lam • Λ) := by
      refine DenseRange.equalizer (h3 M hM) (Λ.comp (Planar.Lsec hM 2)).continuous
        (lam • Λ).continuous ?_
      funext f
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← heL, hΛe, hΛe, hℓL]
    intro f
    have := congrFun hF1 f
    simpa using this
  have hΛq : Λ q' = 1 := by rw [hq'def, hΛe, hs.ell_q]
  have hℓ₂ : ∀ x, ℓ₂ x = Λ x := by
    intro x
    have := ExternalInputs.apply_eq_apply_proj hP2 hΛL x
    rw [this, Infra.Dunford.rankOneProj_apply, map_smul, hΛq, smul_eq_mul, mul_one]
  -- sector `-2`
  have hΛmL : ∀ f, starFunctional Λ (Planar.Lsec hM (-2) f) =
      (starRingEnd ℂ) lam * starFunctional Λ f := by
    intro f
    have h1 := Planar.Lsec_star hM 2 (star f)
    rw [star_star] at h1
    have h2' : star (Planar.Lsec hM (-2) f) = Planar.Lsec hM 2 (star f) := by
      rw [h1, star_star]
    rw [starFunctional_apply, starFunctional_apply, h2', hΛL, map_mul]
  have hΛmq : starFunctional Λ (star q') = 1 := by
    rw [starFunctional_apply, star_star, hΛq, map_one]
  have hℓm : ∀ x, ℓm x = starFunctional Λ x := by
    intro x
    have := ExternalInputs.apply_eq_apply_proj hPm hΛmL x
    rw [this, Infra.Dunford.rankOneProj_apply, map_smul, hΛmq, smul_eq_mul, mul_one]
  -- the formula for the growing projection
  have hform : (((Planar.growingProj hM (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) f :
      Planar.X0 hM) : Planar.L2w M)) =
      ℓ₂ (Planar.secProf M 2 (f : Planar.L2w M)) • Planar.secEmb M 2 q' +
        ℓm (Planar.secProf M (-2) (f : Planar.L2w M)) • Planar.secEmb M (-2) (star q') :=
    Planar.growingProjW_rankOne_apply ℓ₂ ℓm q' (star q') (f : Planar.L2w M)
  -- profile identifications
  have hqh : ⇑q' =ᵐ[Planar.profileMeasure M] h := by
    have h1 := coeFn_xgEmbM hM q
    have h2' : ⇑q =ᵐ[B0010.xGMeasure] h := hh.coeFn_toLp
    filter_upwards [h1, (profileMeasure_ac_xGMeasure (xgEmbM_nonneg hM)).ae_le h2'] with r a b
    rw [hq'def, a, b]
  have hP1 : Planar.NUE.Ang.ofProfile 2 (⇑q') =ᵐ[volume] seedPlanar h :=
    Planar.ofProfile_congr_ae 2 ((Planar.ac_profileMeasure M).ae_le hqh)
  have hstar : ⇑(star q') =ᵐ[Planar.profileMeasure M] fun r => (starRingEnd ℂ) (h r) := by
    filter_upwards [Planar.coeFn_star_prof q', hqh] with r a b
    rw [a, b]
  have hP2' : Planar.NUE.Ang.ofProfile (-2) (⇑(star q')) =ᵐ[volume]
      Planar.NUE.Ang.ofProfile (-2) (fun r => (starRingEnd ℂ) (h r)) :=
    Planar.ofProfile_congr_ae (-2) ((Planar.ac_profileMeasure M).ae_le hstar)
  -- sector values
  have hFae : (⇑(f : Planar.L2w M) : ℂ → ℂ) =ᵐ[volume] F := hF
  have hsec := Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hFae
  have hv2 : ℓ₂ (Planar.secProf M 2 (f : Planar.L2w M)) =
      seedEll h (Planar.NUE.Polar.angularSector F 2) := by
    rw [hℓ₂, hΛ]
    refine (seedEll_congr_prof M (coeFn_secProf M 2 _)).trans (seedEll_congr ?_)
    filter_upwards [hsec] with r hr
    exact hr 2
  have hvm : ℓm (Planar.secProf M (-2) (f : Planar.L2w M)) =
      (starRingEnd ℂ) (seedEll h
        (fun r => (starRingEnd ℂ) (Planar.NUE.Polar.angularSector F (-2) r))) := by
    rw [hℓm, starFunctional_apply, hΛ]
    congr 1
    refine (seedEll_congr_prof M (Planar.coeFn_star_prof _)).trans (seedEll_congr ?_)
    have h3' := (Planar.ac_profileMeasure M).ae_le (coeFn_secProf M (-2) (f : Planar.L2w M))
    filter_upwards [h3', hsec] with r a b
    rw [a, b (-2)]
  -- assemble
  have hwae : ⇑(((Planar.growingProj hM (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) f :
      Planar.X0 hM) : Planar.L2w M)) =ᵐ[volume] fun y =>
      ℓ₂ (Planar.secProf M 2 (f : Planar.L2w M)) * Planar.NUE.Ang.ofProfile 2 (⇑q') y +
        ℓm (Planar.secProf M (-2) (f : Planar.L2w M)) *
          Planar.NUE.Ang.ofProfile (-2) (⇑(star q')) y := by
    rw [hform]
    refine (Planar.volume_ac M).ae_le ?_
    filter_upwards [Lp.coeFn_add (ℓ₂ (Planar.secProf M 2 (f : Planar.L2w M)) •
        Planar.secEmb M 2 q') (ℓm (Planar.secProf M (-2) (f : Planar.L2w M)) •
        Planar.secEmb M (-2) (star q')),
      Lp.coeFn_smul (ℓ₂ (Planar.secProf M 2 (f : Planar.L2w M))) (Planar.secEmb M 2 q'),
      Lp.coeFn_smul (ℓm (Planar.secProf M (-2) (f : Planar.L2w M))) (Planar.secEmb M (-2) (star q')),
      Planar.coeFn_secEmb M 2 q', Planar.coeFn_secEmb M (-2) (star q')] with y a b c d g
    rw [a, Pi.add_apply, b, c, Pi.smul_apply, Pi.smul_apply, d, g, smul_eq_mul, smul_eq_mul]
  filter_upwards [hwae, hP1, hP2', ofProfile_two_conj h] with y a b c d
  rw [a, hv2, hvm, seedProjFun, b, c, d]

end UnforcedLeray.Short.PartI
