import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_3
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Part II-b, task `PartII-b:G4/3/1/2` (`RawGoodAll`)

Source of record: `the November 2 reference manuscript`, lines 1206-1216, 1292,
2042-2046.  With `ν₀ = 1`: off the axis `p.raw τ` is the ring lift `Nv R (rawProfile ..)`, and for
`s > 0` the raw profile is the profile `merProfile R ψ̃` of the stream `ψ̃` of the train
(`rawProfile_eq_merProfile_of_smooth`), which is `C^∞` on `s > 0` because `ψ̃` is
(`BgRegime.train_stream_smooth`) and `merProfile` is built from its first derivatives.  So
`(τ, y) ↦ p.raw τ y` is `C^∞` on the open set `y ∉ axis`; periodicity off the axis is
`Nv_add_period_of_not_mem_axis`, on the axis it follows because `axisExt` only sees the values off
the axis; solenoidality off the axis is `offAxis_divFree`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0184 UnforcedLeray.B0185
  UnforcedLeray.B0190

/-- `C^∞` smoothness of the train stream profile on the age domain. -/
theorem trainStream_contDiffOn_top {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp) :
    ContDiffOn ℝ ∞ (trainStream p) ageDomain := by
  have h := hb.train_stream_smooth
  have hc : ContDiffOn ℝ ∞
      ((fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ x.1 x.2) ∘
        fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) ageDomain := by
    refine h.comp (by fun_prop : ContDiff ℝ ∞ fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))).contDiffOn ?_
    intro x hx
    exact ⟨hx, trivial⟩
  exact hc

/-- The profile `merProfile R ψ̃` is `C^∞` on `s > 0` when `ψ̃` is `C^∞` on the age domain. -/
theorem contDiffOn_merProfile {R : ℝ} {ψ : ProfilePoint → ℝ} (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (merProfile R ψ) (Ioi (0 : ℝ) ×ˢ univ) := by
  have hF : ContDiffOn ℝ ∞ (fun y => fderiv ℝ ψ y) ageDomain :=
    hψ.fderiv_of_isOpen isOpen_ageDomain (by simp)
  set g : ℝ × (ℝ × ℝ) → ProfilePoint := fun x => (x.2.1, (x.2.2, x.1)) with hg
  have hgc : ContDiff ℝ ∞ g := by rw [hg]; fun_prop
  have hmaps : MapsTo g (Ioi (0 : ℝ) ×ˢ univ) ageDomain := fun x hx => hx.1
  have hFg : ContDiffOn ℝ ∞ (fun x => fderiv ℝ ψ (g x)) (Ioi (0 : ℝ) ×ˢ univ) :=
    hF.comp hgc.contDiffOn hmaps
  have hψg : ContDiffOn ℝ ∞ (fun x => ψ (g x)) (Ioi (0 : ℝ) ×ˢ univ) :=
    hψ.comp hgc.contDiffOn hmaps
  have hdir : ∀ v : ProfilePoint, ContDiffOn ℝ ∞ (fun x => fderiv ℝ ψ (g x) v)
      (Ioi (0 : ℝ) ×ˢ univ) := fun v => hFg.clm_apply contDiffOn_const
  have hV1 : ContDiffOn ℝ ∞ (fun x => streamV1 ψ (g x)) (Ioi (0 : ℝ) ×ˢ univ) :=
    (hdir eηDir).neg
  have hV2 : ContDiffOn ℝ ∞ (fun x => axialProfile R ψ (g x)) (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold axialProfile streamV2 ageDefect ageOperator partialQ partialEta partialAge
    refine (hdir eqDir).add (contDiffOn_const.mul (hψg.sub ?_))
    have e1 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.2) (Ioi (0 : ℝ) ×ˢ univ) :=
      (by fun_prop : ContDiff ℝ ∞ fun x : ℝ × (ℝ × ℝ) => x.2.2).contDiffOn
    have e2 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.1) (Ioi (0 : ℝ) ×ˢ univ) :=
      (by fun_prop : ContDiff ℝ ∞ fun x : ℝ × (ℝ × ℝ) => x.1).contDiffOn
    exact (e1.mul (hdir eηDir)).add ((contDiffOn_const.mul e2).mul (hdir esDir))
  have : merProfile R ψ = fun x => streamV1 ψ (g x) • UnforcedLeray.Axi.m0 +
      axialProfile R ψ (g x) • UnforcedLeray.Axi.m1 := rfl
  rw [this]
  exact (hV1.smul contDiffOn_const).add (hV2.smul contDiffOn_const)

/-- Joint smoothness of the ring lift `Nv` off the axis for a profile smooth only on `s > 0`. -/
theorem contDiffOn_Nv_pos {R : ℝ} (hR : R ≠ 0) {b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid}
    (hb : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2)
      {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} := by
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} with hW
  have hϱ : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.ϱ x.2) W :=
    UnforcedLeray.Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hϱ0 : ∀ x ∈ W, UnforcedLeray.Axi.ϱ x.2 ≠ 0 := fun x hx => UnforcedLeray.Axi.ϱ_ne_zero hx
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.age R x.2) W := by
    unfold UnforcedLeray.Axi.age
    exact contDiffOn_const.div (hϱ.pow 2) fun x hx => pow_ne_zero 2 (hϱ0 x hx)
  have hage0 : ∀ x ∈ W, UnforcedLeray.Axi.age R x.2 ≠ 0 := fun x hx =>
    (UnforcedLeray.Axi.age_pos hR hx).ne'
  have hphase : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.phase R x.1 x.2) W := by
    unfold UnforcedLeray.Axi.phase
    exact (contDiff_const.mul contDiff_fst).div_const 2 |>.contDiffOn.sub
      (contDiffOn_const.mul (hage.log hage0))
  have htrans : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.trans R x.2) W := by
    unfold UnforcedLeray.Axi.trans
    have h2 : ContDiff ℝ ∞ (fun x : ℝ × Space => x.2 2) := by fun_prop
    exact ((contDiff_const.mul h2).contDiffOn (s := W)).div hϱ hϱ0
  have hchart : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) W := by
    unfold UnforcedLeray.Axi.chart
    exact hage.prodMk (hphase.prodMk htrans)
  have hmaps : MapsTo (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) W
      (Ioi (0 : ℝ) ×ˢ univ) := fun x hx => ⟨UnforcedLeray.Axi.age_pos hR hx, trivial⟩
  have hbc : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2)) W :=
    hb.comp hchart hmaps
  have hb0 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2) 0) W :=
    (EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have hb1 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2) 1) W :=
    (EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have heR : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.eR x.2) W :=
    UnforcedLeray.Axi.contDiffOn_eR.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hsq : ContDiffOn ℝ ∞ (fun x : ℝ × Space => √(UnforcedLeray.Axi.age R x.2)) W :=
    hage.sqrt hage0
  have : (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2) = fun x =>
      √(UnforcedLeray.Axi.age R x.2) •
        (b (UnforcedLeray.Axi.chart R x.1 x.2) 0 • UnforcedLeray.Axi.eR x.2 +
          b (UnforcedLeray.Axi.chart R x.1 x.2) 1 • UnforcedLeray.Axi.e3) := by
    funext x
    simp [UnforcedLeray.Axi.Nv, UnforcedLeray.Axi.frameL_apply]
  rw [this]
  exact hsq.smul ((hb0.smul heR).add (hb1.smul contDiffOn_const))

/-- Off the axis, `p.raw τ y` is the ring lift of the `merProfile` of the train stream. -/
theorem raw_eq_Nv_mer {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp) (τ : ℝ) {y : Space}
    (hy : y ∉ Axi.axis) :
    p.raw τ y = Axi.Nv p.R (merProfile p.R (trainStream p)) τ y := by
  have hR : 0 < p.R := p.R_pos
  have hRε : p.ε = p.R⁻¹ := by
    show p.ε = (p.ε⁻¹)⁻¹
    exact (inv_inv _).symm
  rw [p.raw_eq_off_axis τ y hy]
  have hs : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hR.ne' hy
  have hprof := rawProfile_eq_merProfile_of_smooth UnforcedLeray.Short.PartI.trainStreamSmooth
    p.ν_pos p.c_pos p.train hb.train_buc hRε hs
  change Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y =
    Axi.Nv p.R (merProfile p.R (trainStream p)) τ y
  unfold Axi.Nv
  rw [hprof]
  rfl

theorem raw_periodic_off {p : Params} (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    p.raw (τ + p.period) y = p.raw τ y := by
  rw [p.raw_eq_off_axis _ y hy, p.raw_eq_off_axis _ y hy]
  refine Cons.C03.Nv_add_period_of_not_mem_axis (c := p.c) p.R_pos.ne' ?_ ?_ τ hy
  · show 2 * p.ε * p.c = 2 * p.c / p.ε⁻¹
    field_simp
  · intro s hs ξ η
    exact Cons.C03.rawProfile_periodic p.train hs ξ η

theorem rawGoodAll : UnforcedLeray.Short.IIb.RawGoodAll := by
  intro Sig lam q hSig hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg _ _ _
  refine ⟨?_, ?_, ?_⟩
  · have hN : ContDiffOn ℝ ∞ (fun x : ℝ × Space =>
        Axi.Nv p.R (merProfile p.R (trainStream p)) x.1 x.2) {x | x.2 ∉ Axi.axis} :=
      contDiffOn_Nv_pos p.R_pos.ne'
        (contDiffOn_merProfile (trainStream_contDiffOn_top hreg))
    exact hN.congr fun x hx => raw_eq_Nv_mer hreg x.1 hx
  · intro τ y
    by_cases hy : y ∈ Axi.axis
    · have hev : (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
          (τ + p.period)) =ᶠ[𝓝[Axi.axisᶜ] y]
          (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        have h1 := raw_periodic_off (p := p) τ hz
        rwa [p.raw_eq_off_axis _ z hz, p.raw_eq_off_axis _ z hz] at h1
      show UnforcedLeray.Cons.C03.Concrete.axisExt _ y = UnforcedLeray.Cons.C03.Concrete.axisExt _ y
      unfold UnforcedLeray.Cons.C03.Concrete.axisExt
      simp only [hy, ↓reduceIte]
      simp only [limUnder]
      rw [Filter.map_congr hev]
    · exact raw_periodic_off τ hy
  · intro τ y hy
    exact offAxis_divFree hreg τ hy

end UnforcedLeray.Short.IIb
