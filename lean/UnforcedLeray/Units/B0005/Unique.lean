import UnforcedLeray.Units.B0005.Spaces
import UnforcedLeray.Lib.PhaseTrace.ChartTest

/-!
# B0005, part 3: phase tests separate `𝒴_q`; `𝒱_q` as a space of fields

Blueprint unit B0005, `paper/main.tex` lines 141–145. The graph norm
`‖f‖ + ‖hΔf‖ + ‖𝒯₀f‖` of `𝒱_q` is a function of `f` only because a distribution in `𝒴_q` is
determined by its pairings with phase tests. This file proves that (`eq_zero_of_phasePair`,
`HasPhaseOp.unique`) for every `1 ≤ q ≤ ∞`, so the graph triple `(f, hΔf, 𝒯₀f)` is determined
by `f` (`V_ext`), and defines `𝒱_q` as a subspace of `𝒴_q` (`Vq`) with its graph norm
(`graphNormV`) and the linear isomorphism with the closed graph (`graphEquiv`).

**Proof of separation.** Let `⟪Φ, g⟫ = 0` for all phase tests and `g̃(t) = g(t mod 𝒯)`. For
a time test `θ`, a spatial test `ψ` and `e ∈ ℂ³`, the periodization of `θ(t) ψ(y) e` is a phase
test, and the unfolding `PhaseTrace.phasePair_perT` gives `∫ θ(t) ⟨ψ e, g̃(t)⟩ dt = 0`. The
functionals `⟨ψ e, ·⟩` are continuous and separate `L^q(ℝ³; ℂ³)` (`PhaseTrace.exists_ell`,
`PhaseTrace.eq_zero_of_ell`), so the Bochner integral `∫ θ g̃ dt ∈ L^q` vanishes; by
Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `g̃ = 0` a.e. on `ℝ`, hence `g = 0`.

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

section Separation

/-- The product test `θ(τ) ψ(y) e`. -/
def prodTest (θ : ℝ → ℝ) (ψ : Space → ℝ) (e : CVec3) : ℝ × Space → CVec3 :=
  fun p => (θ p.1 * ψ p.2) • e

theorem exists_bound_of_hasCompactSupport {ψ : Space → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ R, ∀ y, R < ‖y‖ → ψ y = 0 := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun y hy => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

theorem exists_Icc_of_hasCompactSupport {θ : ℝ → ℝ} (hθc : HasCompactSupport θ) :
    ∃ A B, A ≤ B ∧ ∀ t, t ∉ Icc A B → θ t = 0 := by
  obtain ⟨R, hR⟩ := hθc.isCompact.isBounded.subset_closedBall 0
  refine ⟨-|R|, |R|, by linarith [abs_nonneg R], fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem => ht ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have h2 := le_abs_self R
  exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

theorem isPhaseTest_prodTest {θ : ℝ → ℝ} {ψ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    IsPhaseTest 0 (prodTest θ ψ e) where
  smooth := ((hθ.comp contDiff_fst).mul (hψ.comp contDiff_snd)).smul contDiff_const
  periodic := fun τ y => by simp [prodTest]
  bounded_support := by
    obtain ⟨R, hR⟩ := exists_bound_of_hasCompactSupport hψc
    exact ⟨R, fun τ y hy => by simp [prodTest, hR y hy]⟩

theorem timeSupp_prodTest {θ : ℝ → ℝ} {A B : ℝ} (hθ : ∀ t, t ∉ Icc A B → θ t = 0)
    (ψ : Space → ℝ) (e : CVec3) : TimeSupp A B (prodTest θ ψ e) := by
  intro τ y hτ
  simp [prodTest, hθ τ hτ]

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem pairH_prodTest {θ : ℝ → ℝ} {ψ : Space → ℝ} {e : CVec3}
    (hG0 : IsPhaseTest 0 (prodTest θ ψ e)) (g : Yq P q) (t : ℝ) :
    pairH hG0 g t =
      θ t • ∫ y, ψ y • dotL e ((g (t : AddCircle P) : Space → CVec3) y) := by
  rw [pairH_eq, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [prodTest]
  rw [ContinuousLinearMap.map_smul_of_tower, FunLike.coe_smul, Pi.smul_apply, mul_smul]

theorem locallyIntegrable_comp_mk (g : Yq P q) :
    LocallyIntegrable (fun t : ℝ => g (t : AddCircle P)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine IntegrableOn.mono_set ?_ (hR.trans (Metric.closedBall_subset_ball
    (lt_add_one R)))
  rw [Real.ball_eq_Ioo]
  exact integrableOn_comp_mk g

/-- **Phase tests separate points of `𝒴_q`** (`1 ≤ q ≤ ∞`). -/
theorem eq_zero_of_phasePair {g : Yq P q}
    (h : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → phasePair P q Φ g = 0) : g = 0 := by
  set gt : ℝ → Lp CVec3 q (volume : Measure Space) := fun t => g (t : AddCircle P) with hgt
  have hloc : LocallyIntegrable gt volume := locallyIntegrable_comp_mk g
  -- Step 1: every `∫ θ g̃` vanishes.
  have hI : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∫ t, θ t • gt t = 0 := by
    intro θ hθ hθc
    have hint : Integrable (fun t => θ t • gt t) :=
      hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
    obtain ⟨A, B, hAB, hθAB⟩ := exists_Icc_of_hasCompactSupport hθc
    refine eq_zero_of_ell _ fun ψ hψ hψc e => ?_
    obtain ⟨L, hL⟩ := exists_ell (q := q) hψ.continuous hψc e
    have hG0 := isPhaseTest_prodTest hθ hψ hψc e
    have hper := phasePair_perT hG0 hAB (timeSupp_prodTest hθAB ψ e) g
    rw [h _ (isPhaseTest_perT hP.out (timeSupp_prodTest hθAB ψ e) hG0)] at hper
    have hpair : ∫ t, pairH hG0 g t = 0 := by
      have hPinv : (P⁻¹ : ℂ) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hP.out.ne')
      have h0 := hper.symm
      rw [show (P⁻¹ : ℝ) • ∫ t, pairH hG0 g t = ((P⁻¹ : ℂ)) * ∫ t, pairH hG0 g t by
        rw [Complex.real_smul]; push_cast; ring] at h0
      exact (mul_eq_zero.mp h0).resolve_left hPinv
    rw [← hL, ← L.integral_comp_comm hint]
    simp_rw [L.map_smul, hL]
    rw [← hpair]
    exact integral_congr_ae (Eventually.of_forall fun t => (pairH_prodTest hG0 g t).symm)
  -- Step 2: `g̃ = 0` a.e. on `ℝ`.
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ), gt t = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hI
  -- Step 3: back to the circle.
  rw [Lp.eq_zero_iff_ae_eq_zero]
  set gm := (Lp.aestronglyMeasurable g).mk _ with hgm_def
  have hgm : (g : AddCircle P → Lp CVec3 q volume) =ᵐ[AddCircle.haarAddCircle] gm :=
    (Lp.aestronglyMeasurable g).ae_eq_mk
  have hsm : StronglyMeasurable gm := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk
  have hmp := measurePreserving_phase P
  have hac : ((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)) ≪ (volume : Measure ℝ) :=
    (Measure.smul_absolutelyContinuous).trans Measure.restrict_le_self.absolutelyContinuous
  have h1 : ∀ᵐ t ∂((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)), gm (phase P t) = 0 := by
    filter_upwards [hac.ae_le hzero, hmp.quasiMeasurePreserving.ae_eq_comp hgm] with t ht ht'
    exact (show gm (phase P t) = g (phase P t) from ht'.symm).trans ht
  have h2 : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), gm τ = 0 := by
    rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable
      (hsm.measurableSet_eq_fun stronglyMeasurable_const)]
    exact h1
  filter_upwards [hgm, h2] with τ hτ hτ'
  rw [hτ, hτ']
  rfl

/-- **Uniqueness of distributional images in `𝒴_q`**: `L f = g` and `L f = g'` in
distributions force `g = g'`. -/
theorem HasPhaseOp.unique {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3} {f g g' : Yq P q}
    (h : HasPhaseOp Lt f g) (h' : HasPhaseOp Lt f g') : g = g' :=
  sub_eq_zero.mp (eq_zero_of_phasePair fun Φ hΦ => by
    rw [map_sub, ← h Φ hΦ, ← h' Φ hΦ, sub_self])

end Separation

/-! ### `𝒱_q` as a space of fields with its graph norm -/

section Vq

variable {𝒯 : ℝ} [Fact (0 < 𝒯)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The graph triple is determined by its first entry. -/
theorem V_ext {h : ℝ} {x y : Y 𝒯 q × Y 𝒯 q × Y 𝒯 q} (hx : x ∈ V 𝒯 q h) (hy : y ∈ V 𝒯 q h)
    (hxy : x.1 = y.1) : x = y := by
  obtain ⟨f, a, b⟩ := x
  obtain ⟨f', a', b'⟩ := y
  simp only at hxy
  subst hxy
  rw [mem_V_iff] at hx hy
  rw [HasPhaseOp.unique hx.2.1 hy.2.1, HasPhaseOp.unique hx.2.2 hy.2.2]

variable (𝒯 q) in
/-- The first projection `𝒱_q → 𝒴_q`, `(f, hΔf, 𝒯₀f) ↦ f`. -/
def graphFst (h : ℝ) : V 𝒯 q h →ₗ[ℂ] Y 𝒯 q :=
  (LinearMap.fst ℂ (Y 𝒯 q) (Y 𝒯 q × Y 𝒯 q)).comp (V 𝒯 q h).subtype

theorem graphFst_injective (h : ℝ) : Function.Injective (graphFst 𝒯 q h) :=
  fun x y hxy => Subtype.ext (V_ext x.2 y.2 hxy)

variable (𝒯 q) in
/-- **`𝒱_q = {f ∈ 𝒴_{q,div} : hΔf, 𝒯₀f ∈ 𝒴_q}`** (tex 141–142) as a subspace of `𝒴_q`. -/
def Vq (h : ℝ) : Submodule ℂ (Y 𝒯 q) := LinearMap.range (graphFst 𝒯 q h)

theorem mem_Vq_iff {h : ℝ} {f : Y 𝒯 q} :
    f ∈ Vq 𝒯 q h ↔ f ∈ Ydiv 𝒯 q ∧ (∃ a, HasHLap h f a) ∧ ∃ b, HasT0 f b := by
  constructor
  · rintro ⟨⟨⟨f', a, b⟩, hx⟩, rfl⟩
    have := mem_V_iff.mp hx
    exact ⟨this.1, ⟨a, this.2.1⟩, ⟨b, this.2.2⟩⟩
  · rintro ⟨hf, ⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨(f, a, b), mem_V_iff.mpr ⟨hf, ha, hb⟩⟩, rfl⟩

variable (𝒯 q) in
/-- The linear isomorphism of the closed graph with `𝒱_q`. -/
def graphEquiv (h : ℝ) : V 𝒯 q h ≃ₗ[ℂ] Vq 𝒯 q h :=
  LinearEquiv.ofInjective (graphFst 𝒯 q h) (graphFst_injective h)

/-- The graph triple `(f, hΔf, 𝒯₀f)` of `f ∈ 𝒱_q`. -/
def graphOf {h : ℝ} (f : Vq 𝒯 q h) : Y 𝒯 q × Y 𝒯 q × Y 𝒯 q :=
  ((graphEquiv 𝒯 q h).symm f : Y 𝒯 q × Y 𝒯 q × Y 𝒯 q)

/-- `hΔf ∈ 𝒴_q` for `f ∈ 𝒱_q`. -/
def hLapOf {h : ℝ} (f : Vq 𝒯 q h) : Y 𝒯 q := (graphOf f).2.1

/-- `𝒯₀f ∈ 𝒴_q` for `f ∈ 𝒱_q`. -/
def T0Of {h : ℝ} (f : Vq 𝒯 q h) : Y 𝒯 q := (graphOf f).2.2

theorem graphOf_mem {h : ℝ} (f : Vq 𝒯 q h) : graphOf f ∈ V 𝒯 q h :=
  ((graphEquiv 𝒯 q h).symm f).2

theorem graphOf_fst {h : ℝ} (f : Vq 𝒯 q h) : (graphOf f).1 = (f : Y 𝒯 q) := by
  have h2 : (graphEquiv 𝒯 q h) ((graphEquiv 𝒯 q h).symm f) = f :=
    (graphEquiv 𝒯 q h).apply_symm_apply f
  have h1 : (((graphEquiv 𝒯 q h) ((graphEquiv 𝒯 q h).symm f) : Vq 𝒯 q h) : Y 𝒯 q) =
      graphFst 𝒯 q h ((graphEquiv 𝒯 q h).symm f) :=
    LinearEquiv.ofInjective_apply _ _
  rw [h2] at h1
  exact h1.symm

theorem graphOf_eq {h : ℝ} (f : Vq 𝒯 q h) :
    graphOf f = ((f : Y 𝒯 q), hLapOf f, T0Of f) := by
  exact Prod.ext (graphOf_fst f) (Prod.ext rfl rfl)

/-- `hΔf = hLapOf f` and `𝒯₀ f = T0Of f` in distributions, and `div f = 0`. -/
theorem mem_V_graphOf {h : ℝ} (f : Vq 𝒯 q h) :
    (f : Y 𝒯 q) ∈ Ydiv 𝒯 q ∧ HasHLap h (f : Y 𝒯 q) (hLapOf f) ∧ HasT0 (f : Y 𝒯 q) (T0Of f) := by
  have := graphOf_mem f
  rw [graphOf_eq] at this
  exact mem_V_iff.mp this

theorem hLapOf_eq {h : ℝ} (f : Vq 𝒯 q h) {a : Y 𝒯 q} (ha : HasHLap h (f : Y 𝒯 q) a) :
    hLapOf f = a :=
  HasPhaseOp.unique (mem_V_graphOf f).2.1 ha

theorem T0Of_eq {h : ℝ} (f : Vq 𝒯 q h) {b : Y 𝒯 q} (hb : HasT0 (f : Y 𝒯 q) b) : T0Of f = b :=
  HasPhaseOp.unique (mem_V_graphOf f).2.2 hb

/-- **The graph norm of `𝒱_q`** (tex 144): `‖f‖ + ‖hΔf‖ + ‖𝒯₀f‖`. -/
def graphNormV {h : ℝ} (f : Vq 𝒯 q h) : ℝ := ‖(f : Y 𝒯 q)‖ + ‖hLapOf f‖ + ‖T0Of f‖

theorem graphNormV_eq {h : ℝ} (f : Vq 𝒯 q h) : graphNormV f = graphNorm (graphOf f) := by
  rw [graphOf_eq]
  rfl

/-- The graph norm is equivalent to the norm of the closed graph `𝒱_q ⊂ 𝒴_q³` (a Banach
space), through `graphEquiv`. -/
theorem graphNormV_equiv {h : ℝ} (f : Vq 𝒯 q h) :
    ‖(graphEquiv 𝒯 q h).symm f‖ ≤ graphNormV f ∧
      graphNormV f ≤ 3 * ‖(graphEquiv 𝒯 q h).symm f‖ := by
  rw [graphNormV_eq]
  exact graphNorm_equiv _

end Vq

end UnforcedLeray.B0005
