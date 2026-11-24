import UnforcedLeray.Units.B0449.GraphTime

/-!
# B0449 spatial graph equation as a space-time distribution

The a.e.-time B0447 slice identity permits time-dependent spatial tests because its null set is
uniform over all spatial tests. Fubini then gives the space-time distribution identity for every
test with smooth compactly supported spatial slices, provided the tested chart fields are
integrable. The cutoff package supplies those local integrability bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The graph Laplacian equation for `chartJ`, tested against arbitrary space-time scalar tests
with smooth compactly supported spatial slices. The hypothesis `hq1` supplies the B0447 slice
identity and can later be combined with local chart integrability for cutoff tests. -/
theorem chartJ_spaceTime_laplacian {ν : ℝ} (hν : 0 < ν) (hq1 : 1 < q)
    {w a : Yq P q} (h : HasPhaseOp (nuLapT ν) w a) (τ₀ : ℝ)
    {θ : ℝ × Space → ℝ}
    (hθsmooth : ∀ t, ContDiff ℝ ∞ (fun z => θ (t, z)))
    (hθsupp : ∀ t, HasCompactSupport (fun z => θ (t, z)))
    (e : CVec3)
    (hL : Integrable (fun p : ℝ × Space =>
      Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p)) volume)
    (hR : Integrable (fun p : ℝ × Space =>
      (Real.exp (-p.1) : ℂ) * (θ p : ℂ) * dotL e (chartJ a ν τ₀ p)) volume) :
    ∫ p : ℝ × Space,
      Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p) =
    ∫ p : ℝ × Space,
      (Real.exp (-p.1) : ℂ) * (θ p : ℂ) * dotL e (chartJ a ν τ₀ p) := by
  have hLprod : Integrable
      (fun p : ℝ × Space =>
        Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact hL
  have hRprod : Integrable
      (fun p : ℝ × Space =>
        (Real.exp (-p.1) : ℂ) * (θ p : ℂ) * dotL e (chartJ a ν τ₀ p))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact hR
  have hslice := B0447.chart_laplacian hν hq1 h τ₀ (0 : Space)
  have hinner : ∀ᵐ t ∂(volume : Measure ℝ),
      (∫ z, Heat.laplacian (fun z => θ (t, z)) z • dotL e (chartJ w ν τ₀ (t, z))) =
      ∫ z, (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
        dotL e (chartJ a ν τ₀ (t, z)) := by
    filter_upwards [hslice] with t ht
    have hW : (fun z => Heat.laplacian (fun z => θ (t, z)) z •
        dotL e (chartJ w ν τ₀ (t, z))) =ᵐ[volume]
        (fun z => Heat.laplacian (fun z => θ (t, z)) z •
          dotL e (chartPullback w ν τ₀ 0 t z)) := by
      filter_upwards [chartJ_slice hν w τ₀ t] with z hz
      rw [hz]
    have hA : (fun z => (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
        dotL e (chartJ a ν τ₀ (t, z))) =ᵐ[volume]
        (fun z => (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
          dotL e (chartPullback a ν τ₀ 0 t z)) := by
      filter_upwards [chartJ_slice hν a τ₀ t] with z hz
      rw [hz]
    have hwi := integral_congr_ae hW
    have hai := integral_congr_ae hA
    have hs := ht (fun z => θ (t, z)) (hθsmooth t) (hθsupp t) e
    calc
      ∫ z, Heat.laplacian (fun z => θ (t, z)) z •
          dotL e (chartJ w ν τ₀ (t, z)) =
          ∫ z, Heat.laplacian (fun z => θ (t, z)) z •
            dotL e (chartPullback w ν τ₀ 0 t z) := hwi
      _ = (Real.exp (-t) : ℂ) *
          ∫ z, (θ (t, z) : ℂ) * dotL e (chartPullback a ν τ₀ 0 t z) := by
            simpa only [Complex.real_smul] using hs
      _ = ∫ z, (Real.exp (-t) : ℂ) *
          ((θ (t, z) : ℂ) * dotL e (chartPullback a ν τ₀ 0 t z)) := by
            rw [← integral_const_mul]
      _ = ∫ z, (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
          dotL e (chartPullback a ν τ₀ 0 t z) := by
            congr 1
            funext z
            ring
      _ = ∫ z, (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
          dotL e (chartJ a ν τ₀ (t, z)) := hai.symm
  have hleft :
      ∫ p : ℝ × Space,
        Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p) =
      ∫ t, ∫ z, Heat.laplacian (fun z => θ (t, z)) z •
        dotL e (chartJ w ν τ₀ (t, z)) := by
    rw [Measure.volume_eq_prod, integral_prod _ hLprod]
  have hright :
      ∫ p : ℝ × Space,
        (Real.exp (-p.1) : ℂ) * (θ p : ℂ) * dotL e (chartJ a ν τ₀ p) =
      ∫ t, ∫ z, (Real.exp (-t) : ℂ) * (θ (t, z) : ℂ) *
        dotL e (chartJ a ν τ₀ (t, z)) := by
    rw [Measure.volume_eq_prod, integral_prod _ hRprod]
  rw [hleft, hright]
  exact integral_congr_ae hinner



/-- A bounded compact-cylinder scalar multiplier times a scalar projection of the joint chart is
locally integrable. The proof uses the B0449 slice representative and the Bochner `L¹_t L^q_z`
estimate. -/
theorem integrable_scalar_mul_chartJ {ν : ℝ} (hν : 0 < ν)
    (f : Yq P q) (τ₀ : ℝ) (e : CVec3) {g : ℝ × Space → ℂ} {a b M R : ℝ}
    (hJ : MeasurableSet (Icc a b)) (hpath : IntegrableOn (B0447.chartLp f ν τ₀ 0) (Icc a b))
    (hg : StronglyMeasurable g) (hM : 0 ≤ M)
    (hbound : ∀ t z, ‖g (t, z)‖ ≤ M * (Icc a b).indicator (fun _ => (1 : ℝ)) t * ballInd R z) :
    Integrable (fun p => g p * dotL e (chartJ f ν τ₀ p)) volume := by
  let L0 : CVec3 →L[ℝ] ℂ := (dotL e).restrictScalars ℝ
  let L : Lp CVec3 q (volume : Measure Space) →L[ℝ]
      Lp ℂ q (volume : Measure Space) := L0.compLpL q volume
  let u : ℝ → Lp ℂ q (volume : Measure Space) := fun t => L (B0447.chartLp f ν τ₀ 0 t)
  have hu : IntegrableOn u (Icc a b) := by
    simpa [IntegrableOn, u, L] using L.integrable_comp hpath
  have hU : StronglyMeasurable (fun p : ℝ × Space => dotL e (chartJ f ν τ₀ p)) :=
    (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ f ν τ₀)
  have hUu : ∀ t ∈ Icc a b,
      (fun z => dotL e (chartJ f ν τ₀ (t, z))) =ᵐ[volume] u t := by
    intro t ht
    have hJslice := chartJ_slice_lp hν f τ₀ t
    have hmap := L0.coeFn_compLpL (B0447.chartLp f ν τ₀ 0 t)
    have hslice : (fun z => dotL e (chartJ f ν τ₀ (t, z))) =ᵐ[volume]
        (fun z => L0 ((B0447.chartLp f ν τ₀ 0 t : Space → CVec3) z)) := by
      filter_upwards [hJslice] with z hz
      rw [hz]
      rfl
    simpa [u, L, L0] using hslice.trans hmap.symm
  exact integrable_mul_path hU hJ hu hUu hg hM hbound

/-- For any bounded interval, every chart slice has an integrable `L^q` path. -/
theorem integrableOn_chartLp {ν : ℝ} (hq : q ≠ ⊤)
    (f : Yq P q) (τ₀ : ℝ) (a b : ℝ) :
    IntegrableOn (B0447.chartLp f ν τ₀ 0) (Icc a b) := by
  have hcom := UnforcedLeray.PhaseTrace.integrableOn_comoving hq f τ₀ (a - 1) (b + 1)
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcom' := hcom.mono_set hsub
  have h' : IntegrableOn
      (fun t => B0447.affL ν (0 : Space) (comoving f τ₀ t)) (Icc a b) :=
    (B0447.affL ν (0 : Space)).integrable_comp hcom'
  change IntegrableOn (fun t => B0447.affL ν (0 : Space) (comoving f τ₀ t)) (Icc a b)
  simpa [B0447.chartLp] using h'


/-- The space-time Laplacian identity with integrability discharged by bounded compact-cylinder
bounds on the tested scalar multipliers. This is the form used for cut-off resolvent tests. -/
theorem chartJ_spaceTime_laplacian_of_bounds {ν : ℝ} (hν : 0 < ν) (hq : q ≠ ⊤)
    (hq1 : 1 < q) {w a : Yq P q} (h : HasPhaseOp (nuLapT ν) w a) (τ₀ : ℝ)
    {θ : ℝ × Space → ℝ}
    (hθsmooth : ∀ t, ContDiff ℝ ∞ (fun z => θ (t, z)))
    (hθsupp : ∀ t, HasCompactSupport (fun z => θ (t, z)))
    (e : CVec3) {a₀ b₀ M₁ M₂ R : ℝ}
    (hGL : StronglyMeasurable (fun p : ℝ × Space =>
      (Heat.laplacian (fun z => θ (p.1, z)) p.2 : ℂ)))
    (hGR : StronglyMeasurable (fun p : ℝ × Space =>
      (Real.exp (-p.1) : ℂ) * (θ p : ℂ)))
    (hGLbound : ∀ t z, ‖(Heat.laplacian (fun z => θ (t, z)) z : ℂ)‖ ≤
      M₁ * (Icc a₀ b₀).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hGRbound : ∀ t z, ‖(Real.exp (-t) : ℂ) * (θ (t, z) : ℂ)‖ ≤
      M₂ * (Icc a₀ b₀).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) :
    ∫ p : ℝ × Space,
      Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p) =
    ∫ p : ℝ × Space,
      (Real.exp (-p.1) : ℂ) * (θ p : ℂ) * dotL e (chartJ a ν τ₀ p) := by
  have hJ : MeasurableSet (Icc a₀ b₀) := measurableSet_Icc
  have hpathW := integrableOn_chartLp (ν := ν) (q := q) hq w τ₀ a₀ b₀
  have hpathA := integrableOn_chartLp (ν := ν) (q := q) hq a τ₀ a₀ b₀
  have hL := integrable_scalar_mul_chartJ hν w τ₀ e hJ hpathW hGL hM₁ hGLbound
  have hR := integrable_scalar_mul_chartJ hν a τ₀ e hJ hpathA hGR hM₂ hGRbound
  have hL' : Integrable (fun p : ℝ × Space =>
      Heat.laplacian (fun z => θ (p.1, z)) p.2 • dotL e (chartJ w ν τ₀ p)) volume := by
    simpa only [Complex.real_smul] using hL
  exact chartJ_spaceTime_laplacian hν hq1 h τ₀ hθsmooth hθsupp e hL' hR

set_option maxHeartbeats 1600000 in
/-- The temporal cutoff test inherits the two graph identities together. The temporal identity
uses the explicit product rule derivative, and the spatial identity uses the cutoff Laplacian. -/
theorem chartJ_cutoff_graph_identities {ν : ℝ} (hν : 0 < ν) (hq : q ≠ ⊤)
    (hq1 : 1 < q) {w a b : Yq P q}
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
    (τ₀ : ℝ) (e : CVec3) {χ χt : ℝ → ℝ} {φ φt : ℝ × Space → ℝ}
    (hθsmooth : ∀ t, ContDiff ℝ ∞ (fun z => χ t * φ (t, z)))
    (hθsupp : ∀ t, HasCompactSupport (fun z => χ t * φ (t, z)))
    (hθcont : Continuous (fun p : ℝ × Space => ((χ p.1 * φ p : ℝ) : ℂ)))
    (hθtcont : Continuous (fun p : ℝ × Space =>
      (((χt p.1 * φ p) + χ p.1 * φt p : ℝ) : ℂ)))
    (hθderiv : ∀ t z, HasDerivAt
      (fun s : ℝ => ((χ s * φ (s, z) : ℝ) : ℂ))
      ((((χt t * φ (t, z)) + χ t * φt (t, z) : ℝ) : ℂ)) t)
    {lo hi Mθ Mθt ML MR R : ℝ} (hlohi : lo ≤ hi)
    (hθbound : ∀ t z, ‖((χ t * φ (t, z) : ℝ) : ℂ)‖ ≤
      Mθ * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hθtbound : ∀ t z,
      ‖((((χt t * φ (t, z)) + χ t * φt (t, z) : ℝ) : ℂ))‖ ≤
        Mθt * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hGL : StronglyMeasurable (fun p : ℝ × Space =>
      (Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ)))
    (hGR : StronglyMeasurable (fun p : ℝ × Space =>
      (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ)))
    (hGLbound : ∀ t z, ‖(Heat.laplacian (fun z => χ t * φ (t, z)) z : ℂ)‖ ≤
      ML * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hGRbound : ∀ t z,
      ‖(Real.exp (-t) : ℂ) * ((χ t * φ (t, z) : ℝ) : ℂ)‖ ≤
      MR * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z)
    (hMθ : 0 ≤ Mθ) (hML : 0 ≤ ML) (hMR : 0 ≤ MR) :
    (∫ p : ℝ × Space,
      (((χt p.1 * φ p) + χ p.1 * φt p : ℝ) : ℂ) * dotL e (chartJ w ν τ₀ p) =
      -∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * dotL e (chartJ b ν τ₀ p)) ∧
    (∫ p : ℝ × Space,
      (Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ) •
        dotL e (chartJ w ν τ₀ p) =
      ∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) *
        dotL e (chartJ a ν τ₀ p)) := by
  let Mtime := max Mθ Mθt
  have hMtime : 0 ≤ Mtime := le_trans hMθ (le_max_left _ _)
  have hθbound' : ∀ t z, ‖((χ t * φ (t, z) : ℝ) : ℂ)‖ ≤
      Mtime * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    calc
      _ ≤ Mθ * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := hθbound t z
      _ ≤ Mtime * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (ind_nonneg _ _))
          (ballInd_nonneg _ _)
  have hθtbound' : ∀ t z,
      ‖((((χt t * φ (t, z)) + χ t * φt (t, z) : ℝ) : ℂ))‖ ≤
        Mtime * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    calc
      _ ≤ Mθt * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := hθtbound t z
      _ ≤ Mtime * (Icc lo hi).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (ind_nonneg _ _))
          (ballInd_nonneg _ _)
  constructor
  · exact chartJ_timeDerivative hν hq hTime τ₀ e
      (a₀ := lo - 1) (b₀ := hi + 1) (a' := lo) (b' := hi)
      hθcont hθtcont hθderiv (by linarith) hlohi (by linarith) hMtime
      hθbound' hθtbound'
  · have hspace := chartJ_spaceTime_laplacian_of_bounds hν hq hq1 hLap τ₀
      hθsmooth hθsupp e hGL hGR hGLbound hGRbound hML hMR
    exact hspace

/-- The iterated strip norm is exactly the product-space eLpNorm on the open unit strip.
This converts B0447's chart estimate into an Lq input for the compactly time-supported
resolvent argument. -/
theorem memLp_unitStrip_of_stripNorm {f : ℝ × Space → CVec3} (hq : q ≠ ⊤)
    (hf : StronglyMeasurable f)
    (hfin : stripNorm q (fun t z => f (t, z)) < ⊤) :
    MemLp f q (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
  let S : Set (ℝ × Space) := Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space)
  let μS : Measure (ℝ × Space) := volume.restrict S
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hμS : μS = ((volume : Measure ℝ).restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod (volume : Measure Space) := by
    dsimp [μS, S]
    rw [Measure.volume_eq_prod ℝ Space, ← Measure.prod_restrict, Measure.restrict_univ]
  have hnorm : eLpNorm f q μS = stripNorm q (fun t z => f (t, z)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
    rw [hμS]
    rw [lintegral_prod _ (hf.enorm.pow_const _).aemeasurable]
    rfl
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hnorm]
  exact hfin

/-- The joint representative on one unit strip has the same MemLp bound as its B0447 chart
pullback, since every time slice agrees a.e. in space. -/
theorem memLp_chartJ_unitStrip {ν : ℝ} (hν : 0 < ν) (hP1 : P ≤ 1) (hq : q ≠ ⊤)
    (f : Yq P q) (τ₀ : ℝ) :
    MemLp (chartJ f ν τ₀) q (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
  let W : ℝ → Space → CVec3 := fun t z => chartPullback f ν τ₀ 0 t z
  have hchart := PhaseSpace.chart_norm_le hP1 hν hq f f f τ₀ 0
  have hW : stripNorm q W ≤
      ENNReal.ofReal (Real.exp (1 / 2) * (2 * Real.exp (3 / 4)) ^
        (1 / q.toReal) * ν ^ (-(3 / (2 * q.toReal))) * (‖f‖ + ‖f‖ + ‖f‖)) := by
    have hfirst : stripNorm q W ≤
        stripNorm q (chartPullback f ν τ₀ 0) + stripNorm q (chartPullback f ν τ₀ 0) +
          stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback f ν τ₀ 0 t z) := by
      change stripNorm q (chartPullback f ν τ₀ 0) ≤ _ + _ + _
      have htail : 0 ≤ stripNorm q (chartPullback f ν τ₀ 0) +
          stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback f ν τ₀ 0 t z) :=
        add_nonneg (by positivity) (by positivity)
      simpa [add_assoc] using le_add_of_nonneg_right htail
    exact le_trans (by simpa [W] using hfirst) hchart
  have hslice : ∀ t, (fun z => chartJ f ν τ₀ (t, z)) =ᵐ[volume] W t := by
    intro t
    simpa [W] using chartJ_slice hν f τ₀ t
  have hEq : stripNorm q (fun t z => chartJ f ν τ₀ (t, z)) = stripNorm q W := by
    unfold PhaseSpace.stripNorm
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with t
    apply lintegral_congr_ae
    filter_upwards [hslice t] with z hz
    rw [hz]
  have hfinite : stripNorm q (fun t z => chartJ f ν τ₀ (t, z)) < ⊤ := by
    rw [hEq]
    exact lt_of_le_of_lt hW (ENNReal.ofReal_lt_top)
  exact memLp_unitStrip_of_stripNorm hq
    (stronglyMeasurable_chartJ f ν τ₀) hfinite

/-- Every scalar projection of a joint chart is Lq on the unit strip. -/
theorem memLp_dotL_chartJ_unitStrip {ν : ℝ} (hν : 0 < ν) (hP1 : P ≤ 1)
    (hq : q ≠ ⊤) (f : Yq P q) (τ₀ : ℝ) (e : CVec3) :
    MemLp (fun p : ℝ × Space => dotL e (chartJ f ν τ₀ p)) q
      (volume.restrict (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
  exact (memLp_chartJ_unitStrip hν hP1 hq f τ₀).continuousLinearMap_comp (dotL e)

/-- A bounded continuous time multiplier supported in the open unit strip turns a strip MemLp
field into a full space-time MemLp field. -/
theorem memLp_timeMul_unitStrip {g : ℝ × Space → ℂ} (hg : MemLp g q
    (volume.restrict (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))))
    {κ : ℝ → ℝ} {M : ℝ} (hκ : Continuous κ) (hM : 0 ≤ M)
    (hκbound : ∀ t, ‖(κ t : ℂ)‖ ≤ M)
    (hκzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → κ t = 0) :
    MemLp (fun p : ℝ × Space => (κ p.1 : ℂ) * g p) q volume := by
  let S : Set (ℝ × Space) := Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space)
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have hgind : MemLp (S.indicator g) q volume := by
    rw [memLp_indicator_iff_restrict hS]
    exact hg
  have hκmeas : AEStronglyMeasurable (fun p : ℝ × Space => (κ p.1 : ℂ)) volume := by
    exact (Complex.continuous_ofReal.comp (hκ.comp continuous_fst)).aestronglyMeasurable
  have hmul : AEStronglyMeasurable (fun p : ℝ × Space =>
      (κ p.1 : ℂ) * S.indicator g p) volume := hκmeas.mul hgind.1
  have heq : (fun p : ℝ × Space => (κ p.1 : ℂ) * g p) =ᵐ[volume]
      fun p => (κ p.1 : ℂ) * S.indicator g p := by
    filter_upwards [] with p
    by_cases hp : p ∈ S
    · simp [Set.indicator_of_mem hp]
    · have ht : p.1 ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun ht => hp ⟨ht, Set.mem_univ _⟩
      simp [Set.indicator_of_notMem hp, hκzero p.1 ht]
  have hmul' : AEStronglyMeasurable
      (fun p : ℝ × Space => (κ p.1 : ℂ) * g p) volume := hmul.congr heq.symm
  apply hgind.of_le_mul hmul'
  filter_upwards [] with p
  by_cases hp : p ∈ S
  · rw [Set.indicator_of_mem hp]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hκbound p.1) (norm_nonneg _)
  · have ht : p.1 ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun ht => hp ⟨ht, Set.mem_univ _⟩
    simp [Set.indicator_of_notMem hp, hκzero p.1 ht]

/-- The temporal cutoff produces the Lq resolvent pair from the three graph fields on one strip.
The last multiplier is χ(t)e^{-t}, so the source term has exactly the weight in B0447. -/
theorem memLp_cutoff_resolvent_pair {U B A : ℝ × Space → ℂ}
    (hU : MemLp U q (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))))
    (hB : MemLp B q (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))))
    (hA : MemLp A q (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))))
    {χ χt κA : ℝ → ℝ} {Mχ Mχt MA : ℝ}
    (hχc : Continuous χ) (hχtc : Continuous χt) (hκAc : Continuous κA)
    (hχM : 0 ≤ Mχ) (hχtM : 0 ≤ Mχt) (hAM : 0 ≤ MA)
    (hχbound : ∀ t, ‖(χ t : ℂ)‖ ≤ Mχ)
    (hχtbound : ∀ t, ‖(χt t : ℂ)‖ ≤ Mχt)
    (hAbound : ∀ t, ‖(κA t : ℂ)‖ ≤ MA)
    (hχzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → χ t = 0)
    (hχtzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → χt t = 0)
    (hAzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → κA t = 0) :
    MemLp (fun p => (χ p.1 : ℂ) * U p) q volume ∧
    MemLp (fun p => (χt p.1 : ℂ) * U p + (χ p.1 : ℂ) * B p -
      (κA p.1 : ℂ) * A p + (χ p.1 : ℂ) * U p) q volume := by
  have hχU := memLp_timeMul_unitStrip hU hχc hχM hχbound hχzero
  have hχtU := memLp_timeMul_unitStrip hU hχtc hχtM hχtbound hχtzero
  have hχB := memLp_timeMul_unitStrip hB hχc hχM hχbound hχzero
  have hκAA := memLp_timeMul_unitStrip hA hκAc hAM hAbound hAzero
  exact ⟨hχU, ((hχtU.add hχB).sub hκAA).add hχU⟩

end UnforcedLeray.B0449
