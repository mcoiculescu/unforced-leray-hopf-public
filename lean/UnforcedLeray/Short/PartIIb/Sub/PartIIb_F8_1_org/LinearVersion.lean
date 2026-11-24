import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace F8L

/-- `φ` vanishes near every point with `s ≤ 0`. -/
def Vanish (φ : Coord → ℝ) : Prop := ∀ x : Coord, ¬ 0 < x.1 → φ =ᶠ[𝓝 x] 0

theorem Vanish.of_test {φ : Coord → ℝ} (h : IsCoordTest φ) : Vanish φ := by
  intro x hx
  have : x ∉ tsupport φ := fun hm => by
    have := h.supp hm
    simp at this
    exact hx this
  exact notMem_tsupport_iff_eventuallyEq.1 this

theorem Vanish.dcpd {φ : Coord → ℝ} (h : Vanish φ) (j : Fin 3) : Vanish (cpd j φ) := by
  intro x hx
  have h1 : ∀ᶠ y in 𝓝 x, φ =ᶠ[𝓝 y] 0 := (h x hx).eventuallyEq_nhds
  filter_upwards [h1] with y hy
  simp [UnforcedLeray.Short.IIb.cpd, hy.fderiv_eq]

theorem Vanish.eq {φ : Coord → ℝ} (h : Vanish φ) {x : Coord} (hx : ¬ 0 < x.1) : φ x = 0 :=
  (h x hx).eq_of_nhds

theorem Vanish.cpd_eq {φ : Coord → ℝ} (h : Vanish φ) (j : Fin 3) {x : Coord} (hx : ¬ 0 < x.1) :
    cpd j φ x = 0 := (h.dcpd j).eq hx

theorem coordTranspose_eq_zero (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {φ : Coord → ℝ}
    (h : IsCoordTest φ) {x : Coord} (hx : ¬ 0 < x.1) : coordTranspose v d φ x = 0 := by
  have hv := Vanish.of_test h
  have hj : ∀ j : Fin 3, UnforcedLeray.Short.IIb.cpd j (fun y => v y j * φ y) x = 0 := by
    intro j
    have : (fun y => v y j * φ y) =ᶠ[𝓝 x] 0 := (hv x hx).mono (fun y hy => by simp [hy])
    simp [UnforcedLeray.Short.IIb.cpd, this.fderiv_eq]
  simp [coordTranspose, hj, hv.eq hx]

theorem ae_mul_eq {u u' h : Coord → ℂ}
    (hu : u =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u')
    (hh : ∀ x : Coord, ¬ 0 < x.1 → h x = 0) :
    (fun x => u x * h x) =ᵐ[volume] (fun x => u' x * h x) := by
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)] at hu
  filter_upwards [hu] with x hx
  by_cases h0 : 0 < x.1
  · simp [hx h0]
  · simp [hh x h0]

theorem hasWeakFO_congr (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {u u' g g' : Coord → ℂ}
    (hu : u =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u')
    (hg : g =ᵐ[volume.restrict {x : Coord | 0 < x.1}] g') (h : HasWeakFO v d u g) :
    HasWeakFO v d u' g' := by
  obtain ⟨hI, hE⟩ := h
  have e1 : ∀ φ, IsCoordTest φ → (fun x => u x * (coordTranspose v d φ x : ℂ)) =ᵐ[volume]
      (fun x => u' x * (coordTranspose v d φ x : ℂ)) := fun φ hφ =>
    ae_mul_eq hu (fun x hx => by simp [coordTranspose_eq_zero v d hφ hx])
  have e2 : ∀ φ, IsCoordTest φ → (fun x => g x * (φ x : ℂ)) =ᵐ[volume]
      (fun x => g' x * (φ x : ℂ)) := fun φ hφ =>
    ae_mul_eq hg (fun x hx => by simp [(Vanish.of_test hφ).eq hx])
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · exact (integrable_congr (e1 φ hφ)).1 (hI φ hφ).1
  · exact (integrable_congr (e2 φ hφ)).1 (hI φ hφ).2
  · rw [← integral_congr_ae (e2 φ hφ), hE φ hφ]
    exact integral_congr_ae (e1 φ hφ)

theorem hasWeakFO_comb (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (u g : ι → Coord → ℂ) (h : ∀ i ∈ s, HasWeakFO v d (u i) (g i)) :
    HasWeakFO v d (fun x => ∑ i ∈ s, r i • u i x) (fun x => ∑ i ∈ s, r i • g i x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun i hi => ((h i hi).1 φ hφ).1.smul (r i))
  · simp only [Finset.sum_mul, smul_mul_assoc]
    exact integrable_finsetSum _ (fun i hi => ((h i hi).1 φ hφ).2.smul (r i))
  · simp only [Finset.sum_mul, smul_mul_assoc]
    have a1 : ∀ i ∈ s, Integrable (fun x => r i • (g i x * (φ x : ℂ))) volume :=
      fun i hi => ((h i hi).1 φ hφ).2.smul (r i)
    have a2 : ∀ i ∈ s, Integrable (fun x => r i • (u i x * (coordTranspose v d φ x : ℂ))) volume :=
      fun i hi => ((h i hi).1 φ hφ).1.smul (r i)
    rw [integral_finsetSum s a1, integral_finsetSum s a2]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [integral_smul, integral_smul, (h i hi).2 φ hφ]

/-- Uniqueness of weak derivatives on `s > 0`. -/
theorem weak_unique (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {u g1 g2 : Coord → ℂ}
    (h1 : HasWeakFO v d u g1) (h2 : HasWeakFO v d u g2) :
    g1 =ᵐ[volume.restrict {x : Coord | 0 < x.1}] g2 := by
  have hU : IsOpen {x : Coord | 0 < x.1} := isOpen_lt continuous_const continuous_fst
  have hint : ∀ φ, IsCoordTest φ → Integrable (fun x => (g1 x - g2 x) * (φ x : ℂ)) := by
    intro φ hφ
    have := ((h1.1 φ hφ).2).sub ((h2.1 φ hφ).2)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [sub_mul]
  have loc : LocallyIntegrableOn (fun x => g1 x - g2 x) {x : Coord | 0 < x.1} volume := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    let f : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hφ : IsCoordTest f := by
      refine ⟨f.contDiff, f.hasCompactSupport, ?_⟩
      rw [f.tsupport_eq]
      intro y hy
      have : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball]
        have := Metric.mem_closedBall.1 hy
        show dist y x < ε
        simp only [f] at this
        linarith
      have := hball this
      simpa using this
    refine ⟨Metric.closedBall x (ε / 4), ?_, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (by positivity))
    · have := (hint f hφ).integrableOn (s := Metric.closedBall x (ε / 4))
      refine this.congr_fun (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
      have : f y = 1 := f.one_of_mem_closedBall hy
      simp [this]
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero loc (μ := volume) ?_
  · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
    filter_upwards [key] with x hx hx0
    exact sub_eq_zero.1 (hx hx0)
  · intro φ hφs hφc hsub
    have hφ : IsCoordTest φ := ⟨hφs, hφc, by
      intro y hy
      have := hsub hy
      simpa using this⟩
    have := (h1.2 φ hφ).trans (h2.2 φ hφ).symm
    have e : ∫ x, φ x • (g1 x - g2 x) = ∫ x, ((g1 x - g2 x) * (φ x : ℂ)) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [mul_comm, Complex.real_smul]
    rw [e]
    simp only [sub_mul]
    rw [integral_sub (h1.1 φ hφ).2 (h2.1 φ hφ).2, this, sub_self]



/-! ### Shift in `q` -/

/-- Shift vector. -/
def shiftVec (c : ℝ) : Coord := (0, (c, 0))

theorem qShift_eq (c : ℝ) (x : Coord) : qShift c x = x + shiftVec c := by
  ext <;> simp [qShift, shiftVec]

theorem shift_mp (c : ℝ) : MeasurePreserving (qShift c) (volume : Measure Coord) volume := by
  have : qShift c = fun x => x + shiftVec c := funext (qShift_eq c)
  rw [this]
  exact measurePreserving_add_right volume (shiftVec c)

theorem shift_emb (c : ℝ) : MeasurableEmbedding (qShift c) := by
  have : qShift c = fun x => x + shiftVec c := funext (qShift_eq c)
  rw [this]
  exact measurableEmbedding_addRight (shiftVec c)

theorem shift_mp_pos (c : ℝ) : MeasurePreserving (qShift c)
    (volume.restrict {x : Coord | 0 < x.1}) (volume.restrict {x : Coord | 0 < x.1}) := by
  have h := (shift_mp c).restrict_preimage (s := {x : Coord | 0 < x.1})
    (measurableSet_lt measurable_const measurable_fst)
  have e : (qShift c) ⁻¹' {x : Coord | 0 < x.1} = {x : Coord | 0 < x.1} := by
    ext x; simp [qShift]
  rwa [e] at h

theorem qperiodic_congr {c : ℝ} {z z₀ : CProf}
    (h : z =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z₀) (h₀ : QPeriodic c z₀) :
    QPeriodic c z := by
  have h1 := (shift_mp_pos c).quasiMeasurePreserving.ae_eq_comp h
  unfold QPeriodic at h₀ ⊢
  filter_upwards [h1, h₀, h] with x hx1 hx2 hx3
  simp only [Function.comp] at hx1
  rw [hx1, hx2, hx3]

theorem coordTranspose_const (w : Fin 3 → ℝ) {φ : Coord → ℝ} (hφ : Differentiable ℝ φ) (x : Coord) :
    coordTranspose (fun _ => w) dZero φ x = -(∑ j : Fin 3, w j * cpd j φ x) := by
  simp only [coordTranspose, dZero, zero_mul, add_zero]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [UnforcedLeray.Short.IIb.cpd]
  rw [fderiv_const_mul (hφ x)]
  simp

theorem hasWeakFO_shift (c : ℝ) (w : Fin 3 → ℝ) {u g : Coord → ℂ}
    (h : HasWeakFO (fun _ => w) dZero u g) :
    HasWeakFO (fun _ => w) dZero (fun x => u (qShift c x)) (fun x => g (qShift c x)) := by
  set e := shiftVec c
  -- shifted test function
  have htest : ∀ φ, IsCoordTest φ → IsCoordTest (fun y => φ (y + -e)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
      hφ.compact.comp_homeomorph (Homeomorph.addRight (-e)), ?_⟩
    have hc : IsClosed ((fun y : Coord => y + -e) ⁻¹' tsupport φ) :=
      (isClosed_tsupport φ).preimage (continuous_id.add continuous_const)
    have : tsupport (fun y => φ (y + -e)) ⊆ (fun y : Coord => y + -e) ⁻¹' tsupport φ := by
      refine closure_minimal (fun y hy => ?_) hc
      exact subset_tsupport φ (by simpa [Function.mem_support] using hy)
    intro y hy
    have := hφ.supp (this hy)
    simpa [e, shiftVec] using this
  have hTr : ∀ φ, IsCoordTest φ → ∀ y, coordTranspose (fun _ => w) dZero (fun y => φ (y + -e)) y =
      coordTranspose (fun _ => w) dZero φ (y + -e) := by
    intro φ hφ y
    have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hd' : Differentiable ℝ (fun y => φ (y + -e)) := hd.comp (differentiable_id.add_const _)
    rw [coordTranspose_const w hd', coordTranspose_const w hd]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [UnforcedLeray.Short.IIb.cpd]
    rw [fderiv_comp_add_right]
  have hS : ∀ x, qShift c x + -e = x := by intro x; rw [qShift_eq]; simp [e]
  have hmp := shift_mp c
  have hem := shift_emb c
  have I1 : ∀ φ, IsCoordTest φ → Integrable (fun y => u y *
      ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ)) := by
    intro φ hφ
    have := (h.1 _ (htest φ hφ)).1
    exact this.congr (Eventually.of_forall fun y => by simp [hTr φ hφ y])
  have I2 : ∀ φ, IsCoordTest φ → Integrable (fun y => g y * (φ (y + -e) : ℂ)) :=
    fun φ hφ => (h.1 _ (htest φ hφ)).2
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have := (hmp.integrable_comp_emb hem).2 (I1 φ hφ)
    exact this.congr (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have := (hmp.integrable_comp_emb hem).2 (I2 φ hφ)
    exact this.congr (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have e1 : ∫ x, g (qShift c x) * (φ x : ℂ) = ∫ y, g y * (φ (y + -e) : ℂ) := by
      have := hmp.integral_comp hem (fun y => g y * (φ (y + -e) : ℂ))
      simpa [hS] using this
    have e2 : ∫ x, u (qShift c x) * (coordTranspose (fun _ => w) dZero φ x : ℂ) =
        ∫ y, u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ) := by
      have := hmp.integral_comp hem
        (fun y => u y * ((coordTranspose (fun _ => w) dZero φ (y + -e) : ℝ) : ℂ))
      simpa [hS] using this
    rw [e1, e2, h.2 _ (htest φ hφ)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hTr φ hφ y]

/-- Weak derivatives along a constant direction of a `q`-periodic profile are `q`-periodic. -/
theorem qperiodic_deriv {c : ℝ} (w : Fin 3 → ℝ) {z zq : CProf} (hz : QPeriodic c z)
    (hw : HasWeakVec (fun _ => w) dZero z zq) : QPeriodic c zq := by
  have hi : ∀ i : Fin 2, (fun x => zq (qShift c x) i) =ᵐ[volume.restrict {x : Coord | 0 < x.1}]
      (fun x => zq x i) := by
    intro i
    have h1 := hasWeakFO_shift c w (hw i)
    have hu : (fun x => z (qShift c x) i) =ᵐ[volume.restrict {x : Coord | 0 < x.1}]
        (fun x => z x i) := by
      filter_upwards [hz] with x hx
      rw [hx]
    have h2 := hasWeakFO_congr (fun _ => w) dZero hu (Filter.EventuallyEq.refl _ _) h1
    exact weak_unique _ _ h2 (hw i)
  have := (ae_all_iff.2 hi)
  unfold QPeriodic
  filter_upwards [this] with x hx
  ext i
  exact hx i


/-! ### Transfer of the meridional correction -/

theorem ae_pos {E : Type*} {f f' : Coord → E}
    (h : f =ᵐ[volume.restrict {x : Coord | 0 < x.1}] f') :
    ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → f x = f' x := by
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
    at h
  exact h

theorem transfer_solenoidal {z z' : CProf} (hz : z =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z')
    (h : ∀ φ, IsCoordTest φ →
      Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0) :
    ∀ φ, IsCoordTest φ →
      Integrable (fun x => z' x 0 * (cpd 1 φ x : ℂ) + z' x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z' x 0 * (cpd 1 φ x : ℂ) + z' x 1 * (cpd 2 φ x : ℂ)) = 0 := by
  intro φ hφ
  have e : (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
      (fun x => z' x 0 * (cpd 1 φ x : ℂ) + z' x 1 * (cpd 2 φ x : ℂ)) := by
    filter_upwards [ae_pos hz] with x hx
    by_cases h0 : 0 < x.1
    · rw [hx h0]
    · simp [(Vanish.of_test hφ).cpd_eq 1 h0, (Vanish.of_test hφ).cpd_eq 2 h0]
  exact ⟨(integrable_congr e).1 (h φ hφ).1, by rw [← integral_congr_ae e]; exact (h φ hφ).2⟩

theorem meridTranspose_eq_zero (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {x : Coord} (hx : ¬ 0 < x.1) (i : Fin 2) : meridTranspose ν Ψ x i = 0 := by
  have V := Vanish.of_test (hΨ.smooth i)
  have h0 := V.cpd_eq 0 hx
  have h1 := (V.dcpd 1).cpd_eq 1 hx
  have h2 := (V.dcpd 2).cpd_eq 2 hx
  simp only [meridTranspose]
  rw [show (fun y => cpd 1 (fun z => Ψ z i) y) = cpd 1 (fun z => Ψ z i) from rfl,
    show (fun y => cpd 2 (fun z => Ψ z i) y) = cpd 2 (fun z => Ψ z i) from rfl, h0, h1, h2]
  simp

theorem transfer_equation (p : Params) {g z zq zη z' zq' zη' : CProf}
    (hz : z =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z')
    (hzq : zq =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zq')
    (hzη : zη =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zη')
    (h : ∀ Ψ, IsPlanarSolTest Ψ →
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) =
        ∫ x, cdot g Ψ x) :
    ∀ Ψ, IsPlanarSolTest Ψ →
    Integrable (fun x => ∑ i : Fin 2, z' x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z' zq' zη') Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z' x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z' zq' zη') Ψ x) =
        ∫ x, cdot g Ψ x := by
  intro Ψ hΨ
  have V : ∀ i, Vanish (fun x => Ψ x i) := fun i => Vanish.of_test (hΨ.smooth i)
  have eA : (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) =ᵐ[volume]
      (fun x => ∑ i : Fin 2, z' x i * meridTranspose p.ν Ψ x i) := by
    filter_upwards [ae_pos hz] with x hx
    by_cases h0 : 0 < x.1
    · rw [hx h0]
    · simp [meridTranspose_eq_zero p.ν hΨ h0]
  have eB : cdot (flatBv p.train z zq zη) Ψ =ᵐ[volume] cdot (flatBv p.train z' zq' zη') Ψ := by
    filter_upwards [ae_pos hz, ae_pos hzq, ae_pos hzη] with x hx hxq hxη
    by_cases h0 : 0 < x.1
    · simp only [cdot, flatBv]
      rw [hx h0, hxq h0, hxη h0]
    · simp [cdot, (V _).eq h0]
  obtain ⟨h1, h2, h3, h4⟩ := h Ψ hΨ
  refine ⟨(integrable_congr eA).1 h1, (integrable_congr eB).1 h2, h3, ?_⟩
  rw [← h4]
  refine (integral_congr_ae ?_).symm
  filter_upwards [eA, eB] with x ha hb
  simp only [ha, hb]

/-! ### Slices -/

theorem slice_ae {E : Type*} {f f' : Coord → E}
    (h : f =ᵐ[volume.restrict {x : Coord | 0 < x.1}] f') :
    ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), f (s, y) = f' (s, y) := by
  have e : (volume.restrict {x : Coord | 0 < x.1} : Measure Coord) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ)) := by
    have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
      (Ioi 0) univ
    rw [Measure.restrict_univ] at this
    rw [this, Measure.volume_eq_prod,
      show {x : Coord | 0 < x.1} = Ioi (0 : ℝ) ×ˢ univ from by ext x; simp [Set.mem_prod]]
  rw [e] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  rw [ae_restrict_iff' measurableSet_Ioi] at h2
  exact h2

theorem cellMeasure_zero (c : ℝ) :
    B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  unfold B0579.cellMeasure
  have : (fun x => (B0579.density 0 x : ℝ≥0∞)) = fun _ => 1 := by
    funext x; simp [B0579.density]
  rw [this]; exact withDensity_one


/-! ### Triangle inequality with a non-measurable summand -/

theorem eLpNorm_two_sub_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {m m' e : X → E} (hm : AEStronglyMeasurable m μ) (hm' : AEStronglyMeasurable m' μ) :
    eLpNorm (m - e) 2 μ ≤ eLpNorm (m' - e) 2 μ + eLpNorm (m - m') 2 μ := by
  have two : (2 : ℝ≥0∞).toReal = 2 := rfl
  have key : ∀ f : X → E, eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro f
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), two]
  rw [key, key, key]
  obtain ⟨g, hg, hgle, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x => ‖(m - e) x‖ₑ ^ (2 : ℝ))
  set d : X → ℝ≥0∞ := fun x => ‖(m - m') x‖ₑ with hd
  have hdm : AEMeasurable d μ := (hm.sub hm').enorm
  let k : X → ℝ≥0∞ := fun x => g x ^ (1 / (2 : ℝ))
  have hk : Measurable k := hg.pow_const _
  have hk2 : ∀ x, k x ^ (2 : ℝ) = g x := by
    intro x
    simp only [k]
    rw [← ENNReal.rpow_mul]; norm_num
  have hkle : ∀ x, k x ≤ ‖(m - e) x‖ₑ := by
    intro x
    have := ENNReal.rpow_le_rpow (hgle x) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    simp only [k]
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]; norm_num
  have hk' : ∀ x, k x - d x ≤ ‖(m' - e) x‖ₑ := by
    intro x
    rw [tsub_le_iff_right]
    refine (hkle x).trans ?_
    have : (m - e) x = (m' - e) x + (m - m') x := by simp
    rw [this]
    exact enorm_add_le _ _
  have hkd : AEMeasurable (k - d) μ := hk.aemeasurable.sub hdm
  rw [hint]
  calc (∫⁻ a, g a ∂μ) ^ (1 / (2 : ℝ)) = (∫⁻ a, k a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        simp_rw [hk2]
    _ ≤ (∫⁻ a, ((k - d) + d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono (fun a => ?_)) (by norm_num)
        exact ENNReal.rpow_le_rpow (by simpa using (le_tsub_add : k a ≤ k a - d a + d a))
          (by norm_num)
    _ ≤ (∫⁻ a, (k - d) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) + (∫⁻ a, d a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_Lp_add_le hkd hdm (by norm_num)
    _ ≤ _ := by
        gcongr with a
        exact hk' a


/-! ### Finite combinations and `H¹`-continuity -/

/-- Finite real combination of profiles. -/
def comb {ι : Type*} (a : ι →₀ ℝ) (w : ι → CProf) : CProf :=
  fun x => ∑ i ∈ a.support, a i • w i x

/-- `L²(cell)` distance of the slices of `w` at ages `s` and `s'`. -/
def dd (c : ℝ) (w : CProf) (s s' : ℝ) : ℝ≥0∞ :=
  F8U.cellL2 c (fun y => w (s', y) - w (s, y))

theorem sliceMeas {w : CProf} (hw : StronglyMeasurable w) (s : ℝ) :
    StronglyMeasurable (fun y : B0579.Plane => w (s, y)) :=
  hw.comp_measurable measurable_prodMk_left

theorem compMeas {α : Type*} [MeasurableSpace α] {w : α → CMerid} (hw : StronglyMeasurable w)
    (i : Fin 2) : StronglyMeasurable (fun x => w x i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw

theorem comb_meas {ι : Type*} (a : ι →₀ ℝ) {w : ι → CProf} (hw : ∀ i, StronglyMeasurable (w i)) :
    StronglyMeasurable (comb a w) := by
  have := Finset.stronglyMeasurable_sum a.support (fun i _ => (hw i).const_smul (a i))
  convert this using 1
  funext x
  simp [comb, Finset.sum_apply]

theorem cellL2_le (c : ℝ) {w : CProf} (hw : StronglyMeasurable w) (s s' : ℝ) :
    F8U.cellL2 c (F8U.slice w s) ≤ F8U.cellL2 c (F8U.slice w s') + dd c w s s' := by
  have e : F8U.slice w s = F8U.slice w s' - (fun y => w (s', y) - w (s, y)) := by
    funext y; simp [F8U.slice]
  unfold F8U.cellL2 dd
  rw [e]
  exact eLpNorm_sub_le (sliceMeas hw s').aestronglyMeasurable
    ((sliceMeas hw s').sub (sliceMeas hw s)).aestronglyMeasurable (by norm_num)

theorem dd_comb_le {ι : Type*} (c : ℝ) (a : ι →₀ ℝ) {w : ι → CProf}
    (hw : ∀ i, StronglyMeasurable (w i)) (s s' : ℝ) :
    dd c (comb a w) s s' ≤ ∑ i ∈ a.support, ENNReal.ofReal |a i| * dd c (w i) s s' := by
  have e : (fun y => comb a w (s', y) - comb a w (s, y)) =
      ∑ i ∈ a.support, a i • (fun y => w i (s', y) - w i (s, y)) := by
    funext y
    simp [comb, Finset.sum_sub_distrib, smul_sub, Finset.sum_apply]
  unfold dd F8U.cellL2
  rw [e]
  refine (eLpNorm_sum_le (fun i _ => (((sliceMeas (hw i) s').sub (sliceMeas (hw i) s)).const_smul
    (a i)).aestronglyMeasurable) (by norm_num)).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine eLpNorm_const_smul_le.trans ?_
  rw [Real.enorm_eq_ofReal_abs]
  exact le_of_eq rfl

theorem dd_tendsto_comb {ι : Type*} (c : ℝ) (a : ι →₀ ℝ) {w : ι → CProf}
    (hw : ∀ i, StronglyMeasurable (w i)) {s : ℝ}
    (h : ∀ i, Tendsto (dd c (w i) s) (𝓝 s) (𝓝 0)) : Tendsto (dd c (comb a w) s) (𝓝 s) (𝓝 0) := by
  have hsum : Tendsto (fun s' => ∑ i ∈ a.support, ENNReal.ofReal |a i| * dd c (w i) s s')
      (𝓝 s) (𝓝 0) := by
    have := tendsto_finsetSum a.support (fun i _ =>
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a i|) (h i) (Or.inr ENNReal.ofReal_ne_top))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    (fun s' => dd_comb_le c a hw s s')

theorem dd_tendsto_of_cylH1 {c : ℝ} {z zq zη : CProf} {s : ℝ}
    (h : Tendsto (fun s' => F8U.cylH1 c (fun y => z (s', y) - z (s, y))
      (fun y => zq (s', y) - zq (s, y)) (fun y => zη (s', y) - zη (s, y))) (𝓝 s) (𝓝 0)) :
    Tendsto (dd c z s) (𝓝 s) (𝓝 0) ∧ Tendsto (dd c zq s) (𝓝 s) (𝓝 0) ∧
      Tendsto (dd c zη s) (𝓝 s) (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun s' => ?_)
  · unfold dd F8U.cylH1
    exact (le_self_add).trans le_self_add
  · unfold dd F8U.cylH1
    exact le_add_self.trans le_self_add
  · unfold dd F8U.cylH1
    exact le_add_self

/-- A function bounded at almost every point of an open set, and upper semicontinuous in the sense
`G s ≤ G s' + ε` for `s'` near `s`, is bounded everywhere on the set. -/
theorem ae_dense_le {G : ℝ → ℝ≥0∞} {U : Set ℝ} (hU : IsOpen U) {B : ℝ≥0∞}
    (hgood : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ U → G s ≤ B)
    (hcont : ∀ s ∈ U, ∀ ε : ℝ≥0∞, ε ≠ 0 → ∀ᶠ s' in 𝓝 s, G s ≤ G s' + ε) :
    ∀ s ∈ U, G s ≤ B := by
  intro s hs
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have h1 := hcont s hs ε (by simpa using hε.ne')
  have h2 : ∀ᶠ s' in 𝓝 s, s' ∈ U := hU.mem_nhds hs
  obtain ⟨V, hVsub, hV, hsV⟩ := mem_nhds_iff.1 (h1.and h2)
  have hN : volume {s' : ℝ | ¬(s' ∈ U → G s' ≤ B)} = 0 := ae_iff.1 hgood
  have hpos : 0 < volume V := hV.measure_pos volume ⟨s, hsV⟩
  obtain ⟨s', hs'V, hs'N⟩ : ∃ s' ∈ V, s' ∉ {s' : ℝ | ¬(s' ∈ U → G s' ≤ B)} := by
    by_contra hcon
    have hsub : V ⊆ {s' : ℝ | ¬(s' ∈ U → G s' ≤ B)} := by
      intro x hxV
      by_contra hx
      exact hcon ⟨x, hxV, hx⟩
    exact hpos.ne' (measure_mono_null hsub hN)
  have hb := hVsub hs'V
  have hg : G s' ≤ B := by
    by_contra hh
    exact hs'N (fun h' => hh (h' hb.2))
  exact hb.1.trans (add_le_add_left hg _)


theorem sliceH1_le (c : ℝ) {Z Zq Zη : CProf} (hZ : StronglyMeasurable Z)
    (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη) (s s' : ℝ) :
    sliceH1Norm c Z Zq Zη s ≤
      sliceH1Norm c Z Zq Zη s' + (dd c Z s s' + dd c Zq s s' + dd c Zη s s') := by
  have h1 := cellL2_le c hZ s s'
  have h2 := cellL2_le c hZq s s'
  have h3 := cellL2_le c hZη s s'
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  unfold sliceH1Norm F8U.cellL2 F8U.slice
  ac_rfl

theorem sliceH1_ae (c : ℝ) {Z Zq Zη z0 zq0 zη0 : CProf}
    (h1 : Z =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z0)
    (h2 : Zq =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zq0)
    (h3 : Zη =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zη0) :
    ∀ᵐ s ∂(volume : Measure ℝ), 0 < s →
      sliceH1Norm c Z Zq Zη s = sliceH1Norm c z0 zq0 zη0 s := by
  filter_upwards [slice_ae h1, slice_ae h2, slice_ae h3] with s e1 e2 e3 hs
  unfold sliceH1Norm
  rw [eLpNorm_congr_ae (ae_restrict_of_ae (e1 hs)), eLpNorm_congr_ae (ae_restrict_of_ae (e2 hs)),
    eLpNorm_congr_ae (ae_restrict_of_ae (e3 hs))]

theorem cellL2_slice_ae (c : ℝ) {f f' : CProf}
    (h : f =ᵐ[volume.restrict {x : Coord | 0 < x.1}] f') :
    ∀ᵐ s ∂(volume : Measure ℝ), 0 < s →
      F8U.cellL2 c (F8U.slice f s) = F8U.cellL2 c (F8U.slice f' s) := by
  filter_upwards [slice_ae h] with s e hs
  exact eLpNorm_congr_ae (ae_restrict_of_ae (e hs))

theorem curl_le (c : ℝ) {Zq Zη : CProf} (hq : StronglyMeasurable Zq) (hη : StronglyMeasurable Zη)
    (ent : B0579.Plane → ℝ) (s s' : ℝ) :
    eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) ≤
      eLpNorm (fun x => profCurl Zq Zη (s', x) - ((ent x : ℝ) : ℂ)) 2 (B0579.cellMeasure c 0) +
        (dd c Zq s s' + dd c Zη s s') := by
  rw [cellMeasure_zero]
  set μ : Measure B0579.Plane := volume.restrict (B0579.cell c)
  let m : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s, x)
  let m' : B0579.Plane → ℂ := fun x => profCurl Zq Zη (s', x)
  let e : B0579.Plane → ℂ := fun x => ((ent x : ℝ) : ℂ)
  have hm : StronglyMeasurable m :=
    (compMeas (sliceMeas hq s) 1).sub (compMeas (sliceMeas hη s) 0)
  have hm' : StronglyMeasurable m' :=
    (compMeas (sliceMeas hq s') 1).sub (compMeas (sliceMeas hη s') 0)
  have h1 := eLpNorm_two_sub_le (μ := μ) (e := e) hm.aestronglyMeasurable hm'.aestronglyMeasurable
  refine h1.trans (add_le_add_right ?_ _)
  let Dq : B0579.Plane → CMerid := fun y => Zq (s', y) - Zq (s, y)
  let Dη : B0579.Plane → CMerid := fun y => Zη (s', y) - Zη (s, y)
  have hDq : StronglyMeasurable Dq := (sliceMeas hq s').sub (sliceMeas hq s)
  have hDη : StronglyMeasurable Dη := (sliceMeas hη s').sub (sliceMeas hη s)
  have hb : ∀ x, ‖(m - m') x‖ ≤ ‖‖Dq x‖ + ‖Dη x‖‖ := by
    intro x
    have e1 : (m - m') x = -(Dq x 1) + Dη x 0 := by
      simp [m, m', Dq, Dη, profCurl]; ring
    rw [e1, Real.norm_of_nonneg (by positivity)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    exact add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
  calc eLpNorm (m - m') 2 μ ≤ eLpNorm (fun x => ‖Dq x‖ + ‖Dη x‖) 2 μ := eLpNorm_mono hb
    _ ≤ eLpNorm (fun x => ‖Dq x‖) 2 μ + eLpNorm (fun x => ‖Dη x‖) 2 μ :=
        eLpNorm_add_le hDq.norm.aestronglyMeasurable hDη.norm.aestronglyMeasurable (by norm_num)
    _ = dd c Zq s s' + dd c Zη s s' := by
        simp only [dd, F8U.cellL2, eLpNorm_norm]
        rfl


theorem curl_transfer (c : ℝ) {Zq Zη zq0 zη0 : CProf} (hq : StronglyMeasurable Zq)
    (hη : StronglyMeasurable Zη)
    (hdq : ∀ s : ℝ, 0 < s → Tendsto (dd c Zq s) (𝓝 s) (𝓝 0))
    (hdη : ∀ s : ℝ, 0 < s → Tendsto (dd c Zη s) (𝓝 s) (𝓝 0))
    (haq : Zq =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zq0)
    (haη : Zη =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zη0)
    (ent : B0579.Plane → ℝ)
    (h0 : Tendsto (fun s => eLpNorm (fun x => profCurl zq0 zη0 (s, x) - ((ent x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c 0)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c 0)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h0 ⊢
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h0 (ε / 2) (ENNReal.half_pos hε.ne'))
  have hδ' : (0 : ℝ) < δ := hδ
  set φ : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun x => profCurl Zq Zη (s, x) - ((ent x : ℝ) : ℂ)) 2
    (B0579.cellMeasure c 0) with hφ
  have key : ∀ s ∈ Ioo (0 : ℝ) δ, φ s ≤ ε / 2 := by
    refine ae_dense_le (isOpen_Ioo) ?_ ?_
    · filter_upwards [slice_ae haq, slice_ae haη] with s e1 e2 hs
      have hs0 : 0 < s := hs.1
      have : φ s = eLpNorm (fun x => profCurl zq0 zη0 (s, x) - ((ent x : ℝ) : ℂ)) 2
          (B0579.cellMeasure c 0) := by
        simp only [hφ]
        rw [cellMeasure_zero]
        refine eLpNorm_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (e1 hs0), ae_restrict_of_ae (e2 hs0)] with x x1 x2
        simp [profCurl, x1, x2]
      rw [this]
      exact hsub hs
    · intro s hs ε' hε'
      have hsum : Tendsto (fun s' => dd c Zq s s' + dd c Zη s s') (𝓝 s) (𝓝 0) := by
        simpa using (hdq s hs.1).add (hdη s hs.1)
      have := (ENNReal.tendsto_nhds_zero.1 hsum) ε' (pos_iff_ne_zero.2 hε')
      filter_upwards [this] with s' hs'
      exact (curl_le c hq hη ent s s').trans (add_le_add_right hs' _)
  filter_upwards [Ioo_mem_nhdsGT hδ'] with s hs
  exact (key s hs).trans (ENNReal.half_le_self)

/-! ### Linear combinations over a basis -/

theorem constr_eq_comb {ι V : Type*} [AddCommGroup V] [Module ℝ V] (b : Module.Basis ι ℝ V)
    (f : ι → CProf) (F : V) : b.constr ℝ f F = comb (b.repr F) f := by
  funext x
  simp [Module.Basis.constr_apply, Finsupp.sum, comb, Finset.sum_apply]

theorem comb_ae {ι V : Type*} [AddCommGroup V] [Module ℝ V] (b : Module.Basis ι ℝ V)
    (L : V →ₗ[ℝ] CProf) (w : ι → CProf)
    (h : ∀ i, w i =ᵐ[volume.restrict {x : Coord | 0 < x.1}] L (b i)) (F : V) :
    comb (b.repr F) w =ᵐ[volume.restrict {x : Coord | 0 < x.1}] L F := by
  have hL : L = b.constr ℝ (fun i => L (b i)) := b.ext (fun i => by simp)
  have e : L F = comb (b.repr F) (fun i => L (b i)) := by
    rw [← constr_eq_comb b (fun i => L (b i)) F, ← hL]
  have hall := (Filter.eventually_all_finset (b.repr F).support).2 (fun i _ => h i)
  filter_upwards [hall] with x hx
  rw [e]
  exact Finset.sum_congr rfl (fun i hi => by rw [hx i hi])

theorem comb_apply {ι : Type*} (a : ι →₀ ℝ) (w : ι → CProf) (x : Coord) (i : Fin 2) :
    comb a w x i = ∑ k ∈ a.support, a k • w k x i := by
  simp [comb]

theorem hasWeakVec_comb (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {ι : Type*} (a : ι →₀ ℝ)
    {w g : ι → CProf} (h : ∀ k, HasWeakVec v d (w k) (g k)) :
    HasWeakVec v d (comb a w) (comb a g) := fun i => by
  have := hasWeakFO_comb v d a.support (fun k => a k) (fun k x => w k x i) (fun k x => g k x i)
    (fun k _ => h k i)
  simpa [comb_apply] using this

theorem hasWeakVec_congr (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {b b' g g' : CProf}
    (hb : b =ᵐ[volume.restrict {x : Coord | 0 < x.1}] b')
    (hg : g =ᵐ[volume.restrict {x : Coord | 0 < x.1}] g') (h : HasWeakVec v d b g) :
    HasWeakVec v d b' g' := fun i =>
  hasWeakFO_congr v d (hb.mono fun x hx => by simp [hx]) (hg.mono fun x hx => by simp [hx]) (h i)

theorem weakVec_unique (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) {u u' g g' : CProf}
    (hu : u =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u')
    (h1 : HasWeakVec v d u g) (h2 : HasWeakVec v d u' g') :
    g =ᵐ[volume.restrict {x : Coord | 0 < x.1}] g' := by
  have h2' := hasWeakVec_congr v d hu.symm (Filter.EventuallyEq.refl _ g') h2
  have : ∀ i : Fin 2, (fun x => g x i) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] (fun x => g' x i) :=
    fun i => weak_unique v d (h1 i) (h2' i)
  filter_upwards [ae_all_iff.2 this] with x hx
  ext i
  exact hx i


set_option maxHeartbeats 1600000 in
theorem main : MeridionalLinearVersion := by
  intro p αMap gOf zOf₀ zqOf₀ zηOf₀ Mz Bnd hsol hbound hver
  classical
  let b := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  choose z' zq' zη' D2 hz'm hzq'm hzη'm hD2m haez haezq haezη hcont hw00 hw01 hw10 hw11 hbd
    using fun i => hver (b i)
  refine ⟨b.constr ℝ z', b.constr ℝ zq', b.constr ℝ zη',
    fun i j => b.constr ℝ (fun k => D2 k i j), fun F => ?_⟩
  simp only [constr_eq_comb]
  set a := b.repr F with ha
  obtain ⟨Zf, Zqf, Zηf, D2f, -, -, -, hD2fm, hZf, hZqf, hZηf, -, hq00, hq01, hq10, hq11, hbndF⟩ :=
    hver F
  have hZ : comb a z' =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zOf₀ F := comb_ae b zOf₀ z' haez F
  have hZq : comb a zq' =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zqOf₀ F :=
    comb_ae b zqOf₀ zq' haezq F
  have hZη : comb a zη' =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zηOf₀ F :=
    comb_ae b zηOf₀ zη' haezη F
  have hZqf' : Zqf =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zqOf₀ F := hZqf
  have hZηf' : Zηf =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zηOf₀ F := hZηf
  have mZ := comb_meas a hz'm
  have mZq := comb_meas a hzq'm
  have mZη := comb_meas a hzη'm
  have h0 := hsol F
  have hwq : HasWeakVec vQ0 dZero (comb a z') (comb a zq') :=
    hasWeakVec_congr vQ0 dZero hZ.symm hZq.symm h0.weak_q
  have hwη : HasWeakVec vEta dZero (comb a z') (comb a zη') :=
    hasWeakVec_congr vEta dZero hZ.symm hZη.symm h0.weak_eta
  have hper : QPeriodic p.c (comb a z') := qperiodic_congr hZ h0.periodic
  -- H¹ continuity of the combination
  have hdd : ∀ s : ℝ, 0 < s → Tendsto (dd p.c (comb a z') s) (𝓝 s) (𝓝 0) ∧
      Tendsto (dd p.c (comb a zq') s) (𝓝 s) (𝓝 0) ∧ Tendsto (dd p.c (comb a zη') s) (𝓝 s) (𝓝 0) := by
    intro s hs
    have := fun i => dd_tendsto_of_cylH1 (hcont i s hs)
    exact ⟨dd_tendsto_comb p.c a hz'm (fun i => (this i).1),
      dd_tendsto_comb p.c a hzq'm (fun i => (this i).2.1),
      dd_tendsto_comb p.c a hzη'm (fun i => (this i).2.2)⟩
  have hD2 : ∀ i j : Fin 2, comb a (fun k => D2 k i j) =ᵐ[volume.restrict {x : Coord | 0 < x.1}]
      D2f i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact weakVec_unique vQ0 dZero (hZq.trans hZqf'.symm)
        (hasWeakVec_comb vQ0 dZero a (fun k => hw00 k)) hq00
    · exact weakVec_unique vEta dZero (hZq.trans hZqf'.symm)
        (hasWeakVec_comb vEta dZero a (fun k => hw01 k)) hq01
    · exact weakVec_unique vQ0 dZero (hZη.trans hZηf'.symm)
        (hasWeakVec_comb vQ0 dZero a (fun k => hw10 k)) hq10
    · exact weakVec_unique vEta dZero (hZη.trans hZηf'.symm)
        (hasWeakVec_comb vEta dZero a (fun k => hw11 k)) hq11
  refine ⟨⟨hper, hwq, hwη, transfer_solenoidal hZ.symm h0.solenoidal,
    transfer_equation p hZ.symm hZq.symm hZη.symm h0.equation, ?_⟩, hper,
    qperiodic_deriv (w := ![0, 1, 0]) hper hwq, qperiodic_deriv (w := ![0, 0, 1]) hper hwη,
    mZ, mZq, mZη, fun i j => comb_meas a (fun k => hD2m k i j),
    hasWeakVec_comb vQ0 dZero a (fun k => hw00 k), hasWeakVec_comb vEta dZero a (fun k => hw01 k),
    hasWeakVec_comb vQ0 dZero a (fun k => hw10 k), hasWeakVec_comb vEta dZero a (fun k => hw11 k),
    ?_, ?_⟩
  · exact curl_transfer p.c mZq mZη (fun s hs => (hdd s hs).2.1) (fun s hs => (hdd s hs).2.2)
      hZq hZη _ h0.initial_curl
  · -- slice bound at every age
    have key : ∀ s ∈ Ioi (0 : ℝ), sliceH1Norm p.c (comb a z') (comb a zq') (comb a zη') s +
        ENNReal.ofReal ‖αMap F‖ ≤ ENNReal.ofReal (Mz F) := by
      refine ae_dense_le (G := fun s => sliceH1Norm p.c (comb a z') (comb a zq') (comb a zη') s +
        ENNReal.ofReal ‖αMap F‖) isOpen_Ioi ?_ ?_
      · filter_upwards [sliceH1_ae p.c hZ hZq hZη] with s hs hs0
        have hs0' : 0 < s := hs0
        rw [hs hs0']
        exact hbound F s hs0'
      · intro s hs ε hε
        have hsum : Tendsto (fun s' => dd p.c (comb a z') s s' + dd p.c (comb a zq') s s' +
            dd p.c (comb a zη') s s') (𝓝 s) (𝓝 0) := by
          simpa using ((hdd s hs).1.add (hdd s hs).2.1).add (hdd s hs).2.2
        have := (ENNReal.tendsto_nhds_zero.1 hsum) ε (pos_iff_ne_zero.2 hε)
        filter_upwards [this] with s' hs'
        calc sliceH1Norm p.c (comb a z') (comb a zq') (comb a zη') s + ENNReal.ofReal ‖αMap F‖
            ≤ (sliceH1Norm p.c (comb a z') (comb a zq') (comb a zη') s' + _) +
              ENNReal.ofReal ‖αMap F‖ :=
              add_le_add_left (sliceH1_le p.c mZ mZq mZη s s') _
          _ ≤ (sliceH1Norm p.c (comb a z') (comb a zq') (comb a zη') s' + ε) +
              ENNReal.ofReal ‖αMap F‖ := add_le_add_left (add_le_add_right hs' _) _
          _ = _ := by ring
    intro s hs
    exact key s hs
  · have e' := ae_all_iff.2 (fun i : Fin 2 => ae_all_iff.2 (fun j : Fin 2 =>
      cellL2_slice_ae p.c (hD2 i j)))
    filter_upwards [e', hbndF] with s hs hb hs0
    calc _ = ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2f i j) s) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hs i j hs0
      _ ≤ Bnd F s := hb hs0

end F8L

end UnforcedLeray.Short.IIb

theorem meridionalLinearVersion_proof : UnforcedLeray.Short.IIb.MeridionalLinearVersion :=
  UnforcedLeray.Short.IIb.F8L.main
