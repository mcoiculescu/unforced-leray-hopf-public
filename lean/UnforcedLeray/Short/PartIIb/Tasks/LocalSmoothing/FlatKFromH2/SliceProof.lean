import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.SliceDef
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.PlaneSobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `PartII-b:F8/2` helper: proof of `SliceSobolev`

1. `qper_of_weak`: the weak chart derivative `∂_q u` or `∂_η u` of a `c`-periodic `u` is
   `c`-periodic (uniqueness of weak derivatives on `s > 0`).
2. `slice_ident_all`: on almost every age slice, the weak derivative identity holds against the
   mollifiers `kern n (x - ·)` for all `n` and all `x` of a countable dense set (Fubini and the
   fundamental lemma of the calculus of variations in the age variable).
3. `sliceSobolev_proof`: componentwise `plane_sobolev` on almost every slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb.FlatKH2

open UnforcedLeray.Short.IIb

/-! ## 1. Transposes of the constant fields -/

theorem ct_vQ0 (φ : Coord → ℝ) (x : Coord) : coordTranspose vQ0 dZero φ x = -cpd 1 φ x := by
  simp [coordTranspose, vQ0, dZero, Fin.sum_univ_three, cpd]

theorem ct_vEta (φ : Coord → ℝ) (x : Coord) : coordTranspose vEta dZero φ x = -cpd 2 φ x := by
  simp [coordTranspose, vEta, dZero, Fin.sum_univ_three, cpd]

/-! ## 2. Local integrability from tests -/

theorem locIntOn_of_tests {f : Coord → ℂ}
    (hf : ∀ φ, IsCoordTest φ → Integrable (fun x => f x * (φ x : ℂ))) :
    LocallyIntegrableOn f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume := by
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hx
  let β : ContDiffBump x :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hβsub : tsupport β ⊆ Ioi (0 : ℝ) ×ˢ univ := by
    rw [β.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  have hβtest : IsCoordTest β := ⟨β.contDiff, β.hasCompactSupport, hβsub⟩
  have J1 : Integrable (fun y => f y * (β y : ℂ)) volume := hf β hβtest
  have hB1 : IntegrableOn f (Metric.ball x (ε / 4)) volume := by
    apply (J1.integrableOn).congr_fun _ measurableSet_ball
    intro y hy
    have h1 : β y = 1 := β.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [h1]
  have hat : IntegrableAtFilter f (𝓝 x) volume :=
    ⟨Metric.ball x (ε / 4), Metric.ball_mem_nhds x (by linarith), hB1⟩
  exact hat.filter_mono nhdsWithin_le_nhds

/-! ## 3. Periodicity of weak derivatives -/

theorem qper_of_weak {v : Coord → Fin 3 → ℝ} {j : Fin 3}
    (hv : ∀ φ x, coordTranspose v dZero φ x = -cpd j φ x) {c : ℝ} {u g : Coord → ℂ}
    (h : HasWeakFO v dZero u g)
    (hu : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), u (qShift c x) = u x) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), g (qShift c x) = g x := by
  set a : Coord := (0, (c, 0)) with ha
  have hq : ∀ x : Coord, qShift c x = x + a := fun x => by
    simp only [qShift, ha]
    ext <;> simp
  set U : Set Coord := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) with hU
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hUeq : {x : Coord | 0 < x.1} = U := by
    ext x
    simp [hU]
  have hshift : ∀ φ, IsCoordTest φ → IsCoordTest (fun x => φ (x - a)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
    · exact hφ.compact.comp_homeomorph (Homeomorph.subRight a)
    · have hsub : tsupport (fun x => φ (x - a)) ⊆ (fun x => x - a) ⁻¹' tsupport φ :=
        closure_minimal (fun x hx => subset_tsupport φ hx)
          ((isClosed_tsupport φ).preimage (continuous_id.sub continuous_const))
      intro x hx
      have h1 := hφ.supp (hsub hx)
      simp only [mem_prod, mem_Ioi, mem_univ, and_true] at h1 ⊢
      simpa [ha] using h1
  have hga : ∀ φ, IsCoordTest φ → Integrable (fun x => g (x + a) * (φ x : ℂ)) := by
    intro φ hφ
    have h1 := ((h.1 _ (hshift φ hφ)).2).comp_add_right a
    simpa using h1
  have hloc : LocallyIntegrableOn (fun x => g (x + a) - g x) U volume :=
    (locIntOn_of_tests hga).sub (locIntOn_of_tests (fun φ hφ => (h.1 φ hφ).2))
  have hCTs : ∀ φ : Coord → ℝ, ∀ x,
      coordTranspose v dZero (fun y => φ (y - a)) x = coordTranspose v dZero φ (x - a) := by
    intro φ x
    rw [hv, hv, cpd, cpd, fderiv_comp_sub]
  have hCT0 : ∀ φ, IsCoordTest φ → ∀ x, x ∉ U → coordTranspose v dZero φ x = 0 := by
    intro φ hφ x hx
    rw [hv, cpd]
    have hx' : x ∉ tsupport φ := fun h' => hx (hφ.supp h')
    have h0 : fderiv ℝ φ x = 0 := by
      by_contra hne
      exact hx' (support_fderiv_subset ℝ hne)
    rw [h0]
    simp
  have hu' : ∀ᵐ x, x ∈ U → u (x + a) = u x := by
    rw [← ae_restrict_iff' hUo.measurableSet, ← hUeq]
    filter_upwards [hu] with x hx
    rwa [hq] at hx
  have hint : ∀ φ : Coord → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, φ x • (g (x + a) - g x) = 0 := by
    intro φ hφs hφc hφU
    have hφ : IsCoordTest φ := ⟨hφs, hφc, hφU⟩
    have hφ' := hshift φ hφ
    have i1 : Integrable (fun x => g (x + a) * (φ x : ℂ)) := hga φ hφ
    have i2 : Integrable (fun x => g x * (φ x : ℂ)) := (h.1 φ hφ).2
    have e1 : ∫ x, g (x + a) * (φ x : ℂ) = ∫ x, g x * (φ (x - a) : ℂ) := by
      have := integral_add_right_eq_self (μ := (volume : Measure Coord))
        (fun x => g x * (φ (x - a) : ℂ)) a
      simpa using this
    have e2 : ∫ x, g x * (φ (x - a) : ℂ) = ∫ x, u x * (coordTranspose v dZero φ (x - a) : ℂ) := by
      rw [h.2 _ hφ']
      congr 1
      funext x
      rw [hCTs]
    have e3 : ∫ x, u x * (coordTranspose v dZero φ (x - a) : ℂ) =
        ∫ x, u (x + a) * (coordTranspose v dZero φ x : ℂ) := by
      have := integral_add_right_eq_self (μ := (volume : Measure Coord))
        (fun x => u x * (coordTranspose v dZero φ (x - a) : ℂ)) a
      simp only [add_sub_cancel_right] at this
      exact this.symm
    have e4 : ∫ x, u (x + a) * (coordTranspose v dZero φ x : ℂ) =
        ∫ x, u x * (coordTranspose v dZero φ x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hu'] with x hx
      by_cases hxU : x ∈ U
      · rw [hx hxU]
      · rw [hCT0 φ hφ x hxU]
        simp
    have e5 := h.2 φ hφ
    have hfun : (fun x => φ x • (g (x + a) - g x)) =
        fun x => g (x + a) * (φ x : ℂ) - g x * (φ x : ℂ) := by
      funext x
      rw [Complex.real_smul]
      ring
    rw [hfun, integral_sub i1 i2, e1, e2, e3, e4, ← e5, sub_self]
  have hfund := hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hint
  rw [hUeq, ae_restrict_iff' hUo.measurableSet]
  filter_upwards [hfund] with x hx hxU
  rw [hq]
  exact sub_eq_zero.mp (hx hxU)

/-! ## 4. Slicing the weak derivative identity -/

/-- The product test `χ(t) ψ(y)`. -/
def tprod (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) : Coord → ℝ := fun p => χ p.1 * ψ p.2

theorem tsupport_tprod_subset (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) :
    tsupport (tprod χ ψ) ⊆ tsupport χ ×ˢ tsupport ψ := by
  refine closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport ψ))
  intro p hp
  simp only [Function.mem_support, tprod] at hp
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hp), subset_tsupport _ (right_ne_zero_of_mul hp)⟩

theorem isCoordTest_tprod {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioi 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : IsCoordTest (tprod χ ψ) := by
  have hK : IsCompact (tsupport χ ×ˢ tsupport ψ) := hχc.isCompact.prod hψc.isCompact
  refine ⟨(hχ.comp contDiff_fst).mul (hψ.comp contDiff_snd), ?_, ?_⟩
  · exact hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_tprod_subset χ ψ)
  · exact (tsupport_tprod_subset χ ψ).trans (prod_mono hχs (subset_univ _))

theorem cpd_tprod {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (e : ℝ × ℝ) (p : Coord) :
    fderiv ℝ (tprod χ ψ) p (0, e) = χ p.1 * fderiv ℝ ψ p.2 e := by
  have h1 : HasFDerivAt (fun p : Coord => χ p.1)
      ((deriv χ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hχ p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : Coord => ψ p.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hψ p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h12 : HasFDerivAt (tprod χ ψ)
      (χ p.1 • (fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        ψ p.2 • (deriv χ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p := h1.mul h2
  rw [h12.fderiv]
  simp

theorem fderiv_kern_sub (n : ℕ) (x y e : ℝ × ℝ) :
    fderiv ℝ (fun y => kern n (x - y)) y e = -(fderiv ℝ (kern n) (x - y) e) := by
  have hd := ((kern_contDiff1 n).differentiable (by norm_num) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change (fderiv ℝ (kern n ∘ (fun z : ℝ × ℝ => x - z)) y) e = _
  rw [hd.fderiv]
  simp

theorem slice_ident {v : Coord → Fin 3 → ℝ} {j : Fin 3} {e : ℝ × ℝ} (hcd : cdir j = (0, e))
    (hv : ∀ φ x, coordTranspose v dZero φ x = -cpd j φ x) {u g : Coord → ℂ}
    (h : HasWeakFO v dZero u g) (x : ℝ × ℝ) (n : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ y, (kern n (x - y) : ℂ) * g (t, y) =
        ∫ y, ((fderiv ℝ (kern n) (x - y) e : ℝ) : ℂ) * u (t, y) := by
  set ψ : ℝ × ℝ → ℝ := fun y => kern n (x - y) with hψ
  have hψs : ContDiff ℝ ∞ ψ := (kern_contDiff n).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ :=
    (kern_hasCompactSupport n).comp_homeomorph (Homeomorph.subLeft x)
  have hCT : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → ∀ p : Coord,
      coordTranspose v dZero (tprod χ ψ) p = χ p.1 * fderiv ℝ (kern n) (x - p.2) e := by
    intro χ hχ p
    rw [hv, cpd, hcd, cpd_tprod (hχ.differentiable (by simp)) (hψs.differentiable (by simp)),
      hψ, fderiv_kern_sub]
    ring
  set A : ℝ → ℂ := fun t => ∫ y, (kern n (x - y) : ℂ) * g (t, y) with hA
  set B : ℝ → ℂ := fun t => ∫ y, ((fderiv ℝ (kern n) (x - y) e : ℝ) : ℂ) * u (t, y) with hB
  have key : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioi 0 →
      Integrable (fun t => (χ t : ℂ) * A t) ∧ Integrable (fun t => (χ t : ℂ) * B t) ∧
        ∫ t, (χ t : ℂ) * A t = ∫ t, (χ t : ℂ) * B t := by
    intro χ hχ hχc hχs
    have hT := isCoordTest_tprod hχ hχc hχs hψs hψc
    obtain ⟨hI1, hI2⟩ := h.1 _ hT
    have hE := h.2 _ hT
    have hgA : (fun t => (χ t : ℂ) * A t) =
        fun t => ∫ y, g (t, y) * (tprod χ ψ (t, y) : ℂ) := by
      funext t
      simp only [hA]
      rw [← integral_const_mul]
      congr 1
      funext y
      simp only [tprod, hψ]
      push_cast
      ring
    have huB : (fun t => (χ t : ℂ) * B t) =
        fun t => ∫ y, u (t, y) * (coordTranspose v dZero (tprod χ ψ) (t, y) : ℂ) := by
      funext t
      simp only [hB]
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [hCT χ hχ (t, y)]
      push_cast
      ring
    have hI2' : Integrable (fun p : ℝ × (ℝ × ℝ) => g p * (tprod χ ψ p : ℂ))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
      rw [← Measure.volume_eq_prod]
      exact hI2
    have hI1' : Integrable
        (fun p : ℝ × (ℝ × ℝ) => u p * (coordTranspose v dZero (tprod χ ψ) p : ℂ))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
      rw [← Measure.volume_eq_prod]
      exact hI1
    refine ⟨?_, ?_, ?_⟩
    · rw [hgA]
      exact hI2'.integral_prod_left
    · rw [huB]
      exact hI1'.integral_prod_left
    · rw [hgA, huB, ← integral_prod _ hI2', ← integral_prod _ hI1', ← Measure.volume_eq_prod]
      exact hE
  have hloc : LocallyIntegrableOn (fun t => A t - B t) (Ioi 0) volume := by
    intro t₀ ht₀
    have ht₀' : (0 : ℝ) < t₀ := ht₀
    let β : ContDiffBump t₀ :=
      { rIn := t₀ / 4
        rOut := t₀ / 2
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    have hβs : tsupport β ⊆ Ioi 0 := by
      rw [β.tsupport_eq]
      intro t ht
      rw [Metric.mem_closedBall, Real.dist_eq] at ht
      have := (abs_le.mp ht).1
      simp only [mem_Ioi]
      change -(t₀ / 2) ≤ t - t₀ at this
      linarith
    obtain ⟨hAi, hBi, -⟩ := key β β.contDiff β.hasCompactSupport hβs
    refine ⟨Metric.ball t₀ (t₀ / 4), ?_, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
    · refine (hAi.sub hBi).integrableOn.congr_fun (fun t ht => ?_) measurableSet_ball
      have h1 : β t = 1 := β.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)
      simp only [Pi.sub_apply, h1, Complex.ofReal_one, one_mul]
  have hfund := (isOpen_Ioi (a := (0 : ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun χ hχ hχc hχs => by
      obtain ⟨hAi, hBi, hE⟩ := key χ hχ hχc hχs
      have hfun : (fun t => χ t • (A t - B t)) = fun t => (χ t : ℂ) * A t - (χ t : ℂ) * B t := by
        funext t
        rw [Complex.real_smul]
        ring
      rw [hfun, integral_sub hAi hBi, hE, sub_self])
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hfund] with t ht ht0
  exact sub_eq_zero.mp (ht ht0)

theorem slice_ident_all {v : Coord → Fin 3 → ℝ} {j : Fin 3} {e : ℝ × ℝ} (hcd : cdir j = (0, e))
    (hv : ∀ φ x, coordTranspose v dZero φ x = -cpd j φ x) {u g : Coord → ℂ}
    (h : HasWeakFO v dZero u g) {D : Set (ℝ × ℝ)} (hDc : D.Countable) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n : ℕ, ∀ x ∈ D,
      ∫ y, (kern n (x - y) : ℂ) * g (t, y) =
        ∫ y, ((fderiv ℝ (kern n) (x - y) e : ℝ) : ℂ) * u (t, y) := by
  haveI : Countable D := hDc.to_subtype
  have hall : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ p : ℕ × D,
      ∫ y, (kern p.1 ((p.2 : ℝ × ℝ) - y) : ℂ) * g (t, y) =
        ∫ y, ((fderiv ℝ (kern p.1) ((p.2 : ℝ × ℝ) - y) e : ℝ) : ℂ) * u (t, y) :=
    ae_all_iff.2 (fun p => slice_ident hcd hv h p.2 p.1)
  filter_upwards [hall] with t ht n x hx
  exact ht (n, ⟨x, hx⟩)

/-! ## 5. Slices of periodic profiles -/

theorem slice_aper {c : ℝ} {f : Coord → ℂ}
    (hf : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), f (qShift c x) = f x) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), APer c (fun y => f (t, y)) := by
  have hprod : volume.restrict {x : Coord | 0 < x.1} =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ)) := by
    have hset : {x : Coord | 0 < x.1} = Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
      ext x
      simp
    rw [hset, ← Measure.restrict_univ (μ := (volume : Measure (ℝ × ℝ))), Measure.prod_restrict,
      Measure.volume_eq_prod]
  rw [hprod] at hf
  filter_upwards [Measure.ae_ae_of_ae_prod hf] with t ht
  unfold APer
  filter_upwards [ht] with y hy
  have e : ((t, y + (c, 0)) : Coord) = qShift c (t, y) := by
    simp only [qShift]
    ext <;> simp
  rw [e, hy]

/-! ## 6. The slice Sobolev embedding -/

theorem norm_le_comp_add (w : EuclideanSpace ℂ (Fin 2)) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  calc Real.sqrt (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2) ≤ Real.sqrt ((‖w 0‖ + ‖w 1‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (w 0), norm_nonneg (w 1)])
    _ = ‖w 0‖ + ‖w 1‖ := Real.sqrt_sq (by positivity)

theorem sliceSobolev_proof : SliceSobolev := by
  refine ⟨2 * planeK + 1, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) planeK_ne_top,
    by norm_num⟩, ?_⟩
  intro c hc u uq uη hpu hmu hmq hmη hwq hwη
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℝ)
  have hpu_i : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      u (qShift c x) i = u x i := fun i => by
    filter_upwards [hpu] with x hx
    rw [hx]
  have hpq_i : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      uq (qShift c x) i = uq x i := fun i => qper_of_weak ct_vQ0 (hwq i) (hpu_i i)
  have hpη_i : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      uη (qShift c x) i = uη x i := fun i => qper_of_weak ct_vEta (hwη i) (hpu_i i)
  have hidq : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n : ℕ, ∀ x ∈ D,
      ∫ y, (kern n (x - y) : ℂ) * uq (t, y) i =
        ∫ y, ((fderiv ℝ (kern n) (x - y) (1, 0) : ℝ) : ℂ) * u (t, y) i := fun i =>
    slice_ident_all (j := 1) (e := (1, 0)) rfl ct_vQ0 (hwq i) hDc
  have hidη : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n : ℕ, ∀ x ∈ D,
      ∫ y, (kern n (x - y) : ℂ) * uη (t, y) i =
        ∫ y, ((fderiv ℝ (kern n) (x - y) (0, 1) : ℝ) : ℂ) * u (t, y) i := fun i =>
    slice_ident_all (j := 2) (e := (0, 1)) rfl ct_vEta (hwη i) hDc
  filter_upwards [hidq 0, hidq 1, hidη 0, hidη 1,
    slice_aper (f := fun x => u x 0) (hpu_i 0), slice_aper (f := fun x => u x 1) (hpu_i 1),
    slice_aper (f := fun x => uq x 0) (hpq_i 0), slice_aper (f := fun x => uq x 1) (hpq_i 1),
    slice_aper (f := fun x => uη x 0) (hpη_i 0), slice_aper (f := fun x => uη x 1) (hpη_i 1)]
    with t hq0 hq1 hη0 hη1 hu0 hu1 hq0' hq1' hη0' hη1'
  set S := sliceH1Norm c u uq uη t with hS
  have hKne : (2 * planeK + 1) ≠ 0 := by
    intro h0
    have := le_add_self (a := (1 : ℝ≥0∞)) (b := 2 * planeK)
    rw [h0] at this
    exact absurd this (by norm_num)
  by_cases hStop : S = ⊤
  · rw [hStop, ENNReal.mul_top hKne]
    exact le_top
  have hSlt : S < ⊤ := lt_top_iff_ne_top.2 hStop
  have hcell : B0579.cell c = strip (-(c / 2)) (c / 2) := rfl
  have hms : Measurable (fun y : ℝ × ℝ => ((t, y) : Coord)) := measurable_prodMk_left
  have hcompm : ∀ (f : Coord → CMerid), StronglyMeasurable f → ∀ i : Fin 2,
      AEStronglyMeasurable (fun y : ℝ × ℝ => f (t, y) i) volume := fun f hf i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).comp_stronglyMeasurable
      (hf.comp_measurable hms)).aestronglyMeasurable
  have hcomp_le : ∀ (f : Coord → CMerid) (i : Fin 2),
      eLpNorm (fun y : ℝ × ℝ => f (t, y) i) 2 (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun y : ℝ × ℝ => f (t, y)) 2 (volume.restrict (B0579.cell c)) := fun f i =>
    eLpNorm_mono (fun y => PiLp.norm_apply_le (f (t, y)) i)
  have hSu : eLpNorm (fun y : ℝ × ℝ => u (t, y)) 2 (volume.restrict (B0579.cell c)) ≤ S := by
    rw [hS, sliceH1Norm]
    exact le_self_add.trans le_self_add
  have hSq : eLpNorm (fun y : ℝ × ℝ => uq (t, y)) 2 (volume.restrict (B0579.cell c)) ≤ S := by
    rw [hS, sliceH1Norm]
    exact le_add_self.trans le_self_add
  have hSη : eLpNorm (fun y : ℝ × ℝ => uη (t, y)) 2 (volume.restrict (B0579.cell c)) ≤ S := by
    rw [hS, sliceH1Norm]
    exact le_add_self
  have hcomp : ∀ i : Fin 2,
      (∀ n : ℕ, ∀ x ∈ D, ∫ y, (kern n (x - y) : ℂ) * uq (t, y) i =
        ∫ y, ((fderiv ℝ (kern n) (x - y) (1, 0) : ℝ) : ℂ) * u (t, y) i) →
      (∀ n : ℕ, ∀ x ∈ D, ∫ y, (kern n (x - y) : ℂ) * uη (t, y) i =
        ∫ y, ((fderiv ℝ (kern n) (x - y) (0, 1) : ℝ) : ℂ) * u (t, y) i) →
      APer c (fun y => u (t, y) i) → APer c (fun y => uq (t, y) i) →
      APer c (fun y => uη (t, y) i) →
      eLpNorm (fun y => u (t, y) i) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) ≤
        planeK * S := by
    intro i h1 h2 a1 a2 a3
    have fu := ((hcomp_le u i).trans hSu).trans_lt hSlt
    have fq := ((hcomp_le uq i).trans hSq).trans_lt hSlt
    have fη := ((hcomp_le uη i).trans hSη).trans_lt hSlt
    rw [hcell] at fu fq fη
    have hb := plane_sobolev hc (hcompm u hmu i) (hcompm uq hmq i) (hcompm uη hmη i) a1 a2 a3
      fu fq fη hD h1 h2
    rw [hcell]
    calc eLpNorm (fun y => u (t, y) i) (ENNReal.ofReal bgp)
          (volume.restrict (strip (-(c / 2)) (c / 2)))
        = eLpNorm (fun y => u (t, y) i) (ENNReal.ofReal (11 / 4))
          (volume.restrict (strip (-(c / 2)) (c / 2))) := rfl
      _ ≤ _ := hb
      _ ≤ planeK * S := by
          gcongr
          rw [← hcell]
          calc _ ≤ eLpNorm (fun y : ℝ × ℝ => u (t, y)) 2 (volume.restrict (B0579.cell c)) +
                eLpNorm (fun y : ℝ × ℝ => uq (t, y)) 2 (volume.restrict (B0579.cell c)) +
                eLpNorm (fun y : ℝ × ℝ => uη (t, y)) 2 (volume.restrict (B0579.cell c)) := by
                gcongr
                · exact hcomp_le u i
                · exact hcomp_le uq i
                · exact hcomp_le uη i
            _ = S := by rw [hS, sliceH1Norm]
  have hb0 := hcomp 0 hq0 hη0 hu0 hq0' hη0'
  have hb1 := hcomp 1 hq1 hη1 hu1 hq1' hη1'
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  calc eLpNorm (fun x => u (t, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c))
      ≤ eLpNorm (fun y => ‖u (t, y) 0‖ + ‖u (t, y) 1‖) (ENNReal.ofReal bgp)
          (volume.restrict (B0579.cell c)) :=
        eLpNorm_mono_real (fun y => norm_le_comp_add (u (t, y)))
    _ ≤ eLpNorm (fun y => ‖u (t, y) 0‖) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) +
          eLpNorm (fun y => ‖u (t, y) 1‖) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) :=
        eLpNorm_add_le ((hcompm u hmu 0).norm.restrict) ((hcompm u hmu 1).norm.restrict) hp1
    _ ≤ planeK * S + planeK * S := by
        simp only [eLpNorm_norm]
        exact add_le_add hb0 hb1
    _ = 2 * planeK * S := by ring
    _ ≤ (2 * planeK + 1) * S := by
        gcongr
        exact le_self_add

end UnforcedLeray.Short.IIb.FlatKH2
