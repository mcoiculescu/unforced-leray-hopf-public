import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `CutBounds`: scaling bounds of the radial cutoff

Source `the November 2 reference manuscript` lines 1470-1480 ("their drift
commutator is bounded on an escaping annulus"): `χₙ(y) = ψ(y/(n+1))`, so each `y`-derivative of
`χₙ` is `(n+1)⁻ᵏ` times the corresponding derivative of the fixed bump `ψ` at `y/(n+1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cb_sd_eq_zero_of_open {S : Set Space} (hS : IsOpen S) {f : Space → ℝ}
    (hf : ∀ y ∈ S, f y = 0) (j : Fin 3) : ∀ y ∈ S, sd j f y = 0 := by
  intro y hy
  have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hS.mem_nhds hy] with z hz using hf z hz
  simp [sd, hev.fderiv_eq]

theorem cb_gradC_eq_zero {a : Space → ℝ} {y : Space} (h : ∀ j, sd j a y = 0) :
    gradC a y = 0 := by
  ext j; simp [gradC, h j]

theorem cb_vanish_pkg {S : Set Space} (hS : IsOpen S) {f : Space → ℝ}
    (hf : ∀ k, ∀ y ∈ S, sd k f y = 0) :
    ∀ y ∈ S, gradC f y = 0 ∧ gradC (radS f) y = 0 ∧ gradC (lapS f) y = 0 ∧
      radS f y = 0 ∧ lapS f y = 0 ∧ ∀ k : Fin 3, sd k f y = 0 ∧ gradC (sd k f) y = 0 := by
  intro y hy
  have h2 : ∀ k l, ∀ z ∈ S, sd l (sd k f) z = 0 := fun k l => cb_sd_eq_zero_of_open hS (hf k) l
  have hr : ∀ z ∈ S, radS f z = 0 := fun z hz => by simp [radS, hf _ z hz]
  have hl : ∀ z ∈ S, lapS f z = 0 := fun z hz => by simp [lapS, h2 _ _ z hz]
  exact ⟨cb_gradC_eq_zero fun j => hf j y hy,
    cb_gradC_eq_zero fun j => cb_sd_eq_zero_of_open hS hr j y hy,
    cb_gradC_eq_zero fun j => cb_sd_eq_zero_of_open hS hl j y hy, hr y hy, hl y hy,
    fun k => ⟨hf k y hy, cb_gradC_eq_zero fun l => h2 k l y hy⟩⟩

theorem cb_norm_gradC_le (a : Space → ℝ) (y : Space) :
    ‖gradC a y‖ ≤ ∑ j : Fin 3, |sd j a y| := by
  have h : gradC a y = ∑ j : Fin 3, ((sd j a y : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ) := by
    ext i; simp [gradC, Pi.single_apply]
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp [norm_smul]

theorem cb_gradC_bound {a : Space → ℝ} {y : Space} {M : ℝ} (h : ∀ j, |sd j a y| ≤ M) :
    ‖gradC a y‖ ≤ 3 * M := by
  refine (cb_norm_gradC_le a y).trans ?_
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem cb_abs_mul_le {s t g M : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (hg : |g| ≤ M) :
    |s * g| ≤ t * M := by
  rw [abs_mul, abs_of_nonneg hs0]
  exact mul_le_mul hst hg (abs_nonneg _) (hs0.trans hst)

theorem cb_bdd_of_cs {g : Space → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    ∃ B, 0 ≤ B ∧ ∀ z, |g z| ≤ B := by
  obtain ⟨B, hB⟩ := bounded_of_compact hc hs
  exact ⟨B, (abs_nonneg _).trans (hB 0), hB⟩

theorem cb_bdd_fin {ι : Type} [Fintype ι] {g : ι → Space → ℝ}
    (h : ∀ i, ∃ B, 0 ≤ B ∧ ∀ z, |g i z| ≤ B) :
    ∃ B, 0 ≤ B ∧ ∀ i z, |g i z| ≤ B := by
  choose B hB0 hB using h
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB0 i, fun i z => (hB i z).trans ?_⟩
  exact Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)

theorem cb_cs_radS {f : Space → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (radS f) := by
  refine hf.mono' fun z hz => ?_
  by_contra hzt
  apply hz
  simp [radS, sd, fderiv_of_notMem_tsupport ℝ hzt]

theorem cb_cs_lapS {f : Space → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (lapS f) := by
  have : lapS f = ∑ j : Fin 3, sd j (sd j f) := by
    funext y
    simp [lapS]
  rw [this]
  exact HasCompactSupport.finset_sum fun j _ =>
    hasCompactSupport_sd (hasCompactSupport_sd hf j) j

theorem cb_contDiff_radS {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (radS u) :=
  ContDiff.sum fun j _ => (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.mul (contDiff_sd hu j)

theorem cb_contDiff_lapS {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (lapS u) :=
  ContDiff.sum fun j _ => contDiff_sd (contDiff_sd hu j) j

theorem cb_master {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ∃ M, 0 ≤ M ∧ ∀ (z : Space) (k l : Fin 3),
      |sd k u z| ≤ M ∧ |radS u z| ≤ M ∧ |lapS u z| ≤ M ∧ |sd l (sd k u) z| ≤ M ∧
      |sd l (radS u) z| ≤ M ∧ |sd l (lapS u) z| ≤ M := by
  obtain ⟨B1, h10, h1⟩ := cb_bdd_fin (g := fun k => sd k u) fun k =>
    cb_bdd_of_cs (contDiff_sd hu k).continuous (hasCompactSupport_sd hus k)
  obtain ⟨B2, h20, h2⟩ := cb_bdd_of_cs (cb_contDiff_radS hu).continuous (cb_cs_radS hus)
  obtain ⟨B3, h30, h3⟩ := cb_bdd_of_cs (cb_contDiff_lapS hu).continuous (cb_cs_lapS hus)
  obtain ⟨B4, h40, h4⟩ := cb_bdd_fin (g := fun p : Fin 3 × Fin 3 => sd p.2 (sd p.1 u)) fun p =>
    cb_bdd_of_cs (contDiff_sd (contDiff_sd hu p.1) p.2).continuous
      (hasCompactSupport_sd (hasCompactSupport_sd hus p.1) p.2)
  obtain ⟨B5, h50, h5⟩ := cb_bdd_fin (g := fun l => sd l (radS u)) fun l =>
    cb_bdd_of_cs (contDiff_sd (cb_contDiff_radS hu) l).continuous
      (hasCompactSupport_sd (cb_cs_radS hus) l)
  obtain ⟨B6, h60, h6⟩ := cb_bdd_fin (g := fun l => sd l (lapS u)) fun l =>
    cb_bdd_of_cs (contDiff_sd (cb_contDiff_lapS hu) l).continuous
      (hasCompactSupport_sd (cb_cs_lapS hus) l)
  refine ⟨B1 + B2 + B3 + B4 + B5 + B6, by positivity, fun z k l => ?_⟩
  exact ⟨(h1 k z).trans (by linarith), (h2 z).trans (by linarith), (h3 z).trans (by linarith),
    (h4 (k, l) z).trans (by linarith), (h5 l z).trans (by linarith),
    (h6 l z).trans (by linarith)⟩

theorem cb_sd_scale {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (s c : ℝ) (j : Fin 3) :
    sd j (fun y => s * u (c • y)) = fun y => s * c * sd j u (c • y) := by
  have hgc : Differentiable ℝ (fun y : Space => u (c • y)) :=
    (hu.differentiable (by simp)).comp (differentiable_id.const_smul c)
  rw [sd_const_mul hgc, sd_comp_smul (hu.differentiable (by simp))]
  funext y
  simp [mul_assoc]

theorem cb_radS_scale {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    radS (fun y => u (c • y)) = fun y => radS u (c • y) := by
  funext y
  simp only [radS, sd_comp_smul (hu.differentiable (by simp)), PiLp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cb_lapS_scale {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    lapS (fun y => u (c • y)) = fun y => c ^ 2 * lapS u (c • y) := by
  funext y
  have h1 : ∀ j, sd j (fun y => u (c • y)) = fun y => 1 * c * sd j u (c • y) := by
    intro j
    simpa using sd_comp_smul (hu.differentiable (by simp)) c j
  have h2 : ∀ j, sd j (sd j (fun y => u (c • y))) y = c ^ 2 * sd j (sd j u) (c • y) := by
    intro j
    have e : sd j (fun y => u (c • y)) = fun y => c * sd j u (c • y) := by
      simpa using h1 j
    rw [e, cb_sd_scale (contDiff_sd hu j) c c j]
    ring
  simp only [lapS, h2, Finset.mul_sum]

theorem cb_scale_bounds {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ∃ B, 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ y : Space,
      ‖gradC (fun y => u (c • y)) y‖ ≤ B * c ∧
      ‖gradC (radS (fun y => u (c • y))) y‖ ≤ B * c ∧
      ‖gradC (lapS (fun y => u (c • y))) y‖ ≤ B * c ∧
      |radS (fun y => u (c • y)) y| ≤ B ∧ |lapS (fun y => u (c • y)) y| ≤ B ∧
      ∀ k : Fin 3, |sd k (fun y => u (c • y)) y| ≤ B ∧
        ‖gradC (sd k (fun y => u (c • y))) y‖ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := cb_master hu hus
  refine ⟨3 * M, by positivity, fun c hc0 hc1 y => ?_⟩
  have hcc : c * c ≤ 1 := by nlinarith
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hc3 : c ^ 2 * c ≤ c := by nlinarith
  have e1 : ∀ j, sd j (fun y => u (c • y)) = fun y => c * sd j u (c • y) := fun j => by
    simpa using sd_comp_smul (hu.differentiable (by simp)) c j
  refine ⟨?_, ?_, ?_, ?_, ?_, fun k => ⟨?_, ?_⟩⟩
  · have := cb_gradC_bound (a := fun y => u (c • y)) (y := y) (M := c * M) fun j => by
      rw [e1 j]
      exact cb_abs_mul_le hc0 le_rfl (hM _ j 0).1
    linarith
  · have e : radS (fun y => u (c • y)) = fun y => 1 * radS u (c • y) := by
      rw [cb_radS_scale hu]; simp
    have := cb_gradC_bound (a := radS (fun y => u (c • y))) (y := y) (M := c * M) fun j => by
      rw [e, cb_sd_scale (cb_contDiff_radS hu) 1 c j]
      simp only [one_mul]
      exact cb_abs_mul_le hc0 le_rfl (hM _ 0 j).2.2.2.2.1
    linarith
  · have e : lapS (fun y => u (c • y)) = fun y => c ^ 2 * lapS u (c • y) := cb_lapS_scale hu c
    have := cb_gradC_bound (a := lapS (fun y => u (c • y))) (y := y) (M := c * M) fun j => by
      rw [e, cb_sd_scale (cb_contDiff_lapS hu) (c ^ 2) c j]
      exact cb_abs_mul_le (by positivity) hc3 (hM _ 0 j).2.2.2.2.2
    linarith
  · rw [cb_radS_scale hu]
    exact (hM _ 0 0).2.1.trans (by linarith)
  · rw [cb_lapS_scale hu]
    exact (cb_abs_mul_le (by positivity) hc2 (hM _ 0 0).2.2.1).trans (by nlinarith)
  · rw [e1 k]
    exact (cb_abs_mul_le hc0 hc1 (hM _ k 0).1).trans (by nlinarith)
  · have := cb_gradC_bound (a := sd k (fun y => u (c • y))) (y := y) (M := c * c * M) fun l => by
      rw [e1 k, cb_sd_scale (contDiff_sd hu k) c c l]
      exact cb_abs_mul_le (mul_nonneg hc0 hc0) le_rfl (hM _ k l).2.2.2.1
    nlinarith

/-- **Scaling bounds of the cutoff** (source 1470-1480). -/
theorem cutBounds : CutBounds := by
  obtain ⟨B, hB0, hB⟩ := cb_scale_bounds contDiff_unitBump unitBump.hasCompactSupport
  refine ⟨B, hB0, fun n y => ?_⟩
  have hcut : cutχ n = fun y => (unitBump : Space → ℝ) (cutC n • y) := rfl
  have hBc : B * cutC n = B / ((n : ℝ) + 1) := by simp [cutC, div_eq_mul_inv]
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcn : cutC n * ((n : ℝ) + 1) = 1 := by simp [cutC]; field_simp
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB (cutC n) (cutC_pos n).le (cutC_le_one n) y
  rw [← hcut] at b1 b2 b3 b4 b5 b6
  rw [hBc] at b1 b2 b3
  refine ⟨?_, b1, b2, b3, b4, b5, b6⟩
  rintro (hy | hy)
  · refine cb_vanish_pkg (S := {z : Space | ‖z‖ < (n : ℝ) + 1}) (isOpen_lt continuous_norm continuous_const)
      (f := cutχ n) (fun k z hz => ?_) y hy
    rw [hcut, sd_comp_smul (contDiff_unitBump.differentiable (by simp)) (cutC n) k]
    have : ‖cutC n • z‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutC_pos n)]
      have : cutC n * ‖z‖ < cutC n * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left hz (cutC_pos n)
      linarith
    simp [sd_unitBump_eq_zero this k]
  · refine cb_vanish_pkg (S := {z : Space | 2 * ((n : ℝ) + 1) < ‖z‖})
      (isOpen_lt continuous_const continuous_norm) (f := cutχ n) (fun k z hz => ?_) y hy
    exact cb_sd_eq_zero_of_open (isOpen_lt continuous_const continuous_norm)
      (fun w hw => cutχ_eq_zero n (le_of_lt hw)) k z hz

end UnforcedLeray.Short.PartIIIb.Concrete
