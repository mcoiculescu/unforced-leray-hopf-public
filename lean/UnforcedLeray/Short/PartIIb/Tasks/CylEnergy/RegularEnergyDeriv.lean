import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Lib.Cylinder.Weight

/-!
# Part II-b, task `PartII-b:T22` leaf 3: the energy of a regular flow

Source of record: `the November 2 reference manuscript`, lines 2092-2101
(weighted integration by parts for the energy). Proves `RegularEnergyDeriv` by differentiation under
the integral sign, using the slope characterization of `HasDerivWithinAt` along `Ici τ` and
dominated convergence. The domination comes from the uniform decay in `IsRegularCylFlow`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The weight `jb^(m - 2N)` is integrable on the plane when `2N - m > 1`. -/
theorem regEnergyDeriv_integrable_jb (m N : ℝ) (h : 1 < N + N - m) :
    Integrable (fun x : B0579.Plane => B0579.jb x ^ (m - (N + N))) := by
  have hI := UnforcedLeray.Cyl.integrable_rpow_neg_ρc h
  have heq : (fun x : B0579.Plane => B0579.jb x ^ (m - (N + N))) =
      (fun z : B0579.Plane => UnforcedLeray.Cyl.ρc z ^ (-(N + N - m))) := by
    funext z
    rw [show -(N + N - m) = m - (N + N) by ring]
    rfl
  rw [heq]
  exact hI

/-- The density `w = jb^m` divided by `(jb^N)^2` is `jb^(m - 2N)`. -/
theorem regEnergyDeriv_rpow_eq (x : B0579.Plane) (m N : ℝ) :
    B0579.jb x ^ (m - (N + N)) = (B0579.density m x : ℝ) / (B0579.jb x ^ N * B0579.jb x ^ N) := by
  rw [B0579.coe_density, Real.rpow_sub (B0579.jb_pos x), Real.rpow_add (B0579.jb_pos x)]

/-- Pure real estimate: the integrand of the energy derivative and the energy integrand are
dominated by `K w / u²` when `|ω| u ≤ C`, `(|ω| + |∂₀ω| + |∂₁ω| + |Δω|) u ≤ C`, `|v_i| ≤ M`. -/
theorem regEnergyDeriv_pointwise (w0 p0 p1 L v0 v1 ν M u w C : ℝ) (hu : 0 < u) (hw : 0 ≤ w)
    (hdec : (|w0| + |p0| + |p1| + |L|) * u ≤ C) (hv0 : |v0| ≤ M) (hv1 : |v1| ≤ M)
    (hM0 : 0 ≤ M) :
    |2 * (w0 * (ν * L - (v0 * p0 + v1 * p1)) * w)| ≤
        ((2 * (|ν| + M) + 1) * C ^ 2) * (w / (u * u)) ∧
      |w0 ^ 2 * w| ≤ ((2 * (|ν| + M) + 1) * C ^ 2) * (w / (u * u)) := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = |w0| + |p0| + |p1| + |L| := ⟨_, rfl⟩
  rw [← hGdef] at hdec
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hC : 0 ≤ C := le_trans (mul_nonneg hG0 hu.le) hdec
  have hw0 : |w0| * u ≤ C := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hu.le) hdec
    rw [hGdef]
    linarith [abs_nonneg p0, abs_nonneg p1, abs_nonneg L]
  have hGu : G * u ≤ C := hdec
  have hV : |ν * L - (v0 * p0 + v1 * p1)| ≤ (|ν| + M) * G := by
    have h1 := abs_add_le (ν * L) (-(v0 * p0 + v1 * p1))
    have h2 := abs_add_le (v0 * p0) (v1 * p1)
    simp only [abs_mul, abs_neg] at h1 h2
    rw [← sub_eq_add_neg] at h1
    have f1 : |v0| * |p0| ≤ M * |p0| := mul_le_mul_of_nonneg_right hv0 (abs_nonneg _)
    have f2 : |v1| * |p1| ≤ M * |p1| := mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
    have g1 : |ν| * |L| ≤ |ν| * G :=
      mul_le_mul_of_nonneg_left (by rw [hGdef]; linarith [abs_nonneg w0, abs_nonneg p0, abs_nonneg p1])
        (abs_nonneg ν)
    have g2 : M * (|p0| + |p1|) ≤ M * G :=
      mul_le_mul_of_nonneg_left (by rw [hGdef]; linarith [abs_nonneg w0, abs_nonneg L]) hM0
    have g3 : M * (|p0| + |p1|) = M * |p0| + M * |p1| := mul_add M _ _
    rw [add_mul]
    linarith [h1, h2, f1, f2, g1, g2, g3]
  have hA0 : 0 ≤ 2 * (|ν| + M) := by linarith [abs_nonneg ν]
  have hpos2 : 0 < u * u := mul_pos hu hu
  have hX : 0 ≤ w / (u * u) := div_nonneg hw hpos2.le
  have hC2X : 0 ≤ C ^ 2 * (w / (u * u)) := mul_nonneg (sq_nonneg C) hX
  have hWG : |w0| * G ≤ C ^ 2 / (u * u) := by
    rw [le_div_iff₀ hpos2]
    calc |w0| * G * (u * u) = (|w0| * u) * (G * u) := by ring
      _ ≤ C * C := mul_le_mul hw0 hGu (mul_nonneg hG0 hu.le) hC
      _ = C ^ 2 := by ring
  have hWG2 : |w0| * G * w ≤ C ^ 2 * (w / (u * u)) := by
    calc |w0| * G * w ≤ (C ^ 2 / (u * u)) * w := mul_le_mul_of_nonneg_right hWG hw
      _ = C ^ 2 * (w / (u * u)) := by ring
  have hsq : w0 ^ 2 * (u * u) ≤ C ^ 2 := by
    have hw0sq : w0 ^ 2 = |w0| * |w0| := by rw [abs_mul_abs_self, sq]
    calc w0 ^ 2 * (u * u) = (|w0| * u) * (|w0| * u) := by rw [hw0sq]; ring
      _ ≤ C * C := mul_le_mul hw0 hw0 (mul_nonneg (abs_nonneg _) hu.le) hC
      _ = C ^ 2 := by ring
  have hWsq : w0 ^ 2 * w ≤ C ^ 2 * (w / (u * u)) := by
    have hw2 : w0 ^ 2 ≤ C ^ 2 / (u * u) := (le_div_iff₀ hpos2).2 hsq
    calc w0 ^ 2 * w ≤ (C ^ 2 / (u * u)) * w := mul_le_mul_of_nonneg_right hw2 hw
      _ = C ^ 2 * (w / (u * u)) := by ring
  constructor
  · have habs : |2 * (w0 * (ν * L - (v0 * p0 + v1 * p1)) * w)| =
        2 * (|w0| * |ν * L - (v0 * p0 + v1 * p1)|) * w := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hw]
      ring
    rw [habs]
    have h1 : |w0| * |ν * L - (v0 * p0 + v1 * p1)| ≤ |w0| * ((|ν| + M) * G) :=
      mul_le_mul_of_nonneg_left hV (abs_nonneg _)
    have h2 : 2 * (|w0| * |ν * L - (v0 * p0 + v1 * p1)|) * w ≤
        2 * (|ν| + M) * (|w0| * G * w) := by
      calc 2 * (|w0| * |ν * L - (v0 * p0 + v1 * p1)|) * w
          ≤ 2 * (|w0| * ((|ν| + M) * G)) * w :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hw
        _ = 2 * (|ν| + M) * (|w0| * G * w) := by ring
    have h3 : 2 * (|ν| + M) * (|w0| * G * w) ≤ 2 * (|ν| + M) * (C ^ 2 * (w / (u * u))) :=
      mul_le_mul_of_nonneg_left hWG2 hA0
    have h4 : ((2 * (|ν| + M) + 1) * C ^ 2) * (w / (u * u)) =
        2 * (|ν| + M) * (C ^ 2 * (w / (u * u))) + C ^ 2 * (w / (u * u)) := by ring
    linarith [h2, h3, h4, hC2X]
  · rw [abs_of_nonneg (mul_nonneg (sq_nonneg w0) hw)]
    have h5 : 0 ≤ 2 * (|ν| + M) * (C ^ 2 * (w / (u * u))) := mul_nonneg hA0 hC2X
    have h6 : ((2 * (|ν| + M) + 1) * C ^ 2) * (w / (u * u)) =
        2 * (|ν| + M) * (C ^ 2 * (w / (u * u))) + C ^ 2 * (w / (u * u)) := by ring
    linarith [hWsq, h5, hC2X, h6]

/-- The pointwise domination of the energy integrand and of the derivative integrand, for a
regular flow, with the bound `K jb^(m - 2N)`, `K = (2(|ν| + M) + 1) C²`. -/
theorem regEnergyDeriv_bound (c ν m M N C : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec)
    (ω : ℝ → B0579.Plane → ℝ) (s T : ℝ)
    (hMb : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |v σ x 0| + |v σ x 1| ≤ M)
    (hC : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
        B0579.jb x ^ N ≤ C)
    (r : ℝ) (hr : r ∈ Icc s T) (x : B0579.Plane) (hx : |x.1| ≤ c / 2) :
    |2 * (ω r x * (ν * lapP (ω r) x - (v r x 0 * B0579.pd 0 (ω r) x +
          v r x 1 * B0579.pd 1 (ω r) x)) * (B0579.density m x : ℝ))| ≤
        ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) ∧
    |ω r x ^ 2 * (B0579.density m x : ℝ)| ≤
        ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) := by
  have hv0 : |v r x 0| ≤ M := by
    have := hMb r hr x
    linarith [abs_nonneg (v r x 1)]
  have hv1 : |v r x 1| ≤ M := by
    have := hMb r hr x
    linarith [abs_nonneg (v r x 0)]
  have hM0 : 0 ≤ M := le_trans (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hMb r hr x)
  have hu : 0 < B0579.jb x ^ N := Real.rpow_pos_of_pos (B0579.jb_pos x) N
  have hw0 : 0 ≤ (B0579.density m x : ℝ) := (B0579.density_pos m x).le
  have hkey := regEnergyDeriv_pointwise (ω r x) (B0579.pd 0 (ω r) x) (B0579.pd 1 (ω r) x)
    (lapP (ω r) x) (v r x 0) (v r x 1) ν M (B0579.jb x ^ N) (B0579.density m x : ℝ) C hu hw0
    (hC r hr x hx) hv0 hv1 hM0
  rw [regEnergyDeriv_rpow_eq x m N]
  exact hkey

/-- **Leaf 3 (`RegularEnergyDeriv`).** Differentiation under the integral sign for the energy of a
regular flow: continuity on `[s, T]`, and the right derivative on `[s, T)`. -/
theorem regularEnergyDeriv : UnforcedLeray.Short.IIb.RegularEnergyDeriv := by
  intro c ν m s T v ω hc hω hM
  obtain ⟨M, hMb⟩ := hM
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = |m| + 2 := ⟨_, rfl⟩
  have hN1 : 1 < N + N - m := by
    rw [hNdef]
    linarith [le_abs_self m, abs_nonneg m]
  obtain ⟨C, hC⟩ := hω.cell_decay N
  have hbndI : IntegrableOn
      (fun x : B0579.Plane => ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)))
      (B0579.cell c) :=
    ((regEnergyDeriv_integrable_jb m N hN1).const_mul _).integrableOn
  have hcont_x : ∀ σ ∈ Icc s T, Continuous (ω σ) :=
    fun σ hσ => (hω.slice σ hσ).smooth.continuous
  have hdens_cont : Continuous fun x : B0579.Plane => (B0579.density m x : ℝ) := by
    simp only [B0579.coe_density]
    exact B0579.continuous_jb_rpow m
  have hjoint : ∀ x : B0579.Plane, ContinuousOn (fun σ => ω σ x) (Icc s T) := by
    intro x
    have h2 : ContinuousOn (fun σ : ℝ => (σ, x)) (Icc s T) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact hω.jointCont.comp h2 (fun σ hσ => ⟨hσ, mem_univ x⟩)
  have hFint : ∀ σ ∈ Icc s T,
      Integrable (fun x : B0579.Plane => ω σ x ^ 2 * (B0579.density m x : ℝ))
        (volume.restrict (B0579.cell c)) := by
    intro σ hσ
    refine Integrable.mono' hbndI ?_ ?_
    · exact (((hcont_x σ hσ).pow 2).mul hdens_cont).aestronglyMeasurable
    · refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (MeasureTheory.ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs]
      exact (regEnergyDeriv_bound c ν m M N C v ω s T hMb hC σ hσ x (abs_fst_le_of_mem_cell hx)).2
  have hcontE : ContinuousOn
      (fun σ => ∫ x in B0579.cell c, ω σ x ^ 2 * (B0579.density m x : ℝ)) (Icc s T) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun x => ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N))) ?_ ?_ hbndI ?_
    · intro σ hσ
      exact (((hcont_x σ hσ).pow 2).mul hdens_cont).aestronglyMeasurable
    · intro σ hσ
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (MeasureTheory.ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs]
      exact (regEnergyDeriv_bound c ν m M N C v ω s T hMb hC σ hσ x (abs_fst_le_of_mem_cell hx)).2
    · refine MeasureTheory.ae_of_all _ (fun x => ?_)
      exact ((hjoint x).pow 2).mul continuousOn_const
  refine ⟨hcontE, ?_⟩
  intro τ hτ
  obtain ⟨hsτ, hτT⟩ := hτ
  have hτI : τ ∈ Icc s T := ⟨hsτ, hτT.le⟩
  have hnhds : Icc s T ∈ 𝓝[Ici τ] τ :=
    Filter.mem_of_superset (Ico_mem_nhdsGE hτT) (fun y hy => ⟨le_trans hsτ hy.1, hy.2.le⟩)
  have hder_pt : ∀ x : B0579.Plane,
      HasDerivWithinAt (fun σ => ω σ x ^ 2 * (B0579.density m x : ℝ))
        (2 * (ω τ x * (ν * lapP (ω τ) x - (v τ x 0 * B0579.pd 0 (ω τ) x +
          v τ x 1 * B0579.pd 1 (ω τ) x)) * (B0579.density m x : ℝ)))
        (Ici τ) τ := by
    intro x
    have h1 : HasDerivWithinAt (fun r => ω r x)
        (ν * lapP (ω τ) x - (v τ x 0 * B0579.pd 0 (ω τ) x + v τ x 1 * B0579.pd 1 (ω τ) x))
        (Ici τ) τ :=
      (hω.pde τ hτI x).mono_of_mem_nhdsWithin hnhds
    have h2 := (h1.pow 2).mul_const (B0579.density m x : ℝ)
    exact h2.congr_deriv (by norm_num; ring)
  have hev : ∀ᶠ σ in 𝓝[Ici τ \ {τ}] τ, σ ∈ Ioo τ T := by
    have hsub : Ici τ \ {τ} ⊆ Ioi τ := fun y hy =>
      lt_of_le_of_ne hy.1 (fun h => hy.2 (Set.mem_singleton_iff.mpr h.symm))
    exact Filter.eventually_of_mem (nhdsWithin_mono τ hsub (Ioo_mem_nhdsGT hτT))
      (fun σ hσ => hσ)
  have hL : ∀ x : B0579.Plane,
      Tendsto (fun σ => (σ - τ)⁻¹ * (ω σ x ^ 2 * (B0579.density m x : ℝ) -
          ω τ x ^ 2 * (B0579.density m x : ℝ)))
        (𝓝[Ici τ \ {τ}] τ)
        (𝓝 (2 * (ω τ x * (ν * lapP (ω τ) x - (v τ x 0 * B0579.pd 0 (ω τ) x +
          v τ x 1 * B0579.pd 1 (ω τ) x)) * (B0579.density m x : ℝ)))) := by
    intro x
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (hder_pt x)
    exact Tendsto.congr (fun σ => by simp only [slope, smul_eq_mul, vsub_eq_sub]) h
  have hT : Tendsto
      (fun σ => ∫ x in B0579.cell c, (σ - τ)⁻¹ * (ω σ x ^ 2 * (B0579.density m x : ℝ) -
          ω τ x ^ 2 * (B0579.density m x : ℝ)))
      (𝓝[Ici τ \ {τ}] τ)
      (𝓝 (∫ x in B0579.cell c, 2 * (ω τ x * (ν * lapP (ω τ) x - (v τ x 0 * B0579.pd 0 (ω τ) x +
          v τ x 1 * B0579.pd 1 (ω τ) x)) * (B0579.density m x : ℝ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N))) ?_ ?_ hbndI ?_
    · filter_upwards [hev] with σ hσ
      have hσI : σ ∈ Icc s T := ⟨le_trans hsτ hσ.1.le, hσ.2.le⟩
      exact (continuous_const.mul ((((hcont_x σ hσI).pow 2).mul hdens_cont).sub
        (((hcont_x τ hτI).pow 2).mul hdens_cont))).aestronglyMeasurable
    · filter_upwards [hev] with σ hσ
      have hσI : σ ∈ Icc s T := ⟨le_trans hsτ hσ.1.le, hσ.2.le⟩
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (MeasureTheory.ae_of_all _ (fun x hx => ?_))
      have hpos : 0 < σ - τ := sub_pos.mpr hσ.1
      have hne : σ - τ ≠ 0 := hpos.ne'
      have hbd : ∀ r ∈ Icc τ σ,
          ‖2 * (ω r x * (ν * lapP (ω r) x - (v r x 0 * B0579.pd 0 (ω r) x +
            v r x 1 * B0579.pd 1 (ω r) x)) * (B0579.density m x : ℝ))‖ ≤
            ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) := by
        intro r hr
        have hrI : r ∈ Icc s T := ⟨le_trans hsτ hr.1, le_trans hr.2 hσ.2.le⟩
        rw [Real.norm_eq_abs]
        exact (regEnergyDeriv_bound c ν m M N C v ω s T hMb hC r hrI x (abs_fst_le_of_mem_cell hx)).1
      have hder : ∀ r ∈ Icc τ σ,
          HasDerivWithinAt (fun r' => ω r' x ^ 2 * (B0579.density m x : ℝ))
            (2 * (ω r x * (ν * lapP (ω r) x - (v r x 0 * B0579.pd 0 (ω r) x +
              v r x 1 * B0579.pd 1 (ω r) x)) * (B0579.density m x : ℝ)))
            (Icc τ σ) r := by
        intro r hr
        have hrI : r ∈ Icc s T := ⟨le_trans hsτ hr.1, le_trans hr.2 hσ.2.le⟩
        have h1 := (hω.pde r hrI x).mono (Icc_subset_Icc hsτ hσ.2.le)
        have h2 := (h1.pow 2).mul_const (B0579.density m x : ℝ)
        exact h2.congr_deriv (by norm_num; ring)
      have hmvt : ‖ω σ x ^ 2 * (B0579.density m x : ℝ) - ω τ x ^ 2 * (B0579.density m x : ℝ)‖ ≤
          ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) * ‖σ - τ‖ :=
        Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Icc τ σ)
          (left_mem_Icc.2 hσ.1.le) (right_mem_Icc.2 hσ.1.le)
      rw [Real.norm_of_nonneg hpos.le] at hmvt
      rw [norm_mul, norm_inv, Real.norm_of_nonneg hpos.le]
      calc (σ - τ)⁻¹ * ‖ω σ x ^ 2 * (B0579.density m x : ℝ) -
            ω τ x ^ 2 * (B0579.density m x : ℝ)‖
          ≤ (σ - τ)⁻¹ * (((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) * (σ - τ)) :=
            mul_le_mul_of_nonneg_left hmvt (inv_nonneg.2 hpos.le)
        _ = ((2 * (|ν| + M) + 1) * C ^ 2) * B0579.jb x ^ (m - (N + N)) := by
            field_simp
    · exact MeasureTheory.ae_of_all _ (fun x => hL x)
  have hEq : (slope (fun σ => cylEnergy c m (ω σ)) τ) =ᶠ[𝓝[Ici τ \ {τ}] τ]
      (fun σ => ∫ x in B0579.cell c, (σ - τ)⁻¹ * (ω σ x ^ 2 * (B0579.density m x : ℝ) -
          ω τ x ^ 2 * (B0579.density m x : ℝ))) := by
    filter_upwards [hev] with σ hσ
    have hσI : σ ∈ Icc s T := ⟨le_trans hsτ hσ.1.le, hσ.2.le⟩
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    unfold cylEnergy
    rw [integral_const_mul, integral_sub (hFint σ hσI) (hFint τ hτI)]
  rw [hasDerivWithinAt_iff_tendsto_slope, ← integral_const_mul]
  exact Tendsto.congr' hEq.symm hT

end UnforcedLeray.Short.IIb
