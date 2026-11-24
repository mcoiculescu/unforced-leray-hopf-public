import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1

/-!
# Decomposition of `sepWSmoothOn_of` (`PartIII-b:IIIb-D2/3/1/1/2`)

Source of record: `the November 2 reference manuscript`
3604-3621 (`sep:kernel`, `sep:resolvent`), 3631-3646 (`sep:young`, the Hölder / Cauchy-Schwarz
bookkeeping with `L^{22/19}_z`, `Re μ > -1/4`).

`sepW` is an iterated integral over `l ∈ (0,1)` then `z`.  On the product measure
`ρ = (vol|_{(0,1)}) ⊗ vol` it is `∫ Φ(l,z,y) dρ` with the explicit integrand `sepPhi`.  `C²` in `y`
near a point `y₀` of the gap `rOut < ϱ y` then follows from a generic parametric `C²` lemma
(`ParamContDiff`), the smoothness of `heatLerayK` (`HeatLerayKSmooth`), measurability
(`SepPhiMeasurable`), a pointwise bound from `sep:kernel` (`SepGapPointwise`, uses
`|y - l z| ≥ ϱ y - rOut` on the support of `T`) and integrability of the majorant
(`SepGapMajorantIntegrable`, Cauchy-Schwarz in `z` against the `L²_τL²_z` moment `SepMoment`,
then `L²` in `τ'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The product measure `(vol|_{(0,1)}) ⊗ vol` on `(l, z) ∈ ℝ × Space`. -/
def sepRho : Measure (ℝ × Space) := (volume.restrict (Ioo (0 : ℝ) 1)).prod volume

/-- The integrand of `sepW` (3611-3617) as a function of `p = (l, z)` and the observation point
`y`, with the factor `-2 l^{2μ+2}` included. -/
def sepPhi (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (p : ℝ × Space) (y : Space) : ℂ :=
  -2 * (p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
      (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)

/-- The explicit majorant `l^{2Re μ+2} (1 + l|z|)^{-4-n} |T(τ + 2 log l, z)|`. -/
def sepMajorant (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (p : ℝ × Space) : ℝ :=
  p.1 ^ (2 * μ.re + 2) * (1 + p.1 * ‖p.2‖) ^ (-(4 + (n : ℝ))) *
    IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)

/-- Generic `C²` dependence of a parametric integral on the parameter `y ∈ Space`
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`, applied twice). -/
def ParamContDiff : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (m : Measure α) (F : α → Space → ℂ) (U : Set Space)
    (g : ℕ → α → ℝ), IsOpen U → Convex ℝ U → (∀ᵐ a ∂m, ContDiffOn ℝ 2 (F a) U) →
    (∀ n, n ≤ 2 → Integrable (g n) m) →
    (∀ n, n ≤ 2 → ∀ᵐ a ∂m, ∀ y ∈ U, ‖iteratedFDeriv ℝ n (F a) y‖ ≤ g n a) →
    (∀ n, n ≤ 2 → ∀ y ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) y) m) →
    ContDiffOn ℝ 2 (fun y => ∫ a, F a y ∂m) U

/-- `K_t` is `C³` (indeed smooth) on all of `ℝ³` for `t > 0` (`heatG` and `∫_t^∞ G_a da` are smooth). -/
def HeatLerayKSmooth : Prop :=
  ∀ t : ℝ, 0 < t → ∀ i j : Fin 3, ContDiff ℝ 3 (fun x => IIIa.heatLerayK t i j x)

/-- Measurability of the `y`-derivatives of the integrand on `(0,1) × Space`
(joint smoothness of `(t,x) ↦ K_t(x)` on `t > 0` gives joint measurability). -/
def SepPhiMeasurable : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → IIIa.IsSepSource P rOut T → ∀ (τ : ℝ) (i : Fin 3) (n : ℕ), n ≤ 2 → ∀ y : Space,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y) sepRho

/-- **`sep:kernel` at the gap** (3604-3621): near `y₀` with `rOut < ϱ y₀`, for `l ∈ (0,1)`,
`|D^n_y Φ(l,z,y)| ≤ C l^{2Re μ+2}(1+l|z|)^{-4-n}|T|` (`n ≤ 2`).  Uses
`|D^j∇K_t(x)| ≤ C_j|x|^{-4-j}` uniformly in `t > 0`, and on `supp T`:
`|y - l z| ≥ ϱ y - rOut ≥ d > 0` and `|y - l z| ≥ l|z| - |y|`, so
`|y - l z| ≥ c(1 + l|z|)`; off the support `Φ(l,z,·) = 0`. -/
def SepGapPointwise : Prop :=
  IIIa.SepKernelBounds → ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P →
    IIIa.IsSepSource P rOut T → ∀ (τ : ℝ) (i : Fin 3) (y₀ : Space), rOut < ϱ y₀ →
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.ball y₀ ε, ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space,
        ∀ n : ℕ, n ≤ 2 →
          ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y‖ ≤ C * sepMajorant μ T τ n (l, z)

/-- **Cauchy-Schwarz step** (3631-3646 with `p = 2`, 3604-3621): for `P`-periodic `T` with finite
`L²_τ L²_z` moment (`SepMoment`) and `Re μ > -1/4`, the majorant is `ρ`-integrable.
`‖(1+l|·|)^{-4-n}‖_{L²_z} = l^{-3/2}‖(1+|·|)^{-4-n}‖_{L²}`, so after Cauchy-Schwarz in `z` the
`l`-integrand is `l^{2Re μ + 1/2} f(τ + 2 log l)`, `f(τ') = ‖T(τ',·)‖_{L²_z}` periodic and in
`L²(0,P)`; `l = e^{s}` and summation over periods converges since `2 Re μ + 3/2 > 0`. -/
def SepGapMajorantIntegrable : Prop :=
  ∀ (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), -(1 / 4) < μ.re → 0 < P →
    IIIa.IsSepSource P rOut T → SepMoment P T → ∀ (τ : ℝ) (n : ℕ), n ≤ 2 →
      Integrable (sepMajorant μ T τ n) sepRho

theorem sepW_eq_integral (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (y : Space) (h : Integrable (fun p => sepPhi ν μ T τ i p y) sepRho) :
    IIIa.sepW ν μ T y τ i = ∫ p, sepPhi ν μ T τ i p y ∂sepRho := by
  unfold sepRho at h ⊢
  rw [integral_prod _ h]
  unfold IIIa.sepW sepPhi
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

theorem ae_mem_Ioo_sepRho : ∀ᵐ p ∂sepRho, p.1 ∈ Ioo (0 : ℝ) 1 := by
  have h : sepRho {p : ℝ × Space | p.1 ∉ Ioo (0 : ℝ) 1} = 0 := by
    have : {p : ℝ × Space | p.1 ∉ Ioo (0 : ℝ) 1} = (Ioo (0 : ℝ) 1)ᶜ ×ˢ (univ : Set Space) := by
      ext p; simp
    rw [this, sepRho, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  exact measure_eq_zero_iff_ae_notMem.mp h |> fun h' => by
    filter_upwards [h'] with p hp
    simpa using hp

theorem sepPhi_contDiff (h2 : HeatLerayKSmooth) (ν : ℝ) (μ : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3) (l : ℝ) (z : Space)
    (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1) : ContDiff ℝ 2 (sepPhi ν μ T τ i (l, z)) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  unfold sepPhi
  refine contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_)
  refine ContDiff.mul ?_ contDiff_const
  have h1 : ContDiff ℝ 2 (fun x => fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) x) :=
    (h2 _ ht i j).fderiv_right (by norm_num)
  have h3 : ContDiff ℝ 2 (fun y : Space => y - l • z) := contDiff_id.sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp ((h1.comp h3).clm_apply contDiff_const)

theorem sepWSmoothOn_of_of (hK : IIIa.SepKernelBounds) (h1 : ParamContDiff)
    (h2 : HeatLerayKSmooth) (h3 : SepPhiMeasurable) (h4 : SepGapPointwise)
    (h5 : SepGapMajorantIntegrable) : SepWSmoothOn := by
  intro ν μ rOut P T hν hμ hr hP hS hM τ i
  refine contDiffOn_of_locally_contDiffOn fun y₀ hy₀ => ?_
  obtain ⟨ε, hε, C, hC0, hb⟩ := h4 hK ν μ rOut P T hν hμ hr hP hS τ i y₀ hy₀
  refine ⟨Metric.ball y₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable (fun p => C * sepMajorant μ T τ n p) sepRho :=
    fun n hn => (h5 μ P rOut T hμ hP hS hM τ n hn).const_mul C
  have hbound : ∀ n : ℕ, n ≤ 2 → ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ ε,
      ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y‖ ≤ C * sepMajorant μ T τ n p := by
    intro n hn
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y hy
    exact hb y hy p.1 hp p.2 n hn
  have key : ContDiffOn ℝ 2 (fun y => ∫ p, sepPhi ν μ T τ i p y ∂sepRho) (Metric.ball y₀ ε) :=
    h1 sepRho (sepPhi ν μ T τ i) (Metric.ball y₀ ε) (fun n p => C * sepMajorant μ T τ n p)
      Metric.isOpen_ball (convex_ball _ _)
      (by
        filter_upwards [ae_mem_Ioo_sepRho] with p hp
        exact (sepPhi_contDiff h2 ν μ T τ i p.1 p.2 hν hp).contDiffOn)
      hint hbound (fun n hn y _ => h3 ν μ P rOut T hν hS τ i n hn y)
  refine (key.mono inter_subset_right).congr fun y hy => ?_
  apply sepW_eq_integral
  have hm : AEStronglyMeasurable (fun p => sepPhi ν μ T τ i p y) sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (h3 ν μ P rOut T hν hS τ i 0 (by norm_num) y)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine Integrable.mono' (hint 0 (by norm_num)) hm ?_
  filter_upwards [hbound 0 (by norm_num)] with p hp
  have := hp y hy.2
  simpa [norm_iteratedFDeriv_zero] using this

end UnforcedLeray.Short.PartIIIb.Concrete
