import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.Mink
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.Bridge

/-!
# Right derivative of the heat factor on `C²` phase tests

For a `C²` phase test `ψ` with representatives `Ψ` of `ψ` and `ΨΔ` of `Δ_xψ` (`lapT`):
`d/dθ|_{0+} e^{θΔ}Ψ = ΨΔ` in `X`. Route: the heat FTC (`Heat.average_sub_eq_integral`) on each
slice gives `e^{θΔ}ψ - ψ - θΔψ = ∫_0^θ (e^{sΔ}Δψ - Δψ) ds` pointwise; Minkowski's integral
inequality bounds its `X`-norm by `θ · sup_{0<s≤θ} ‖e^{sΔ}ΨΔ - ΨΔ‖`, which is `o(θ)` by strong
continuity of the heat semigroup.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.Short.PartIIIb.NearInst (XC cellFn mink_joint odhtBridge)
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0223 (PSpace SpaceC ιx)

/-! ### Slices -/

theorem slice_contDiff2 {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ 2 ψ) (τ : ℝ) :
    ContDiff ℝ 2 (fun y : Space => ψ (τ, y)) :=
  hψ.comp (contDiff_const.prodMk contDiff_id)

theorem fderiv_fderiv_apply_eq2 {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ 2 ψ)
    (p v w : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ ψ q v) p w = fderiv ℝ (fderiv ℝ ψ) p w v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ ψ) p :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) p
  have hA : HasFDerivAt (fun q => fderiv ℝ ψ q v)
      ((ContinuousLinearMap.apply ℝ CVec3 v).comp (fderiv ℝ (fderiv ℝ ψ) p)) p :=
    (ContinuousLinearMap.apply ℝ CVec3 v).hasFDerivAt.comp p hc.hasFDerivAt
  rw [hA.fderiv]
  rfl

theorem slice_iteratedFDeriv_two {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ 2 ψ) (τ : ℝ)
    (x : Space) :
    iteratedFDeriv ℝ 2 (fun y => ψ (τ, y)) x
      = (iteratedFDeriv ℝ 2 ψ (τ, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hc : ContDiff ℝ 2 (fun q : ℝ × Space => (τ, (0 : Space)) + q) :=
    contDiff_const.add contDiff_id
  have hf : ContDiff ℝ 2 (fun q : ℝ × Space => ψ ((τ, (0 : Space)) + q)) :=
    hψ.comp hc
  have h1 : (fun y : Space => ψ (τ, y))
      = (fun q : ℝ × Space => ψ ((τ, (0 : Space)) + q)) ∘ ContinuousLinearMap.inr ℝ ℝ Space := by
    funext y
    simp
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (i := 2)
    (ContinuousLinearMap.inr ℝ ℝ Space) hf x (by simp)]
  rw [iteratedFDeriv_comp_add_left (f := ψ)]
  simp

theorem lapT_eq_vlap_slice2 {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ 2 ψ) (τ : ℝ) (z : Space) :
    lapT ψ (τ, z) = UnforcedLeray.Heat.vlap (fun y => ψ (τ, y)) z := by
  have hdy : ∀ (j : Fin 3) (p : ℝ × Space),
      dy j (dy j ψ) p
        = iteratedFDeriv ℝ 2 ψ p
            ![(0, UnforcedLeray.coordinateVector j), (0, UnforcedLeray.coordinateVector j)] := by
    intro j p
    rw [iteratedFDeriv_two_apply]
    simp only [dy, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact fderiv_fderiv_apply_eq2 hψ p _ _
  have hslice : ∀ i : Fin 3,
      iteratedFDeriv ℝ 2 (fun y => ψ (τ, y)) z
          ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector i]
        = iteratedFDeriv ℝ 2 ψ (τ, z)
          ![(0, UnforcedLeray.coordinateVector i), (0, UnforcedLeray.coordinateVector i)] := by
    intro i
    rw [slice_iteratedFDeriv_two hψ τ z, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext m
    fin_cases m <;> simp
  simp only [lapT, UnforcedLeray.Heat.vlap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdy j (τ, z), hslice j]

theorem slice_bound2 {P : ℝ} {ψ : ℝ × Space → CVec3} (hψ : IsPhaseTest2 P ψ) (τ : ℝ) :
    ∃ M : ℝ, ∀ k : ℕ, k ≤ 2 → ∀ x : Space,
      ‖iteratedFDeriv ℝ k (fun y => ψ (τ, y)) x‖ ≤ M := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  have hcs : HasCompactSupport (fun y : Space => ψ (τ, y)) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => by
      refine hR τ y ?_
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  have hs := slice_contDiff2 hψ.smooth τ
  have hb : ∀ k : ℕ, k ≤ 2 → ∃ C : ℝ, ∀ x : Space,
      ‖iteratedFDeriv ℝ k (fun y => ψ (τ, y)) x‖ ≤ C := by
    intro k hk
    exact (hs.continuous_iteratedFDeriv (by exact_mod_cast hk)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv k)
  obtain ⟨C0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hb 2 le_rfl
  refine ⟨max C0 (max C1 C2), fun k hk x => ?_⟩
  interval_cases k
  · exact (h0 x).trans (le_max_left _ _)
  · exact (h1 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-! ### Pointwise heat Duhamel -/

theorem heat_pointwise2 {P : ℝ} [Fact (0 < P)] {ψ : ℝ × Space → CVec3}
    (hψ : IsPhaseTest2 P ψ) {θ : ℝ} (hθ : 0 < θ) (z : PSpace P) :
    UnforcedLeray.Heat.heatConv (ιx P) θ (cellFn ψ) z - cellFn ψ z - θ • cellFn (lapT ψ) z
      = ∫ s in Ioc (0 : ℝ) θ,
          (UnforcedLeray.Heat.heatConv (ιx P) s (cellFn (lapT ψ)) z - cellFn (lapT ψ) z) := by
  set τ : ℝ := (UnforcedLeray.B0223.toCell P z).2
  set x : Space := (UnforcedLeray.B0223.toCell P z).1
  have hB : ∀ (g : ℝ × Space → SpaceC) (s : ℝ),
      UnforcedLeray.Heat.heatConv (ιx P) s (cellFn g) z
        = UnforcedLeray.Heat.average s (fun y : Space => g (τ, y)) x :=
    fun g s => odhtBridge P g s z
  have hc : ∀ g : ℝ × Space → SpaceC, cellFn g z = g (τ, x) := fun g => rfl
  simp only [hB, hc]
  obtain ⟨M, hM⟩ := slice_bound2 hψ τ
  have hu2 := slice_contDiff2 hψ.smooth τ
  have hF := UnforcedLeray.Heat.average_sub_eq_integral hu2 hM hθ x
  have hvl : UnforcedLeray.Heat.vlap (fun y : Space => ψ (τ, y)) = fun y => lapT ψ (τ, y) :=
    funext fun y => (lapT_eq_vlap_slice2 hψ.smooth τ y).symm
  rw [hvl] at hF
  have hvc : Continuous fun y : Space => lapT ψ (τ, y) :=
    hψ.continuous_lapT.comp (continuous_const.prodMk continuous_id)
  have hvb : ∀ y : Space, ‖lapT ψ (τ, y)‖ ≤ 3 * M := by
    intro y
    rw [← congrFun hvl y]
    exact UnforcedLeray.Heat.norm_vlap_le (hM 2 le_rfl) y
  have hfc : ContinuousOn (fun s : ℝ => UnforcedLeray.Heat.average s
      (fun y : Space => lapT ψ (τ, y)) x) (Ioi 0) :=
    UnforcedLeray.Heat.continuousOn_average_time_of_bound hvc.aestronglyMeasurable hvb x
  have hint : IntervalIntegrable (fun s : ℝ => UnforcedLeray.Heat.average s
      (fun y : Space => lapT ψ (τ, y)) x) volume 0 θ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.le]
    refine ⟨(hfc.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc, ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := 3 * M) measure_Ioc_lt_top ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact UnforcedLeray.Heat.norm_average_le_of_bound ht.1 hvb x
  have hsplit : ∫ s in (0 : ℝ)..θ,
      (UnforcedLeray.Heat.average s (fun y : Space => lapT ψ (τ, y)) x - lapT ψ (τ, x))
      = (∫ s in (0 : ℝ)..θ, UnforcedLeray.Heat.average s (fun y : Space => lapT ψ (τ, y)) x)
        - θ • lapT ψ (τ, x) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  rw [← intervalIntegral.integral_of_le hθ.le, hsplit, ← hF]

/-! ### Minkowski step -/

theorem heat_mink2 {P : ℝ} [Fact (0 < P)] (w : PSpace P → SpaceC) (hw : Measurable w)
    {θ : ℝ} (hθ : 0 < θ) (W : XC P) (hWw : (W : PSpace P → SpaceC) =ᵐ[volume] w) {B : ℝ}
    (hB : ∀ s ∈ Ioc (0 : ℝ) θ,
      ‖UnforcedLeray.B0223.heatC (E := SpaceC) s W - W‖ ≤ B)
    (R : XC P)
    (hR : (R : PSpace P → SpaceC) =ᵐ[volume] fun z => ∫ s in Ioc (0 : ℝ) θ,
      (UnforcedLeray.Heat.heatConv (ιx P) s w z - w z)) :
    ‖R‖ ≤ θ * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB θ ⟨hθ, le_rfl⟩)
  have hG : Measurable (fun q : ℝ × PSpace P =>
      UnforcedLeray.Heat.heatConv (ιx P) q.1 w q.2 - w q.2) :=
    (mink_joint P w hw).sub (hw.comp measurable_snd)
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (z : PSpace P) (s : ℝ) =>
        UnforcedLeray.Heat.heatConv (ιx P) s w z - w z)
      ((volume : Measure (PSpace P)).prod (volume.restrict (Ioc (0 : ℝ) θ))) :=
    (hG.comp measurable_swap).aestronglyMeasurable
  have hslice : ∀ s ∈ Ioc (0 : ℝ) θ,
      eLpNorm (fun z => UnforcedLeray.Heat.heatConv (ιx P) s w z - w z) 2
        (volume : Measure (PSpace P)) ≤ ENNReal.ofReal B := by
    intro s hs
    have hae : ((UnforcedLeray.B0223.heatC (E := SpaceC) s W - W : XC P) :
        PSpace P → SpaceC) =ᵐ[volume]
          fun z => UnforcedLeray.Heat.heatConv (ιx P) s w z - w z := by
      filter_upwards [Lp.coeFn_sub (UnforcedLeray.B0223.heatC (E := SpaceC) s W) W,
        UnforcedLeray.B0223.heatC_rep hs.1 W,
        UnforcedLeray.Heat.heatConv_congr_ae (ιx P) UnforcedLeray.B0223.continuous_ιx.measurable
          s hWw, hWw] with z h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4]
    rw [← eLpNorm_congr_ae hae]
    have hn := hB s hs
    rw [Lp.norm_def] at hn
    have hfin := Lp.eLpNorm_ne_top (UnforcedLeray.B0223.heatC (E := SpaceC) s W - W)
    calc eLpNorm (((UnforcedLeray.B0223.heatC (E := SpaceC) s W - W : XC P) :
          PSpace P → SpaceC)) 2 volume
        = ENNReal.ofReal (eLpNorm (((UnforcedLeray.B0223.heatC (E := SpaceC) s W - W : XC P) :
            PSpace P → SpaceC)) 2 volume).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hn
  have hmink : eLpNorm (fun z => ∫ s in Ioc (0 : ℝ) θ,
      (UnforcedLeray.Heat.heatConv (ιx P) s w z - w z)) 2 (volume : Measure (PSpace P))
      ≤ ENNReal.ofReal θ * ENNReal.ofReal B := by
    calc eLpNorm (fun z => ∫ s in Ioc (0 : ℝ) θ,
          (UnforcedLeray.Heat.heatConv (ιx P) s w z - w z)) 2 (volume : Measure (PSpace P))
        ≤ ∫⁻ s in Ioc (0 : ℝ) θ,
            eLpNorm (fun z => UnforcedLeray.Heat.heatConv (ιx P) s w z - w z) 2
              (volume : Measure (PSpace P)) :=
          UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hmeas (by norm_num) (by simp)
      _ ≤ ∫⁻ _s in Ioc (0 : ℝ) θ, ENNReal.ofReal B :=
          setLIntegral_mono' measurableSet_Ioc hslice
      _ = ENNReal.ofReal θ * ENNReal.ofReal B := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hle : eLpNorm (R : PSpace P → SpaceC) 2 (volume : Measure (PSpace P))
      ≤ ENNReal.ofReal θ * ENNReal.ofReal B := by
    rw [eLpNorm_congr_ae hR]
    exact hmink
  have hfin : ENNReal.ofReal θ * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [Lp.norm_def]
  calc (eLpNorm (R : PSpace P → SpaceC) 2 (volume : Measure (PSpace P))).toReal
      ≤ (ENNReal.ofReal θ * ENNReal.ofReal B).toReal := ENNReal.toReal_mono hfin hle
    _ = θ * B := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le, ENNReal.toReal_ofReal hB0]

/-! ### The right derivative -/

/-- `d/dθ|_{0+} e^{θΔ}Ψ = ΨΔ` in `X` on a `C²` phase test. -/
theorem heatDeriv2 {P : ℝ} [Fact (0 < P)] (ψ : ℝ × Space → CVec3) (hψ : IsPhaseTest2 P ψ)
    (Ψ ΨΔ : XC P) (hΨ : (Ψ : PSpace P → SpaceC) =ᵐ[volume] cellFn ψ)
    (hΔ : (ΨΔ : PSpace P → SpaceC) =ᵐ[volume] cellFn (lapT ψ)) :
    HasDerivWithinAt (fun θ : ℝ => UnforcedLeray.B0223.heatC (E := SpaceC) θ Ψ) ΨΔ
      (Ici 0) 0 := by
  have hw : Measurable (cellFn (P := P) (lapT ψ)) :=
    hψ.continuous_lapT.measurable.comp
      ((measurable_snd.comp (UnforcedLeray.B0223.measurable_toCell (P := P))).prodMk
        (measurable_fst.comp (UnforcedLeray.B0223.measurable_toCell (P := P))))
  have h0 : UnforcedLeray.B0223.heatC (E := SpaceC) 0 Ψ = Ψ :=
    UnforcedLeray.B0223.heatC_of_nonpos le_rfl Ψ
  have h0' : UnforcedLeray.B0223.heatC (E := SpaceC) 0 ΨΔ = ΨΔ :=
    UnforcedLeray.B0223.heatC_of_nonpos le_rfl ΨΔ
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcont := UnforcedLeray.B0223.heatC_continuousOn (P := P) ΨΔ 0 (mem_Ici.2 le_rfl)
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδc⟩ := hcont c hc
  have hev : ∀ᶠ θ in 𝓝[Ici 0] (0 : ℝ), θ ∈ Ici (0 : ℝ) ∧ θ < δ := by
    exact Filter.Eventually.and self_mem_nhdsWithin
      (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hδ))
  filter_upwards [hev] with θ hθ
  obtain ⟨hθ0, hθδ⟩ := hθ
  rw [h0, sub_zero]
  rcases (mem_Ici.1 hθ0).lt_or_eq with hpos | hzero
  · have hB : ∀ s ∈ Ioc (0 : ℝ) θ,
        ‖UnforcedLeray.B0223.heatC (E := SpaceC) s ΨΔ - ΨΔ‖ ≤ c := by
      intro s hs
      have hs' : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact lt_of_le_of_lt hs.2 hθδ
      have := hδc (mem_Ici.2 hs.1.le) hs'
      rw [dist_eq_norm, h0'] at this
      exact this.le
    have hR : ((UnforcedLeray.B0223.heatC (E := SpaceC) θ Ψ - Ψ - θ • ΨΔ : XC P) :
        PSpace P → SpaceC) =ᵐ[volume] fun z => ∫ s in Ioc (0 : ℝ) θ,
          (UnforcedLeray.Heat.heatConv (ιx P) s (cellFn (lapT ψ)) z - cellFn (lapT ψ) z) := by
      filter_upwards [Lp.coeFn_sub (UnforcedLeray.B0223.heatC (E := SpaceC) θ Ψ - Ψ) (θ • ΨΔ),
        Lp.coeFn_sub (UnforcedLeray.B0223.heatC (E := SpaceC) θ Ψ) Ψ, Lp.coeFn_smul θ ΨΔ,
        UnforcedLeray.B0223.heatC_rep hpos Ψ,
        UnforcedLeray.Heat.heatConv_congr_ae (ιx P) UnforcedLeray.B0223.continuous_ιx.measurable
          θ hΨ, hΨ, hΔ] with z e1 e2 e3 e4 e5 e6 e7
      rw [e1, Pi.sub_apply, e2, Pi.sub_apply, e3, Pi.smul_apply, e4, e5, e6, e7]
      exact heat_pointwise2 hψ hpos z
    have hmain := heat_mink2 (cellFn (lapT ψ)) hw hpos ΨΔ hΔ hB _ hR
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    linarith
  · subst hzero
    simp [h0]

end UnforcedLeray.Short.PartIIa.OuterSGen
