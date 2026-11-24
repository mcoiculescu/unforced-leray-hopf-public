import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxDuhamel.CellInt

/-!
# Part III-a, `PartIII-a:T21/3/2/2/3/2`: joint continuity of the smoothed flux pairing

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `FluxPairHeatContinuous` (`Smooth/DuhamelSplit.lean`): `(r, θ) ↦ ⟨F(r), ∇P_θ g⟩` is
continuous on `[a, b] × [-1, 1]` for a flux path `F` continuous on `[a, b]` and a cylinder test `g`.
The bound `|∫_cell f ψ| ≤ ‖f‖_{X_m} (sup|ψ|) K` (weighted Cauchy-Schwarz via `abs_integral_mul_le`,
the `X_{-m}` norm of a bounded function being controlled by that of the constant `1`) gives the
uniform-in-`θ` dependence on `F`; dominated convergence gives the continuity in `θ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem abs_add_mul_le_aux (a b c d Q : ℝ) (h0 : |b| ≤ Q) (h1 : |d| ≤ Q) :
    |a * b + c * d| ≤ (|a| + |c|) * Q := by
  have hQ : 0 ≤ Q := (abs_nonneg _).trans h0
  calc |a * b + c * d| ≤ |a * b| + |c * d| := abs_add_le _ _
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * Q + |c| * Q :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = (|a| + |c|) * Q := by ring

/-- Uniform weighted bound: `|∫_cell f ψ| ≤ ‖f‖_{X_m} · sup|ψ| · K` for a fixed constant `K`. -/
theorem exists_bound_abs_cell (c m : ℝ) (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ (f : UnforcedLeray.B0579.X c m) {ψ : ℝ × ℝ → ℝ}, Continuous ψ → ∀ {M : ℝ},
      (∀ x, |ψ x| ≤ M) →
      |∫ x in UnforcedLeray.B0579.cell c, f x * ψ x| ≤ ‖f‖ * (|M| * K) := by
  have ht1 := memLp_cellMeasure_neg_of_bdd (c := c) hm (g := fun _ : ℝ × ℝ => (1 : ℝ))
    continuous_const (M := 1) (fun x => by simp)
  refine ⟨‖ht1.toLp (fun _ : ℝ × ℝ => (1 : ℝ))‖, fun f ψ hψ M hM => ?_⟩
  have hφ := memLp_cellMeasure_neg_of_bdd (c := c) hm hψ hM
  have hae : (hφ.toLp ψ) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)] ψ :=
    (UnforcedLeray.B0579.ac_cellMeasure c (-m)).ae_le hφ.coeFn_toLp
  have hnorm : ‖hφ.toLp ψ‖ ≤ |M| * ‖ht1.toLp (fun _ : ℝ × ℝ => (1 : ℝ))‖ := by
    have h := Lp.norm_le_norm_of_ae_le (f := hφ.toLp ψ)
      (g := M • ht1.toLp (fun _ : ℝ × ℝ => (1 : ℝ)))
      (by
        filter_upwards [hφ.coeFn_toLp, Lp.coeFn_smul M (ht1.toLp (fun _ : ℝ × ℝ => (1 : ℝ))),
          ht1.coeFn_toLp] with x h1 h2 h3
        have key : ‖ψ x‖ ≤ ‖M‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          exact (hM x).trans (le_abs_self M)
        rw [h1]
        simp only [h2, Pi.smul_apply, smul_eq_mul, h3, mul_one]
        exact key)
    rw [norm_smul, Real.norm_eq_abs] at h
    exact h
  have hint : (∫ x in UnforcedLeray.B0579.cell c, f x * ψ x) =
      ∫ x in UnforcedLeray.B0579.cell c, f x * (hφ.toLp ψ) x :=
    integral_congr_ae (by
      filter_upwards [hae] with x hx
      rw [hx])
  rw [hint]
  exact (UnforcedLeray.B0579.abs_integral_mul_le c m f (hφ.toLp ψ)).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

/-- The flux pairing bounded by the weighted norms of its components. -/
theorem fluxPair_abs_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) {K : ℝ}
    (hK : ∀ (f : UnforcedLeray.B0579.X c m) {ψ : ℝ × ℝ → ℝ}, Continuous ψ → ∀ {M : ℝ},
      (∀ x, |ψ x| ≤ M) → |∫ x in UnforcedLeray.B0579.cell c, f x * ψ x| ≤ ‖f‖ * (|M| * K))
    (G : ActualFlux (c := c) (m := m)) {ψ : ℝ × ℝ → ℝ}
    (hψ0 : Continuous (UnforcedLeray.B0579.pd 0 ψ)) (hψ1 : Continuous (UnforcedLeray.B0579.pd 1 ψ))
    {M : ℝ} (h0 : ∀ x, |UnforcedLeray.B0579.pd 0 ψ x| ≤ M)
    (h1 : ∀ x, |UnforcedLeray.B0579.pd 1 ψ x| ≤ M) :
    |fluxPair hm G ψ| ≤ (‖G 0‖ + ‖G 1‖) * (|M| * K) := by
  have i0 := integrableOn_mul_bdd_cont hm (G 0) hψ0 h0
  have i1 := integrableOn_mul_bdd_cont hm (G 1) hψ1 h1
  unfold fluxPair fluxFn
  rw [integral_add i0 i1]
  refine (abs_add_le _ _).trans ?_
  have a0 := hK (G 0) hψ0 h0
  have a1 := hK (G 1) hψ1 h1
  calc _ ≤ ‖G 0‖ * (|M| * K) + ‖G 1‖ * (|M| * K) := add_le_add a0 a1
    _ = (‖G 0‖ + ‖G 1‖) * (|M| * K) := by ring

/-- Linearity of the flux pairing in the flux (an `L²` identity almost everywhere). -/
theorem fluxPair_sub {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) (F F' : ActualFlux (c := c) (m := m))
    {ψ : ℝ × ℝ → ℝ} (hψ0 : Continuous (UnforcedLeray.B0579.pd 0 ψ))
    (hψ1 : Continuous (UnforcedLeray.B0579.pd 1 ψ)) {M : ℝ}
    (h0 : ∀ x, |UnforcedLeray.B0579.pd 0 ψ x| ≤ M) (h1 : ∀ x, |UnforcedLeray.B0579.pd 1 ψ x| ≤ M) :
    fluxPair hm F ψ - fluxPair hm F' ψ = fluxPair hm (F - F') ψ := by
  have iF0 := integrableOn_mul_bdd_cont hm (F 0) hψ0 h0
  have iF1 := integrableOn_mul_bdd_cont hm (F 1) hψ1 h1
  have iG0 := integrableOn_mul_bdd_cont hm (F' 0) hψ0 h0
  have iG1 := integrableOn_mul_bdd_cont hm (F' 1) hψ1 h1
  have iA : IntegrableOn (fun x => fluxFn F 0 x * UnforcedLeray.B0579.pd 0 ψ x +
      fluxFn F 1 x * UnforcedLeray.B0579.pd 1 ψ x) (UnforcedLeray.B0579.cell c) := iF0.add iF1
  have iB : IntegrableOn (fun x => fluxFn F' 0 x * UnforcedLeray.B0579.pd 0 ψ x +
      fluxFn F' 1 x * UnforcedLeray.B0579.pd 1 ψ x) (UnforcedLeray.B0579.cell c) := iG0.add iG1
  unfold fluxPair
  rw [← integral_sub iA iB]
  apply integral_congr_ae
  filter_upwards [(UnforcedLeray.B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub (F 0) (F' 0)),
    (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub (F 1) (F' 1))] with x e0 e1
  simp only [fluxFn, Pi.sub_apply]
  rw [e0, e1]
  simp only [Pi.sub_apply]
  ring

theorem fluxPairHeatContinuous : FluxPairHeatContinuous := by
  intro c m _ hm F a b hF g hg
  have hc : 0 < c := Fact.out
  obtain ⟨K, hK⟩ := exists_bound_abs_cell c m hm
  obtain ⟨M0, hM0, hb0⟩ := exists_bound_pdWord_cylHeatSmooth hc hg [0]
  obtain ⟨M1, hM1, hb1⟩ := exists_bound_pdWord_cylHeatSmooth hc hg [1]
  have hQ : ∀ (i : Fin 2) (θ : ℝ) (x : ℝ × ℝ),
      |UnforcedLeray.B0579.pd i (cylHeatSmooth c θ g) x| ≤ M0 + M1 := by
    intro i θ x
    fin_cases i
    · exact (hb0 θ x).trans (by linarith)
    · exact (hb1 θ x).trans (by linarith)
  have hjoint : ∀ i : Fin 2, Continuous (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0579.pd i (cylHeatSmooth c p.1 g) p.2) :=
    fun i => continuous_pd_cylHeatSmooth_joint hc hg i
  have hcontθ : ∀ (i : Fin 2) (x : ℝ × ℝ),
      Continuous (fun θ : ℝ => UnforcedLeray.B0579.pd i (cylHeatSmooth c θ g) x) :=
    fun i x => (hjoint i).comp (continuous_id.prodMk continuous_const)
  have hcontx : ∀ (i : Fin 2) (θ : ℝ),
      Continuous (fun x : ℝ × ℝ => UnforcedLeray.B0579.pd i (cylHeatSmooth c θ g) x) :=
    fun i θ => (hjoint i).comp (continuous_const.prodMk continuous_id)
  -- continuity in the time variable, for a fixed flux
  have hθcont : ∀ G : ActualFlux (c := c) (m := m),
      Continuous (fun θ : ℝ => fluxPair hm G (cylHeatSmooth c θ g)) := by
    intro G
    have hI : ∀ i : Fin 2,
        Integrable (fun x => fluxFn G i x) (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      intro i
      have h := integrableOn_mul_bdd_cont hm (G i) (g := fun _ : ℝ × ℝ => (1 : ℝ))
        continuous_const (M := 1) (fun x => by simp)
      have h2 : IntegrableOn (fun x => fluxFn G i x) (UnforcedLeray.B0579.cell c) := by
        simpa [fluxFn] using h
      exact h2
    have hA : ∀ i : Fin 2, AEStronglyMeasurable (fun x => fluxFn G i x)
        (volume.restrict (UnforcedLeray.B0579.cell c)) := fun i =>
      (Lp.aestronglyMeasurable (G i)).mono_ac (UnforcedLeray.B0579.ac_cellMeasure c m)
    have hbnd : ∀ θ : ℝ, ∀ x : ℝ × ℝ,
        ‖fluxFn G 0 x * UnforcedLeray.B0579.pd 0 (cylHeatSmooth c θ g) x +
          fluxFn G 1 x * UnforcedLeray.B0579.pd 1 (cylHeatSmooth c θ g) x‖ ≤
          (|fluxFn G 0 x| + |fluxFn G 1 x|) * (M0 + M1) := fun θ x => by
      rw [Real.norm_eq_abs]
      exact abs_add_mul_le_aux _ _ _ _ _ (hQ 0 θ x) (hQ 1 θ x)
    have hcont := continuous_of_dominated
      (μ := volume.restrict (UnforcedLeray.B0579.cell c))
      (F := fun θ x => fluxFn G 0 x * UnforcedLeray.B0579.pd 0 (cylHeatSmooth c θ g) x +
        fluxFn G 1 x * UnforcedLeray.B0579.pd 1 (cylHeatSmooth c θ g) x)
      (bound := fun x => (|fluxFn G 0 x| + |fluxFn G 1 x|) * (M0 + M1))
      (fun θ => ((hA 0).mul (hcontx 0 θ).aestronglyMeasurable).add
        ((hA 1).mul (hcontx 1 θ).aestronglyMeasurable))
      (fun θ => Eventually.of_forall fun x => hbnd θ x)
      (((hI 0).abs.add (hI 1).abs).mul_const (M0 + M1))
      (Eventually.of_forall fun x =>
        (continuous_const.mul (hcontθ 0 x)).add (continuous_const.mul (hcontθ 1 x)))
    exact hcont
  -- joint continuity
  intro p0 hp0
  have hΨc : Continuous (fun p : ℝ × ℝ => fluxPair hm (F p0.1) (cylHeatSmooth c p.2 g)) :=
    (hθcont (F p0.1)).comp continuous_snd
  have hFt : ∀ i : Fin 2, Tendsto (fun p : ℝ × ℝ => ‖F p.1 i - F p0.1 i‖)
      (𝓝[Icc a b ×ˢ Icc (-1 : ℝ) 1] p0) (𝓝 0) := by
    intro i
    have hcontF : ContinuousOn (fun r => F r i) (Icc a b) :=
      (continuous_apply i).comp_continuousOn hF
    have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[Icc a b ×ˢ Icc (-1 : ℝ) 1] p0)
        (𝓝[Icc a b] p0.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun p hp => hp.1⟩
    have h1 : Tendsto (fun p : ℝ × ℝ => F p.1 i) (𝓝[Icc a b ×ˢ Icc (-1 : ℝ) 1] p0)
        (𝓝 (F p0.1 i)) :=
      (hcontF p0.1 hp0.1).tendsto.comp hfst
    exact tendsto_iff_norm_sub_tendsto_zero.1 h1
  have hsq : Tendsto (fun p : ℝ × ℝ => (|M0 + M1| * K) *
      (‖F p.1 0 - F p0.1 0‖ + ‖F p.1 1 - F p0.1 1‖))
      (𝓝[Icc a b ×ˢ Icc (-1 : ℝ) 1] p0) (𝓝 0) := by
    have := ((hFt 0).add (hFt 1)).const_mul (|M0 + M1| * K)
    simpa using this
  have hdiff : Tendsto (fun p : ℝ × ℝ => fluxPair hm (F p.1) (cylHeatSmooth c p.2 g) -
      fluxPair hm (F p0.1) (cylHeatSmooth c p.2 g)) (𝓝[Icc a b ×ˢ Icc (-1 : ℝ) 1] p0) (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun p => ?_) hsq
    rw [fluxPair_sub hm (F p.1) (F p0.1) (hcontx 0 p.2) (hcontx 1 p.2)
      (fun x => hQ 0 p.2 x) (fun x => hQ 1 p.2 x), Real.norm_eq_abs]
    have h := fluxPair_abs_le hm hK (F p.1 - F p0.1) (hcontx 0 p.2) (hcontx 1 p.2)
      (fun x => hQ 0 p.2 x) (fun x => hQ 1 p.2 x)
    simp only [Pi.sub_apply] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have e : (fun p : ℝ × ℝ => fluxPair hm (F p.1) (cylHeatSmooth c p.2 g)) =
      fun p => (fluxPair hm (F p.1) (cylHeatSmooth c p.2 g) -
        fluxPair hm (F p0.1) (cylHeatSmooth c p.2 g)) +
        fluxPair hm (F p0.1) (cylHeatSmooth c p.2 g) :=
    funext fun p => (sub_add_cancel _ _).symm
  have hfin := hdiff.add ((hΨc.tendsto p0).mono_left nhdsWithin_le_nhds)
  rw [zero_add] at hfin
  rw [ContinuousWithinAt, e]
  exact hfin

end UnforcedLeray.Short.IIIa.Exist
