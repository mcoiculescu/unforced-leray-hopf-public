import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# `GEQInletGlobal` from the ring-lift calculus (decomposition)

Source `the November 2 reference manuscript`
lines 2562-2564 (Hölder step needs `∂e ∈ L^{2q₀}`, `∂²e ∈ L^{q₀}`, `e ∈ L^∞` on the cell),
2385-2387 (the inlet jets decay in `η`), 1515-1531.

Only qualitative finiteness is needed, so no uniformity in `Σ = p.ageCut` is required: for each
fixed `p` the profile `b = ∑ αᵢ ψᵢ` is smooth, `ξ`-periodic, vanishes for `s ≥ H/2`, and its jets of
order `≤ 2` decay like `e^{-κ|η|/c}` for *some* `C, κ`.  The `R³` integrability then follows from the
chart `(s, ξ, η) = (R²/ϱ², …, Ry₃/ϱ)` of the ring lift `Nv`: with `ϱ⁻¹ = √s / R`,
`|∂Nv| ≲ s · J₁`, `|∂²Nv| ≲ s^{3/2} · J₂` (`J_l` the chart jets times `(1+s+|η|)^l`), and
`P⁻¹∫∫|Nv b|^q = πR² ∫ |b|^q dageμ(q/2-5/2)` (`Axi.lintegral_Nv_rpow`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The hypotheses on a chart profile `b` used by the `R³` calculus: smooth, `c`-periodic in `ξ`,
zero for `s ≥ T`, and jets of order `≤ 2` bounded by `C e^{-κ|η|/c}`. -/
def InletProfHyp (c T C κ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) : Prop :=
  ContDiff ℝ ∞ b ∧ (∀ s ξ η : ℝ, b (s, (ξ + c, η)) = b (s, (ξ, η))) ∧
  (∀ m : ℝ × (ℝ × ℝ), T ≤ m.1 → b m = 0) ∧
  ∀ l ≤ 2, ∀ m : ℝ × (ℝ × ℝ), ‖iteratedFDeriv ℝ l b m‖ ≤ C * Real.exp (-(κ * |m.2.2| / c))

/-- **Sub1: the inlet profile combination satisfies the hypotheses** (source 2347-2369, 2385-2387;
the proof is `IIb.frozenStreamBounds` for `periodicStream p.c` with `c ≥ 1`, the cutoff `ageCutoff`
vanishing for `s ≥ H/2` (`ageCutoff_eq_zero`), `inletProfile_periodic`, and the jet formulas of
`IIb.inletJetDecay`/`CutStreamJets`/`RingStreamJetsDecay` — here the constants `C, κ` may depend on
`p` including `ageCut`, only `κ > 0` is needed). -/
def InletProfGlobal : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ 1 →
      p.mode = q → ∀ α : Fin 2 → ℝ, ∃ C κ : ℝ, 0 < κ ∧
        InletProfHyp p.c (p.H / 2) C κ (∑ i : Fin 2, α i • p.inletProfile i)

/-- **Sub2: first-derivative pointwise bound of the ring lift** (chain rule through
`age R y = R²/ϱ²`, `phase`, `trans`; `ϱ⁻¹ = √s/R`; `Axi.Nv`, `Axi.chart`): `∂_{y_j}` of
`(τ,y) ↦ realC (Nv R b τ y)` is bounded by `K C s (1+T+|η|)² e^{-κ|η|/c}` on `s = age R y ≤ T`
and vanishes for `age R y > T`. `K` depends on `R` only. -/
def NvFirstPt : Prop :=
  ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 < K ∧ ∀ (c T C κ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid),
    InletProfHyp c T C κ b → ∀ (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space),
      ‖dy j (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b x.1 x.2)) (τ, y)‖ ≤
        if age R y ≤ T then
          K * C * age R y * (1 + T + |trans R y|) ^ 2 * Real.exp (-(κ * |trans R y| / c))
        else 0

/-- **Sub3: second-derivative pointwise bound of the ring lift** (as Sub2, one more derivative):
`≤ K C s^{3/2} (1+T+|η|)² e^{-κ|η|/c}` on `age R y ≤ T`, zero beyond. -/
def NvSecondPt : Prop :=
  ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 < K ∧ ∀ (c T C κ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid),
    InletProfHyp c T C κ b → ∀ (j k : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space),
      ‖dy j (dy k (fun x : ℝ × UnforcedLeray.Space =>
          UnforcedLeray.B0412.realC (Nv R b x.1 x.2))) (τ, y)‖ ≤
        if age R y ≤ T then
          K * C * age R y ^ (3 / 2 : ℝ) * (1 + T + |trans R y|) ^ 2 *
            Real.exp (-(κ * |trans R y| / c))
        else 0

/-- **Sub4: `L^q` of a chart-majorized field on `(0,P] × ℝ³`** (`Axi.lintegral_Nv_rpow` with the
majorant profile, then `Axi.lintegral_ageμ`: the integral is
`πR² ∫_{(0,T]×cell} s^{kq-5/2}(1+T+|η|)^{Nq}e^{-qκ|η|/c} c⁻¹ < ∞` as `kq > 3/2`). -/
def MajLp : Prop :=
  ∀ (R c P T κ k qr M : ℝ) (N : ℕ) (q : ℝ≥0∞), 0 < R → 0 < c → P = 2 * c / R → 0 < T → 0 < κ →
    q = ENNReal.ofReal qr → 0 < qr → 3 / 2 < k * qr →
    ∀ F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3, Continuous F →
      (∀ (τ : ℝ) (y : UnforcedLeray.Space), ‖F (τ, y)‖ ≤
        if age R y ≤ T then
          M * age R y ^ k * (1 + T + |trans R y|) ^ N * Real.exp (-(κ * |trans R y| / c))
        else 0) →
      MemLp F q ((volume.restrict (Ioc (0 : ℝ) P)).prod volume)

/-- **Sub5: the ring lift is bounded** (`‖Nv R b τ y‖ = √(age R y) ‖b(chart)‖ ≤ √T · C`, using
`b = 0` for `age R y ≥ T`; `Axi.norm_Nv`; on the axis `age R y = 0`). -/
def NvBdd : Prop :=
  ∀ (R c T C κ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid), 0 < c → 0 ≤ κ → 0 ≤ T → InletProfHyp c T C κ b →
    ∀ (τ : ℝ) (y : UnforcedLeray.Space),
      ‖UnforcedLeray.B0412.realC (Nv R b τ y)‖ ≤ Real.sqrt T * C

/-- The affine inlet is the ring lift of the combination profile. -/
theorem eFun_eq_Nv (p : Params) (α : Fin 2 → ℝ) :
    p.eFun α = fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (Nv p.R (∑ i : Fin 2, α i • p.inletProfile i) x.1 x.2) := by
  funext x
  simp only [Params.eFun, Params.inlet, Fin.sum_univ_two, Nv_add, Nv_smul]

theorem gEQInletGlobal_of (h1 : InletProfGlobal) (h2 : NvFirstPt) (h3 : NvSecondPt)
    (h4 : MajLp) (h5 : NvBdd) : GEQInletGlobal := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g _hd j k
  obtain ⟨C, κ, hκ, hprof⟩ := h1 lam q hq dm dp hdm p d hreg hν hmode (p.coord z)
  have hH : 0 < p.H / 2 := half_pos p.H_pos
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  have hP : p.period = 2 * p.c / p.R := p.period_eq
  rw [eFun_eq_Nv] at hsm ⊢
  obtain ⟨K1, hK1, H1⟩ := h2 p.R p.R_pos
  obtain ⟨K2, hK2, H2⟩ := h3 p.R p.R_pos
  have hq0 : (2 * UnforcedLeray.B0412.q0E) = ENNReal.ofReal (11 / 2) := by
    rw [UnforcedLeray.B0412.q0E, UnforcedLeray.B0281.q0_eq,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hq1 : UnforcedLeray.B0412.q0E = ENNReal.ofReal (11 / 4) := by
    rw [UnforcedLeray.B0412.q0E, UnforcedLeray.B0281.q0_eq]
  refine ⟨?_, ?_, ?_⟩
  · refine h4 p.R p.c p.period (p.H / 2) κ 1 (11 / 2) (K1 * C) 2 _ p.R_pos p.c_pos hP hH hκ hq0
      (by norm_num) (by norm_num) _ (contDiff_dyT hsm j).continuous ?_
    intro τ y
    have h := H1 _ _ _ _ _ hprof j τ y
    by_cases hc : age p.R y ≤ p.H / 2
    · rw [if_pos hc] at h ⊢
      rw [Real.rpow_one]
      exact h
    · rw [if_neg hc] at h ⊢
      exact h
  · refine h4 p.R p.c p.period (p.H / 2) κ (3 / 2) (11 / 4) (K2 * C) 2 _ p.R_pos p.c_pos hP hH hκ
      hq1 (by norm_num) (by norm_num) _ (contDiff_dyT (contDiff_dyT hsm k) j).continuous ?_
    intro τ y
    have h := H2 _ _ _ _ _ hprof j k τ y
    by_cases hc : age p.R y ≤ p.H / 2
    · rw [if_pos hc] at h ⊢
      exact h
    · rw [if_neg hc] at h ⊢
      exact h
  · exact ⟨Real.sqrt (p.H / 2) * C, fun x => h5 p.R p.c (p.H / 2) C κ _ p.c_pos hκ.le hH.le hprof x.1 x.2⟩

end UnforcedLeray.Short.PartIIIb.Concrete
